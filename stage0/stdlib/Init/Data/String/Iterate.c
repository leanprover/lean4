// Lean compiler output
// Module: Init.Data.String.Iterate
// Imports: public import Init.Data.String.Basic public import Init.Data.String.FindPos public import Init.Data.Iterators.Combinators.FilterMap public import Init.Data.Iterators.Consumers.Loop import Init.Omega import Init.Data.Iterators.Consumers.Collect import Init.Data.String.Lemmas.FindPos
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_positions(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_positions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_chars(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_chars___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_length(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_length___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revPositions(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revPositions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revChars(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revChars___boxed(lean_object*);
static const lean_string_object l_String_Slice_instInhabitedByteIterator_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_Slice_instInhabitedByteIterator_default___closed__0 = (const lean_object*)&l_String_Slice_instInhabitedByteIterator_default___closed__0_value;
static const lean_ctor_object l_String_Slice_instInhabitedByteIterator_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_instInhabitedByteIterator_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_instInhabitedByteIterator_default___closed__1 = (const lean_object*)&l_String_Slice_instInhabitedByteIterator_default___closed__1_value;
static const lean_ctor_object l_String_Slice_instInhabitedByteIterator_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_instInhabitedByteIterator_default___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_instInhabitedByteIterator_default___closed__2 = (const lean_object*)&l_String_Slice_instInhabitedByteIterator_default___closed__2_value;
LEAN_EXPORT const lean_object* l_String_Slice_instInhabitedByteIterator_default = (const lean_object*)&l_String_Slice_instInhabitedByteIterator_default___closed__2_value;
LEAN_EXPORT const lean_object* l_String_Slice_instInhabitedByteIterator = (const lean_object*)&l_String_Slice_instInhabitedByteIterator_default___closed__2_value;
LEAN_EXPORT lean_object* l_String_Slice_bytes(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revBytes(lean_object*);
static const lean_ctor_object l_String_Slice_instInhabitedRevByteIterator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_instInhabitedByteIterator_default___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_instInhabitedRevByteIterator___closed__0 = (const lean_object*)&l_String_Slice_instInhabitedRevByteIterator___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instInhabitedRevByteIterator = (const lean_object*)&l_String_Slice_instInhabitedRevByteIterator___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_foldl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_positionsFrom___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_positionsFrom___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_positionsFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_positionsFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_positions(lean_object*);
LEAN_EXPORT lean_object* l_String_positions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_chars(lean_object*);
LEAN_EXPORT lean_object* l_String_chars___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_revPositionsFrom___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_revPositionsFrom___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_revPositionsFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revPositionsFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_revPositions(lean_object*);
LEAN_EXPORT lean_object* l_String_revPositions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_revChars(lean_object*);
LEAN_EXPORT lean_object* l_String_byteIterator(lean_object*);
LEAN_EXPORT lean_object* l_String_revBytes(lean_object*);
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_string_foldl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default(lean_object* v_s_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default___boxed(lean_object* v_s_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_String_Slice_instInhabitedPosIterator_default(v_s_3_);
lean_dec_ref(v_s_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator(lean_object* v_a_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(0u);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator___boxed(lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_String_Slice_instInhabitedPosIterator(v_a_7_);
lean_dec_ref(v_a_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___redArg(lean_object* v_p_9_){
_start:
{
lean_inc(v_p_9_);
return v_p_9_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___redArg___boxed(lean_object* v_p_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_String_Slice_positionsFrom___redArg(v_p_10_);
lean_dec(v_p_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom(lean_object* v_s_12_, lean_object* v_p_13_){
_start:
{
lean_inc(v_p_13_);
return v_p_13_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___boxed(lean_object* v_s_14_, lean_object* v_p_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_String_Slice_positionsFrom(v_s_14_, v_p_15_);
lean_dec(v_p_15_);
lean_dec_ref(v_s_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positions(lean_object* v_s_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(0u);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positions___boxed(lean_object* v_s_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_String_Slice_positions(v_s_19_);
lean_dec_ref(v_s_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(lean_object* v_s_21_, lean_object* v_inst_22_, lean_object* v_x_23_){
_start:
{
lean_object* v_str_24_; lean_object* v_startInclusive_25_; lean_object* v_endExclusive_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v_str_24_ = lean_ctor_get(v_s_21_, 0);
v_startInclusive_25_ = lean_ctor_get(v_s_21_, 1);
v_endExclusive_26_ = lean_ctor_get(v_s_21_, 2);
v___x_27_ = lean_nat_sub(v_endExclusive_26_, v_startInclusive_25_);
v___x_28_ = lean_nat_dec_eq(v_x_23_, v___x_27_);
lean_dec(v___x_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_29_ = lean_nat_add(v_startInclusive_25_, v_x_23_);
v___x_30_ = lean_string_utf8_next_fast(v_str_24_, v___x_29_);
lean_dec(v___x_29_);
v___x_31_ = lean_nat_sub(v___x_30_, v_startInclusive_25_);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v_x_23_);
v___x_33_ = lean_apply_2(v_inst_22_, lean_box(0), v___x_32_);
return v___x_33_;
}
else
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v_x_23_);
v___x_34_ = lean_box(2);
v___x_35_ = lean_apply_2(v_inst_22_, lean_box(0), v___x_34_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(lean_object* v_s_36_, lean_object* v_inst_37_, lean_object* v_x_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(v_s_36_, v_inst_37_, v_x_38_);
lean_dec_ref(v_s_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(lean_object* v_s_40_, lean_object* v_inst_41_){
_start:
{
lean_object* v___f_42_; 
v___f_42_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_42_, 0, v_s_40_);
lean_closure_set(v___f_42_, 1, v_inst_41_);
return v___f_42_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure(lean_object* v_m_43_, lean_object* v_s_44_, lean_object* v_inst_45_){
_start:
{
lean_object* v___f_46_; 
v___f_46_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_46_, 0, v_s_44_);
lean_closure_set(v___f_46_, 1, v_inst_45_);
return v___f_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation(lean_object* v_m_47_, lean_object* v_s_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_box(0);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___boxed(lean_object* v_m_51_, lean_object* v_s_52_, lean_object* v_inst_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation(v_m_51_, v_s_52_, v_inst_53_);
lean_dec(v_inst_53_);
lean_dec_ref(v_s_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(lean_object* v_toPure_55_, lean_object* v_recur_56_, lean_object* v_it_57_, lean_object* v_____do__lift_58_){
_start:
{
if (lean_obj_tag(v_____do__lift_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_60_; 
lean_dec(v_it_57_);
lean_dec(v_recur_56_);
v_a_59_ = lean_ctor_get(v_____do__lift_58_, 0);
lean_inc(v_a_59_);
lean_dec_ref(v_____do__lift_58_);
v___x_60_ = lean_apply_2(v_toPure_55_, lean_box(0), v_a_59_);
return v___x_60_;
}
else
{
lean_object* v_a_61_; lean_object* v___x_62_; 
lean_dec(v_toPure_55_);
v_a_61_ = lean_ctor_get(v_____do__lift_58_, 0);
lean_inc(v_a_61_);
lean_dec_ref(v_____do__lift_58_);
v___x_62_ = lean_apply_4(v_recur_56_, v_it_57_, v_a_61_, lean_box(0), lean_box(0));
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1(lean_object* v_toPure_63_, lean_object* v_recur_64_, lean_object* v___y_65_, lean_object* v_acc_66_, lean_object* v_toBind_67_, lean_object* v_s_68_){
_start:
{
switch(lean_obj_tag(v_s_68_))
{
case 0:
{
lean_object* v_it_69_; lean_object* v_out_70_; lean_object* v___f_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_it_69_ = lean_ctor_get(v_s_68_, 0);
lean_inc(v_it_69_);
v_out_70_ = lean_ctor_get(v_s_68_, 1);
lean_inc(v_out_70_);
lean_dec_ref(v_s_68_);
v___f_71_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_71_, 0, v_toPure_63_);
lean_closure_set(v___f_71_, 1, v_recur_64_);
lean_closure_set(v___f_71_, 2, v_it_69_);
v___x_72_ = lean_apply_3(v___y_65_, v_out_70_, lean_box(0), v_acc_66_);
v___x_73_ = lean_apply_4(v_toBind_67_, lean_box(0), lean_box(0), v___x_72_, v___f_71_);
return v___x_73_;
}
case 1:
{
lean_object* v_it_74_; lean_object* v___x_75_; 
lean_dec(v_toBind_67_);
lean_dec(v___y_65_);
lean_dec(v_toPure_63_);
v_it_74_ = lean_ctor_get(v_s_68_, 0);
lean_inc(v_it_74_);
lean_dec_ref(v_s_68_);
v___x_75_ = lean_apply_4(v_recur_64_, v_it_74_, v_acc_66_, lean_box(0), lean_box(0));
return v___x_75_;
}
default: 
{
lean_object* v___x_76_; 
lean_dec(v_toBind_67_);
lean_dec(v___y_65_);
lean_dec(v_recur_64_);
v___x_76_ = lean_apply_2(v_toPure_63_, lean_box(0), v_acc_66_);
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(lean_object* v_s_77_, lean_object* v_toPure_78_, lean_object* v___y_79_, lean_object* v_toBind_80_, lean_object* v_toPure_81_, lean_object* v_lift_82_, lean_object* v_it_83_, lean_object* v_acc_84_, lean_object* v_hP_85_, lean_object* v_recur_86_){
_start:
{
lean_object* v_str_87_; lean_object* v_startInclusive_88_; lean_object* v_endExclusive_89_; lean_object* v___f_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_str_87_ = lean_ctor_get(v_s_77_, 0);
v_startInclusive_88_ = lean_ctor_get(v_s_77_, 1);
v_endExclusive_89_ = lean_ctor_get(v_s_77_, 2);
v___f_90_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_90_, 0, v_toPure_78_);
lean_closure_set(v___f_90_, 1, v_recur_86_);
lean_closure_set(v___f_90_, 2, v___y_79_);
lean_closure_set(v___f_90_, 3, v_acc_84_);
lean_closure_set(v___f_90_, 4, v_toBind_80_);
v___x_91_ = lean_nat_sub(v_endExclusive_89_, v_startInclusive_88_);
v___x_92_ = lean_nat_dec_eq(v_it_83_, v___x_91_);
lean_dec(v___x_91_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_93_ = lean_nat_add(v_startInclusive_88_, v_it_83_);
v___x_94_ = lean_string_utf8_next_fast(v_str_87_, v___x_93_);
lean_dec(v___x_93_);
v___x_95_ = lean_nat_sub(v___x_94_, v_startInclusive_88_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v_it_83_);
v___x_97_ = lean_apply_2(v_toPure_81_, lean_box(0), v___x_96_);
v___x_98_ = lean_apply_4(v_lift_82_, lean_box(0), lean_box(0), v___f_90_, v___x_97_);
return v___x_98_;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_it_83_);
v___x_99_ = lean_box(2);
v___x_100_ = lean_apply_2(v_toPure_81_, lean_box(0), v___x_99_);
v___x_101_ = lean_apply_4(v_lift_82_, lean_box(0), lean_box(0), v___f_90_, v___x_100_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(lean_object* v_s_102_, lean_object* v_toPure_103_, lean_object* v___y_104_, lean_object* v_toBind_105_, lean_object* v_toPure_106_, lean_object* v_lift_107_, lean_object* v_it_108_, lean_object* v_acc_109_, lean_object* v_hP_110_, lean_object* v_recur_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(v_s_102_, v_toPure_103_, v___y_104_, v_toBind_105_, v_toPure_106_, v_lift_107_, v_it_108_, v_acc_109_, v_hP_110_, v_recur_111_);
lean_dec_ref(v_s_102_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__3(lean_object* v_inst_113_, lean_object* v_s_114_, lean_object* v_toPure_115_, lean_object* v_lift_116_, lean_object* v_00_u03b3_117_, lean_object* v_Pl_118_, lean_object* v_it_119_, lean_object* v_init_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_toApplicative_122_; lean_object* v_toBind_123_; lean_object* v_toPure_124_; lean_object* v___f_125_; lean_object* v___x_126_; 
v_toApplicative_122_ = lean_ctor_get(v_inst_113_, 0);
lean_inc_ref(v_toApplicative_122_);
v_toBind_123_ = lean_ctor_get(v_inst_113_, 1);
lean_inc(v_toBind_123_);
lean_dec_ref(v_inst_113_);
v_toPure_124_ = lean_ctor_get(v_toApplicative_122_, 1);
lean_inc(v_toPure_124_);
lean_dec_ref(v_toApplicative_122_);
v___f_125_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed), 10, 6);
lean_closure_set(v___f_125_, 0, v_s_114_);
lean_closure_set(v___f_125_, 1, v_toPure_124_);
lean_closure_set(v___f_125_, 2, v___y_121_);
lean_closure_set(v___f_125_, 3, v_toBind_123_);
lean_closure_set(v___f_125_, 4, v_toPure_115_);
lean_closure_set(v___f_125_, 5, v_lift_116_);
v___x_126_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_125_, v_it_119_, v_init_120_, lean_box(0));
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(lean_object* v_s_127_, lean_object* v_inst_128_, lean_object* v_inst_129_){
_start:
{
lean_object* v_toApplicative_130_; lean_object* v_toPure_131_; lean_object* v___f_132_; 
v_toApplicative_130_ = lean_ctor_get(v_inst_128_, 0);
lean_inc_ref(v_toApplicative_130_);
lean_dec_ref(v_inst_128_);
v_toPure_131_ = lean_ctor_get(v_toApplicative_130_, 1);
lean_inc(v_toPure_131_);
lean_dec_ref(v_toApplicative_130_);
v___f_132_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_132_, 0, v_inst_129_);
lean_closure_set(v___f_132_, 1, v_s_127_);
lean_closure_set(v___f_132_, 2, v_toPure_131_);
return v___f_132_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(lean_object* v_m_133_, lean_object* v_n_134_, lean_object* v_s_135_, lean_object* v_inst_136_, lean_object* v_inst_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(v_s_135_, v_inst_136_, v_inst_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_chars(lean_object* v_s_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_unsigned_to_nat(0u);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_chars___boxed(lean_object* v_s_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_String_Slice_chars(v_s_141_);
lean_dec_ref(v_s_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(lean_object* v_s_143_, lean_object* v_a_144_, lean_object* v_b_145_){
_start:
{
lean_object* v_str_146_; lean_object* v_startInclusive_147_; lean_object* v_endExclusive_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v_str_146_ = lean_ctor_get(v_s_143_, 0);
v_startInclusive_147_ = lean_ctor_get(v_s_143_, 1);
v_endExclusive_148_ = lean_ctor_get(v_s_143_, 2);
v___x_149_ = lean_nat_sub(v_endExclusive_148_, v_startInclusive_147_);
v___x_150_ = lean_nat_dec_eq(v_a_144_, v___x_149_);
lean_dec(v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_151_ = lean_nat_add(v_startInclusive_147_, v_a_144_);
lean_dec(v_a_144_);
v___x_152_ = lean_string_utf8_next_fast(v_str_146_, v___x_151_);
lean_dec(v___x_151_);
v___x_153_ = lean_nat_sub(v___x_152_, v_startInclusive_147_);
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_b_145_, v___x_154_);
lean_dec(v_b_145_);
v_a_144_ = v___x_153_;
v_b_145_ = v___x_155_;
goto _start;
}
else
{
lean_dec(v_a_144_);
return v_b_145_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg___boxed(lean_object* v_s_157_, lean_object* v_a_158_, lean_object* v_b_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(v_s_157_, v_a_158_, v_b_159_);
lean_dec_ref(v_s_157_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_length(lean_object* v_s_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(v_s_161_, v___x_162_, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_length___boxed(lean_object* v_s_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_String_Slice_length(v_s_164_);
lean_dec_ref(v_s_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0(lean_object* v_s_166_, lean_object* v_inst_167_, lean_object* v_R_168_, lean_object* v_a_169_, lean_object* v_b_170_, lean_object* v_c_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(v_s_166_, v_a_169_, v_b_170_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___boxed(lean_object* v_s_173_, lean_object* v_inst_174_, lean_object* v_R_175_, lean_object* v_a_176_, lean_object* v_b_177_, lean_object* v_c_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0(v_s_173_, v_inst_174_, v_R_175_, v_a_176_, v_b_177_, v_c_178_);
lean_dec_ref(v_s_173_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default(lean_object* v_s_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_unsigned_to_nat(0u);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default___boxed(lean_object* v_s_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_String_Slice_instInhabitedRevPosIterator_default(v_s_182_);
lean_dec_ref(v_s_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator(lean_object* v_a_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_unsigned_to_nat(0u);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator___boxed(lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_String_Slice_instInhabitedRevPosIterator(v_a_186_);
lean_dec_ref(v_a_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___redArg(lean_object* v_p_188_){
_start:
{
lean_inc(v_p_188_);
return v_p_188_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___redArg___boxed(lean_object* v_p_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_String_Slice_revPositionsFrom___redArg(v_p_189_);
lean_dec(v_p_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom(lean_object* v_s_191_, lean_object* v_p_192_){
_start:
{
lean_inc(v_p_192_);
return v_p_192_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___boxed(lean_object* v_s_193_, lean_object* v_p_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_String_Slice_revPositionsFrom(v_s_193_, v_p_194_);
lean_dec(v_p_194_);
lean_dec_ref(v_s_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositions(lean_object* v_s_196_){
_start:
{
lean_object* v_startInclusive_197_; lean_object* v_endExclusive_198_; lean_object* v___x_199_; 
v_startInclusive_197_ = lean_ctor_get(v_s_196_, 1);
v_endExclusive_198_ = lean_ctor_get(v_s_196_, 2);
v___x_199_ = lean_nat_sub(v_endExclusive_198_, v_startInclusive_197_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositions___boxed(lean_object* v_s_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_String_Slice_revPositions(v_s_200_);
lean_dec_ref(v_s_200_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(lean_object* v_s_202_, lean_object* v_inst_203_, lean_object* v_x_204_){
_start:
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_nat_dec_eq(v_x_204_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_prevPos_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_sub(v_x_204_, v___x_207_);
v_prevPos_209_ = l_String_Slice_posLE(v_s_202_, v___x_208_);
lean_inc(v_prevPos_209_);
v___x_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_210_, 0, v_prevPos_209_);
lean_ctor_set(v___x_210_, 1, v_prevPos_209_);
v___x_211_ = lean_apply_2(v_inst_203_, lean_box(0), v___x_210_);
return v___x_211_;
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_box(2);
v___x_213_ = lean_apply_2(v_inst_203_, lean_box(0), v___x_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(lean_object* v_s_214_, lean_object* v_inst_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(v_s_214_, v_inst_215_, v_x_216_);
lean_dec(v_x_216_);
lean_dec_ref(v_s_214_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(lean_object* v_s_218_, lean_object* v_inst_219_){
_start:
{
lean_object* v___f_220_; 
v___f_220_ = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_220_, 0, v_s_218_);
lean_closure_set(v___f_220_, 1, v_inst_219_);
return v___f_220_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure(lean_object* v_m_221_, lean_object* v_s_222_, lean_object* v_inst_223_){
_start:
{
lean_object* v___f_224_; 
v___f_224_ = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_224_, 0, v_s_222_);
lean_closure_set(v___f_224_, 1, v_inst_223_);
return v___f_224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation(lean_object* v_m_225_, lean_object* v_s_226_, lean_object* v_inst_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = lean_box(0);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___boxed(lean_object* v_m_229_, lean_object* v_s_230_, lean_object* v_inst_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation(v_m_229_, v_s_230_, v_inst_231_);
lean_dec(v_inst_231_);
lean_dec_ref(v_s_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(lean_object* v_toPure_233_, lean_object* v___y_234_, lean_object* v_toBind_235_, lean_object* v_s_236_, lean_object* v_toPure_237_, lean_object* v_lift_238_, lean_object* v_it_239_, lean_object* v_acc_240_, lean_object* v_hP_241_, lean_object* v_recur_242_){
_start:
{
lean_object* v___f_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___f_243_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_243_, 0, v_toPure_233_);
lean_closure_set(v___f_243_, 1, v_recur_242_);
lean_closure_set(v___f_243_, 2, v___y_234_);
lean_closure_set(v___f_243_, 3, v_acc_240_);
lean_closure_set(v___f_243_, 4, v_toBind_235_);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_nat_dec_eq(v_it_239_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v_prevPos_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = lean_nat_sub(v_it_239_, v___x_246_);
v_prevPos_248_ = l_String_Slice_posLE(v_s_236_, v___x_247_);
lean_inc(v_prevPos_248_);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v_prevPos_248_);
lean_ctor_set(v___x_249_, 1, v_prevPos_248_);
v___x_250_ = lean_apply_2(v_toPure_237_, lean_box(0), v___x_249_);
v___x_251_ = lean_apply_4(v_lift_238_, lean_box(0), lean_box(0), v___f_243_, v___x_250_);
return v___x_251_;
}
else
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_box(2);
v___x_253_ = lean_apply_2(v_toPure_237_, lean_box(0), v___x_252_);
v___x_254_ = lean_apply_4(v_lift_238_, lean_box(0), lean_box(0), v___f_243_, v___x_253_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(lean_object* v_toPure_255_, lean_object* v___y_256_, lean_object* v_toBind_257_, lean_object* v_s_258_, lean_object* v_toPure_259_, lean_object* v_lift_260_, lean_object* v_it_261_, lean_object* v_acc_262_, lean_object* v_hP_263_, lean_object* v_recur_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(v_toPure_255_, v___y_256_, v_toBind_257_, v_s_258_, v_toPure_259_, v_lift_260_, v_it_261_, v_acc_262_, v_hP_263_, v_recur_264_);
lean_dec(v_it_261_);
lean_dec_ref(v_s_258_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(lean_object* v_inst_266_, lean_object* v_s_267_, lean_object* v_toPure_268_, lean_object* v_lift_269_, lean_object* v_00_u03b3_270_, lean_object* v_Pl_271_, lean_object* v_it_272_, lean_object* v_init_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_toApplicative_275_; lean_object* v_toBind_276_; lean_object* v_toPure_277_; lean_object* v___f_278_; lean_object* v___x_279_; 
v_toApplicative_275_ = lean_ctor_get(v_inst_266_, 0);
lean_inc_ref(v_toApplicative_275_);
v_toBind_276_ = lean_ctor_get(v_inst_266_, 1);
lean_inc(v_toBind_276_);
lean_dec_ref(v_inst_266_);
v_toPure_277_ = lean_ctor_get(v_toApplicative_275_, 1);
lean_inc(v_toPure_277_);
lean_dec_ref(v_toApplicative_275_);
v___f_278_ = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed), 10, 6);
lean_closure_set(v___f_278_, 0, v_toPure_277_);
lean_closure_set(v___f_278_, 1, v___y_274_);
lean_closure_set(v___f_278_, 2, v_toBind_276_);
lean_closure_set(v___f_278_, 3, v_s_267_);
lean_closure_set(v___f_278_, 4, v_toPure_268_);
lean_closure_set(v___f_278_, 5, v_lift_269_);
v___x_279_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_278_, v_it_272_, v_init_273_, lean_box(0));
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(lean_object* v_s_280_, lean_object* v_inst_281_, lean_object* v_inst_282_){
_start:
{
lean_object* v_toApplicative_283_; lean_object* v_toPure_284_; lean_object* v___f_285_; 
v_toApplicative_283_ = lean_ctor_get(v_inst_281_, 0);
lean_inc_ref(v_toApplicative_283_);
lean_dec_ref(v_inst_281_);
v_toPure_284_ = lean_ctor_get(v_toApplicative_283_, 1);
lean_inc(v_toPure_284_);
lean_dec_ref(v_toApplicative_283_);
v___f_285_ = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0), 9, 3);
lean_closure_set(v___f_285_, 0, v_inst_282_);
lean_closure_set(v___f_285_, 1, v_s_280_);
lean_closure_set(v___f_285_, 2, v_toPure_284_);
return v___f_285_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(lean_object* v_m_286_, lean_object* v_n_287_, lean_object* v_s_288_, lean_object* v_inst_289_, lean_object* v_inst_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(v_s_288_, v_inst_289_, v_inst_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revChars(lean_object* v_s_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_String_Slice_revPositions(v_s_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revChars___boxed(lean_object* v_s_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_String_Slice_revChars(v_s_294_);
lean_dec_ref(v_s_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_bytes(lean_object* v_s_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v_s_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0(lean_object* v_inst_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_s_310_; lean_object* v_offset_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_332_; 
v_s_310_ = lean_ctor_get(v_x_309_, 0);
v_offset_311_ = lean_ctor_get(v_x_309_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_309_);
if (v_isSharedCheck_332_ == 0)
{
v___x_313_ = v_x_309_;
v_isShared_314_ = v_isSharedCheck_332_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_offset_311_);
lean_inc(v_s_310_);
lean_dec(v_x_309_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_332_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v_str_315_; lean_object* v_startInclusive_316_; lean_object* v_endExclusive_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v_str_315_ = lean_ctor_get(v_s_310_, 0);
lean_inc_ref(v_str_315_);
v_startInclusive_316_ = lean_ctor_get(v_s_310_, 1);
lean_inc(v_startInclusive_316_);
v_endExclusive_317_ = lean_ctor_get(v_s_310_, 2);
v___x_318_ = lean_nat_sub(v_endExclusive_317_, v_startInclusive_316_);
v___x_319_ = lean_nat_dec_lt(v_offset_311_, v___x_318_);
lean_dec(v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_321_; 
lean_dec(v_startInclusive_316_);
lean_dec_ref(v_str_315_);
lean_del_object(v___x_313_);
lean_dec(v_offset_311_);
lean_dec_ref(v_s_310_);
v___x_320_ = lean_box(2);
v___x_321_ = lean_apply_2(v_inst_308_, lean_box(0), v___x_320_);
return v___x_321_;
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_add(v_offset_311_, v___x_322_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v___x_323_);
v___x_325_ = v___x_313_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_s_310_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_331_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_326_ = lean_nat_add(v_startInclusive_316_, v_offset_311_);
lean_dec(v_offset_311_);
lean_dec(v_startInclusive_316_);
v___x_327_ = lean_string_get_byte_fast(v_str_315_, v___x_326_);
lean_dec_ref(v_str_315_);
v___x_328_ = lean_box(v___x_327_);
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_325_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = lean_apply_2(v_inst_308_, lean_box(0), v___x_329_);
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg(lean_object* v_inst_333_){
_start:
{
lean_object* v___f_334_; 
v___f_334_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_334_, 0, v_inst_333_);
return v___f_334_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure(lean_object* v_m_335_, lean_object* v_inst_336_){
_start:
{
lean_object* v___f_337_; 
v___f_337_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_337_, 0, v_inst_336_);
return v___f_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation(lean_object* v_m_338_, lean_object* v_inst_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = lean_box(0);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___boxed(lean_object* v_m_341_, lean_object* v_inst_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation(v_m_341_, v_inst_342_);
lean_dec(v_inst_342_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0(lean_object* v_toPure_344_, lean_object* v_recur_345_, lean_object* v_it_346_, lean_object* v_____do__lift_347_){
_start:
{
if (lean_obj_tag(v_____do__lift_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_349_; 
lean_dec_ref(v_it_346_);
lean_dec(v_recur_345_);
v_a_348_ = lean_ctor_get(v_____do__lift_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref(v_____do__lift_347_);
v___x_349_ = lean_apply_2(v_toPure_344_, lean_box(0), v_a_348_);
return v___x_349_;
}
else
{
lean_object* v_a_350_; lean_object* v___x_351_; 
lean_dec(v_toPure_344_);
v_a_350_ = lean_ctor_get(v_____do__lift_347_, 0);
lean_inc(v_a_350_);
lean_dec_ref(v_____do__lift_347_);
v___x_351_ = lean_apply_4(v_recur_345_, v_it_346_, v_a_350_, lean_box(0), lean_box(0));
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1(lean_object* v_toPure_352_, lean_object* v_recur_353_, lean_object* v___y_354_, lean_object* v_acc_355_, lean_object* v_toBind_356_, lean_object* v_s_357_){
_start:
{
switch(lean_obj_tag(v_s_357_))
{
case 0:
{
lean_object* v_it_358_; lean_object* v_out_359_; lean_object* v___f_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_it_358_ = lean_ctor_get(v_s_357_, 0);
lean_inc(v_it_358_);
v_out_359_ = lean_ctor_get(v_s_357_, 1);
lean_inc(v_out_359_);
lean_dec_ref(v_s_357_);
v___f_360_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_360_, 0, v_toPure_352_);
lean_closure_set(v___f_360_, 1, v_recur_353_);
lean_closure_set(v___f_360_, 2, v_it_358_);
v___x_361_ = lean_apply_3(v___y_354_, v_out_359_, lean_box(0), v_acc_355_);
v___x_362_ = lean_apply_4(v_toBind_356_, lean_box(0), lean_box(0), v___x_361_, v___f_360_);
return v___x_362_;
}
case 1:
{
lean_object* v_it_363_; lean_object* v___x_364_; 
lean_dec(v_toBind_356_);
lean_dec(v___y_354_);
lean_dec(v_toPure_352_);
v_it_363_ = lean_ctor_get(v_s_357_, 0);
lean_inc(v_it_363_);
lean_dec_ref(v_s_357_);
v___x_364_ = lean_apply_4(v_recur_353_, v_it_363_, v_acc_355_, lean_box(0), lean_box(0));
return v___x_364_;
}
default: 
{
lean_object* v___x_365_; 
lean_dec(v_toBind_356_);
lean_dec(v___y_354_);
lean_dec(v_recur_353_);
v___x_365_ = lean_apply_2(v_toPure_352_, lean_box(0), v_acc_355_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2(lean_object* v_toPure_366_, lean_object* v___y_367_, lean_object* v_toBind_368_, lean_object* v_toPure_369_, lean_object* v_lift_370_, lean_object* v_it_371_, lean_object* v_acc_372_, lean_object* v_hP_373_, lean_object* v_recur_374_){
_start:
{
lean_object* v_s_375_; lean_object* v_offset_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_400_; 
v_s_375_ = lean_ctor_get(v_it_371_, 0);
v_offset_376_ = lean_ctor_get(v_it_371_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v_it_371_);
if (v_isSharedCheck_400_ == 0)
{
v___x_378_ = v_it_371_;
v_isShared_379_ = v_isSharedCheck_400_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_offset_376_);
lean_inc(v_s_375_);
lean_dec(v_it_371_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_400_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v_str_380_; lean_object* v_startInclusive_381_; lean_object* v_endExclusive_382_; lean_object* v___f_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v_str_380_ = lean_ctor_get(v_s_375_, 0);
lean_inc_ref(v_str_380_);
v_startInclusive_381_ = lean_ctor_get(v_s_375_, 1);
lean_inc(v_startInclusive_381_);
v_endExclusive_382_ = lean_ctor_get(v_s_375_, 2);
v___f_383_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_383_, 0, v_toPure_366_);
lean_closure_set(v___f_383_, 1, v_recur_374_);
lean_closure_set(v___f_383_, 2, v___y_367_);
lean_closure_set(v___f_383_, 3, v_acc_372_);
lean_closure_set(v___f_383_, 4, v_toBind_368_);
v___x_384_ = lean_nat_sub(v_endExclusive_382_, v_startInclusive_381_);
v___x_385_ = lean_nat_dec_lt(v_offset_376_, v___x_384_);
lean_dec(v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
lean_dec(v_startInclusive_381_);
lean_dec_ref(v_str_380_);
lean_del_object(v___x_378_);
lean_dec(v_offset_376_);
lean_dec_ref(v_s_375_);
v___x_386_ = lean_box(2);
v___x_387_ = lean_apply_2(v_toPure_369_, lean_box(0), v___x_386_);
v___x_388_ = lean_apply_4(v_lift_370_, lean_box(0), lean_box(0), v___f_383_, v___x_387_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_add(v_offset_376_, v___x_389_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 1, v___x_390_);
v___x_392_ = v___x_378_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_s_375_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_390_);
v___x_392_ = v_reuseFailAlloc_399_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_393_ = lean_nat_add(v_startInclusive_381_, v_offset_376_);
lean_dec(v_offset_376_);
lean_dec(v_startInclusive_381_);
v___x_394_ = lean_string_get_byte_fast(v_str_380_, v___x_393_);
lean_dec_ref(v_str_380_);
v___x_395_ = lean_box(v___x_394_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_392_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = lean_apply_2(v_toPure_369_, lean_box(0), v___x_396_);
v___x_398_ = lean_apply_4(v_lift_370_, lean_box(0), lean_box(0), v___f_383_, v___x_397_);
return v___x_398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3(lean_object* v_inst_401_, lean_object* v_toPure_402_, lean_object* v_lift_403_, lean_object* v_00_u03b3_404_, lean_object* v_Pl_405_, lean_object* v_it_406_, lean_object* v_init_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_toApplicative_409_; lean_object* v_toBind_410_; lean_object* v_toPure_411_; lean_object* v___f_412_; lean_object* v___x_413_; 
v_toApplicative_409_ = lean_ctor_get(v_inst_401_, 0);
lean_inc_ref(v_toApplicative_409_);
v_toBind_410_ = lean_ctor_get(v_inst_401_, 1);
lean_inc(v_toBind_410_);
lean_dec_ref(v_inst_401_);
v_toPure_411_ = lean_ctor_get(v_toApplicative_409_, 1);
lean_inc(v_toPure_411_);
lean_dec_ref(v_toApplicative_409_);
v___f_412_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2), 9, 5);
lean_closure_set(v___f_412_, 0, v_toPure_411_);
lean_closure_set(v___f_412_, 1, v___y_408_);
lean_closure_set(v___f_412_, 2, v_toBind_410_);
lean_closure_set(v___f_412_, 3, v_toPure_402_);
lean_closure_set(v___f_412_, 4, v_lift_403_);
v___x_413_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_412_, v_it_406_, v_init_407_, lean_box(0));
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg(lean_object* v_inst_414_, lean_object* v_inst_415_){
_start:
{
lean_object* v_toApplicative_416_; lean_object* v_toPure_417_; lean_object* v___f_418_; 
v_toApplicative_416_ = lean_ctor_get(v_inst_414_, 0);
lean_inc_ref(v_toApplicative_416_);
lean_dec_ref(v_inst_414_);
v_toPure_417_ = lean_ctor_get(v_toApplicative_416_, 1);
lean_inc(v_toPure_417_);
lean_dec_ref(v_toApplicative_416_);
v___f_418_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3), 8, 2);
lean_closure_set(v___f_418_, 0, v_inst_415_);
lean_closure_set(v___f_418_, 1, v_toPure_417_);
return v___f_418_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad(lean_object* v_m_419_, lean_object* v_n_420_, lean_object* v_inst_421_, lean_object* v_inst_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg(v_inst_421_, v_inst_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revBytes(lean_object* v_s_424_){
_start:
{
lean_object* v_startInclusive_425_; lean_object* v_endExclusive_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_startInclusive_425_ = lean_ctor_get(v_s_424_, 1);
v_endExclusive_426_ = lean_ctor_get(v_s_424_, 2);
v___x_427_ = lean_nat_sub(v_endExclusive_426_, v_startInclusive_425_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v_s_424_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0(lean_object* v_inst_433_, lean_object* v_x_434_){
_start:
{
lean_object* v_s_435_; lean_object* v_offset_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_456_; 
v_s_435_ = lean_ctor_get(v_x_434_, 0);
v_offset_436_ = lean_ctor_get(v_x_434_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_x_434_);
if (v_isSharedCheck_456_ == 0)
{
v___x_438_ = v_x_434_;
v_isShared_439_ = v_isSharedCheck_456_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_offset_436_);
lean_inc(v_s_435_);
lean_dec(v_x_434_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_456_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = lean_nat_dec_eq(v_offset_436_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v_str_442_; lean_object* v_startInclusive_443_; lean_object* v___x_444_; lean_object* v_nextOffset_445_; lean_object* v___x_447_; 
v_str_442_ = lean_ctor_get(v_s_435_, 0);
lean_inc_ref(v_str_442_);
v_startInclusive_443_ = lean_ctor_get(v_s_435_, 1);
lean_inc(v_startInclusive_443_);
v___x_444_ = lean_unsigned_to_nat(1u);
v_nextOffset_445_ = lean_nat_sub(v_offset_436_, v___x_444_);
lean_dec(v_offset_436_);
lean_inc(v_nextOffset_445_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v_nextOffset_445_);
v___x_447_ = v___x_438_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_s_435_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_nextOffset_445_);
v___x_447_ = v_reuseFailAlloc_453_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_448_ = lean_nat_add(v_startInclusive_443_, v_nextOffset_445_);
lean_dec(v_nextOffset_445_);
lean_dec(v_startInclusive_443_);
v___x_449_ = lean_string_get_byte_fast(v_str_442_, v___x_448_);
lean_dec_ref(v_str_442_);
v___x_450_ = lean_box(v___x_449_);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_447_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = lean_apply_2(v_inst_433_, lean_box(0), v___x_451_);
return v___x_452_;
}
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_del_object(v___x_438_);
lean_dec(v_offset_436_);
lean_dec_ref(v_s_435_);
v___x_454_ = lean_box(2);
v___x_455_ = lean_apply_2(v_inst_433_, lean_box(0), v___x_454_);
return v___x_455_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg(lean_object* v_inst_457_){
_start:
{
lean_object* v___f_458_; 
v___f_458_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_458_, 0, v_inst_457_);
return v___f_458_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure(lean_object* v_m_459_, lean_object* v_inst_460_){
_start:
{
lean_object* v___f_461_; 
v___f_461_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_461_, 0, v_inst_460_);
return v___f_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation(lean_object* v_m_462_, lean_object* v_inst_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = lean_box(0);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___boxed(lean_object* v_m_465_, lean_object* v_inst_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation(v_m_465_, v_inst_466_);
lean_dec(v_inst_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0(lean_object* v_toPure_468_, lean_object* v_recur_469_, lean_object* v_it_470_, lean_object* v_____do__lift_471_){
_start:
{
if (lean_obj_tag(v_____do__lift_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; 
lean_dec_ref(v_it_470_);
lean_dec(v_recur_469_);
v_a_472_ = lean_ctor_get(v_____do__lift_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref(v_____do__lift_471_);
v___x_473_ = lean_apply_2(v_toPure_468_, lean_box(0), v_a_472_);
return v___x_473_;
}
else
{
lean_object* v_a_474_; lean_object* v___x_475_; 
lean_dec(v_toPure_468_);
v_a_474_ = lean_ctor_get(v_____do__lift_471_, 0);
lean_inc(v_a_474_);
lean_dec_ref(v_____do__lift_471_);
v___x_475_ = lean_apply_4(v_recur_469_, v_it_470_, v_a_474_, lean_box(0), lean_box(0));
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1(lean_object* v_toPure_476_, lean_object* v_recur_477_, lean_object* v___y_478_, lean_object* v_acc_479_, lean_object* v_toBind_480_, lean_object* v_s_481_){
_start:
{
switch(lean_obj_tag(v_s_481_))
{
case 0:
{
lean_object* v_it_482_; lean_object* v_out_483_; lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_it_482_ = lean_ctor_get(v_s_481_, 0);
lean_inc(v_it_482_);
v_out_483_ = lean_ctor_get(v_s_481_, 1);
lean_inc(v_out_483_);
lean_dec_ref(v_s_481_);
v___f_484_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_484_, 0, v_toPure_476_);
lean_closure_set(v___f_484_, 1, v_recur_477_);
lean_closure_set(v___f_484_, 2, v_it_482_);
v___x_485_ = lean_apply_3(v___y_478_, v_out_483_, lean_box(0), v_acc_479_);
v___x_486_ = lean_apply_4(v_toBind_480_, lean_box(0), lean_box(0), v___x_485_, v___f_484_);
return v___x_486_;
}
case 1:
{
lean_object* v_it_487_; lean_object* v___x_488_; 
lean_dec(v_toBind_480_);
lean_dec(v___y_478_);
lean_dec(v_toPure_476_);
v_it_487_ = lean_ctor_get(v_s_481_, 0);
lean_inc(v_it_487_);
lean_dec_ref(v_s_481_);
v___x_488_ = lean_apply_4(v_recur_477_, v_it_487_, v_acc_479_, lean_box(0), lean_box(0));
return v___x_488_;
}
default: 
{
lean_object* v___x_489_; 
lean_dec(v_toBind_480_);
lean_dec(v___y_478_);
lean_dec(v_recur_477_);
v___x_489_ = lean_apply_2(v_toPure_476_, lean_box(0), v_acc_479_);
return v___x_489_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2(lean_object* v_toPure_490_, lean_object* v___y_491_, lean_object* v_toBind_492_, lean_object* v_toPure_493_, lean_object* v_lift_494_, lean_object* v_it_495_, lean_object* v_acc_496_, lean_object* v_hP_497_, lean_object* v_recur_498_){
_start:
{
lean_object* v_s_499_; lean_object* v_offset_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_523_; 
v_s_499_ = lean_ctor_get(v_it_495_, 0);
v_offset_500_ = lean_ctor_get(v_it_495_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_it_495_);
if (v_isSharedCheck_523_ == 0)
{
v___x_502_ = v_it_495_;
v_isShared_503_ = v_isSharedCheck_523_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_offset_500_);
lean_inc(v_s_499_);
lean_dec(v_it_495_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_523_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___f_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v___f_504_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_504_, 0, v_toPure_490_);
lean_closure_set(v___f_504_, 1, v_recur_498_);
lean_closure_set(v___f_504_, 2, v___y_491_);
lean_closure_set(v___f_504_, 3, v_acc_496_);
lean_closure_set(v___f_504_, 4, v_toBind_492_);
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_nat_dec_eq(v_offset_500_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v_str_507_; lean_object* v_startInclusive_508_; lean_object* v___x_509_; lean_object* v_nextOffset_510_; lean_object* v___x_512_; 
v_str_507_ = lean_ctor_get(v_s_499_, 0);
lean_inc_ref(v_str_507_);
v_startInclusive_508_ = lean_ctor_get(v_s_499_, 1);
lean_inc(v_startInclusive_508_);
v___x_509_ = lean_unsigned_to_nat(1u);
v_nextOffset_510_ = lean_nat_sub(v_offset_500_, v___x_509_);
lean_dec(v_offset_500_);
lean_inc(v_nextOffset_510_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v_nextOffset_510_);
v___x_512_ = v___x_502_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_s_499_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_nextOffset_510_);
v___x_512_ = v_reuseFailAlloc_519_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; uint8_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_513_ = lean_nat_add(v_startInclusive_508_, v_nextOffset_510_);
lean_dec(v_nextOffset_510_);
lean_dec(v_startInclusive_508_);
v___x_514_ = lean_string_get_byte_fast(v_str_507_, v___x_513_);
lean_dec_ref(v_str_507_);
v___x_515_ = lean_box(v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_512_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_apply_2(v_toPure_493_, lean_box(0), v___x_516_);
v___x_518_ = lean_apply_4(v_lift_494_, lean_box(0), lean_box(0), v___f_504_, v___x_517_);
return v___x_518_;
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_del_object(v___x_502_);
lean_dec(v_offset_500_);
lean_dec_ref(v_s_499_);
v___x_520_ = lean_box(2);
v___x_521_ = lean_apply_2(v_toPure_493_, lean_box(0), v___x_520_);
v___x_522_ = lean_apply_4(v_lift_494_, lean_box(0), lean_box(0), v___f_504_, v___x_521_);
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3(lean_object* v_inst_524_, lean_object* v_toPure_525_, lean_object* v_lift_526_, lean_object* v_00_u03b3_527_, lean_object* v_Pl_528_, lean_object* v_it_529_, lean_object* v_init_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_toApplicative_532_; lean_object* v_toBind_533_; lean_object* v_toPure_534_; lean_object* v___f_535_; lean_object* v___x_536_; 
v_toApplicative_532_ = lean_ctor_get(v_inst_524_, 0);
lean_inc_ref(v_toApplicative_532_);
v_toBind_533_ = lean_ctor_get(v_inst_524_, 1);
lean_inc(v_toBind_533_);
lean_dec_ref(v_inst_524_);
v_toPure_534_ = lean_ctor_get(v_toApplicative_532_, 1);
lean_inc(v_toPure_534_);
lean_dec_ref(v_toApplicative_532_);
v___f_535_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2), 9, 5);
lean_closure_set(v___f_535_, 0, v_toPure_534_);
lean_closure_set(v___f_535_, 1, v___y_531_);
lean_closure_set(v___f_535_, 2, v_toBind_533_);
lean_closure_set(v___f_535_, 3, v_toPure_525_);
lean_closure_set(v___f_535_, 4, v_lift_526_);
v___x_536_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_535_, v_it_529_, v_init_530_, lean_box(0));
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg(lean_object* v_inst_537_, lean_object* v_inst_538_){
_start:
{
lean_object* v_toApplicative_539_; lean_object* v_toPure_540_; lean_object* v___f_541_; 
v_toApplicative_539_ = lean_ctor_get(v_inst_537_, 0);
lean_inc_ref(v_toApplicative_539_);
lean_dec_ref(v_inst_537_);
v_toPure_540_ = lean_ctor_get(v_toApplicative_539_, 1);
lean_inc(v_toPure_540_);
lean_dec_ref(v_toApplicative_539_);
v___f_541_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3), 8, 2);
lean_closure_set(v___f_541_, 0, v_inst_538_);
lean_closure_set(v___f_541_, 1, v_toPure_540_);
return v___f_541_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad(lean_object* v_m_542_, lean_object* v_n_543_, lean_object* v_inst_544_, lean_object* v_inst_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg(v_inst_544_, v_inst_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0(lean_object* v_toPure_547_, lean_object* v_____do__lift_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = lean_apply_2(v_toPure_547_, lean_box(0), v_____do__lift_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1(lean_object* v_toPure_550_, lean_object* v_recur_551_, lean_object* v___x_552_, lean_object* v_____do__lift_553_){
_start:
{
if (lean_obj_tag(v_____do__lift_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_555_; 
lean_dec(v___x_552_);
lean_dec(v_recur_551_);
v_a_554_ = lean_ctor_get(v_____do__lift_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref(v_____do__lift_553_);
v___x_555_ = lean_apply_2(v_toPure_550_, lean_box(0), v_a_554_);
return v___x_555_;
}
else
{
lean_object* v_a_556_; lean_object* v___x_557_; 
lean_dec(v_toPure_550_);
v_a_556_ = lean_ctor_get(v_____do__lift_553_, 0);
lean_inc(v_a_556_);
lean_dec_ref(v_____do__lift_553_);
v___x_557_ = lean_apply_4(v_recur_551_, v___x_552_, v_a_556_, lean_box(0), lean_box(0));
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2(lean_object* v_s_558_, lean_object* v_toPure_559_, lean_object* v_f_560_, lean_object* v_toBind_561_, lean_object* v___f_562_, lean_object* v_it_563_, lean_object* v_acc_564_, lean_object* v_hP_565_, lean_object* v_recur_566_){
_start:
{
lean_object* v_str_567_; lean_object* v_startInclusive_568_; lean_object* v_endExclusive_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v_str_567_ = lean_ctor_get(v_s_558_, 0);
v_startInclusive_568_ = lean_ctor_get(v_s_558_, 1);
v_endExclusive_569_ = lean_ctor_get(v_s_558_, 2);
v___x_570_ = lean_nat_sub(v_endExclusive_569_, v_startInclusive_568_);
v___x_571_ = lean_nat_dec_eq(v_it_563_, v___x_570_);
lean_dec(v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___f_575_; uint32_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_572_ = lean_nat_add(v_startInclusive_568_, v_it_563_);
v___x_573_ = lean_string_utf8_next_fast(v_str_567_, v___x_572_);
v___x_574_ = lean_nat_sub(v___x_573_, v_startInclusive_568_);
v___f_575_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_575_, 0, v_toPure_559_);
lean_closure_set(v___f_575_, 1, v_recur_566_);
lean_closure_set(v___f_575_, 2, v___x_574_);
v___x_576_ = lean_string_utf8_get_fast(v_str_567_, v___x_572_);
lean_dec(v___x_572_);
v___x_577_ = lean_box_uint32(v___x_576_);
v___x_578_ = lean_apply_2(v_f_560_, v___x_577_, v_acc_564_);
lean_inc(v_toBind_561_);
v___x_579_ = lean_apply_4(v_toBind_561_, lean_box(0), lean_box(0), v___x_578_, v___f_562_);
v___x_580_ = lean_apply_4(v_toBind_561_, lean_box(0), lean_box(0), v___x_579_, v___f_575_);
return v___x_580_;
}
else
{
lean_object* v___x_581_; 
lean_dec(v_recur_566_);
lean_dec(v___f_562_);
lean_dec(v_toBind_561_);
lean_dec(v_f_560_);
v___x_581_ = lean_apply_2(v_toPure_559_, lean_box(0), v_acc_564_);
return v___x_581_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2___boxed(lean_object* v_s_582_, lean_object* v_toPure_583_, lean_object* v_f_584_, lean_object* v_toBind_585_, lean_object* v___f_586_, lean_object* v_it_587_, lean_object* v_acc_588_, lean_object* v_hP_589_, lean_object* v_recur_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2(v_s_582_, v_toPure_583_, v_f_584_, v_toBind_585_, v___f_586_, v_it_587_, v_acc_588_, v_hP_589_, v_recur_590_);
lean_dec(v_it_587_);
lean_dec_ref(v_s_582_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3(lean_object* v_inst_592_, lean_object* v_00_u03b2_593_, lean_object* v_s_594_, lean_object* v_b_595_, lean_object* v_f_596_){
_start:
{
lean_object* v_toApplicative_597_; lean_object* v_toBind_598_; lean_object* v_toPure_599_; lean_object* v___x_600_; lean_object* v___f_601_; lean_object* v___f_602_; lean_object* v___x_603_; 
v_toApplicative_597_ = lean_ctor_get(v_inst_592_, 0);
lean_inc_ref(v_toApplicative_597_);
v_toBind_598_ = lean_ctor_get(v_inst_592_, 1);
lean_inc(v_toBind_598_);
lean_dec_ref(v_inst_592_);
v_toPure_599_ = lean_ctor_get(v_toApplicative_597_, 1);
lean_inc_n(v_toPure_599_, 2);
lean_dec_ref(v_toApplicative_597_);
v___x_600_ = lean_unsigned_to_nat(0u);
v___f_601_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_601_, 0, v_toPure_599_);
v___f_602_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2___boxed), 9, 5);
lean_closure_set(v___f_602_, 0, v_s_594_);
lean_closure_set(v___f_602_, 1, v_toPure_599_);
lean_closure_set(v___f_602_, 2, v_f_596_);
lean_closure_set(v___f_602_, 3, v_toBind_598_);
lean_closure_set(v___f_602_, 4, v___f_601_);
v___x_603_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_602_, v___x_600_, v_b_595_, lean_box(0));
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg(lean_object* v_inst_604_){
_start:
{
lean_object* v___f_605_; 
v___f_605_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_605_, 0, v_inst_604_);
return v___f_605_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad(lean_object* v_m_606_, lean_object* v_inst_607_){
_start:
{
lean_object* v___f_608_; 
v___f_608_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_608_, 0, v_inst_607_);
return v___f_608_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg___lam__0(lean_object* v_s_609_, lean_object* v_f_610_, lean_object* v_it_611_, lean_object* v_acc_612_, lean_object* v_hP_613_, lean_object* v_recur_614_){
_start:
{
lean_object* v_str_615_; lean_object* v_startInclusive_616_; lean_object* v_endExclusive_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v_str_615_ = lean_ctor_get(v_s_609_, 0);
v_startInclusive_616_ = lean_ctor_get(v_s_609_, 1);
v_endExclusive_617_ = lean_ctor_get(v_s_609_, 2);
v___x_618_ = lean_nat_sub(v_endExclusive_617_, v_startInclusive_616_);
v___x_619_ = lean_nat_dec_eq(v_it_611_, v___x_618_);
lean_dec(v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint32_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_620_ = lean_nat_add(v_startInclusive_616_, v_it_611_);
v___x_621_ = lean_string_utf8_next_fast(v_str_615_, v___x_620_);
v___x_622_ = lean_nat_sub(v___x_621_, v_startInclusive_616_);
v___x_623_ = lean_string_utf8_get_fast(v_str_615_, v___x_620_);
lean_dec(v___x_620_);
v___x_624_ = lean_box_uint32(v___x_623_);
v___x_625_ = lean_apply_2(v_f_610_, v_acc_612_, v___x_624_);
v___x_626_ = lean_apply_4(v_recur_614_, v___x_622_, v___x_625_, lean_box(0), lean_box(0));
return v___x_626_;
}
else
{
lean_dec(v_recur_614_);
lean_dec(v_f_610_);
return v_acc_612_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg___lam__0___boxed(lean_object* v_s_627_, lean_object* v_f_628_, lean_object* v_it_629_, lean_object* v_acc_630_, lean_object* v_hP_631_, lean_object* v_recur_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_String_Slice_foldl___redArg___lam__0(v_s_627_, v_f_628_, v_it_629_, v_acc_630_, v_hP_631_, v_recur_632_);
lean_dec(v_it_629_);
lean_dec_ref(v_s_627_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg(lean_object* v_f_634_, lean_object* v_init_635_, lean_object* v_s_636_){
_start:
{
lean_object* v___f_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___f_637_ = lean_alloc_closure((void*)(l_String_Slice_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_637_, 0, v_s_636_);
lean_closure_set(v___f_637_, 1, v_f_634_);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_637_, v___x_638_, v_init_635_, lean_box(0));
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl(lean_object* v_00_u03b1_640_, lean_object* v_f_641_, lean_object* v_init_642_, lean_object* v_s_643_){
_start:
{
lean_object* v___f_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___f_644_ = lean_alloc_closure((void*)(l_String_Slice_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_644_, 0, v_s_643_);
lean_closure_set(v___f_644_, 1, v_f_641_);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_644_, v___x_645_, v_init_642_, lean_box(0));
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg___lam__0(lean_object* v_s_647_, lean_object* v_f_648_, lean_object* v_it_649_, lean_object* v_acc_650_, lean_object* v_hP_651_, lean_object* v_recur_652_){
_start:
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_nat_dec_eq(v_it_649_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v_str_655_; lean_object* v_startInclusive_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v_prevPos_659_; lean_object* v___x_660_; uint32_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v_str_655_ = lean_ctor_get(v_s_647_, 0);
v_startInclusive_656_ = lean_ctor_get(v_s_647_, 1);
v___x_657_ = lean_unsigned_to_nat(1u);
v___x_658_ = lean_nat_sub(v_it_649_, v___x_657_);
v_prevPos_659_ = l_String_Slice_posLE(v_s_647_, v___x_658_);
v___x_660_ = lean_nat_add(v_startInclusive_656_, v_prevPos_659_);
v___x_661_ = lean_string_utf8_get_fast(v_str_655_, v___x_660_);
lean_dec(v___x_660_);
v___x_662_ = lean_box_uint32(v___x_661_);
v___x_663_ = lean_apply_2(v_f_648_, v___x_662_, v_acc_650_);
v___x_664_ = lean_apply_4(v_recur_652_, v_prevPos_659_, v___x_663_, lean_box(0), lean_box(0));
return v___x_664_;
}
else
{
lean_dec(v_recur_652_);
lean_dec(v_f_648_);
return v_acc_650_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg___lam__0___boxed(lean_object* v_s_665_, lean_object* v_f_666_, lean_object* v_it_667_, lean_object* v_acc_668_, lean_object* v_hP_669_, lean_object* v_recur_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_String_Slice_foldr___redArg___lam__0(v_s_665_, v_f_666_, v_it_667_, v_acc_668_, v_hP_669_, v_recur_670_);
lean_dec(v_it_667_);
lean_dec_ref(v_s_665_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg(lean_object* v_f_672_, lean_object* v_init_673_, lean_object* v_s_674_){
_start:
{
lean_object* v___f_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_inc_ref(v_s_674_);
v___f_675_ = lean_alloc_closure((void*)(l_String_Slice_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_675_, 0, v_s_674_);
lean_closure_set(v___f_675_, 1, v_f_672_);
v___x_676_ = l_String_Slice_revPositions(v_s_674_);
lean_dec_ref(v_s_674_);
v___x_677_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_675_, v___x_676_, v_init_673_, lean_box(0));
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr(lean_object* v_00_u03b1_678_, lean_object* v_f_679_, lean_object* v_init_680_, lean_object* v_s_681_){
_start:
{
lean_object* v___f_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_inc_ref(v_s_681_);
v___f_682_ = lean_alloc_closure((void*)(l_String_Slice_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_682_, 0, v_s_681_);
lean_closure_set(v___f_682_, 1, v_f_679_);
v___x_683_ = l_String_Slice_revPositions(v_s_681_);
lean_dec_ref(v_s_681_);
v___x_684_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_682_, v___x_683_, v_init_680_, lean_box(0));
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___redArg(lean_object* v_x_685_){
_start:
{
lean_inc(v_x_685_);
return v_x_685_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___redArg___boxed(lean_object* v_x_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_String_Internal_ofToSliceWithProof___redArg(v_x_686_);
lean_dec(v_x_686_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof(lean_object* v_s_688_, lean_object* v_x_689_){
_start:
{
lean_inc(v_x_689_);
return v_x_689_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___boxed(lean_object* v_s_690_, lean_object* v_x_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_String_Internal_ofToSliceWithProof(v_s_690_, v_x_691_);
lean_dec(v_x_691_);
lean_dec_ref(v_s_690_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom___redArg(lean_object* v_p_693_){
_start:
{
lean_inc(v_p_693_);
return v_p_693_;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom___redArg___boxed(lean_object* v_p_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_String_positionsFrom___redArg(v_p_694_);
lean_dec(v_p_694_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom(lean_object* v_s_696_, lean_object* v_p_697_){
_start:
{
lean_inc(v_p_697_);
return v_p_697_;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom___boxed(lean_object* v_s_698_, lean_object* v_p_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_String_positionsFrom(v_s_698_, v_p_699_);
lean_dec(v_p_699_);
lean_dec_ref(v_s_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_String_positions(lean_object* v_s_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = lean_unsigned_to_nat(0u);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_String_positions___boxed(lean_object* v_s_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_String_positions(v_s_703_);
lean_dec_ref(v_s_703_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_String_chars(lean_object* v_s_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = lean_unsigned_to_nat(0u);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_String_chars___boxed(lean_object* v_s_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_String_chars(v_s_707_);
lean_dec_ref(v_s_707_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom___redArg(lean_object* v_p_709_){
_start:
{
lean_inc(v_p_709_);
return v_p_709_;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom___redArg___boxed(lean_object* v_p_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_String_revPositionsFrom___redArg(v_p_710_);
lean_dec(v_p_710_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom(lean_object* v_s_712_, lean_object* v_p_713_){
_start:
{
lean_inc(v_p_713_);
return v_p_713_;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom___boxed(lean_object* v_s_714_, lean_object* v_p_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_String_revPositionsFrom(v_s_714_, v_p_715_);
lean_dec(v_p_715_);
lean_dec_ref(v_s_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_String_revPositions(lean_object* v_s_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_string_utf8_byte_size(v_s_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_String_revPositions___boxed(lean_object* v_s_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_String_revPositions(v_s_719_);
lean_dec_ref(v_s_719_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_String_revChars(lean_object* v_s_721_){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_string_utf8_byte_size(v_s_721_);
v___x_724_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_724_, 0, v_s_721_);
lean_ctor_set(v___x_724_, 1, v___x_722_);
lean_ctor_set(v___x_724_, 2, v___x_723_);
v___x_725_ = l_String_Slice_revPositions(v___x_724_);
lean_dec_ref(v___x_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_String_byteIterator(lean_object* v_s_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_727_ = lean_unsigned_to_nat(0u);
v___x_728_ = lean_string_utf8_byte_size(v_s_726_);
v___x_729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_729_, 0, v_s_726_);
lean_ctor_set(v___x_729_, 1, v___x_727_);
lean_ctor_set(v___x_729_, 2, v___x_728_);
v___x_730_ = l_String_Slice_bytes(v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_String_revBytes(lean_object* v_s_731_){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_string_utf8_byte_size(v_s_731_);
v___x_734_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_734_, 0, v_s_731_);
lean_ctor_set(v___x_734_, 1, v___x_732_);
lean_ctor_set(v___x_734_, 2, v___x_733_);
v___x_735_ = l_String_Slice_revBytes(v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__2(lean_object* v___x_736_, lean_object* v_s_737_, lean_object* v_toPure_738_, lean_object* v_f_739_, lean_object* v_toBind_740_, lean_object* v___f_741_, lean_object* v_it_742_, lean_object* v_acc_743_, lean_object* v_hP_744_, lean_object* v_recur_745_){
_start:
{
uint8_t v___x_746_; 
v___x_746_ = lean_nat_dec_eq(v_it_742_, v___x_736_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___f_748_; uint32_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_747_ = lean_string_utf8_next_fast(v_s_737_, v_it_742_);
v___f_748_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_748_, 0, v_toPure_738_);
lean_closure_set(v___f_748_, 1, v_recur_745_);
lean_closure_set(v___f_748_, 2, v___x_747_);
v___x_749_ = lean_string_utf8_get_fast(v_s_737_, v_it_742_);
v___x_750_ = lean_box_uint32(v___x_749_);
v___x_751_ = lean_apply_2(v_f_739_, v___x_750_, v_acc_743_);
lean_inc(v_toBind_740_);
v___x_752_ = lean_apply_4(v_toBind_740_, lean_box(0), lean_box(0), v___x_751_, v___f_741_);
v___x_753_ = lean_apply_4(v_toBind_740_, lean_box(0), lean_box(0), v___x_752_, v___f_748_);
return v___x_753_;
}
else
{
lean_object* v___x_754_; 
lean_dec(v_recur_745_);
lean_dec(v___f_741_);
lean_dec(v_toBind_740_);
lean_dec(v_f_739_);
v___x_754_ = lean_apply_2(v_toPure_738_, lean_box(0), v_acc_743_);
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__2___boxed(lean_object* v___x_755_, lean_object* v_s_756_, lean_object* v_toPure_757_, lean_object* v_f_758_, lean_object* v_toBind_759_, lean_object* v___f_760_, lean_object* v_it_761_, lean_object* v_acc_762_, lean_object* v_hP_763_, lean_object* v_recur_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_String_instForInCharOfMonad___redArg___lam__2(v___x_755_, v_s_756_, v_toPure_757_, v_f_758_, v_toBind_759_, v___f_760_, v_it_761_, v_acc_762_, v_hP_763_, v_recur_764_);
lean_dec(v_it_761_);
lean_dec_ref(v_s_756_);
lean_dec(v___x_755_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__0(lean_object* v_inst_766_, lean_object* v_00_u03b2_767_, lean_object* v_s_768_, lean_object* v_b_769_, lean_object* v_f_770_){
_start:
{
lean_object* v_toApplicative_771_; lean_object* v_toBind_772_; lean_object* v_toPure_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___f_777_; lean_object* v___x_778_; 
v_toApplicative_771_ = lean_ctor_get(v_inst_766_, 0);
lean_inc_ref(v_toApplicative_771_);
v_toBind_772_ = lean_ctor_get(v_inst_766_, 1);
lean_inc(v_toBind_772_);
lean_dec_ref(v_inst_766_);
v_toPure_773_ = lean_ctor_get(v_toApplicative_771_, 1);
lean_inc_n(v_toPure_773_, 2);
lean_dec_ref(v_toApplicative_771_);
v___x_774_ = lean_string_utf8_byte_size(v_s_768_);
v___x_775_ = lean_unsigned_to_nat(0u);
v___f_776_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_776_, 0, v_toPure_773_);
v___f_777_ = lean_alloc_closure((void*)(l_String_instForInCharOfMonad___redArg___lam__2___boxed), 10, 6);
lean_closure_set(v___f_777_, 0, v___x_774_);
lean_closure_set(v___f_777_, 1, v_s_768_);
lean_closure_set(v___f_777_, 2, v_toPure_773_);
lean_closure_set(v___f_777_, 3, v_f_770_);
lean_closure_set(v___f_777_, 4, v_toBind_772_);
lean_closure_set(v___f_777_, 5, v___f_776_);
v___x_778_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_777_, v___x_775_, v_b_769_, lean_box(0));
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg(lean_object* v_inst_779_){
_start:
{
lean_object* v___f_780_; 
v___f_780_ = lean_alloc_closure((void*)(l_String_instForInCharOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_780_, 0, v_inst_779_);
return v___f_780_;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad(lean_object* v_m_781_, lean_object* v_inst_782_){
_start:
{
lean_object* v___f_783_; 
v___f_783_ = lean_alloc_closure((void*)(l_String_instForInCharOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_783_, 0, v_inst_782_);
return v___f_783_;
}
}
LEAN_EXPORT lean_object* l_String_foldl___redArg___lam__0(lean_object* v___x_784_, lean_object* v_s_785_, lean_object* v_f_786_, lean_object* v_it_787_, lean_object* v_acc_788_, lean_object* v_hP_789_, lean_object* v_recur_790_){
_start:
{
uint8_t v___x_791_; 
v___x_791_ = lean_nat_dec_eq(v_it_787_, v___x_784_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; uint32_t v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_792_ = lean_string_utf8_next_fast(v_s_785_, v_it_787_);
v___x_793_ = lean_string_utf8_get_fast(v_s_785_, v_it_787_);
v___x_794_ = lean_box_uint32(v___x_793_);
v___x_795_ = lean_apply_2(v_f_786_, v_acc_788_, v___x_794_);
v___x_796_ = lean_apply_4(v_recur_790_, v___x_792_, v___x_795_, lean_box(0), lean_box(0));
return v___x_796_;
}
else
{
lean_dec(v_recur_790_);
lean_dec(v_f_786_);
return v_acc_788_;
}
}
}
LEAN_EXPORT lean_object* l_String_foldl___redArg___lam__0___boxed(lean_object* v___x_797_, lean_object* v_s_798_, lean_object* v_f_799_, lean_object* v_it_800_, lean_object* v_acc_801_, lean_object* v_hP_802_, lean_object* v_recur_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_String_foldl___redArg___lam__0(v___x_797_, v_s_798_, v_f_799_, v_it_800_, v_acc_801_, v_hP_802_, v_recur_803_);
lean_dec(v_it_800_);
lean_dec_ref(v_s_798_);
lean_dec(v___x_797_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_String_foldl___redArg(lean_object* v_f_805_, lean_object* v_init_806_, lean_object* v_s_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_808_ = lean_string_utf8_byte_size(v_s_807_);
v___f_809_ = lean_alloc_closure((void*)(l_String_foldl___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_809_, 0, v___x_808_);
lean_closure_set(v___f_809_, 1, v_s_807_);
lean_closure_set(v___f_809_, 2, v_f_805_);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_809_, v___x_810_, v_init_806_, lean_box(0));
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_String_foldl(lean_object* v_00_u03b1_812_, lean_object* v_f_813_, lean_object* v_init_814_, lean_object* v_s_815_){
_start:
{
lean_object* v___x_816_; lean_object* v___f_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_816_ = lean_string_utf8_byte_size(v_s_815_);
v___f_817_ = lean_alloc_closure((void*)(l_String_foldl___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_817_, 0, v___x_816_);
lean_closure_set(v___f_817_, 1, v_s_815_);
lean_closure_set(v___f_817_, 2, v_f_813_);
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_817_, v___x_818_, v_init_814_, lean_box(0));
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(lean_object* v_f_820_, lean_object* v___x_821_, lean_object* v_s_822_, lean_object* v_a_823_, lean_object* v_b_824_){
_start:
{
lean_object* v_startInclusive_825_; lean_object* v_endExclusive_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_startInclusive_825_ = lean_ctor_get(v___x_821_, 1);
v_endExclusive_826_ = lean_ctor_get(v___x_821_, 2);
v___x_827_ = lean_nat_sub(v_endExclusive_826_, v_startInclusive_825_);
v___x_828_ = lean_nat_dec_eq(v_a_823_, v___x_827_);
lean_dec(v___x_827_);
if (v___x_828_ == 0)
{
uint32_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = lean_string_utf8_get_fast(v_s_822_, v_a_823_);
v___x_830_ = lean_string_utf8_next_fast(v_s_822_, v_a_823_);
lean_dec(v_a_823_);
v___x_831_ = lean_box_uint32(v___x_829_);
lean_inc_ref(v_f_820_);
v___x_832_ = lean_apply_2(v_f_820_, v_b_824_, v___x_831_);
v_a_823_ = v___x_830_;
v_b_824_ = v___x_832_;
goto _start;
}
else
{
lean_dec(v_a_823_);
lean_dec_ref(v_f_820_);
return v_b_824_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg___boxed(lean_object* v_f_834_, lean_object* v___x_835_, lean_object* v_s_836_, lean_object* v_a_837_, lean_object* v_b_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(v_f_834_, v___x_835_, v_s_836_, v_a_837_, v_b_838_);
lean_dec_ref(v_s_836_);
lean_dec_ref(v___x_835_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* lean_string_foldl(lean_object* v_f_840_, lean_object* v_init_841_, lean_object* v_s_842_){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = lean_string_utf8_byte_size(v_s_842_);
lean_inc_ref(v_s_842_);
v___x_845_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_845_, 0, v_s_842_);
lean_ctor_set(v___x_845_, 1, v___x_843_);
lean_ctor_set(v___x_845_, 2, v___x_844_);
v___x_846_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(v_f_840_, v___x_845_, v_s_842_, v___x_843_, v_init_841_);
lean_dec_ref(v_s_842_);
lean_dec_ref(v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0(lean_object* v_f_847_, lean_object* v___x_848_, lean_object* v_s_849_, lean_object* v_inst_850_, lean_object* v_R_851_, lean_object* v_a_852_, lean_object* v_b_853_, lean_object* v_c_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(v_f_847_, v___x_848_, v_s_849_, v_a_852_, v_b_853_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___boxed(lean_object* v_f_856_, lean_object* v___x_857_, lean_object* v_s_858_, lean_object* v_inst_859_, lean_object* v_R_860_, lean_object* v_a_861_, lean_object* v_b_862_, lean_object* v_c_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0(v_f_856_, v___x_857_, v_s_858_, v_inst_859_, v_R_860_, v_a_861_, v_b_862_, v_c_863_);
lean_dec_ref(v_s_858_);
lean_dec_ref(v___x_857_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_String_foldr___redArg___lam__0(lean_object* v___x_865_, lean_object* v___x_866_, lean_object* v_s_867_, lean_object* v_f_868_, lean_object* v_it_869_, lean_object* v_acc_870_, lean_object* v_hP_871_, lean_object* v_recur_872_){
_start:
{
uint8_t v___x_873_; 
v___x_873_ = lean_nat_dec_eq(v_it_869_, v___x_865_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v_prevPos_876_; uint32_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_874_ = lean_unsigned_to_nat(1u);
v___x_875_ = lean_nat_sub(v_it_869_, v___x_874_);
v_prevPos_876_ = l_String_Slice_posLE(v___x_866_, v___x_875_);
v___x_877_ = lean_string_utf8_get_fast(v_s_867_, v_prevPos_876_);
v___x_878_ = lean_box_uint32(v___x_877_);
v___x_879_ = lean_apply_2(v_f_868_, v___x_878_, v_acc_870_);
v___x_880_ = lean_apply_4(v_recur_872_, v_prevPos_876_, v___x_879_, lean_box(0), lean_box(0));
return v___x_880_;
}
else
{
lean_dec(v_recur_872_);
lean_dec(v_f_868_);
return v_acc_870_;
}
}
}
LEAN_EXPORT lean_object* l_String_foldr___redArg___lam__0___boxed(lean_object* v___x_881_, lean_object* v___x_882_, lean_object* v_s_883_, lean_object* v_f_884_, lean_object* v_it_885_, lean_object* v_acc_886_, lean_object* v_hP_887_, lean_object* v_recur_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_String_foldr___redArg___lam__0(v___x_881_, v___x_882_, v_s_883_, v_f_884_, v_it_885_, v_acc_886_, v_hP_887_, v_recur_888_);
lean_dec(v_it_885_);
lean_dec_ref(v_s_883_);
lean_dec_ref(v___x_882_);
lean_dec(v___x_881_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_String_foldr___redArg(lean_object* v_f_890_, lean_object* v_init_891_, lean_object* v_s_892_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = lean_string_utf8_byte_size(v_s_892_);
lean_inc_ref(v_s_892_);
v___x_895_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_895_, 0, v_s_892_);
lean_ctor_set(v___x_895_, 1, v___x_893_);
lean_ctor_set(v___x_895_, 2, v___x_894_);
lean_inc_ref(v___x_895_);
v___f_896_ = lean_alloc_closure((void*)(l_String_foldr___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_896_, 0, v___x_893_);
lean_closure_set(v___f_896_, 1, v___x_895_);
lean_closure_set(v___f_896_, 2, v_s_892_);
lean_closure_set(v___f_896_, 3, v_f_890_);
v___x_897_ = l_String_Slice_revPositions(v___x_895_);
lean_dec_ref(v___x_895_);
v___x_898_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_896_, v___x_897_, v_init_891_, lean_box(0));
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_String_foldr(lean_object* v_00_u03b1_899_, lean_object* v_f_900_, lean_object* v_init_901_, lean_object* v_s_902_){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___f_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = lean_string_utf8_byte_size(v_s_902_);
lean_inc_ref(v_s_902_);
v___x_905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_905_, 0, v_s_902_);
lean_ctor_set(v___x_905_, 1, v___x_903_);
lean_ctor_set(v___x_905_, 2, v___x_904_);
lean_inc_ref(v___x_905_);
v___f_906_ = lean_alloc_closure((void*)(l_String_foldr___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_906_, 0, v___x_903_);
lean_closure_set(v___f_906_, 1, v___x_905_);
lean_closure_set(v___f_906_, 2, v_s_902_);
lean_closure_set(v___f_906_, 3, v_f_900_);
v___x_907_ = l_String_Slice_revPositions(v___x_905_);
lean_dec_ref(v___x_905_);
v___x_908_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_906_, v___x_907_, v_init_901_, lean_box(0));
return v___x_908_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Iterate(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Iterate(builtin);
}
#ifdef __cplusplus
}
#endif
