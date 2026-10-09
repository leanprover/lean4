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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default___redArg();
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator___redArg();
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_positions___redArg();
LEAN_EXPORT lean_object* l_String_Slice_positions___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_positions(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_positions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_chars___redArg();
LEAN_EXPORT lean_object* l_String_Slice_chars___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_chars(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_chars___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_length(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_length___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default___redArg();
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator___redArg();
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String_positions___redArg();
LEAN_EXPORT lean_object* l_String_positions___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_positions(lean_object*);
LEAN_EXPORT lean_object* l_String_positions___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_chars___redArg();
LEAN_EXPORT lean_object* l_String_chars___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_instInhabitedPosIterator_default___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
}
LEAN_EXPORT void l_String_Slice_instInhabitedPosIterator_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_String_Slice_instInhabitedPosIterator_default___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_String_Slice_instInhabitedPosIterator_default___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default(lean_object* v_s_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(0u);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default___boxed(lean_object* v_s_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_String_Slice_instInhabitedPosIterator_default(v_s_8_);
lean_dec_ref(v_s_8_);
return v_res_9_;
}
}
lean_object* l_String_Slice_instInhabitedPosIterator___redArg(){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(0u);
return v___x_11_;
}
}
LEAN_EXPORT void l_String_Slice_instInhabitedPosIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_12_;
v_res_12_ = l_String_Slice_instInhabitedPosIterator___redArg();
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator___redArg___boxed(lean_object* v___dummy_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_String_Slice_instInhabitedPosIterator___redArg();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator(lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_unsigned_to_nat(0u);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator___boxed(lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_String_Slice_instInhabitedPosIterator(v_a_17_);
lean_dec_ref(v_a_17_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___redArg(lean_object* v_p_19_){
_start:
{
lean_inc(v_p_19_);
return v_p_19_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___redArg___boxed(lean_object* v_p_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_String_Slice_positionsFrom___redArg(v_p_20_);
lean_dec(v_p_20_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom(lean_object* v_s_22_, lean_object* v_p_23_){
_start:
{
lean_inc(v_p_23_);
return v_p_23_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___boxed(lean_object* v_s_24_, lean_object* v_p_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_String_Slice_positionsFrom(v_s_24_, v_p_25_);
lean_dec(v_p_25_);
lean_dec_ref(v_s_24_);
return v_res_26_;
}
}
lean_object* l_String_Slice_positions___redArg(){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_unsigned_to_nat(0u);
return v___x_28_;
}
}
LEAN_EXPORT void l_String_Slice_positions___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_29_;
v_res_29_ = l_String_Slice_positions___redArg();
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_String_Slice_positions___redArg___boxed(lean_object* v___dummy_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_String_Slice_positions___redArg();
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positions(lean_object* v_s_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_unsigned_to_nat(0u);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positions___boxed(lean_object* v_s_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_String_Slice_positions(v_s_34_);
lean_dec_ref(v_s_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(lean_object* v_s_36_, lean_object* v_inst_37_, lean_object* v_x_38_){
_start:
{
lean_object* v_str_39_; lean_object* v_startInclusive_40_; lean_object* v_endExclusive_41_; lean_object* v___x_42_; uint8_t v_decide_43_; 
v_str_39_ = lean_ctor_get(v_s_36_, 0);
v_startInclusive_40_ = lean_ctor_get(v_s_36_, 1);
v_endExclusive_41_ = lean_ctor_get(v_s_36_, 2);
v___x_42_ = lean_nat_sub(v_endExclusive_41_, v_startInclusive_40_);
v_decide_43_ = lean_nat_dec_eq(v_x_38_, v___x_42_);
lean_dec(v___x_42_);
if (v_decide_43_ == 0)
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_44_ = lean_nat_add(v_startInclusive_40_, v_x_38_);
v___x_45_ = lean_string_utf8_next_fast(v_str_39_, v___x_44_);
lean_dec(v___x_44_);
v___x_46_ = lean_nat_sub(v___x_45_, v_startInclusive_40_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v_x_38_);
v___x_48_ = lean_apply_2(v_inst_37_, lean_box(0), v___x_47_);
return v___x_48_;
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_x_38_);
v___x_49_ = lean_box(2);
v___x_50_ = lean_apply_2(v_inst_37_, lean_box(0), v___x_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(lean_object* v_s_51_, lean_object* v_inst_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(v_s_51_, v_inst_52_, v_x_53_);
lean_dec_ref(v_s_51_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(lean_object* v_s_55_, lean_object* v_inst_56_){
_start:
{
lean_object* v___f_57_; 
v___f_57_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_57_, 0, v_s_55_);
lean_closure_set(v___f_57_, 1, v_inst_56_);
return v___f_57_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure(lean_object* v_m_58_, lean_object* v_s_59_, lean_object* v_inst_60_){
_start:
{
lean_object* v___f_61_; 
v___f_61_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_61_, 0, v_s_59_);
lean_closure_set(v___f_61_, 1, v_inst_60_);
return v___f_61_;
}
}
lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(0);
return v___x_63_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_64_;
v_res_64_ = l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___redArg();
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___redArg();
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation(lean_object* v_m_67_, lean_object* v_s_68_, lean_object* v_inst_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(0);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___boxed(lean_object* v_m_71_, lean_object* v_s_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation(v_m_71_, v_s_72_, v_inst_73_);
lean_dec(v_inst_73_);
lean_dec_ref(v_s_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(lean_object* v_toPure_75_, lean_object* v_recur_76_, lean_object* v_it_77_, lean_object* v_____do__lift_78_){
_start:
{
if (lean_obj_tag(v_____do__lift_78_) == 0)
{
lean_object* v_a_79_; lean_object* v___x_80_; 
lean_dec(v_it_77_);
lean_dec(v_recur_76_);
v_a_79_ = lean_ctor_get(v_____do__lift_78_, 0);
lean_inc(v_a_79_);
lean_dec_ref_known(v_____do__lift_78_, 1);
v___x_80_ = lean_apply_2(v_toPure_75_, lean_box(0), v_a_79_);
return v___x_80_;
}
else
{
lean_object* v_a_81_; lean_object* v___x_82_; 
lean_dec(v_toPure_75_);
v_a_81_ = lean_ctor_get(v_____do__lift_78_, 0);
lean_inc(v_a_81_);
lean_dec_ref_known(v_____do__lift_78_, 1);
v___x_82_ = lean_apply_4(v_recur_76_, v_it_77_, v_a_81_, lean_box(0), lean_box(0));
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1(lean_object* v_toPure_83_, lean_object* v_recur_84_, lean_object* v___y_85_, lean_object* v_acc_86_, lean_object* v_toBind_87_, lean_object* v_s_88_){
_start:
{
switch(lean_obj_tag(v_s_88_))
{
case 0:
{
lean_object* v_it_89_; lean_object* v_out_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_it_89_ = lean_ctor_get(v_s_88_, 0);
lean_inc(v_it_89_);
v_out_90_ = lean_ctor_get(v_s_88_, 1);
lean_inc(v_out_90_);
lean_dec_ref_known(v_s_88_, 2);
v___f_91_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_91_, 0, v_toPure_83_);
lean_closure_set(v___f_91_, 1, v_recur_84_);
lean_closure_set(v___f_91_, 2, v_it_89_);
v___x_92_ = lean_apply_3(v___y_85_, v_out_90_, lean_box(0), v_acc_86_);
v___x_93_ = lean_apply_4(v_toBind_87_, lean_box(0), lean_box(0), v___x_92_, v___f_91_);
return v___x_93_;
}
case 1:
{
lean_object* v_it_94_; lean_object* v___x_95_; 
lean_dec(v_toBind_87_);
lean_dec(v___y_85_);
lean_dec(v_toPure_83_);
v_it_94_ = lean_ctor_get(v_s_88_, 0);
lean_inc(v_it_94_);
lean_dec_ref_known(v_s_88_, 1);
v___x_95_ = lean_apply_4(v_recur_84_, v_it_94_, v_acc_86_, lean_box(0), lean_box(0));
return v___x_95_;
}
default: 
{
lean_object* v___x_96_; 
lean_dec(v_toBind_87_);
lean_dec(v___y_85_);
lean_dec(v_recur_84_);
v___x_96_ = lean_apply_2(v_toPure_83_, lean_box(0), v_acc_86_);
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(lean_object* v_s_97_, lean_object* v_toPure_98_, lean_object* v___y_99_, lean_object* v_toBind_100_, lean_object* v_toPure_101_, lean_object* v_lift_102_, lean_object* v_it_103_, lean_object* v_acc_104_, lean_object* v_hP_105_, lean_object* v_recur_106_){
_start:
{
lean_object* v_str_107_; lean_object* v_startInclusive_108_; lean_object* v_endExclusive_109_; lean_object* v___f_110_; lean_object* v___x_111_; uint8_t v_decide_112_; 
v_str_107_ = lean_ctor_get(v_s_97_, 0);
v_startInclusive_108_ = lean_ctor_get(v_s_97_, 1);
v_endExclusive_109_ = lean_ctor_get(v_s_97_, 2);
v___f_110_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_110_, 0, v_toPure_98_);
lean_closure_set(v___f_110_, 1, v_recur_106_);
lean_closure_set(v___f_110_, 2, v___y_99_);
lean_closure_set(v___f_110_, 3, v_acc_104_);
lean_closure_set(v___f_110_, 4, v_toBind_100_);
v___x_111_ = lean_nat_sub(v_endExclusive_109_, v_startInclusive_108_);
v_decide_112_ = lean_nat_dec_eq(v_it_103_, v___x_111_);
lean_dec(v___x_111_);
if (v_decide_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_113_ = lean_nat_add(v_startInclusive_108_, v_it_103_);
v___x_114_ = lean_string_utf8_next_fast(v_str_107_, v___x_113_);
lean_dec(v___x_113_);
v___x_115_ = lean_nat_sub(v___x_114_, v_startInclusive_108_);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v_it_103_);
v___x_117_ = lean_apply_2(v_toPure_101_, lean_box(0), v___x_116_);
v___x_118_ = lean_apply_4(v_lift_102_, lean_box(0), lean_box(0), v___f_110_, v___x_117_);
return v___x_118_;
}
else
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_it_103_);
v___x_119_ = lean_box(2);
v___x_120_ = lean_apply_2(v_toPure_101_, lean_box(0), v___x_119_);
v___x_121_ = lean_apply_4(v_lift_102_, lean_box(0), lean_box(0), v___f_110_, v___x_120_);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(lean_object* v_s_122_, lean_object* v_toPure_123_, lean_object* v___y_124_, lean_object* v_toBind_125_, lean_object* v_toPure_126_, lean_object* v_lift_127_, lean_object* v_it_128_, lean_object* v_acc_129_, lean_object* v_hP_130_, lean_object* v_recur_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(v_s_122_, v_toPure_123_, v___y_124_, v_toBind_125_, v_toPure_126_, v_lift_127_, v_it_128_, v_acc_129_, v_hP_130_, v_recur_131_);
lean_dec_ref(v_s_122_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__3(lean_object* v_inst_133_, lean_object* v_s_134_, lean_object* v_toPure_135_, lean_object* v_lift_136_, lean_object* v_00_u03b3_137_, lean_object* v_Pl_138_, lean_object* v_it_139_, lean_object* v_init_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_toApplicative_142_; lean_object* v_toBind_143_; lean_object* v_toPure_144_; lean_object* v___f_145_; lean_object* v___x_146_; 
v_toApplicative_142_ = lean_ctor_get(v_inst_133_, 0);
lean_inc_ref(v_toApplicative_142_);
v_toBind_143_ = lean_ctor_get(v_inst_133_, 1);
lean_inc(v_toBind_143_);
lean_dec_ref(v_inst_133_);
v_toPure_144_ = lean_ctor_get(v_toApplicative_142_, 1);
lean_inc(v_toPure_144_);
lean_dec_ref(v_toApplicative_142_);
v___f_145_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed), 10, 6);
lean_closure_set(v___f_145_, 0, v_s_134_);
lean_closure_set(v___f_145_, 1, v_toPure_144_);
lean_closure_set(v___f_145_, 2, v___y_141_);
lean_closure_set(v___f_145_, 3, v_toBind_143_);
lean_closure_set(v___f_145_, 4, v_toPure_135_);
lean_closure_set(v___f_145_, 5, v_lift_136_);
v___x_146_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_145_, v_it_139_, v_init_140_, lean_box(0));
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(lean_object* v_s_147_, lean_object* v_inst_148_, lean_object* v_inst_149_){
_start:
{
lean_object* v_toApplicative_150_; lean_object* v_toPure_151_; lean_object* v___f_152_; 
v_toApplicative_150_ = lean_ctor_get(v_inst_148_, 0);
lean_inc_ref(v_toApplicative_150_);
lean_dec_ref(v_inst_148_);
v_toPure_151_ = lean_ctor_get(v_toApplicative_150_, 1);
lean_inc(v_toPure_151_);
lean_dec_ref(v_toApplicative_150_);
v___f_152_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_152_, 0, v_inst_149_);
lean_closure_set(v___f_152_, 1, v_s_147_);
lean_closure_set(v___f_152_, 2, v_toPure_151_);
return v___f_152_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(lean_object* v_m_153_, lean_object* v_n_154_, lean_object* v_s_155_, lean_object* v_inst_156_, lean_object* v_inst_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(v_s_155_, v_inst_156_, v_inst_157_);
return v___x_158_;
}
}
lean_object* l_String_Slice_chars___redArg(){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_unsigned_to_nat(0u);
return v___x_160_;
}
}
LEAN_EXPORT void l_String_Slice_chars___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_161_;
v_res_161_ = l_String_Slice_chars___redArg();
stack->m_obj
 = v_res_161_;
}
LEAN_EXPORT lean_object* l_String_Slice_chars___redArg___boxed(lean_object* v___dummy_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_String_Slice_chars___redArg();
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_chars(lean_object* v_s_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_unsigned_to_nat(0u);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_chars___boxed(lean_object* v_s_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_String_Slice_chars(v_s_166_);
lean_dec_ref(v_s_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(lean_object* v_s_168_, lean_object* v_a_169_, lean_object* v_b_170_){
_start:
{
lean_object* v_str_171_; lean_object* v_startInclusive_172_; lean_object* v_endExclusive_173_; lean_object* v___x_174_; uint8_t v_decide_175_; 
v_str_171_ = lean_ctor_get(v_s_168_, 0);
v_startInclusive_172_ = lean_ctor_get(v_s_168_, 1);
v_endExclusive_173_ = lean_ctor_get(v_s_168_, 2);
v___x_174_ = lean_nat_sub(v_endExclusive_173_, v_startInclusive_172_);
v_decide_175_ = lean_nat_dec_eq(v_a_169_, v___x_174_);
lean_dec(v___x_174_);
if (v_decide_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_176_ = lean_nat_add(v_startInclusive_172_, v_a_169_);
lean_dec(v_a_169_);
v___x_177_ = lean_string_utf8_next_fast(v_str_171_, v___x_176_);
lean_dec(v___x_176_);
v___x_178_ = lean_nat_sub(v___x_177_, v_startInclusive_172_);
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_nat_add(v_b_170_, v___x_179_);
lean_dec(v_b_170_);
v_a_169_ = v___x_178_;
v_b_170_ = v___x_180_;
goto _start;
}
else
{
lean_dec(v_a_169_);
return v_b_170_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg___boxed(lean_object* v_s_182_, lean_object* v_a_183_, lean_object* v_b_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(v_s_182_, v_a_183_, v_b_184_);
lean_dec_ref(v_s_182_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_length(lean_object* v_s_186_){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(v_s_186_, v___x_187_, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_length___boxed(lean_object* v_s_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_String_Slice_length(v_s_189_);
lean_dec_ref(v_s_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0(lean_object* v_s_191_, lean_object* v_inst_192_, lean_object* v_R_193_, lean_object* v_a_194_, lean_object* v_b_195_, lean_object* v_c_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(v_s_191_, v_a_194_, v_b_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___boxed(lean_object* v_s_198_, lean_object* v_inst_199_, lean_object* v_R_200_, lean_object* v_a_201_, lean_object* v_b_202_, lean_object* v_c_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0(v_s_198_, v_inst_199_, v_R_200_, v_a_201_, v_b_202_, v_c_203_);
lean_dec_ref(v_s_198_);
return v_res_204_;
}
}
lean_object* l_String_Slice_instInhabitedRevPosIterator_default___redArg(){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_unsigned_to_nat(0u);
return v___x_206_;
}
}
LEAN_EXPORT void l_String_Slice_instInhabitedRevPosIterator_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_207_;
v_res_207_ = l_String_Slice_instInhabitedRevPosIterator_default___redArg();
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default___redArg___boxed(lean_object* v___dummy_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_String_Slice_instInhabitedRevPosIterator_default___redArg();
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default(lean_object* v_s_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lean_unsigned_to_nat(0u);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default___boxed(lean_object* v_s_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_String_Slice_instInhabitedRevPosIterator_default(v_s_212_);
lean_dec_ref(v_s_212_);
return v_res_213_;
}
}
lean_object* l_String_Slice_instInhabitedRevPosIterator___redArg(){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_unsigned_to_nat(0u);
return v___x_215_;
}
}
LEAN_EXPORT void l_String_Slice_instInhabitedRevPosIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_216_;
v_res_216_ = l_String_Slice_instInhabitedRevPosIterator___redArg();
stack->m_obj
 = v_res_216_;
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator___redArg___boxed(lean_object* v___dummy_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_String_Slice_instInhabitedRevPosIterator___redArg();
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator(lean_object* v_a_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lean_unsigned_to_nat(0u);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator___boxed(lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_String_Slice_instInhabitedRevPosIterator(v_a_221_);
lean_dec_ref(v_a_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___redArg(lean_object* v_p_223_){
_start:
{
lean_inc(v_p_223_);
return v_p_223_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___redArg___boxed(lean_object* v_p_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_String_Slice_revPositionsFrom___redArg(v_p_224_);
lean_dec(v_p_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom(lean_object* v_s_226_, lean_object* v_p_227_){
_start:
{
lean_inc(v_p_227_);
return v_p_227_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___boxed(lean_object* v_s_228_, lean_object* v_p_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_String_Slice_revPositionsFrom(v_s_228_, v_p_229_);
lean_dec(v_p_229_);
lean_dec_ref(v_s_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositions(lean_object* v_s_231_){
_start:
{
lean_object* v_startInclusive_232_; lean_object* v_endExclusive_233_; lean_object* v___x_234_; 
v_startInclusive_232_ = lean_ctor_get(v_s_231_, 1);
v_endExclusive_233_ = lean_ctor_get(v_s_231_, 2);
v___x_234_ = lean_nat_sub(v_endExclusive_233_, v_startInclusive_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositions___boxed(lean_object* v_s_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_String_Slice_revPositions(v_s_235_);
lean_dec_ref(v_s_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(lean_object* v_s_237_, lean_object* v_inst_238_, lean_object* v_x_239_){
_start:
{
lean_object* v___x_240_; uint8_t v_decide_241_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v_decide_241_ = lean_nat_dec_eq(v_x_239_, v___x_240_);
if (v_decide_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_prevPos_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = lean_nat_sub(v_x_239_, v___x_242_);
v_prevPos_244_ = l_String_Slice_posLE(v_s_237_, v___x_243_);
lean_inc(v_prevPos_244_);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v_prevPos_244_);
lean_ctor_set(v___x_245_, 1, v_prevPos_244_);
v___x_246_ = lean_apply_2(v_inst_238_, lean_box(0), v___x_245_);
return v___x_246_;
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_box(2);
v___x_248_ = lean_apply_2(v_inst_238_, lean_box(0), v___x_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(lean_object* v_s_249_, lean_object* v_inst_250_, lean_object* v_x_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(v_s_249_, v_inst_250_, v_x_251_);
lean_dec(v_x_251_);
lean_dec_ref(v_s_249_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(lean_object* v_s_253_, lean_object* v_inst_254_){
_start:
{
lean_object* v___f_255_; 
v___f_255_ = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_255_, 0, v_s_253_);
lean_closure_set(v___f_255_, 1, v_inst_254_);
return v___f_255_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure(lean_object* v_m_256_, lean_object* v_s_257_, lean_object* v_inst_258_){
_start:
{
lean_object* v___f_259_; 
v___f_259_ = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_259_, 0, v_s_257_);
lean_closure_set(v___f_259_, 1, v_inst_258_);
return v___f_259_;
}
}
lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = lean_box(0);
return v___x_261_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_262_;
v_res_262_ = l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___redArg();
stack->m_obj
 = v_res_262_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___redArg();
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation(lean_object* v_m_265_, lean_object* v_s_266_, lean_object* v_inst_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_box(0);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___boxed(lean_object* v_m_269_, lean_object* v_s_270_, lean_object* v_inst_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation(v_m_269_, v_s_270_, v_inst_271_);
lean_dec(v_inst_271_);
lean_dec_ref(v_s_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(lean_object* v_toPure_273_, lean_object* v___y_274_, lean_object* v_toBind_275_, lean_object* v_s_276_, lean_object* v_toPure_277_, lean_object* v_lift_278_, lean_object* v_it_279_, lean_object* v_acc_280_, lean_object* v_hP_281_, lean_object* v_recur_282_){
_start:
{
lean_object* v___f_283_; lean_object* v___x_284_; uint8_t v_decide_285_; 
v___f_283_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_283_, 0, v_toPure_273_);
lean_closure_set(v___f_283_, 1, v_recur_282_);
lean_closure_set(v___f_283_, 2, v___y_274_);
lean_closure_set(v___f_283_, 3, v_acc_280_);
lean_closure_set(v___f_283_, 4, v_toBind_275_);
v___x_284_ = lean_unsigned_to_nat(0u);
v_decide_285_ = lean_nat_dec_eq(v_it_279_, v___x_284_);
if (v_decide_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v_prevPos_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_286_ = lean_unsigned_to_nat(1u);
v___x_287_ = lean_nat_sub(v_it_279_, v___x_286_);
v_prevPos_288_ = l_String_Slice_posLE(v_s_276_, v___x_287_);
lean_inc(v_prevPos_288_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_prevPos_288_);
lean_ctor_set(v___x_289_, 1, v_prevPos_288_);
v___x_290_ = lean_apply_2(v_toPure_277_, lean_box(0), v___x_289_);
v___x_291_ = lean_apply_4(v_lift_278_, lean_box(0), lean_box(0), v___f_283_, v___x_290_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_box(2);
v___x_293_ = lean_apply_2(v_toPure_277_, lean_box(0), v___x_292_);
v___x_294_ = lean_apply_4(v_lift_278_, lean_box(0), lean_box(0), v___f_283_, v___x_293_);
return v___x_294_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(lean_object* v_toPure_295_, lean_object* v___y_296_, lean_object* v_toBind_297_, lean_object* v_s_298_, lean_object* v_toPure_299_, lean_object* v_lift_300_, lean_object* v_it_301_, lean_object* v_acc_302_, lean_object* v_hP_303_, lean_object* v_recur_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(v_toPure_295_, v___y_296_, v_toBind_297_, v_s_298_, v_toPure_299_, v_lift_300_, v_it_301_, v_acc_302_, v_hP_303_, v_recur_304_);
lean_dec(v_it_301_);
lean_dec_ref(v_s_298_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(lean_object* v_inst_306_, lean_object* v_s_307_, lean_object* v_toPure_308_, lean_object* v_lift_309_, lean_object* v_00_u03b3_310_, lean_object* v_Pl_311_, lean_object* v_it_312_, lean_object* v_init_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_toApplicative_315_; lean_object* v_toBind_316_; lean_object* v_toPure_317_; lean_object* v___f_318_; lean_object* v___x_319_; 
v_toApplicative_315_ = lean_ctor_get(v_inst_306_, 0);
lean_inc_ref(v_toApplicative_315_);
v_toBind_316_ = lean_ctor_get(v_inst_306_, 1);
lean_inc(v_toBind_316_);
lean_dec_ref(v_inst_306_);
v_toPure_317_ = lean_ctor_get(v_toApplicative_315_, 1);
lean_inc(v_toPure_317_);
lean_dec_ref(v_toApplicative_315_);
v___f_318_ = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed), 10, 6);
lean_closure_set(v___f_318_, 0, v_toPure_317_);
lean_closure_set(v___f_318_, 1, v___y_314_);
lean_closure_set(v___f_318_, 2, v_toBind_316_);
lean_closure_set(v___f_318_, 3, v_s_307_);
lean_closure_set(v___f_318_, 4, v_toPure_308_);
lean_closure_set(v___f_318_, 5, v_lift_309_);
v___x_319_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_318_, v_it_312_, v_init_313_, lean_box(0));
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(lean_object* v_s_320_, lean_object* v_inst_321_, lean_object* v_inst_322_){
_start:
{
lean_object* v_toApplicative_323_; lean_object* v_toPure_324_; lean_object* v___f_325_; 
v_toApplicative_323_ = lean_ctor_get(v_inst_321_, 0);
lean_inc_ref(v_toApplicative_323_);
lean_dec_ref(v_inst_321_);
v_toPure_324_ = lean_ctor_get(v_toApplicative_323_, 1);
lean_inc(v_toPure_324_);
lean_dec_ref(v_toApplicative_323_);
v___f_325_ = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0), 9, 3);
lean_closure_set(v___f_325_, 0, v_inst_322_);
lean_closure_set(v___f_325_, 1, v_s_320_);
lean_closure_set(v___f_325_, 2, v_toPure_324_);
return v___f_325_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(lean_object* v_m_326_, lean_object* v_n_327_, lean_object* v_s_328_, lean_object* v_inst_329_, lean_object* v_inst_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(v_s_328_, v_inst_329_, v_inst_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revChars(lean_object* v_s_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_String_Slice_revPositions(v_s_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revChars___boxed(lean_object* v_s_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_String_Slice_revChars(v_s_334_);
lean_dec_ref(v_s_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_bytes(lean_object* v_s_345_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v_s_345_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0(lean_object* v_inst_348_, lean_object* v_x_349_){
_start:
{
lean_object* v_s_350_; lean_object* v_offset_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_372_; 
v_s_350_ = lean_ctor_get(v_x_349_, 0);
v_offset_351_ = lean_ctor_get(v_x_349_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v_x_349_);
if (v_isSharedCheck_372_ == 0)
{
v___x_353_ = v_x_349_;
v_isShared_354_ = v_isSharedCheck_372_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_offset_351_);
lean_inc(v_s_350_);
lean_dec(v_x_349_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_372_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v_str_355_; lean_object* v_startInclusive_356_; lean_object* v_endExclusive_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_str_355_ = lean_ctor_get(v_s_350_, 0);
lean_inc_ref(v_str_355_);
v_startInclusive_356_ = lean_ctor_get(v_s_350_, 1);
lean_inc(v_startInclusive_356_);
v_endExclusive_357_ = lean_ctor_get(v_s_350_, 2);
v___x_358_ = lean_nat_sub(v_endExclusive_357_, v_startInclusive_356_);
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_nat_add(v_offset_351_, v___x_359_);
v___x_361_ = lean_nat_dec_le(v___x_360_, v___x_358_);
lean_dec(v___x_358_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v___x_363_; 
lean_dec(v___x_360_);
lean_dec(v_startInclusive_356_);
lean_dec_ref(v_str_355_);
lean_del_object(v___x_353_);
lean_dec(v_offset_351_);
lean_dec_ref(v_s_350_);
v___x_362_ = lean_box(2);
v___x_363_ = lean_apply_2(v_inst_348_, lean_box(0), v___x_362_);
return v___x_363_;
}
else
{
lean_object* v___x_365_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_360_);
v___x_365_ = v___x_353_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_s_350_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v___x_360_);
v___x_365_ = v_reuseFailAlloc_371_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_366_ = lean_nat_add(v_startInclusive_356_, v_offset_351_);
lean_dec(v_offset_351_);
lean_dec(v_startInclusive_356_);
v___x_367_ = lean_string_get_byte_fast(v_str_355_, v___x_366_);
lean_dec_ref(v_str_355_);
v___x_368_ = lean_box(v___x_367_);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_365_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = lean_apply_2(v_inst_348_, lean_box(0), v___x_369_);
return v___x_370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg(lean_object* v_inst_373_){
_start:
{
lean_object* v___f_374_; 
v___f_374_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_374_, 0, v_inst_373_);
return v___f_374_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure(lean_object* v_m_375_, lean_object* v_inst_376_){
_start:
{
lean_object* v___f_377_; 
v___f_377_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_377_, 0, v_inst_376_);
return v___f_377_;
}
}
lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = lean_box(0);
return v___x_379_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_380_;
v_res_380_ = l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___redArg();
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___redArg();
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation(lean_object* v_m_383_, lean_object* v_inst_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_box(0);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___boxed(lean_object* v_m_386_, lean_object* v_inst_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation(v_m_386_, v_inst_387_);
lean_dec(v_inst_387_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0(lean_object* v_toPure_389_, lean_object* v_recur_390_, lean_object* v_it_391_, lean_object* v_____do__lift_392_){
_start:
{
if (lean_obj_tag(v_____do__lift_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_394_; 
lean_dec_ref(v_it_391_);
lean_dec(v_recur_390_);
v_a_393_ = lean_ctor_get(v_____do__lift_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v_____do__lift_392_, 1);
v___x_394_ = lean_apply_2(v_toPure_389_, lean_box(0), v_a_393_);
return v___x_394_;
}
else
{
lean_object* v_a_395_; lean_object* v___x_396_; 
lean_dec(v_toPure_389_);
v_a_395_ = lean_ctor_get(v_____do__lift_392_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v_____do__lift_392_, 1);
v___x_396_ = lean_apply_4(v_recur_390_, v_it_391_, v_a_395_, lean_box(0), lean_box(0));
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1(lean_object* v_toPure_397_, lean_object* v_recur_398_, lean_object* v___y_399_, lean_object* v_acc_400_, lean_object* v_toBind_401_, lean_object* v_s_402_){
_start:
{
switch(lean_obj_tag(v_s_402_))
{
case 0:
{
lean_object* v_it_403_; lean_object* v_out_404_; lean_object* v___f_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_it_403_ = lean_ctor_get(v_s_402_, 0);
lean_inc(v_it_403_);
v_out_404_ = lean_ctor_get(v_s_402_, 1);
lean_inc(v_out_404_);
lean_dec_ref_known(v_s_402_, 2);
v___f_405_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_405_, 0, v_toPure_397_);
lean_closure_set(v___f_405_, 1, v_recur_398_);
lean_closure_set(v___f_405_, 2, v_it_403_);
v___x_406_ = lean_apply_3(v___y_399_, v_out_404_, lean_box(0), v_acc_400_);
v___x_407_ = lean_apply_4(v_toBind_401_, lean_box(0), lean_box(0), v___x_406_, v___f_405_);
return v___x_407_;
}
case 1:
{
lean_object* v_it_408_; lean_object* v___x_409_; 
lean_dec(v_toBind_401_);
lean_dec(v___y_399_);
lean_dec(v_toPure_397_);
v_it_408_ = lean_ctor_get(v_s_402_, 0);
lean_inc(v_it_408_);
lean_dec_ref_known(v_s_402_, 1);
v___x_409_ = lean_apply_4(v_recur_398_, v_it_408_, v_acc_400_, lean_box(0), lean_box(0));
return v___x_409_;
}
default: 
{
lean_object* v___x_410_; 
lean_dec(v_toBind_401_);
lean_dec(v___y_399_);
lean_dec(v_recur_398_);
v___x_410_ = lean_apply_2(v_toPure_397_, lean_box(0), v_acc_400_);
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2(lean_object* v_toPure_411_, lean_object* v___y_412_, lean_object* v_toBind_413_, lean_object* v_toPure_414_, lean_object* v_lift_415_, lean_object* v_it_416_, lean_object* v_acc_417_, lean_object* v_hP_418_, lean_object* v_recur_419_){
_start:
{
lean_object* v_s_420_; lean_object* v_offset_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_445_; 
v_s_420_ = lean_ctor_get(v_it_416_, 0);
v_offset_421_ = lean_ctor_get(v_it_416_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_it_416_);
if (v_isSharedCheck_445_ == 0)
{
v___x_423_ = v_it_416_;
v_isShared_424_ = v_isSharedCheck_445_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_offset_421_);
lean_inc(v_s_420_);
lean_dec(v_it_416_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_445_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_str_425_; lean_object* v_startInclusive_426_; lean_object* v_endExclusive_427_; lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_str_425_ = lean_ctor_get(v_s_420_, 0);
lean_inc_ref(v_str_425_);
v_startInclusive_426_ = lean_ctor_get(v_s_420_, 1);
lean_inc(v_startInclusive_426_);
v_endExclusive_427_ = lean_ctor_get(v_s_420_, 2);
v___f_428_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_428_, 0, v_toPure_411_);
lean_closure_set(v___f_428_, 1, v_recur_419_);
lean_closure_set(v___f_428_, 2, v___y_412_);
lean_closure_set(v___f_428_, 3, v_acc_417_);
lean_closure_set(v___f_428_, 4, v_toBind_413_);
v___x_429_ = lean_nat_sub(v_endExclusive_427_, v_startInclusive_426_);
v___x_430_ = lean_unsigned_to_nat(1u);
v___x_431_ = lean_nat_add(v_offset_421_, v___x_430_);
v___x_432_ = lean_nat_dec_le(v___x_431_, v___x_429_);
lean_dec(v___x_429_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec(v___x_431_);
lean_dec(v_startInclusive_426_);
lean_dec_ref(v_str_425_);
lean_del_object(v___x_423_);
lean_dec(v_offset_421_);
lean_dec_ref(v_s_420_);
v___x_433_ = lean_box(2);
v___x_434_ = lean_apply_2(v_toPure_414_, lean_box(0), v___x_433_);
v___x_435_ = lean_apply_4(v_lift_415_, lean_box(0), lean_box(0), v___f_428_, v___x_434_);
return v___x_435_;
}
else
{
lean_object* v___x_437_; 
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v___x_431_);
v___x_437_ = v___x_423_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_s_420_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_431_);
v___x_437_ = v_reuseFailAlloc_444_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; uint8_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_438_ = lean_nat_add(v_startInclusive_426_, v_offset_421_);
lean_dec(v_offset_421_);
lean_dec(v_startInclusive_426_);
v___x_439_ = lean_string_get_byte_fast(v_str_425_, v___x_438_);
lean_dec_ref(v_str_425_);
v___x_440_ = lean_box(v___x_439_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_437_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = lean_apply_2(v_toPure_414_, lean_box(0), v___x_441_);
v___x_443_ = lean_apply_4(v_lift_415_, lean_box(0), lean_box(0), v___f_428_, v___x_442_);
return v___x_443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3(lean_object* v_inst_446_, lean_object* v_toPure_447_, lean_object* v_lift_448_, lean_object* v_00_u03b3_449_, lean_object* v_Pl_450_, lean_object* v_it_451_, lean_object* v_init_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_toApplicative_454_; lean_object* v_toBind_455_; lean_object* v_toPure_456_; lean_object* v___f_457_; lean_object* v___x_458_; 
v_toApplicative_454_ = lean_ctor_get(v_inst_446_, 0);
lean_inc_ref(v_toApplicative_454_);
v_toBind_455_ = lean_ctor_get(v_inst_446_, 1);
lean_inc(v_toBind_455_);
lean_dec_ref(v_inst_446_);
v_toPure_456_ = lean_ctor_get(v_toApplicative_454_, 1);
lean_inc(v_toPure_456_);
lean_dec_ref(v_toApplicative_454_);
v___f_457_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2), 9, 5);
lean_closure_set(v___f_457_, 0, v_toPure_456_);
lean_closure_set(v___f_457_, 1, v___y_453_);
lean_closure_set(v___f_457_, 2, v_toBind_455_);
lean_closure_set(v___f_457_, 3, v_toPure_447_);
lean_closure_set(v___f_457_, 4, v_lift_448_);
v___x_458_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_457_, v_it_451_, v_init_452_, lean_box(0));
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg(lean_object* v_inst_459_, lean_object* v_inst_460_){
_start:
{
lean_object* v_toApplicative_461_; lean_object* v_toPure_462_; lean_object* v___f_463_; 
v_toApplicative_461_ = lean_ctor_get(v_inst_459_, 0);
lean_inc_ref(v_toApplicative_461_);
lean_dec_ref(v_inst_459_);
v_toPure_462_ = lean_ctor_get(v_toApplicative_461_, 1);
lean_inc(v_toPure_462_);
lean_dec_ref(v_toApplicative_461_);
v___f_463_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3), 8, 2);
lean_closure_set(v___f_463_, 0, v_inst_460_);
lean_closure_set(v___f_463_, 1, v_toPure_462_);
return v___f_463_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad(lean_object* v_m_464_, lean_object* v_n_465_, lean_object* v_inst_466_, lean_object* v_inst_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg(v_inst_466_, v_inst_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revBytes(lean_object* v_s_469_){
_start:
{
lean_object* v_startInclusive_470_; lean_object* v_endExclusive_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_startInclusive_470_ = lean_ctor_get(v_s_469_, 1);
v_endExclusive_471_ = lean_ctor_get(v_s_469_, 2);
v___x_472_ = lean_nat_sub(v_endExclusive_471_, v_startInclusive_470_);
v___x_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_473_, 0, v_s_469_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0(lean_object* v_inst_478_, lean_object* v_x_479_){
_start:
{
lean_object* v_s_480_; lean_object* v_offset_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_501_; 
v_s_480_ = lean_ctor_get(v_x_479_, 0);
v_offset_481_ = lean_ctor_get(v_x_479_, 1);
v_isSharedCheck_501_ = !lean_is_exclusive(v_x_479_);
if (v_isSharedCheck_501_ == 0)
{
v___x_483_ = v_x_479_;
v_isShared_484_ = v_isSharedCheck_501_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_offset_481_);
lean_inc(v_s_480_);
lean_dec(v_x_479_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_501_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; uint8_t v_decide_486_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v_decide_486_ = lean_nat_dec_eq(v_offset_481_, v___x_485_);
if (v_decide_486_ == 0)
{
lean_object* v_str_487_; lean_object* v_startInclusive_488_; lean_object* v___x_489_; lean_object* v_nextOffset_490_; lean_object* v___x_492_; 
v_str_487_ = lean_ctor_get(v_s_480_, 0);
lean_inc_ref(v_str_487_);
v_startInclusive_488_ = lean_ctor_get(v_s_480_, 1);
lean_inc(v_startInclusive_488_);
v___x_489_ = lean_unsigned_to_nat(1u);
v_nextOffset_490_ = lean_nat_sub(v_offset_481_, v___x_489_);
lean_dec(v_offset_481_);
lean_inc(v_nextOffset_490_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v_nextOffset_490_);
v___x_492_ = v___x_483_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_s_480_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_nextOffset_490_);
v___x_492_ = v_reuseFailAlloc_498_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_493_ = lean_nat_add(v_startInclusive_488_, v_nextOffset_490_);
lean_dec(v_nextOffset_490_);
lean_dec(v_startInclusive_488_);
v___x_494_ = lean_string_get_byte_fast(v_str_487_, v___x_493_);
lean_dec_ref(v_str_487_);
v___x_495_ = lean_box(v___x_494_);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_492_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = lean_apply_2(v_inst_478_, lean_box(0), v___x_496_);
return v___x_497_;
}
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_del_object(v___x_483_);
lean_dec(v_offset_481_);
lean_dec_ref(v_s_480_);
v___x_499_ = lean_box(2);
v___x_500_ = lean_apply_2(v_inst_478_, lean_box(0), v___x_499_);
return v___x_500_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg(lean_object* v_inst_502_){
_start:
{
lean_object* v___f_503_; 
v___f_503_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_503_, 0, v_inst_502_);
return v___f_503_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure(lean_object* v_m_504_, lean_object* v_inst_505_){
_start:
{
lean_object* v___f_506_; 
v___f_506_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_506_, 0, v_inst_505_);
return v___f_506_;
}
}
lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = lean_box(0);
return v___x_508_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_509_;
v_res_509_ = l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___redArg();
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___redArg();
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation(lean_object* v_m_512_, lean_object* v_inst_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = lean_box(0);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___boxed(lean_object* v_m_515_, lean_object* v_inst_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation(v_m_515_, v_inst_516_);
lean_dec(v_inst_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0(lean_object* v_toPure_518_, lean_object* v_recur_519_, lean_object* v_it_520_, lean_object* v_____do__lift_521_){
_start:
{
if (lean_obj_tag(v_____do__lift_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; 
lean_dec_ref(v_it_520_);
lean_dec(v_recur_519_);
v_a_522_ = lean_ctor_get(v_____do__lift_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v_____do__lift_521_, 1);
v___x_523_ = lean_apply_2(v_toPure_518_, lean_box(0), v_a_522_);
return v___x_523_;
}
else
{
lean_object* v_a_524_; lean_object* v___x_525_; 
lean_dec(v_toPure_518_);
v_a_524_ = lean_ctor_get(v_____do__lift_521_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v_____do__lift_521_, 1);
v___x_525_ = lean_apply_4(v_recur_519_, v_it_520_, v_a_524_, lean_box(0), lean_box(0));
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1(lean_object* v_toPure_526_, lean_object* v_recur_527_, lean_object* v___y_528_, lean_object* v_acc_529_, lean_object* v_toBind_530_, lean_object* v_s_531_){
_start:
{
switch(lean_obj_tag(v_s_531_))
{
case 0:
{
lean_object* v_it_532_; lean_object* v_out_533_; lean_object* v___f_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_it_532_ = lean_ctor_get(v_s_531_, 0);
lean_inc(v_it_532_);
v_out_533_ = lean_ctor_get(v_s_531_, 1);
lean_inc(v_out_533_);
lean_dec_ref_known(v_s_531_, 2);
v___f_534_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_534_, 0, v_toPure_526_);
lean_closure_set(v___f_534_, 1, v_recur_527_);
lean_closure_set(v___f_534_, 2, v_it_532_);
v___x_535_ = lean_apply_3(v___y_528_, v_out_533_, lean_box(0), v_acc_529_);
v___x_536_ = lean_apply_4(v_toBind_530_, lean_box(0), lean_box(0), v___x_535_, v___f_534_);
return v___x_536_;
}
case 1:
{
lean_object* v_it_537_; lean_object* v___x_538_; 
lean_dec(v_toBind_530_);
lean_dec(v___y_528_);
lean_dec(v_toPure_526_);
v_it_537_ = lean_ctor_get(v_s_531_, 0);
lean_inc(v_it_537_);
lean_dec_ref_known(v_s_531_, 1);
v___x_538_ = lean_apply_4(v_recur_527_, v_it_537_, v_acc_529_, lean_box(0), lean_box(0));
return v___x_538_;
}
default: 
{
lean_object* v___x_539_; 
lean_dec(v_toBind_530_);
lean_dec(v___y_528_);
lean_dec(v_recur_527_);
v___x_539_ = lean_apply_2(v_toPure_526_, lean_box(0), v_acc_529_);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2(lean_object* v_toPure_540_, lean_object* v___y_541_, lean_object* v_toBind_542_, lean_object* v_toPure_543_, lean_object* v_lift_544_, lean_object* v_it_545_, lean_object* v_acc_546_, lean_object* v_hP_547_, lean_object* v_recur_548_){
_start:
{
lean_object* v_s_549_; lean_object* v_offset_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_573_; 
v_s_549_ = lean_ctor_get(v_it_545_, 0);
v_offset_550_ = lean_ctor_get(v_it_545_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_it_545_);
if (v_isSharedCheck_573_ == 0)
{
v___x_552_ = v_it_545_;
v_isShared_553_ = v_isSharedCheck_573_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_offset_550_);
lean_inc(v_s_549_);
lean_dec(v_it_545_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_573_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___f_554_; lean_object* v___x_555_; uint8_t v_decide_556_; 
v___f_554_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_554_, 0, v_toPure_540_);
lean_closure_set(v___f_554_, 1, v_recur_548_);
lean_closure_set(v___f_554_, 2, v___y_541_);
lean_closure_set(v___f_554_, 3, v_acc_546_);
lean_closure_set(v___f_554_, 4, v_toBind_542_);
v___x_555_ = lean_unsigned_to_nat(0u);
v_decide_556_ = lean_nat_dec_eq(v_offset_550_, v___x_555_);
if (v_decide_556_ == 0)
{
lean_object* v_str_557_; lean_object* v_startInclusive_558_; lean_object* v___x_559_; lean_object* v_nextOffset_560_; lean_object* v___x_562_; 
v_str_557_ = lean_ctor_get(v_s_549_, 0);
lean_inc_ref(v_str_557_);
v_startInclusive_558_ = lean_ctor_get(v_s_549_, 1);
lean_inc(v_startInclusive_558_);
v___x_559_ = lean_unsigned_to_nat(1u);
v_nextOffset_560_ = lean_nat_sub(v_offset_550_, v___x_559_);
lean_dec(v_offset_550_);
lean_inc(v_nextOffset_560_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v_nextOffset_560_);
v___x_562_ = v___x_552_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_s_549_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_nextOffset_560_);
v___x_562_ = v_reuseFailAlloc_569_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; uint8_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_563_ = lean_nat_add(v_startInclusive_558_, v_nextOffset_560_);
lean_dec(v_nextOffset_560_);
lean_dec(v_startInclusive_558_);
v___x_564_ = lean_string_get_byte_fast(v_str_557_, v___x_563_);
lean_dec_ref(v_str_557_);
v___x_565_ = lean_box(v___x_564_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_562_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = lean_apply_2(v_toPure_543_, lean_box(0), v___x_566_);
v___x_568_ = lean_apply_4(v_lift_544_, lean_box(0), lean_box(0), v___f_554_, v___x_567_);
return v___x_568_;
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
lean_del_object(v___x_552_);
lean_dec(v_offset_550_);
lean_dec_ref(v_s_549_);
v___x_570_ = lean_box(2);
v___x_571_ = lean_apply_2(v_toPure_543_, lean_box(0), v___x_570_);
v___x_572_ = lean_apply_4(v_lift_544_, lean_box(0), lean_box(0), v___f_554_, v___x_571_);
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3(lean_object* v_inst_574_, lean_object* v_toPure_575_, lean_object* v_lift_576_, lean_object* v_00_u03b3_577_, lean_object* v_Pl_578_, lean_object* v_it_579_, lean_object* v_init_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_toApplicative_582_; lean_object* v_toBind_583_; lean_object* v_toPure_584_; lean_object* v___f_585_; lean_object* v___x_586_; 
v_toApplicative_582_ = lean_ctor_get(v_inst_574_, 0);
lean_inc_ref(v_toApplicative_582_);
v_toBind_583_ = lean_ctor_get(v_inst_574_, 1);
lean_inc(v_toBind_583_);
lean_dec_ref(v_inst_574_);
v_toPure_584_ = lean_ctor_get(v_toApplicative_582_, 1);
lean_inc(v_toPure_584_);
lean_dec_ref(v_toApplicative_582_);
v___f_585_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2), 9, 5);
lean_closure_set(v___f_585_, 0, v_toPure_584_);
lean_closure_set(v___f_585_, 1, v___y_581_);
lean_closure_set(v___f_585_, 2, v_toBind_583_);
lean_closure_set(v___f_585_, 3, v_toPure_575_);
lean_closure_set(v___f_585_, 4, v_lift_576_);
v___x_586_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_585_, v_it_579_, v_init_580_, lean_box(0));
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg(lean_object* v_inst_587_, lean_object* v_inst_588_){
_start:
{
lean_object* v_toApplicative_589_; lean_object* v_toPure_590_; lean_object* v___f_591_; 
v_toApplicative_589_ = lean_ctor_get(v_inst_587_, 0);
lean_inc_ref(v_toApplicative_589_);
lean_dec_ref(v_inst_587_);
v_toPure_590_ = lean_ctor_get(v_toApplicative_589_, 1);
lean_inc(v_toPure_590_);
lean_dec_ref(v_toApplicative_589_);
v___f_591_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3), 8, 2);
lean_closure_set(v___f_591_, 0, v_inst_588_);
lean_closure_set(v___f_591_, 1, v_toPure_590_);
return v___f_591_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad(lean_object* v_m_592_, lean_object* v_n_593_, lean_object* v_inst_594_, lean_object* v_inst_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg(v_inst_594_, v_inst_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0(lean_object* v_toPure_597_, lean_object* v_____do__lift_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_apply_2(v_toPure_597_, lean_box(0), v_____do__lift_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1(lean_object* v_toPure_600_, lean_object* v_recur_601_, lean_object* v___x_602_, lean_object* v_____do__lift_603_){
_start:
{
if (lean_obj_tag(v_____do__lift_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_605_; 
lean_dec(v___x_602_);
lean_dec(v_recur_601_);
v_a_604_ = lean_ctor_get(v_____do__lift_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v_____do__lift_603_, 1);
v___x_605_ = lean_apply_2(v_toPure_600_, lean_box(0), v_a_604_);
return v___x_605_;
}
else
{
lean_object* v_a_606_; lean_object* v___x_607_; 
lean_dec(v_toPure_600_);
v_a_606_ = lean_ctor_get(v_____do__lift_603_, 0);
lean_inc(v_a_606_);
lean_dec_ref_known(v_____do__lift_603_, 1);
v___x_607_ = lean_apply_4(v_recur_601_, v___x_602_, v_a_606_, lean_box(0), lean_box(0));
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2(lean_object* v_s_608_, lean_object* v_toPure_609_, lean_object* v_f_610_, lean_object* v_toBind_611_, lean_object* v___f_612_, lean_object* v_it_613_, lean_object* v_acc_614_, lean_object* v_hP_615_, lean_object* v_recur_616_){
_start:
{
lean_object* v_str_617_; lean_object* v_startInclusive_618_; lean_object* v_endExclusive_619_; lean_object* v___x_620_; uint8_t v_decide_621_; 
v_str_617_ = lean_ctor_get(v_s_608_, 0);
v_startInclusive_618_ = lean_ctor_get(v_s_608_, 1);
v_endExclusive_619_ = lean_ctor_get(v_s_608_, 2);
v___x_620_ = lean_nat_sub(v_endExclusive_619_, v_startInclusive_618_);
v_decide_621_ = lean_nat_dec_eq(v_it_613_, v___x_620_);
lean_dec(v___x_620_);
if (v_decide_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___f_625_; uint32_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_622_ = lean_nat_add(v_startInclusive_618_, v_it_613_);
v___x_623_ = lean_string_utf8_next_fast(v_str_617_, v___x_622_);
v___x_624_ = lean_nat_sub(v___x_623_, v_startInclusive_618_);
v___f_625_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_625_, 0, v_toPure_609_);
lean_closure_set(v___f_625_, 1, v_recur_616_);
lean_closure_set(v___f_625_, 2, v___x_624_);
v___x_626_ = lean_string_utf8_get_fast(v_str_617_, v___x_622_);
lean_dec(v___x_622_);
v___x_627_ = lean_box_uint32(v___x_626_);
v___x_628_ = lean_apply_2(v_f_610_, v___x_627_, v_acc_614_);
lean_inc(v_toBind_611_);
v___x_629_ = lean_apply_4(v_toBind_611_, lean_box(0), lean_box(0), v___x_628_, v___f_612_);
v___x_630_ = lean_apply_4(v_toBind_611_, lean_box(0), lean_box(0), v___x_629_, v___f_625_);
return v___x_630_;
}
else
{
lean_object* v___x_631_; 
lean_dec(v_recur_616_);
lean_dec(v___f_612_);
lean_dec(v_toBind_611_);
lean_dec(v_f_610_);
v___x_631_ = lean_apply_2(v_toPure_609_, lean_box(0), v_acc_614_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2___boxed(lean_object* v_s_632_, lean_object* v_toPure_633_, lean_object* v_f_634_, lean_object* v_toBind_635_, lean_object* v___f_636_, lean_object* v_it_637_, lean_object* v_acc_638_, lean_object* v_hP_639_, lean_object* v_recur_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2(v_s_632_, v_toPure_633_, v_f_634_, v_toBind_635_, v___f_636_, v_it_637_, v_acc_638_, v_hP_639_, v_recur_640_);
lean_dec(v_it_637_);
lean_dec_ref(v_s_632_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3(lean_object* v_inst_642_, lean_object* v_00_u03b2_643_, lean_object* v_s_644_, lean_object* v_b_645_, lean_object* v_f_646_){
_start:
{
lean_object* v_toApplicative_647_; lean_object* v_toBind_648_; lean_object* v_toPure_649_; lean_object* v___x_650_; lean_object* v___f_651_; lean_object* v___f_652_; lean_object* v___x_653_; 
v_toApplicative_647_ = lean_ctor_get(v_inst_642_, 0);
lean_inc_ref(v_toApplicative_647_);
v_toBind_648_ = lean_ctor_get(v_inst_642_, 1);
lean_inc(v_toBind_648_);
lean_dec_ref(v_inst_642_);
v_toPure_649_ = lean_ctor_get(v_toApplicative_647_, 1);
lean_inc_n(v_toPure_649_, 2);
lean_dec_ref(v_toApplicative_647_);
v___x_650_ = lean_unsigned_to_nat(0u);
v___f_651_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_651_, 0, v_toPure_649_);
v___f_652_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2___boxed), 9, 5);
lean_closure_set(v___f_652_, 0, v_s_644_);
lean_closure_set(v___f_652_, 1, v_toPure_649_);
lean_closure_set(v___f_652_, 2, v_f_646_);
lean_closure_set(v___f_652_, 3, v_toBind_648_);
lean_closure_set(v___f_652_, 4, v___f_651_);
v___x_653_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_652_, v___x_650_, v_b_645_, lean_box(0));
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg(lean_object* v_inst_654_){
_start:
{
lean_object* v___f_655_; 
v___f_655_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_655_, 0, v_inst_654_);
return v___f_655_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad(lean_object* v_m_656_, lean_object* v_inst_657_){
_start:
{
lean_object* v___f_658_; 
v___f_658_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_658_, 0, v_inst_657_);
return v___f_658_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg___lam__0(lean_object* v_s_659_, lean_object* v_f_660_, lean_object* v_it_661_, lean_object* v_acc_662_, lean_object* v_hP_663_, lean_object* v_recur_664_){
_start:
{
lean_object* v_str_665_; lean_object* v_startInclusive_666_; lean_object* v_endExclusive_667_; lean_object* v___x_668_; uint8_t v_decide_669_; 
v_str_665_ = lean_ctor_get(v_s_659_, 0);
v_startInclusive_666_ = lean_ctor_get(v_s_659_, 1);
v_endExclusive_667_ = lean_ctor_get(v_s_659_, 2);
v___x_668_ = lean_nat_sub(v_endExclusive_667_, v_startInclusive_666_);
v_decide_669_ = lean_nat_dec_eq(v_it_661_, v___x_668_);
lean_dec(v___x_668_);
if (v_decide_669_ == 0)
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint32_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_670_ = lean_nat_add(v_startInclusive_666_, v_it_661_);
v___x_671_ = lean_string_utf8_next_fast(v_str_665_, v___x_670_);
v___x_672_ = lean_nat_sub(v___x_671_, v_startInclusive_666_);
v___x_673_ = lean_string_utf8_get_fast(v_str_665_, v___x_670_);
lean_dec(v___x_670_);
v___x_674_ = lean_box_uint32(v___x_673_);
v___x_675_ = lean_apply_2(v_f_660_, v_acc_662_, v___x_674_);
v___x_676_ = lean_apply_4(v_recur_664_, v___x_672_, v___x_675_, lean_box(0), lean_box(0));
return v___x_676_;
}
else
{
lean_dec(v_recur_664_);
lean_dec(v_f_660_);
return v_acc_662_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg___lam__0___boxed(lean_object* v_s_677_, lean_object* v_f_678_, lean_object* v_it_679_, lean_object* v_acc_680_, lean_object* v_hP_681_, lean_object* v_recur_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_String_Slice_foldl___redArg___lam__0(v_s_677_, v_f_678_, v_it_679_, v_acc_680_, v_hP_681_, v_recur_682_);
lean_dec(v_it_679_);
lean_dec_ref(v_s_677_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg(lean_object* v_f_684_, lean_object* v_init_685_, lean_object* v_s_686_){
_start:
{
lean_object* v___f_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___f_687_ = lean_alloc_closure((void*)(l_String_Slice_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_687_, 0, v_s_686_);
lean_closure_set(v___f_687_, 1, v_f_684_);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_687_, v___x_688_, v_init_685_, lean_box(0));
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl(lean_object* v_00_u03b1_690_, lean_object* v_f_691_, lean_object* v_init_692_, lean_object* v_s_693_){
_start:
{
lean_object* v___f_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___f_694_ = lean_alloc_closure((void*)(l_String_Slice_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_694_, 0, v_s_693_);
lean_closure_set(v___f_694_, 1, v_f_691_);
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_694_, v___x_695_, v_init_692_, lean_box(0));
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg___lam__0(lean_object* v_s_697_, lean_object* v_f_698_, lean_object* v_it_699_, lean_object* v_acc_700_, lean_object* v_hP_701_, lean_object* v_recur_702_){
_start:
{
lean_object* v___x_703_; uint8_t v_decide_704_; 
v___x_703_ = lean_unsigned_to_nat(0u);
v_decide_704_ = lean_nat_dec_eq(v_it_699_, v___x_703_);
if (v_decide_704_ == 0)
{
lean_object* v_str_705_; lean_object* v_startInclusive_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_prevPos_709_; lean_object* v___x_710_; uint32_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_str_705_ = lean_ctor_get(v_s_697_, 0);
v_startInclusive_706_ = lean_ctor_get(v_s_697_, 1);
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = lean_nat_sub(v_it_699_, v___x_707_);
v_prevPos_709_ = l_String_Slice_posLE(v_s_697_, v___x_708_);
v___x_710_ = lean_nat_add(v_startInclusive_706_, v_prevPos_709_);
v___x_711_ = lean_string_utf8_get_fast(v_str_705_, v___x_710_);
lean_dec(v___x_710_);
v___x_712_ = lean_box_uint32(v___x_711_);
v___x_713_ = lean_apply_2(v_f_698_, v___x_712_, v_acc_700_);
v___x_714_ = lean_apply_4(v_recur_702_, v_prevPos_709_, v___x_713_, lean_box(0), lean_box(0));
return v___x_714_;
}
else
{
lean_dec(v_recur_702_);
lean_dec(v_f_698_);
return v_acc_700_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg___lam__0___boxed(lean_object* v_s_715_, lean_object* v_f_716_, lean_object* v_it_717_, lean_object* v_acc_718_, lean_object* v_hP_719_, lean_object* v_recur_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_String_Slice_foldr___redArg___lam__0(v_s_715_, v_f_716_, v_it_717_, v_acc_718_, v_hP_719_, v_recur_720_);
lean_dec(v_it_717_);
lean_dec_ref(v_s_715_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg(lean_object* v_f_722_, lean_object* v_init_723_, lean_object* v_s_724_){
_start:
{
lean_object* v___f_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
lean_inc_ref(v_s_724_);
v___f_725_ = lean_alloc_closure((void*)(l_String_Slice_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_725_, 0, v_s_724_);
lean_closure_set(v___f_725_, 1, v_f_722_);
v___x_726_ = l_String_Slice_revPositions(v_s_724_);
lean_dec_ref(v_s_724_);
v___x_727_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_725_, v___x_726_, v_init_723_, lean_box(0));
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr(lean_object* v_00_u03b1_728_, lean_object* v_f_729_, lean_object* v_init_730_, lean_object* v_s_731_){
_start:
{
lean_object* v___f_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
lean_inc_ref(v_s_731_);
v___f_732_ = lean_alloc_closure((void*)(l_String_Slice_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_732_, 0, v_s_731_);
lean_closure_set(v___f_732_, 1, v_f_729_);
v___x_733_ = l_String_Slice_revPositions(v_s_731_);
lean_dec_ref(v_s_731_);
v___x_734_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_732_, v___x_733_, v_init_730_, lean_box(0));
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___redArg(lean_object* v_x_735_){
_start:
{
lean_inc(v_x_735_);
return v_x_735_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___redArg___boxed(lean_object* v_x_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_String_Internal_ofToSliceWithProof___redArg(v_x_736_);
lean_dec(v_x_736_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof(lean_object* v_s_738_, lean_object* v_x_739_){
_start:
{
lean_inc(v_x_739_);
return v_x_739_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___boxed(lean_object* v_s_740_, lean_object* v_x_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_String_Internal_ofToSliceWithProof(v_s_740_, v_x_741_);
lean_dec(v_x_741_);
lean_dec_ref(v_s_740_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom___redArg(lean_object* v_p_743_){
_start:
{
lean_inc(v_p_743_);
return v_p_743_;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom___redArg___boxed(lean_object* v_p_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_String_positionsFrom___redArg(v_p_744_);
lean_dec(v_p_744_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom(lean_object* v_s_746_, lean_object* v_p_747_){
_start:
{
lean_inc(v_p_747_);
return v_p_747_;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom___boxed(lean_object* v_s_748_, lean_object* v_p_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_String_positionsFrom(v_s_748_, v_p_749_);
lean_dec(v_p_749_);
lean_dec_ref(v_s_748_);
return v_res_750_;
}
}
lean_object* l_String_positions___redArg(){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_unsigned_to_nat(0u);
return v___x_752_;
}
}
LEAN_EXPORT void l_String_positions___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_753_;
v_res_753_ = l_String_positions___redArg();
stack->m_obj
 = v_res_753_;
}
LEAN_EXPORT lean_object* l_String_positions___redArg___boxed(lean_object* v___dummy_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_String_positions___redArg();
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_String_positions(lean_object* v_s_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = lean_unsigned_to_nat(0u);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_String_positions___boxed(lean_object* v_s_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_String_positions(v_s_758_);
lean_dec_ref(v_s_758_);
return v_res_759_;
}
}
lean_object* l_String_chars___redArg(){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = lean_unsigned_to_nat(0u);
return v___x_761_;
}
}
LEAN_EXPORT void l_String_chars___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_762_;
v_res_762_ = l_String_chars___redArg();
stack->m_obj
 = v_res_762_;
}
LEAN_EXPORT lean_object* l_String_chars___redArg___boxed(lean_object* v___dummy_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_String_chars___redArg();
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_String_chars(lean_object* v_s_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_unsigned_to_nat(0u);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_String_chars___boxed(lean_object* v_s_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_String_chars(v_s_767_);
lean_dec_ref(v_s_767_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom___redArg(lean_object* v_p_769_){
_start:
{
lean_inc(v_p_769_);
return v_p_769_;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom___redArg___boxed(lean_object* v_p_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_String_revPositionsFrom___redArg(v_p_770_);
lean_dec(v_p_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom(lean_object* v_s_772_, lean_object* v_p_773_){
_start:
{
lean_inc(v_p_773_);
return v_p_773_;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom___boxed(lean_object* v_s_774_, lean_object* v_p_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_String_revPositionsFrom(v_s_774_, v_p_775_);
lean_dec(v_p_775_);
lean_dec_ref(v_s_774_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_String_revPositions(lean_object* v_s_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = lean_string_utf8_byte_size(v_s_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_String_revPositions___boxed(lean_object* v_s_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_String_revPositions(v_s_779_);
lean_dec_ref(v_s_779_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_String_revChars(lean_object* v_s_781_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_string_utf8_byte_size(v_s_781_);
v___x_784_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_784_, 0, v_s_781_);
lean_ctor_set(v___x_784_, 1, v___x_782_);
lean_ctor_set(v___x_784_, 2, v___x_783_);
v___x_785_ = l_String_Slice_revPositions(v___x_784_);
lean_dec_ref_known(v___x_784_, 3);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_String_byteIterator(lean_object* v_s_786_){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = lean_string_utf8_byte_size(v_s_786_);
v___x_789_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_789_, 0, v_s_786_);
lean_ctor_set(v___x_789_, 1, v___x_787_);
lean_ctor_set(v___x_789_, 2, v___x_788_);
v___x_790_ = l_String_Slice_bytes(v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_String_revBytes(lean_object* v_s_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = lean_string_utf8_byte_size(v_s_791_);
v___x_794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_794_, 0, v_s_791_);
lean_ctor_set(v___x_794_, 1, v___x_792_);
lean_ctor_set(v___x_794_, 2, v___x_793_);
v___x_795_ = l_String_Slice_revBytes(v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__2(lean_object* v___x_796_, lean_object* v_s_797_, lean_object* v_toPure_798_, lean_object* v_f_799_, lean_object* v_toBind_800_, lean_object* v___f_801_, lean_object* v_it_802_, lean_object* v_acc_803_, lean_object* v_hP_804_, lean_object* v_recur_805_){
_start:
{
uint8_t v_decide_806_; 
v_decide_806_ = lean_nat_dec_eq(v_it_802_, v___x_796_);
if (v_decide_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___f_808_; uint32_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_807_ = lean_string_utf8_next_fast(v_s_797_, v_it_802_);
v___f_808_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_808_, 0, v_toPure_798_);
lean_closure_set(v___f_808_, 1, v_recur_805_);
lean_closure_set(v___f_808_, 2, v___x_807_);
v___x_809_ = lean_string_utf8_get_fast(v_s_797_, v_it_802_);
v___x_810_ = lean_box_uint32(v___x_809_);
v___x_811_ = lean_apply_2(v_f_799_, v___x_810_, v_acc_803_);
lean_inc(v_toBind_800_);
v___x_812_ = lean_apply_4(v_toBind_800_, lean_box(0), lean_box(0), v___x_811_, v___f_801_);
v___x_813_ = lean_apply_4(v_toBind_800_, lean_box(0), lean_box(0), v___x_812_, v___f_808_);
return v___x_813_;
}
else
{
lean_object* v___x_814_; 
lean_dec(v_recur_805_);
lean_dec(v___f_801_);
lean_dec(v_toBind_800_);
lean_dec(v_f_799_);
v___x_814_ = lean_apply_2(v_toPure_798_, lean_box(0), v_acc_803_);
return v___x_814_;
}
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__2___boxed(lean_object* v___x_815_, lean_object* v_s_816_, lean_object* v_toPure_817_, lean_object* v_f_818_, lean_object* v_toBind_819_, lean_object* v___f_820_, lean_object* v_it_821_, lean_object* v_acc_822_, lean_object* v_hP_823_, lean_object* v_recur_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_String_instForInCharOfMonad___redArg___lam__2(v___x_815_, v_s_816_, v_toPure_817_, v_f_818_, v_toBind_819_, v___f_820_, v_it_821_, v_acc_822_, v_hP_823_, v_recur_824_);
lean_dec(v_it_821_);
lean_dec_ref(v_s_816_);
lean_dec(v___x_815_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__0(lean_object* v_inst_826_, lean_object* v_00_u03b2_827_, lean_object* v_s_828_, lean_object* v_b_829_, lean_object* v_f_830_){
_start:
{
lean_object* v_toApplicative_831_; lean_object* v_toBind_832_; lean_object* v_toPure_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___f_836_; lean_object* v___f_837_; lean_object* v___x_838_; 
v_toApplicative_831_ = lean_ctor_get(v_inst_826_, 0);
lean_inc_ref(v_toApplicative_831_);
v_toBind_832_ = lean_ctor_get(v_inst_826_, 1);
lean_inc(v_toBind_832_);
lean_dec_ref(v_inst_826_);
v_toPure_833_ = lean_ctor_get(v_toApplicative_831_, 1);
lean_inc_n(v_toPure_833_, 2);
lean_dec_ref(v_toApplicative_831_);
v___x_834_ = lean_string_utf8_byte_size(v_s_828_);
v___x_835_ = lean_unsigned_to_nat(0u);
v___f_836_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_836_, 0, v_toPure_833_);
v___f_837_ = lean_alloc_closure((void*)(l_String_instForInCharOfMonad___redArg___lam__2___boxed), 10, 6);
lean_closure_set(v___f_837_, 0, v___x_834_);
lean_closure_set(v___f_837_, 1, v_s_828_);
lean_closure_set(v___f_837_, 2, v_toPure_833_);
lean_closure_set(v___f_837_, 3, v_f_830_);
lean_closure_set(v___f_837_, 4, v_toBind_832_);
lean_closure_set(v___f_837_, 5, v___f_836_);
v___x_838_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_837_, v___x_835_, v_b_829_, lean_box(0));
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg(lean_object* v_inst_839_){
_start:
{
lean_object* v___f_840_; 
v___f_840_ = lean_alloc_closure((void*)(l_String_instForInCharOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_840_, 0, v_inst_839_);
return v___f_840_;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad(lean_object* v_m_841_, lean_object* v_inst_842_){
_start:
{
lean_object* v___f_843_; 
v___f_843_ = lean_alloc_closure((void*)(l_String_instForInCharOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_843_, 0, v_inst_842_);
return v___f_843_;
}
}
LEAN_EXPORT lean_object* l_String_foldl___redArg___lam__0(lean_object* v___x_844_, lean_object* v_s_845_, lean_object* v_f_846_, lean_object* v_it_847_, lean_object* v_acc_848_, lean_object* v_hP_849_, lean_object* v_recur_850_){
_start:
{
uint8_t v_decide_851_; 
v_decide_851_ = lean_nat_dec_eq(v_it_847_, v___x_844_);
if (v_decide_851_ == 0)
{
lean_object* v___x_852_; uint32_t v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_852_ = lean_string_utf8_next_fast(v_s_845_, v_it_847_);
v___x_853_ = lean_string_utf8_get_fast(v_s_845_, v_it_847_);
v___x_854_ = lean_box_uint32(v___x_853_);
v___x_855_ = lean_apply_2(v_f_846_, v_acc_848_, v___x_854_);
v___x_856_ = lean_apply_4(v_recur_850_, v___x_852_, v___x_855_, lean_box(0), lean_box(0));
return v___x_856_;
}
else
{
lean_dec(v_recur_850_);
lean_dec(v_f_846_);
return v_acc_848_;
}
}
}
LEAN_EXPORT lean_object* l_String_foldl___redArg___lam__0___boxed(lean_object* v___x_857_, lean_object* v_s_858_, lean_object* v_f_859_, lean_object* v_it_860_, lean_object* v_acc_861_, lean_object* v_hP_862_, lean_object* v_recur_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_String_foldl___redArg___lam__0(v___x_857_, v_s_858_, v_f_859_, v_it_860_, v_acc_861_, v_hP_862_, v_recur_863_);
lean_dec(v_it_860_);
lean_dec_ref(v_s_858_);
lean_dec(v___x_857_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_String_foldl___redArg(lean_object* v_f_865_, lean_object* v_init_866_, lean_object* v_s_867_){
_start:
{
lean_object* v___x_868_; lean_object* v___f_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_868_ = lean_string_utf8_byte_size(v_s_867_);
v___f_869_ = lean_alloc_closure((void*)(l_String_foldl___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_869_, 0, v___x_868_);
lean_closure_set(v___f_869_, 1, v_s_867_);
lean_closure_set(v___f_869_, 2, v_f_865_);
v___x_870_ = lean_unsigned_to_nat(0u);
v___x_871_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_869_, v___x_870_, v_init_866_, lean_box(0));
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_String_foldl(lean_object* v_00_u03b1_872_, lean_object* v_f_873_, lean_object* v_init_874_, lean_object* v_s_875_){
_start:
{
lean_object* v___x_876_; lean_object* v___f_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_876_ = lean_string_utf8_byte_size(v_s_875_);
v___f_877_ = lean_alloc_closure((void*)(l_String_foldl___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_877_, 0, v___x_876_);
lean_closure_set(v___f_877_, 1, v_s_875_);
lean_closure_set(v___f_877_, 2, v_f_873_);
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_877_, v___x_878_, v_init_874_, lean_box(0));
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(lean_object* v_f_880_, lean_object* v___x_881_, lean_object* v_s_882_, lean_object* v_a_883_, lean_object* v_b_884_){
_start:
{
uint8_t v_decide_885_; 
v_decide_885_ = lean_nat_dec_eq(v_a_883_, v___x_881_);
if (v_decide_885_ == 0)
{
uint32_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_886_ = lean_string_utf8_get_fast(v_s_882_, v_a_883_);
v___x_887_ = lean_string_utf8_next_fast(v_s_882_, v_a_883_);
lean_dec(v_a_883_);
v___x_888_ = lean_box_uint32(v___x_886_);
lean_inc_ref(v_f_880_);
v___x_889_ = lean_apply_2(v_f_880_, v_b_884_, v___x_888_);
v_a_883_ = v___x_887_;
v_b_884_ = v___x_889_;
goto _start;
}
else
{
lean_dec(v_a_883_);
lean_dec_ref(v_f_880_);
return v_b_884_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg___boxed(lean_object* v_f_891_, lean_object* v___x_892_, lean_object* v_s_893_, lean_object* v_a_894_, lean_object* v_b_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(v_f_891_, v___x_892_, v_s_893_, v_a_894_, v_b_895_);
lean_dec_ref(v_s_893_);
lean_dec(v___x_892_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* lean_string_foldl(lean_object* v_f_897_, lean_object* v_init_898_, lean_object* v_s_899_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_900_ = lean_string_utf8_byte_size(v_s_899_);
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(v_f_897_, v___x_900_, v_s_899_, v___x_901_, v_init_898_);
lean_dec_ref(v_s_899_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0(lean_object* v_f_903_, lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v_s_906_, lean_object* v_inst_907_, lean_object* v_R_908_, lean_object* v_a_909_, lean_object* v_b_910_, lean_object* v_c_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(v_f_903_, v___x_905_, v_s_906_, v_a_909_, v_b_910_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___boxed(lean_object* v_f_913_, lean_object* v___x_914_, lean_object* v___x_915_, lean_object* v_s_916_, lean_object* v_inst_917_, lean_object* v_R_918_, lean_object* v_a_919_, lean_object* v_b_920_, lean_object* v_c_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0(v_f_913_, v___x_914_, v___x_915_, v_s_916_, v_inst_917_, v_R_918_, v_a_919_, v_b_920_, v_c_921_);
lean_dec_ref(v_s_916_);
lean_dec(v___x_915_);
lean_dec_ref(v___x_914_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_String_foldr___redArg___lam__0(lean_object* v___x_923_, lean_object* v___x_924_, lean_object* v_s_925_, lean_object* v_f_926_, lean_object* v_it_927_, lean_object* v_acc_928_, lean_object* v_hP_929_, lean_object* v_recur_930_){
_start:
{
uint8_t v_decide_931_; 
v_decide_931_ = lean_nat_dec_eq(v_it_927_, v___x_923_);
if (v_decide_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v_prevPos_934_; uint32_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_932_ = lean_unsigned_to_nat(1u);
v___x_933_ = lean_nat_sub(v_it_927_, v___x_932_);
v_prevPos_934_ = l_String_Slice_posLE(v___x_924_, v___x_933_);
v___x_935_ = lean_string_utf8_get_fast(v_s_925_, v_prevPos_934_);
v___x_936_ = lean_box_uint32(v___x_935_);
v___x_937_ = lean_apply_2(v_f_926_, v___x_936_, v_acc_928_);
v___x_938_ = lean_apply_4(v_recur_930_, v_prevPos_934_, v___x_937_, lean_box(0), lean_box(0));
return v___x_938_;
}
else
{
lean_dec(v_recur_930_);
lean_dec(v_f_926_);
return v_acc_928_;
}
}
}
LEAN_EXPORT lean_object* l_String_foldr___redArg___lam__0___boxed(lean_object* v___x_939_, lean_object* v___x_940_, lean_object* v_s_941_, lean_object* v_f_942_, lean_object* v_it_943_, lean_object* v_acc_944_, lean_object* v_hP_945_, lean_object* v_recur_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_String_foldr___redArg___lam__0(v___x_939_, v___x_940_, v_s_941_, v_f_942_, v_it_943_, v_acc_944_, v_hP_945_, v_recur_946_);
lean_dec(v_it_943_);
lean_dec_ref(v_s_941_);
lean_dec_ref(v___x_940_);
lean_dec(v___x_939_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_String_foldr___redArg(lean_object* v_f_948_, lean_object* v_init_949_, lean_object* v_s_950_){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_951_ = lean_unsigned_to_nat(0u);
v___x_952_ = lean_string_utf8_byte_size(v_s_950_);
lean_inc_ref(v_s_950_);
v___x_953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_953_, 0, v_s_950_);
lean_ctor_set(v___x_953_, 1, v___x_951_);
lean_ctor_set(v___x_953_, 2, v___x_952_);
lean_inc_ref(v___x_953_);
v___f_954_ = lean_alloc_closure((void*)(l_String_foldr___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_954_, 0, v___x_951_);
lean_closure_set(v___f_954_, 1, v___x_953_);
lean_closure_set(v___f_954_, 2, v_s_950_);
lean_closure_set(v___f_954_, 3, v_f_948_);
v___x_955_ = l_String_Slice_revPositions(v___x_953_);
lean_dec_ref_known(v___x_953_, 3);
v___x_956_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_954_, v___x_955_, v_init_949_, lean_box(0));
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_String_foldr(lean_object* v_00_u03b1_957_, lean_object* v_f_958_, lean_object* v_init_959_, lean_object* v_s_960_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___f_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = lean_string_utf8_byte_size(v_s_960_);
lean_inc_ref(v_s_960_);
v___x_963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_963_, 0, v_s_960_);
lean_ctor_set(v___x_963_, 1, v___x_961_);
lean_ctor_set(v___x_963_, 2, v___x_962_);
lean_inc_ref(v___x_963_);
v___f_964_ = lean_alloc_closure((void*)(l_String_foldr___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_964_, 0, v___x_961_);
lean_closure_set(v___f_964_, 1, v___x_963_);
lean_closure_set(v___f_964_, 2, v_s_960_);
lean_closure_set(v___f_964_, 3, v_f_958_);
v___x_965_ = l_String_Slice_revPositions(v___x_963_);
lean_dec_ref_known(v___x_963_, 3);
v___x_966_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_964_, v___x_965_, v_init_959_, lean_box(0));
return v___x_966_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
