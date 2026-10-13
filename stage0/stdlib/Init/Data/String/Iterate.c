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
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_String_Slice_instInhabitedPosIterator_default___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default(lean_object* v_s_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(0u);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default___boxed(lean_object* v_s_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_String_Slice_instInhabitedPosIterator_default(v_s_7_);
lean_dec_ref(v_s_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator___redArg(){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_unsigned_to_nat(0u);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator___redArg___boxed(lean_object* v___dummy_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_String_Slice_instInhabitedPosIterator___redArg();
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator(lean_object* v_a_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_unsigned_to_nat(0u);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator___boxed(lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_String_Slice_instInhabitedPosIterator(v_a_15_);
lean_dec_ref(v_a_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___redArg(lean_object* v_p_17_){
_start:
{
lean_inc(v_p_17_);
return v_p_17_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___redArg___boxed(lean_object* v_p_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_String_Slice_positionsFrom___redArg(v_p_18_);
lean_dec(v_p_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom(lean_object* v_s_20_, lean_object* v_p_21_){
_start:
{
lean_inc(v_p_21_);
return v_p_21_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___boxed(lean_object* v_s_22_, lean_object* v_p_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_String_Slice_positionsFrom(v_s_22_, v_p_23_);
lean_dec(v_p_23_);
lean_dec_ref(v_s_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positions___redArg(){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lean_unsigned_to_nat(0u);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positions___redArg___boxed(lean_object* v___dummy_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_String_Slice_positions___redArg();
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positions(lean_object* v_s_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_unsigned_to_nat(0u);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positions___boxed(lean_object* v_s_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_String_Slice_positions(v_s_31_);
lean_dec_ref(v_s_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(lean_object* v_s_33_, lean_object* v_inst_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_str_36_; lean_object* v_startInclusive_37_; lean_object* v_endExclusive_38_; lean_object* v___x_39_; uint8_t v_decide_40_; 
v_str_36_ = lean_ctor_get(v_s_33_, 0);
v_startInclusive_37_ = lean_ctor_get(v_s_33_, 1);
v_endExclusive_38_ = lean_ctor_get(v_s_33_, 2);
v___x_39_ = lean_nat_sub(v_endExclusive_38_, v_startInclusive_37_);
v_decide_40_ = lean_nat_dec_eq(v_x_35_, v___x_39_);
lean_dec(v___x_39_);
if (v_decide_40_ == 0)
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_41_ = lean_nat_add(v_startInclusive_37_, v_x_35_);
v___x_42_ = lean_string_utf8_next_fast(v_str_36_, v___x_41_);
lean_dec(v___x_41_);
v___x_43_ = lean_nat_sub(v___x_42_, v_startInclusive_37_);
v___x_44_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v_x_35_);
v___x_45_ = lean_apply_2(v_inst_34_, lean_box(0), v___x_44_);
return v___x_45_;
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v_x_35_);
v___x_46_ = lean_box(2);
v___x_47_ = lean_apply_2(v_inst_34_, lean_box(0), v___x_46_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(lean_object* v_s_48_, lean_object* v_inst_49_, lean_object* v_x_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(v_s_48_, v_inst_49_, v_x_50_);
lean_dec_ref(v_s_48_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(lean_object* v_s_52_, lean_object* v_inst_53_){
_start:
{
lean_object* v___f_54_; 
v___f_54_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_54_, 0, v_s_52_);
lean_closure_set(v___f_54_, 1, v_inst_53_);
return v___f_54_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure(lean_object* v_m_55_, lean_object* v_s_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v___f_58_; 
v___f_58_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_58_, 0, v_s_56_);
lean_closure_set(v___f_58_, 1, v_inst_57_);
return v___f_58_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_box(0);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___redArg();
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation(lean_object* v_m_63_, lean_object* v_s_64_, lean_object* v_inst_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___boxed(lean_object* v_m_67_, lean_object* v_s_68_, lean_object* v_inst_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation(v_m_67_, v_s_68_, v_inst_69_);
lean_dec(v_inst_69_);
lean_dec_ref(v_s_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(lean_object* v_toPure_71_, lean_object* v_recur_72_, lean_object* v_it_73_, lean_object* v_____do__lift_74_){
_start:
{
if (lean_obj_tag(v_____do__lift_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_76_; 
lean_dec(v_it_73_);
lean_dec(v_recur_72_);
v_a_75_ = lean_ctor_get(v_____do__lift_74_, 0);
lean_inc(v_a_75_);
lean_dec_ref_known(v_____do__lift_74_, 1);
v___x_76_ = lean_apply_2(v_toPure_71_, lean_box(0), v_a_75_);
return v___x_76_;
}
else
{
lean_object* v_a_77_; lean_object* v___x_78_; 
lean_dec(v_toPure_71_);
v_a_77_ = lean_ctor_get(v_____do__lift_74_, 0);
lean_inc(v_a_77_);
lean_dec_ref_known(v_____do__lift_74_, 1);
v___x_78_ = lean_apply_4(v_recur_72_, v_it_73_, v_a_77_, lean_box(0), lean_box(0));
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1(lean_object* v_toPure_79_, lean_object* v_recur_80_, lean_object* v___y_81_, lean_object* v_acc_82_, lean_object* v_toBind_83_, lean_object* v_s_84_){
_start:
{
switch(lean_obj_tag(v_s_84_))
{
case 0:
{
lean_object* v_it_85_; lean_object* v_out_86_; lean_object* v___f_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_it_85_ = lean_ctor_get(v_s_84_, 0);
lean_inc(v_it_85_);
v_out_86_ = lean_ctor_get(v_s_84_, 1);
lean_inc(v_out_86_);
lean_dec_ref_known(v_s_84_, 2);
v___f_87_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_87_, 0, v_toPure_79_);
lean_closure_set(v___f_87_, 1, v_recur_80_);
lean_closure_set(v___f_87_, 2, v_it_85_);
v___x_88_ = lean_apply_3(v___y_81_, v_out_86_, lean_box(0), v_acc_82_);
v___x_89_ = lean_apply_4(v_toBind_83_, lean_box(0), lean_box(0), v___x_88_, v___f_87_);
return v___x_89_;
}
case 1:
{
lean_object* v_it_90_; lean_object* v___x_91_; 
lean_dec(v_toBind_83_);
lean_dec(v___y_81_);
lean_dec(v_toPure_79_);
v_it_90_ = lean_ctor_get(v_s_84_, 0);
lean_inc(v_it_90_);
lean_dec_ref_known(v_s_84_, 1);
v___x_91_ = lean_apply_4(v_recur_80_, v_it_90_, v_acc_82_, lean_box(0), lean_box(0));
return v___x_91_;
}
default: 
{
lean_object* v___x_92_; 
lean_dec(v_toBind_83_);
lean_dec(v___y_81_);
lean_dec(v_recur_80_);
v___x_92_ = lean_apply_2(v_toPure_79_, lean_box(0), v_acc_82_);
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(lean_object* v_s_93_, lean_object* v_toPure_94_, lean_object* v___y_95_, lean_object* v_toBind_96_, lean_object* v_toPure_97_, lean_object* v_lift_98_, lean_object* v_it_99_, lean_object* v_acc_100_, lean_object* v_hP_101_, lean_object* v_recur_102_){
_start:
{
lean_object* v_str_103_; lean_object* v_startInclusive_104_; lean_object* v_endExclusive_105_; lean_object* v___f_106_; lean_object* v___x_107_; uint8_t v_decide_108_; 
v_str_103_ = lean_ctor_get(v_s_93_, 0);
v_startInclusive_104_ = lean_ctor_get(v_s_93_, 1);
v_endExclusive_105_ = lean_ctor_get(v_s_93_, 2);
v___f_106_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_106_, 0, v_toPure_94_);
lean_closure_set(v___f_106_, 1, v_recur_102_);
lean_closure_set(v___f_106_, 2, v___y_95_);
lean_closure_set(v___f_106_, 3, v_acc_100_);
lean_closure_set(v___f_106_, 4, v_toBind_96_);
v___x_107_ = lean_nat_sub(v_endExclusive_105_, v_startInclusive_104_);
v_decide_108_ = lean_nat_dec_eq(v_it_99_, v___x_107_);
lean_dec(v___x_107_);
if (v_decide_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_109_ = lean_nat_add(v_startInclusive_104_, v_it_99_);
v___x_110_ = lean_string_utf8_next_fast(v_str_103_, v___x_109_);
lean_dec(v___x_109_);
v___x_111_ = lean_nat_sub(v___x_110_, v_startInclusive_104_);
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v_it_99_);
v___x_113_ = lean_apply_2(v_toPure_97_, lean_box(0), v___x_112_);
v___x_114_ = lean_apply_4(v_lift_98_, lean_box(0), lean_box(0), v___f_106_, v___x_113_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec(v_it_99_);
v___x_115_ = lean_box(2);
v___x_116_ = lean_apply_2(v_toPure_97_, lean_box(0), v___x_115_);
v___x_117_ = lean_apply_4(v_lift_98_, lean_box(0), lean_box(0), v___f_106_, v___x_116_);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(lean_object* v_s_118_, lean_object* v_toPure_119_, lean_object* v___y_120_, lean_object* v_toBind_121_, lean_object* v_toPure_122_, lean_object* v_lift_123_, lean_object* v_it_124_, lean_object* v_acc_125_, lean_object* v_hP_126_, lean_object* v_recur_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(v_s_118_, v_toPure_119_, v___y_120_, v_toBind_121_, v_toPure_122_, v_lift_123_, v_it_124_, v_acc_125_, v_hP_126_, v_recur_127_);
lean_dec_ref(v_s_118_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__3(lean_object* v_inst_129_, lean_object* v_s_130_, lean_object* v_toPure_131_, lean_object* v_lift_132_, lean_object* v_00_u03b3_133_, lean_object* v_Pl_134_, lean_object* v_it_135_, lean_object* v_init_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_toApplicative_138_; lean_object* v_toBind_139_; lean_object* v_toPure_140_; lean_object* v___f_141_; lean_object* v___x_142_; 
v_toApplicative_138_ = lean_ctor_get(v_inst_129_, 0);
lean_inc_ref(v_toApplicative_138_);
v_toBind_139_ = lean_ctor_get(v_inst_129_, 1);
lean_inc(v_toBind_139_);
lean_dec_ref(v_inst_129_);
v_toPure_140_ = lean_ctor_get(v_toApplicative_138_, 1);
lean_inc(v_toPure_140_);
lean_dec_ref(v_toApplicative_138_);
v___f_141_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed), 10, 6);
lean_closure_set(v___f_141_, 0, v_s_130_);
lean_closure_set(v___f_141_, 1, v_toPure_140_);
lean_closure_set(v___f_141_, 2, v___y_137_);
lean_closure_set(v___f_141_, 3, v_toBind_139_);
lean_closure_set(v___f_141_, 4, v_toPure_131_);
lean_closure_set(v___f_141_, 5, v_lift_132_);
v___x_142_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_141_, v_it_135_, v_init_136_, lean_box(0));
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(lean_object* v_s_143_, lean_object* v_inst_144_, lean_object* v_inst_145_){
_start:
{
lean_object* v_toApplicative_146_; lean_object* v_toPure_147_; lean_object* v___f_148_; 
v_toApplicative_146_ = lean_ctor_get(v_inst_144_, 0);
lean_inc_ref(v_toApplicative_146_);
lean_dec_ref(v_inst_144_);
v_toPure_147_ = lean_ctor_get(v_toApplicative_146_, 1);
lean_inc(v_toPure_147_);
lean_dec_ref(v_toApplicative_146_);
v___f_148_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_148_, 0, v_inst_145_);
lean_closure_set(v___f_148_, 1, v_s_143_);
lean_closure_set(v___f_148_, 2, v_toPure_147_);
return v___f_148_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(lean_object* v_m_149_, lean_object* v_n_150_, lean_object* v_s_151_, lean_object* v_inst_152_, lean_object* v_inst_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(v_s_151_, v_inst_152_, v_inst_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_chars___redArg(){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_unsigned_to_nat(0u);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_chars___redArg___boxed(lean_object* v___dummy_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_String_Slice_chars___redArg();
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_chars(lean_object* v_s_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_unsigned_to_nat(0u);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_chars___boxed(lean_object* v_s_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_String_Slice_chars(v_s_161_);
lean_dec_ref(v_s_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(lean_object* v_s_163_, lean_object* v_a_164_, lean_object* v_b_165_){
_start:
{
lean_object* v_str_166_; lean_object* v_startInclusive_167_; lean_object* v_endExclusive_168_; lean_object* v___x_169_; uint8_t v_decide_170_; 
v_str_166_ = lean_ctor_get(v_s_163_, 0);
v_startInclusive_167_ = lean_ctor_get(v_s_163_, 1);
v_endExclusive_168_ = lean_ctor_get(v_s_163_, 2);
v___x_169_ = lean_nat_sub(v_endExclusive_168_, v_startInclusive_167_);
v_decide_170_ = lean_nat_dec_eq(v_a_164_, v___x_169_);
lean_dec(v___x_169_);
if (v_decide_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_171_ = lean_nat_add(v_startInclusive_167_, v_a_164_);
lean_dec(v_a_164_);
v___x_172_ = lean_string_utf8_next_fast(v_str_166_, v___x_171_);
lean_dec(v___x_171_);
v___x_173_ = lean_nat_sub(v___x_172_, v_startInclusive_167_);
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = lean_nat_add(v_b_165_, v___x_174_);
lean_dec(v_b_165_);
v_a_164_ = v___x_173_;
v_b_165_ = v___x_175_;
goto _start;
}
else
{
lean_dec(v_a_164_);
return v_b_165_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg___boxed(lean_object* v_s_177_, lean_object* v_a_178_, lean_object* v_b_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(v_s_177_, v_a_178_, v_b_179_);
lean_dec_ref(v_s_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_length(lean_object* v_s_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(v_s_181_, v___x_182_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_length___boxed(lean_object* v_s_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_String_Slice_length(v_s_184_);
lean_dec_ref(v_s_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0(lean_object* v_s_186_, lean_object* v_inst_187_, lean_object* v_R_188_, lean_object* v_a_189_, lean_object* v_b_190_, lean_object* v_c_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(v_s_186_, v_a_189_, v_b_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___boxed(lean_object* v_s_193_, lean_object* v_inst_194_, lean_object* v_R_195_, lean_object* v_a_196_, lean_object* v_b_197_, lean_object* v_c_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0(v_s_193_, v_inst_194_, v_R_195_, v_a_196_, v_b_197_, v_c_198_);
lean_dec_ref(v_s_193_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default___redArg(){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = lean_unsigned_to_nat(0u);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default___redArg___boxed(lean_object* v___dummy_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_String_Slice_instInhabitedRevPosIterator_default___redArg();
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default(lean_object* v_s_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_unsigned_to_nat(0u);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default___boxed(lean_object* v_s_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_String_Slice_instInhabitedRevPosIterator_default(v_s_206_);
lean_dec_ref(v_s_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator___redArg(){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_unsigned_to_nat(0u);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator___redArg___boxed(lean_object* v___dummy_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_String_Slice_instInhabitedRevPosIterator___redArg();
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator(lean_object* v_a_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_unsigned_to_nat(0u);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator___boxed(lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_String_Slice_instInhabitedRevPosIterator(v_a_214_);
lean_dec_ref(v_a_214_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___redArg(lean_object* v_p_216_){
_start:
{
lean_inc(v_p_216_);
return v_p_216_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___redArg___boxed(lean_object* v_p_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_String_Slice_revPositionsFrom___redArg(v_p_217_);
lean_dec(v_p_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom(lean_object* v_s_219_, lean_object* v_p_220_){
_start:
{
lean_inc(v_p_220_);
return v_p_220_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___boxed(lean_object* v_s_221_, lean_object* v_p_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_String_Slice_revPositionsFrom(v_s_221_, v_p_222_);
lean_dec(v_p_222_);
lean_dec_ref(v_s_221_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositions(lean_object* v_s_224_){
_start:
{
lean_object* v_startInclusive_225_; lean_object* v_endExclusive_226_; lean_object* v___x_227_; 
v_startInclusive_225_ = lean_ctor_get(v_s_224_, 1);
v_endExclusive_226_ = lean_ctor_get(v_s_224_, 2);
v___x_227_ = lean_nat_sub(v_endExclusive_226_, v_startInclusive_225_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositions___boxed(lean_object* v_s_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_String_Slice_revPositions(v_s_228_);
lean_dec_ref(v_s_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(lean_object* v_s_230_, lean_object* v_inst_231_, lean_object* v_x_232_){
_start:
{
lean_object* v___x_233_; uint8_t v_decide_234_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v_decide_234_ = lean_nat_dec_eq(v_x_232_, v___x_233_);
if (v_decide_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v_prevPos_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_235_ = lean_unsigned_to_nat(1u);
v___x_236_ = lean_nat_sub(v_x_232_, v___x_235_);
v_prevPos_237_ = l_String_Slice_posLE(v_s_230_, v___x_236_);
lean_inc(v_prevPos_237_);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v_prevPos_237_);
lean_ctor_set(v___x_238_, 1, v_prevPos_237_);
v___x_239_ = lean_apply_2(v_inst_231_, lean_box(0), v___x_238_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_box(2);
v___x_241_ = lean_apply_2(v_inst_231_, lean_box(0), v___x_240_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(lean_object* v_s_242_, lean_object* v_inst_243_, lean_object* v_x_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(v_s_242_, v_inst_243_, v_x_244_);
lean_dec(v_x_244_);
lean_dec_ref(v_s_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(lean_object* v_s_246_, lean_object* v_inst_247_){
_start:
{
lean_object* v___f_248_; 
v___f_248_ = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_248_, 0, v_s_246_);
lean_closure_set(v___f_248_, 1, v_inst_247_);
return v___f_248_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure(lean_object* v_m_249_, lean_object* v_s_250_, lean_object* v_inst_251_){
_start:
{
lean_object* v___f_252_; 
v___f_252_ = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_252_, 0, v_s_250_);
lean_closure_set(v___f_252_, 1, v_inst_251_);
return v___f_252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_box(0);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___redArg();
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation(lean_object* v_m_257_, lean_object* v_s_258_, lean_object* v_inst_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = lean_box(0);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___boxed(lean_object* v_m_261_, lean_object* v_s_262_, lean_object* v_inst_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation(v_m_261_, v_s_262_, v_inst_263_);
lean_dec(v_inst_263_);
lean_dec_ref(v_s_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(lean_object* v_toPure_265_, lean_object* v___y_266_, lean_object* v_toBind_267_, lean_object* v_s_268_, lean_object* v_toPure_269_, lean_object* v_lift_270_, lean_object* v_it_271_, lean_object* v_acc_272_, lean_object* v_hP_273_, lean_object* v_recur_274_){
_start:
{
lean_object* v___f_275_; lean_object* v___x_276_; uint8_t v_decide_277_; 
v___f_275_ = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_275_, 0, v_toPure_265_);
lean_closure_set(v___f_275_, 1, v_recur_274_);
lean_closure_set(v___f_275_, 2, v___y_266_);
lean_closure_set(v___f_275_, 3, v_acc_272_);
lean_closure_set(v___f_275_, 4, v_toBind_267_);
v___x_276_ = lean_unsigned_to_nat(0u);
v_decide_277_ = lean_nat_dec_eq(v_it_271_, v___x_276_);
if (v_decide_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v_prevPos_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_sub(v_it_271_, v___x_278_);
v_prevPos_280_ = l_String_Slice_posLE(v_s_268_, v___x_279_);
lean_inc(v_prevPos_280_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_prevPos_280_);
lean_ctor_set(v___x_281_, 1, v_prevPos_280_);
v___x_282_ = lean_apply_2(v_toPure_269_, lean_box(0), v___x_281_);
v___x_283_ = lean_apply_4(v_lift_270_, lean_box(0), lean_box(0), v___f_275_, v___x_282_);
return v___x_283_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_box(2);
v___x_285_ = lean_apply_2(v_toPure_269_, lean_box(0), v___x_284_);
v___x_286_ = lean_apply_4(v_lift_270_, lean_box(0), lean_box(0), v___f_275_, v___x_285_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(lean_object* v_toPure_287_, lean_object* v___y_288_, lean_object* v_toBind_289_, lean_object* v_s_290_, lean_object* v_toPure_291_, lean_object* v_lift_292_, lean_object* v_it_293_, lean_object* v_acc_294_, lean_object* v_hP_295_, lean_object* v_recur_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(v_toPure_287_, v___y_288_, v_toBind_289_, v_s_290_, v_toPure_291_, v_lift_292_, v_it_293_, v_acc_294_, v_hP_295_, v_recur_296_);
lean_dec(v_it_293_);
lean_dec_ref(v_s_290_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(lean_object* v_inst_298_, lean_object* v_s_299_, lean_object* v_toPure_300_, lean_object* v_lift_301_, lean_object* v_00_u03b3_302_, lean_object* v_Pl_303_, lean_object* v_it_304_, lean_object* v_init_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_toApplicative_307_; lean_object* v_toBind_308_; lean_object* v_toPure_309_; lean_object* v___f_310_; lean_object* v___x_311_; 
v_toApplicative_307_ = lean_ctor_get(v_inst_298_, 0);
lean_inc_ref(v_toApplicative_307_);
v_toBind_308_ = lean_ctor_get(v_inst_298_, 1);
lean_inc(v_toBind_308_);
lean_dec_ref(v_inst_298_);
v_toPure_309_ = lean_ctor_get(v_toApplicative_307_, 1);
lean_inc(v_toPure_309_);
lean_dec_ref(v_toApplicative_307_);
v___f_310_ = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed), 10, 6);
lean_closure_set(v___f_310_, 0, v_toPure_309_);
lean_closure_set(v___f_310_, 1, v___y_306_);
lean_closure_set(v___f_310_, 2, v_toBind_308_);
lean_closure_set(v___f_310_, 3, v_s_299_);
lean_closure_set(v___f_310_, 4, v_toPure_300_);
lean_closure_set(v___f_310_, 5, v_lift_301_);
v___x_311_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_310_, v_it_304_, v_init_305_, lean_box(0));
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(lean_object* v_s_312_, lean_object* v_inst_313_, lean_object* v_inst_314_){
_start:
{
lean_object* v_toApplicative_315_; lean_object* v_toPure_316_; lean_object* v___f_317_; 
v_toApplicative_315_ = lean_ctor_get(v_inst_313_, 0);
lean_inc_ref(v_toApplicative_315_);
lean_dec_ref(v_inst_313_);
v_toPure_316_ = lean_ctor_get(v_toApplicative_315_, 1);
lean_inc(v_toPure_316_);
lean_dec_ref(v_toApplicative_315_);
v___f_317_ = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0), 9, 3);
lean_closure_set(v___f_317_, 0, v_inst_314_);
lean_closure_set(v___f_317_, 1, v_s_312_);
lean_closure_set(v___f_317_, 2, v_toPure_316_);
return v___f_317_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(lean_object* v_m_318_, lean_object* v_n_319_, lean_object* v_s_320_, lean_object* v_inst_321_, lean_object* v_inst_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(v_s_320_, v_inst_321_, v_inst_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revChars(lean_object* v_s_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_String_Slice_revPositions(v_s_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revChars___boxed(lean_object* v_s_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_String_Slice_revChars(v_s_326_);
lean_dec_ref(v_s_326_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_bytes(lean_object* v_s_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v_s_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0(lean_object* v_inst_340_, lean_object* v_x_341_){
_start:
{
lean_object* v_s_342_; lean_object* v_offset_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_364_; 
v_s_342_ = lean_ctor_get(v_x_341_, 0);
v_offset_343_ = lean_ctor_get(v_x_341_, 1);
v_isSharedCheck_364_ = !lean_is_exclusive(v_x_341_);
if (v_isSharedCheck_364_ == 0)
{
v___x_345_ = v_x_341_;
v_isShared_346_ = v_isSharedCheck_364_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_offset_343_);
lean_inc(v_s_342_);
lean_dec(v_x_341_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_364_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_str_347_; lean_object* v_startInclusive_348_; lean_object* v_endExclusive_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v_str_347_ = lean_ctor_get(v_s_342_, 0);
lean_inc_ref(v_str_347_);
v_startInclusive_348_ = lean_ctor_get(v_s_342_, 1);
lean_inc(v_startInclusive_348_);
v_endExclusive_349_ = lean_ctor_get(v_s_342_, 2);
v___x_350_ = lean_nat_sub(v_endExclusive_349_, v_startInclusive_348_);
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_nat_add(v_offset_343_, v___x_351_);
v___x_353_ = lean_nat_dec_le(v___x_352_, v___x_350_);
lean_dec(v___x_350_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v___x_352_);
lean_dec(v_startInclusive_348_);
lean_dec_ref(v_str_347_);
lean_del_object(v___x_345_);
lean_dec(v_offset_343_);
lean_dec_ref(v_s_342_);
v___x_354_ = lean_box(2);
v___x_355_ = lean_apply_2(v_inst_340_, lean_box(0), v___x_354_);
return v___x_355_;
}
else
{
lean_object* v___x_357_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v___x_352_);
v___x_357_ = v___x_345_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_s_342_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v___x_352_);
v___x_357_ = v_reuseFailAlloc_363_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_358_ = lean_nat_add(v_startInclusive_348_, v_offset_343_);
lean_dec(v_offset_343_);
lean_dec(v_startInclusive_348_);
v___x_359_ = lean_string_get_byte_fast(v_str_347_, v___x_358_);
lean_dec_ref(v_str_347_);
v___x_360_ = lean_box(v___x_359_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_357_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = lean_apply_2(v_inst_340_, lean_box(0), v___x_361_);
return v___x_362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg(lean_object* v_inst_365_){
_start:
{
lean_object* v___f_366_; 
v___f_366_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_366_, 0, v_inst_365_);
return v___f_366_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure(lean_object* v_m_367_, lean_object* v_inst_368_){
_start:
{
lean_object* v___f_369_; 
v___f_369_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_369_, 0, v_inst_368_);
return v___f_369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_box(0);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___redArg();
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation(lean_object* v_m_374_, lean_object* v_inst_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_box(0);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___boxed(lean_object* v_m_377_, lean_object* v_inst_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation(v_m_377_, v_inst_378_);
lean_dec(v_inst_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0(lean_object* v_toPure_380_, lean_object* v_recur_381_, lean_object* v_it_382_, lean_object* v_____do__lift_383_){
_start:
{
if (lean_obj_tag(v_____do__lift_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_385_; 
lean_dec_ref(v_it_382_);
lean_dec(v_recur_381_);
v_a_384_ = lean_ctor_get(v_____do__lift_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v_____do__lift_383_, 1);
v___x_385_ = lean_apply_2(v_toPure_380_, lean_box(0), v_a_384_);
return v___x_385_;
}
else
{
lean_object* v_a_386_; lean_object* v___x_387_; 
lean_dec(v_toPure_380_);
v_a_386_ = lean_ctor_get(v_____do__lift_383_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v_____do__lift_383_, 1);
v___x_387_ = lean_apply_4(v_recur_381_, v_it_382_, v_a_386_, lean_box(0), lean_box(0));
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1(lean_object* v_toPure_388_, lean_object* v_recur_389_, lean_object* v___y_390_, lean_object* v_acc_391_, lean_object* v_toBind_392_, lean_object* v_s_393_){
_start:
{
switch(lean_obj_tag(v_s_393_))
{
case 0:
{
lean_object* v_it_394_; lean_object* v_out_395_; lean_object* v___f_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_it_394_ = lean_ctor_get(v_s_393_, 0);
lean_inc(v_it_394_);
v_out_395_ = lean_ctor_get(v_s_393_, 1);
lean_inc(v_out_395_);
lean_dec_ref_known(v_s_393_, 2);
v___f_396_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_396_, 0, v_toPure_388_);
lean_closure_set(v___f_396_, 1, v_recur_389_);
lean_closure_set(v___f_396_, 2, v_it_394_);
v___x_397_ = lean_apply_3(v___y_390_, v_out_395_, lean_box(0), v_acc_391_);
v___x_398_ = lean_apply_4(v_toBind_392_, lean_box(0), lean_box(0), v___x_397_, v___f_396_);
return v___x_398_;
}
case 1:
{
lean_object* v_it_399_; lean_object* v___x_400_; 
lean_dec(v_toBind_392_);
lean_dec(v___y_390_);
lean_dec(v_toPure_388_);
v_it_399_ = lean_ctor_get(v_s_393_, 0);
lean_inc(v_it_399_);
lean_dec_ref_known(v_s_393_, 1);
v___x_400_ = lean_apply_4(v_recur_389_, v_it_399_, v_acc_391_, lean_box(0), lean_box(0));
return v___x_400_;
}
default: 
{
lean_object* v___x_401_; 
lean_dec(v_toBind_392_);
lean_dec(v___y_390_);
lean_dec(v_recur_389_);
v___x_401_ = lean_apply_2(v_toPure_388_, lean_box(0), v_acc_391_);
return v___x_401_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2(lean_object* v_toPure_402_, lean_object* v___y_403_, lean_object* v_toBind_404_, lean_object* v_toPure_405_, lean_object* v_lift_406_, lean_object* v_it_407_, lean_object* v_acc_408_, lean_object* v_hP_409_, lean_object* v_recur_410_){
_start:
{
lean_object* v_s_411_; lean_object* v_offset_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_436_; 
v_s_411_ = lean_ctor_get(v_it_407_, 0);
v_offset_412_ = lean_ctor_get(v_it_407_, 1);
v_isSharedCheck_436_ = !lean_is_exclusive(v_it_407_);
if (v_isSharedCheck_436_ == 0)
{
v___x_414_ = v_it_407_;
v_isShared_415_ = v_isSharedCheck_436_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_offset_412_);
lean_inc(v_s_411_);
lean_dec(v_it_407_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_436_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v_str_416_; lean_object* v_startInclusive_417_; lean_object* v_endExclusive_418_; lean_object* v___f_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_str_416_ = lean_ctor_get(v_s_411_, 0);
lean_inc_ref(v_str_416_);
v_startInclusive_417_ = lean_ctor_get(v_s_411_, 1);
lean_inc(v_startInclusive_417_);
v_endExclusive_418_ = lean_ctor_get(v_s_411_, 2);
v___f_419_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_419_, 0, v_toPure_402_);
lean_closure_set(v___f_419_, 1, v_recur_410_);
lean_closure_set(v___f_419_, 2, v___y_403_);
lean_closure_set(v___f_419_, 3, v_acc_408_);
lean_closure_set(v___f_419_, 4, v_toBind_404_);
v___x_420_ = lean_nat_sub(v_endExclusive_418_, v_startInclusive_417_);
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_add(v_offset_412_, v___x_421_);
v___x_423_ = lean_nat_dec_le(v___x_422_, v___x_420_);
lean_dec(v___x_420_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec(v___x_422_);
lean_dec(v_startInclusive_417_);
lean_dec_ref(v_str_416_);
lean_del_object(v___x_414_);
lean_dec(v_offset_412_);
lean_dec_ref(v_s_411_);
v___x_424_ = lean_box(2);
v___x_425_ = lean_apply_2(v_toPure_405_, lean_box(0), v___x_424_);
v___x_426_ = lean_apply_4(v_lift_406_, lean_box(0), lean_box(0), v___f_419_, v___x_425_);
return v___x_426_;
}
else
{
lean_object* v___x_428_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 1, v___x_422_);
v___x_428_ = v___x_414_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_s_411_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_422_);
v___x_428_ = v_reuseFailAlloc_435_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_429_ = lean_nat_add(v_startInclusive_417_, v_offset_412_);
lean_dec(v_offset_412_);
lean_dec(v_startInclusive_417_);
v___x_430_ = lean_string_get_byte_fast(v_str_416_, v___x_429_);
lean_dec_ref(v_str_416_);
v___x_431_ = lean_box(v___x_430_);
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_428_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = lean_apply_2(v_toPure_405_, lean_box(0), v___x_432_);
v___x_434_ = lean_apply_4(v_lift_406_, lean_box(0), lean_box(0), v___f_419_, v___x_433_);
return v___x_434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3(lean_object* v_inst_437_, lean_object* v_toPure_438_, lean_object* v_lift_439_, lean_object* v_00_u03b3_440_, lean_object* v_Pl_441_, lean_object* v_it_442_, lean_object* v_init_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_toApplicative_445_; lean_object* v_toBind_446_; lean_object* v_toPure_447_; lean_object* v___f_448_; lean_object* v___x_449_; 
v_toApplicative_445_ = lean_ctor_get(v_inst_437_, 0);
lean_inc_ref(v_toApplicative_445_);
v_toBind_446_ = lean_ctor_get(v_inst_437_, 1);
lean_inc(v_toBind_446_);
lean_dec_ref(v_inst_437_);
v_toPure_447_ = lean_ctor_get(v_toApplicative_445_, 1);
lean_inc(v_toPure_447_);
lean_dec_ref(v_toApplicative_445_);
v___f_448_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2), 9, 5);
lean_closure_set(v___f_448_, 0, v_toPure_447_);
lean_closure_set(v___f_448_, 1, v___y_444_);
lean_closure_set(v___f_448_, 2, v_toBind_446_);
lean_closure_set(v___f_448_, 3, v_toPure_438_);
lean_closure_set(v___f_448_, 4, v_lift_439_);
v___x_449_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_448_, v_it_442_, v_init_443_, lean_box(0));
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg(lean_object* v_inst_450_, lean_object* v_inst_451_){
_start:
{
lean_object* v_toApplicative_452_; lean_object* v_toPure_453_; lean_object* v___f_454_; 
v_toApplicative_452_ = lean_ctor_get(v_inst_450_, 0);
lean_inc_ref(v_toApplicative_452_);
lean_dec_ref(v_inst_450_);
v_toPure_453_ = lean_ctor_get(v_toApplicative_452_, 1);
lean_inc(v_toPure_453_);
lean_dec_ref(v_toApplicative_452_);
v___f_454_ = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3), 8, 2);
lean_closure_set(v___f_454_, 0, v_inst_451_);
lean_closure_set(v___f_454_, 1, v_toPure_453_);
return v___f_454_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad(lean_object* v_m_455_, lean_object* v_n_456_, lean_object* v_inst_457_, lean_object* v_inst_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg(v_inst_457_, v_inst_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revBytes(lean_object* v_s_460_){
_start:
{
lean_object* v_startInclusive_461_; lean_object* v_endExclusive_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_startInclusive_461_ = lean_ctor_get(v_s_460_, 1);
v_endExclusive_462_ = lean_ctor_get(v_s_460_, 2);
v___x_463_ = lean_nat_sub(v_endExclusive_462_, v_startInclusive_461_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_s_460_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0(lean_object* v_inst_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_s_471_; lean_object* v_offset_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_492_; 
v_s_471_ = lean_ctor_get(v_x_470_, 0);
v_offset_472_ = lean_ctor_get(v_x_470_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_x_470_);
if (v_isSharedCheck_492_ == 0)
{
v___x_474_ = v_x_470_;
v_isShared_475_ = v_isSharedCheck_492_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_offset_472_);
lean_inc(v_s_471_);
lean_dec(v_x_470_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_492_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; uint8_t v_decide_477_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v_decide_477_ = lean_nat_dec_eq(v_offset_472_, v___x_476_);
if (v_decide_477_ == 0)
{
lean_object* v_str_478_; lean_object* v_startInclusive_479_; lean_object* v___x_480_; lean_object* v_nextOffset_481_; lean_object* v___x_483_; 
v_str_478_ = lean_ctor_get(v_s_471_, 0);
lean_inc_ref(v_str_478_);
v_startInclusive_479_ = lean_ctor_get(v_s_471_, 1);
lean_inc(v_startInclusive_479_);
v___x_480_ = lean_unsigned_to_nat(1u);
v_nextOffset_481_ = lean_nat_sub(v_offset_472_, v___x_480_);
lean_dec(v_offset_472_);
lean_inc(v_nextOffset_481_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v_nextOffset_481_);
v___x_483_ = v___x_474_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_s_471_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_nextOffset_481_);
v___x_483_ = v_reuseFailAlloc_489_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_484_ = lean_nat_add(v_startInclusive_479_, v_nextOffset_481_);
lean_dec(v_nextOffset_481_);
lean_dec(v_startInclusive_479_);
v___x_485_ = lean_string_get_byte_fast(v_str_478_, v___x_484_);
lean_dec_ref(v_str_478_);
v___x_486_ = lean_box(v___x_485_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_483_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = lean_apply_2(v_inst_469_, lean_box(0), v___x_487_);
return v___x_488_;
}
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_del_object(v___x_474_);
lean_dec(v_offset_472_);
lean_dec_ref(v_s_471_);
v___x_490_ = lean_box(2);
v___x_491_ = lean_apply_2(v_inst_469_, lean_box(0), v___x_490_);
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg(lean_object* v_inst_493_){
_start:
{
lean_object* v___f_494_; 
v___f_494_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_494_, 0, v_inst_493_);
return v___f_494_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure(lean_object* v_m_495_, lean_object* v_inst_496_){
_start:
{
lean_object* v___f_497_; 
v___f_497_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(v___f_497_, 0, v_inst_496_);
return v___f_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = lean_box(0);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___redArg();
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation(lean_object* v_m_502_, lean_object* v_inst_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = lean_box(0);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___boxed(lean_object* v_m_505_, lean_object* v_inst_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation(v_m_505_, v_inst_506_);
lean_dec(v_inst_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0(lean_object* v_toPure_508_, lean_object* v_recur_509_, lean_object* v_it_510_, lean_object* v_____do__lift_511_){
_start:
{
if (lean_obj_tag(v_____do__lift_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_513_; 
lean_dec_ref(v_it_510_);
lean_dec(v_recur_509_);
v_a_512_ = lean_ctor_get(v_____do__lift_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v_____do__lift_511_, 1);
v___x_513_ = lean_apply_2(v_toPure_508_, lean_box(0), v_a_512_);
return v___x_513_;
}
else
{
lean_object* v_a_514_; lean_object* v___x_515_; 
lean_dec(v_toPure_508_);
v_a_514_ = lean_ctor_get(v_____do__lift_511_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v_____do__lift_511_, 1);
v___x_515_ = lean_apply_4(v_recur_509_, v_it_510_, v_a_514_, lean_box(0), lean_box(0));
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1(lean_object* v_toPure_516_, lean_object* v_recur_517_, lean_object* v___y_518_, lean_object* v_acc_519_, lean_object* v_toBind_520_, lean_object* v_s_521_){
_start:
{
switch(lean_obj_tag(v_s_521_))
{
case 0:
{
lean_object* v_it_522_; lean_object* v_out_523_; lean_object* v___f_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_it_522_ = lean_ctor_get(v_s_521_, 0);
lean_inc(v_it_522_);
v_out_523_ = lean_ctor_get(v_s_521_, 1);
lean_inc(v_out_523_);
lean_dec_ref_known(v_s_521_, 2);
v___f_524_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_524_, 0, v_toPure_516_);
lean_closure_set(v___f_524_, 1, v_recur_517_);
lean_closure_set(v___f_524_, 2, v_it_522_);
v___x_525_ = lean_apply_3(v___y_518_, v_out_523_, lean_box(0), v_acc_519_);
v___x_526_ = lean_apply_4(v_toBind_520_, lean_box(0), lean_box(0), v___x_525_, v___f_524_);
return v___x_526_;
}
case 1:
{
lean_object* v_it_527_; lean_object* v___x_528_; 
lean_dec(v_toBind_520_);
lean_dec(v___y_518_);
lean_dec(v_toPure_516_);
v_it_527_ = lean_ctor_get(v_s_521_, 0);
lean_inc(v_it_527_);
lean_dec_ref_known(v_s_521_, 1);
v___x_528_ = lean_apply_4(v_recur_517_, v_it_527_, v_acc_519_, lean_box(0), lean_box(0));
return v___x_528_;
}
default: 
{
lean_object* v___x_529_; 
lean_dec(v_toBind_520_);
lean_dec(v___y_518_);
lean_dec(v_recur_517_);
v___x_529_ = lean_apply_2(v_toPure_516_, lean_box(0), v_acc_519_);
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2(lean_object* v_toPure_530_, lean_object* v___y_531_, lean_object* v_toBind_532_, lean_object* v_toPure_533_, lean_object* v_lift_534_, lean_object* v_it_535_, lean_object* v_acc_536_, lean_object* v_hP_537_, lean_object* v_recur_538_){
_start:
{
lean_object* v_s_539_; lean_object* v_offset_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_563_; 
v_s_539_ = lean_ctor_get(v_it_535_, 0);
v_offset_540_ = lean_ctor_get(v_it_535_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_it_535_);
if (v_isSharedCheck_563_ == 0)
{
v___x_542_ = v_it_535_;
v_isShared_543_ = v_isSharedCheck_563_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_offset_540_);
lean_inc(v_s_539_);
lean_dec(v_it_535_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_563_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___f_544_; lean_object* v___x_545_; uint8_t v_decide_546_; 
v___f_544_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_544_, 0, v_toPure_530_);
lean_closure_set(v___f_544_, 1, v_recur_538_);
lean_closure_set(v___f_544_, 2, v___y_531_);
lean_closure_set(v___f_544_, 3, v_acc_536_);
lean_closure_set(v___f_544_, 4, v_toBind_532_);
v___x_545_ = lean_unsigned_to_nat(0u);
v_decide_546_ = lean_nat_dec_eq(v_offset_540_, v___x_545_);
if (v_decide_546_ == 0)
{
lean_object* v_str_547_; lean_object* v_startInclusive_548_; lean_object* v___x_549_; lean_object* v_nextOffset_550_; lean_object* v___x_552_; 
v_str_547_ = lean_ctor_get(v_s_539_, 0);
lean_inc_ref(v_str_547_);
v_startInclusive_548_ = lean_ctor_get(v_s_539_, 1);
lean_inc(v_startInclusive_548_);
v___x_549_ = lean_unsigned_to_nat(1u);
v_nextOffset_550_ = lean_nat_sub(v_offset_540_, v___x_549_);
lean_dec(v_offset_540_);
lean_inc(v_nextOffset_550_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v_nextOffset_550_);
v___x_552_ = v___x_542_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_s_539_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_nextOffset_550_);
v___x_552_ = v_reuseFailAlloc_559_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; uint8_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_553_ = lean_nat_add(v_startInclusive_548_, v_nextOffset_550_);
lean_dec(v_nextOffset_550_);
lean_dec(v_startInclusive_548_);
v___x_554_ = lean_string_get_byte_fast(v_str_547_, v___x_553_);
lean_dec_ref(v_str_547_);
v___x_555_ = lean_box(v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_552_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = lean_apply_2(v_toPure_533_, lean_box(0), v___x_556_);
v___x_558_ = lean_apply_4(v_lift_534_, lean_box(0), lean_box(0), v___f_544_, v___x_557_);
return v___x_558_;
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_del_object(v___x_542_);
lean_dec(v_offset_540_);
lean_dec_ref(v_s_539_);
v___x_560_ = lean_box(2);
v___x_561_ = lean_apply_2(v_toPure_533_, lean_box(0), v___x_560_);
v___x_562_ = lean_apply_4(v_lift_534_, lean_box(0), lean_box(0), v___f_544_, v___x_561_);
return v___x_562_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3(lean_object* v_inst_564_, lean_object* v_toPure_565_, lean_object* v_lift_566_, lean_object* v_00_u03b3_567_, lean_object* v_Pl_568_, lean_object* v_it_569_, lean_object* v_init_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_toApplicative_572_; lean_object* v_toBind_573_; lean_object* v_toPure_574_; lean_object* v___f_575_; lean_object* v___x_576_; 
v_toApplicative_572_ = lean_ctor_get(v_inst_564_, 0);
lean_inc_ref(v_toApplicative_572_);
v_toBind_573_ = lean_ctor_get(v_inst_564_, 1);
lean_inc(v_toBind_573_);
lean_dec_ref(v_inst_564_);
v_toPure_574_ = lean_ctor_get(v_toApplicative_572_, 1);
lean_inc(v_toPure_574_);
lean_dec_ref(v_toApplicative_572_);
v___f_575_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2), 9, 5);
lean_closure_set(v___f_575_, 0, v_toPure_574_);
lean_closure_set(v___f_575_, 1, v___y_571_);
lean_closure_set(v___f_575_, 2, v_toBind_573_);
lean_closure_set(v___f_575_, 3, v_toPure_565_);
lean_closure_set(v___f_575_, 4, v_lift_566_);
v___x_576_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_575_, v_it_569_, v_init_570_, lean_box(0));
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg(lean_object* v_inst_577_, lean_object* v_inst_578_){
_start:
{
lean_object* v_toApplicative_579_; lean_object* v_toPure_580_; lean_object* v___f_581_; 
v_toApplicative_579_ = lean_ctor_get(v_inst_577_, 0);
lean_inc_ref(v_toApplicative_579_);
lean_dec_ref(v_inst_577_);
v_toPure_580_ = lean_ctor_get(v_toApplicative_579_, 1);
lean_inc(v_toPure_580_);
lean_dec_ref(v_toApplicative_579_);
v___f_581_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3), 8, 2);
lean_closure_set(v___f_581_, 0, v_inst_578_);
lean_closure_set(v___f_581_, 1, v_toPure_580_);
return v___f_581_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad(lean_object* v_m_582_, lean_object* v_n_583_, lean_object* v_inst_584_, lean_object* v_inst_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg(v_inst_584_, v_inst_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0(lean_object* v_toPure_587_, lean_object* v_____do__lift_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_apply_2(v_toPure_587_, lean_box(0), v_____do__lift_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1(lean_object* v_toPure_590_, lean_object* v_recur_591_, lean_object* v___x_592_, lean_object* v_____do__lift_593_){
_start:
{
if (lean_obj_tag(v_____do__lift_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; 
lean_dec(v___x_592_);
lean_dec(v_recur_591_);
v_a_594_ = lean_ctor_get(v_____do__lift_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v_____do__lift_593_, 1);
v___x_595_ = lean_apply_2(v_toPure_590_, lean_box(0), v_a_594_);
return v___x_595_;
}
else
{
lean_object* v_a_596_; lean_object* v___x_597_; 
lean_dec(v_toPure_590_);
v_a_596_ = lean_ctor_get(v_____do__lift_593_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v_____do__lift_593_, 1);
v___x_597_ = lean_apply_4(v_recur_591_, v___x_592_, v_a_596_, lean_box(0), lean_box(0));
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2(lean_object* v_s_598_, lean_object* v_toPure_599_, lean_object* v_f_600_, lean_object* v_toBind_601_, lean_object* v___f_602_, lean_object* v_it_603_, lean_object* v_acc_604_, lean_object* v_hP_605_, lean_object* v_recur_606_){
_start:
{
lean_object* v_str_607_; lean_object* v_startInclusive_608_; lean_object* v_endExclusive_609_; lean_object* v___x_610_; uint8_t v_decide_611_; 
v_str_607_ = lean_ctor_get(v_s_598_, 0);
v_startInclusive_608_ = lean_ctor_get(v_s_598_, 1);
v_endExclusive_609_ = lean_ctor_get(v_s_598_, 2);
v___x_610_ = lean_nat_sub(v_endExclusive_609_, v_startInclusive_608_);
v_decide_611_ = lean_nat_dec_eq(v_it_603_, v___x_610_);
lean_dec(v___x_610_);
if (v_decide_611_ == 0)
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___f_615_; uint32_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_612_ = lean_nat_add(v_startInclusive_608_, v_it_603_);
v___x_613_ = lean_string_utf8_next_fast(v_str_607_, v___x_612_);
v___x_614_ = lean_nat_sub(v___x_613_, v_startInclusive_608_);
v___f_615_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_615_, 0, v_toPure_599_);
lean_closure_set(v___f_615_, 1, v_recur_606_);
lean_closure_set(v___f_615_, 2, v___x_614_);
v___x_616_ = lean_string_utf8_get_fast(v_str_607_, v___x_612_);
lean_dec(v___x_612_);
v___x_617_ = lean_box_uint32(v___x_616_);
v___x_618_ = lean_apply_2(v_f_600_, v___x_617_, v_acc_604_);
lean_inc(v_toBind_601_);
v___x_619_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_618_, v___f_602_);
v___x_620_ = lean_apply_4(v_toBind_601_, lean_box(0), lean_box(0), v___x_619_, v___f_615_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; 
lean_dec(v_recur_606_);
lean_dec(v___f_602_);
lean_dec(v_toBind_601_);
lean_dec(v_f_600_);
v___x_621_ = lean_apply_2(v_toPure_599_, lean_box(0), v_acc_604_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2___boxed(lean_object* v_s_622_, lean_object* v_toPure_623_, lean_object* v_f_624_, lean_object* v_toBind_625_, lean_object* v___f_626_, lean_object* v_it_627_, lean_object* v_acc_628_, lean_object* v_hP_629_, lean_object* v_recur_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2(v_s_622_, v_toPure_623_, v_f_624_, v_toBind_625_, v___f_626_, v_it_627_, v_acc_628_, v_hP_629_, v_recur_630_);
lean_dec(v_it_627_);
lean_dec_ref(v_s_622_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3(lean_object* v_inst_632_, lean_object* v_00_u03b2_633_, lean_object* v_s_634_, lean_object* v_b_635_, lean_object* v_f_636_){
_start:
{
lean_object* v_toApplicative_637_; lean_object* v_toBind_638_; lean_object* v_toPure_639_; lean_object* v___x_640_; lean_object* v___f_641_; lean_object* v___f_642_; lean_object* v___x_643_; 
v_toApplicative_637_ = lean_ctor_get(v_inst_632_, 0);
lean_inc_ref(v_toApplicative_637_);
v_toBind_638_ = lean_ctor_get(v_inst_632_, 1);
lean_inc(v_toBind_638_);
lean_dec_ref(v_inst_632_);
v_toPure_639_ = lean_ctor_get(v_toApplicative_637_, 1);
lean_inc_n(v_toPure_639_, 2);
lean_dec_ref(v_toApplicative_637_);
v___x_640_ = lean_unsigned_to_nat(0u);
v___f_641_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_641_, 0, v_toPure_639_);
v___f_642_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2___boxed), 9, 5);
lean_closure_set(v___f_642_, 0, v_s_634_);
lean_closure_set(v___f_642_, 1, v_toPure_639_);
lean_closure_set(v___f_642_, 2, v_f_636_);
lean_closure_set(v___f_642_, 3, v_toBind_638_);
lean_closure_set(v___f_642_, 4, v___f_641_);
v___x_643_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_642_, v___x_640_, v_b_635_, lean_box(0));
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg(lean_object* v_inst_644_){
_start:
{
lean_object* v___f_645_; 
v___f_645_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_645_, 0, v_inst_644_);
return v___f_645_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad(lean_object* v_m_646_, lean_object* v_inst_647_){
_start:
{
lean_object* v___f_648_; 
v___f_648_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_648_, 0, v_inst_647_);
return v___f_648_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg___lam__0(lean_object* v_s_649_, lean_object* v_f_650_, lean_object* v_it_651_, lean_object* v_acc_652_, lean_object* v_hP_653_, lean_object* v_recur_654_){
_start:
{
lean_object* v_str_655_; lean_object* v_startInclusive_656_; lean_object* v_endExclusive_657_; lean_object* v___x_658_; uint8_t v_decide_659_; 
v_str_655_ = lean_ctor_get(v_s_649_, 0);
v_startInclusive_656_ = lean_ctor_get(v_s_649_, 1);
v_endExclusive_657_ = lean_ctor_get(v_s_649_, 2);
v___x_658_ = lean_nat_sub(v_endExclusive_657_, v_startInclusive_656_);
v_decide_659_ = lean_nat_dec_eq(v_it_651_, v___x_658_);
lean_dec(v___x_658_);
if (v_decide_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint32_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_660_ = lean_nat_add(v_startInclusive_656_, v_it_651_);
v___x_661_ = lean_string_utf8_next_fast(v_str_655_, v___x_660_);
v___x_662_ = lean_nat_sub(v___x_661_, v_startInclusive_656_);
v___x_663_ = lean_string_utf8_get_fast(v_str_655_, v___x_660_);
lean_dec(v___x_660_);
v___x_664_ = lean_box_uint32(v___x_663_);
v___x_665_ = lean_apply_2(v_f_650_, v_acc_652_, v___x_664_);
v___x_666_ = lean_apply_4(v_recur_654_, v___x_662_, v___x_665_, lean_box(0), lean_box(0));
return v___x_666_;
}
else
{
lean_dec(v_recur_654_);
lean_dec(v_f_650_);
return v_acc_652_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg___lam__0___boxed(lean_object* v_s_667_, lean_object* v_f_668_, lean_object* v_it_669_, lean_object* v_acc_670_, lean_object* v_hP_671_, lean_object* v_recur_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_String_Slice_foldl___redArg___lam__0(v_s_667_, v_f_668_, v_it_669_, v_acc_670_, v_hP_671_, v_recur_672_);
lean_dec(v_it_669_);
lean_dec_ref(v_s_667_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg(lean_object* v_f_674_, lean_object* v_init_675_, lean_object* v_s_676_){
_start:
{
lean_object* v___f_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___f_677_ = lean_alloc_closure((void*)(l_String_Slice_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_677_, 0, v_s_676_);
lean_closure_set(v___f_677_, 1, v_f_674_);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_677_, v___x_678_, v_init_675_, lean_box(0));
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl(lean_object* v_00_u03b1_680_, lean_object* v_f_681_, lean_object* v_init_682_, lean_object* v_s_683_){
_start:
{
lean_object* v___f_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___f_684_ = lean_alloc_closure((void*)(l_String_Slice_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_684_, 0, v_s_683_);
lean_closure_set(v___f_684_, 1, v_f_681_);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_684_, v___x_685_, v_init_682_, lean_box(0));
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg___lam__0(lean_object* v_s_687_, lean_object* v_f_688_, lean_object* v_it_689_, lean_object* v_acc_690_, lean_object* v_hP_691_, lean_object* v_recur_692_){
_start:
{
lean_object* v___x_693_; uint8_t v_decide_694_; 
v___x_693_ = lean_unsigned_to_nat(0u);
v_decide_694_ = lean_nat_dec_eq(v_it_689_, v___x_693_);
if (v_decide_694_ == 0)
{
lean_object* v_str_695_; lean_object* v_startInclusive_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v_prevPos_699_; lean_object* v___x_700_; uint32_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_str_695_ = lean_ctor_get(v_s_687_, 0);
v_startInclusive_696_ = lean_ctor_get(v_s_687_, 1);
v___x_697_ = lean_unsigned_to_nat(1u);
v___x_698_ = lean_nat_sub(v_it_689_, v___x_697_);
v_prevPos_699_ = l_String_Slice_posLE(v_s_687_, v___x_698_);
v___x_700_ = lean_nat_add(v_startInclusive_696_, v_prevPos_699_);
v___x_701_ = lean_string_utf8_get_fast(v_str_695_, v___x_700_);
lean_dec(v___x_700_);
v___x_702_ = lean_box_uint32(v___x_701_);
v___x_703_ = lean_apply_2(v_f_688_, v___x_702_, v_acc_690_);
v___x_704_ = lean_apply_4(v_recur_692_, v_prevPos_699_, v___x_703_, lean_box(0), lean_box(0));
return v___x_704_;
}
else
{
lean_dec(v_recur_692_);
lean_dec(v_f_688_);
return v_acc_690_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg___lam__0___boxed(lean_object* v_s_705_, lean_object* v_f_706_, lean_object* v_it_707_, lean_object* v_acc_708_, lean_object* v_hP_709_, lean_object* v_recur_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_String_Slice_foldr___redArg___lam__0(v_s_705_, v_f_706_, v_it_707_, v_acc_708_, v_hP_709_, v_recur_710_);
lean_dec(v_it_707_);
lean_dec_ref(v_s_705_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg(lean_object* v_f_712_, lean_object* v_init_713_, lean_object* v_s_714_){
_start:
{
lean_object* v___f_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_inc_ref(v_s_714_);
v___f_715_ = lean_alloc_closure((void*)(l_String_Slice_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_715_, 0, v_s_714_);
lean_closure_set(v___f_715_, 1, v_f_712_);
v___x_716_ = l_String_Slice_revPositions(v_s_714_);
lean_dec_ref(v_s_714_);
v___x_717_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_715_, v___x_716_, v_init_713_, lean_box(0));
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr(lean_object* v_00_u03b1_718_, lean_object* v_f_719_, lean_object* v_init_720_, lean_object* v_s_721_){
_start:
{
lean_object* v___f_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
lean_inc_ref(v_s_721_);
v___f_722_ = lean_alloc_closure((void*)(l_String_Slice_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(v___f_722_, 0, v_s_721_);
lean_closure_set(v___f_722_, 1, v_f_719_);
v___x_723_ = l_String_Slice_revPositions(v_s_721_);
lean_dec_ref(v_s_721_);
v___x_724_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_722_, v___x_723_, v_init_720_, lean_box(0));
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___redArg(lean_object* v_x_725_){
_start:
{
lean_inc(v_x_725_);
return v_x_725_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___redArg___boxed(lean_object* v_x_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_String_Internal_ofToSliceWithProof___redArg(v_x_726_);
lean_dec(v_x_726_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof(lean_object* v_s_728_, lean_object* v_x_729_){
_start:
{
lean_inc(v_x_729_);
return v_x_729_;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___boxed(lean_object* v_s_730_, lean_object* v_x_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_String_Internal_ofToSliceWithProof(v_s_730_, v_x_731_);
lean_dec(v_x_731_);
lean_dec_ref(v_s_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom___redArg(lean_object* v_p_733_){
_start:
{
lean_inc(v_p_733_);
return v_p_733_;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom___redArg___boxed(lean_object* v_p_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_String_positionsFrom___redArg(v_p_734_);
lean_dec(v_p_734_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom(lean_object* v_s_736_, lean_object* v_p_737_){
_start:
{
lean_inc(v_p_737_);
return v_p_737_;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom___boxed(lean_object* v_s_738_, lean_object* v_p_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_String_positionsFrom(v_s_738_, v_p_739_);
lean_dec(v_p_739_);
lean_dec_ref(v_s_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_String_positions___redArg(){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lean_unsigned_to_nat(0u);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_String_positions___redArg___boxed(lean_object* v___dummy_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_String_positions___redArg();
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_String_positions(lean_object* v_s_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = lean_unsigned_to_nat(0u);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_String_positions___boxed(lean_object* v_s_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_String_positions(v_s_747_);
lean_dec_ref(v_s_747_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_String_chars___redArg(){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lean_unsigned_to_nat(0u);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_String_chars___redArg___boxed(lean_object* v___dummy_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_String_chars___redArg();
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_String_chars(lean_object* v_s_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = lean_unsigned_to_nat(0u);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_String_chars___boxed(lean_object* v_s_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_String_chars(v_s_755_);
lean_dec_ref(v_s_755_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom___redArg(lean_object* v_p_757_){
_start:
{
lean_inc(v_p_757_);
return v_p_757_;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom___redArg___boxed(lean_object* v_p_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_String_revPositionsFrom___redArg(v_p_758_);
lean_dec(v_p_758_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom(lean_object* v_s_760_, lean_object* v_p_761_){
_start:
{
lean_inc(v_p_761_);
return v_p_761_;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom___boxed(lean_object* v_s_762_, lean_object* v_p_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_String_revPositionsFrom(v_s_762_, v_p_763_);
lean_dec(v_p_763_);
lean_dec_ref(v_s_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_String_revPositions(lean_object* v_s_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = lean_string_utf8_byte_size(v_s_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_String_revPositions___boxed(lean_object* v_s_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_String_revPositions(v_s_767_);
lean_dec_ref(v_s_767_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_String_revChars(lean_object* v_s_769_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_string_utf8_byte_size(v_s_769_);
v___x_772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_772_, 0, v_s_769_);
lean_ctor_set(v___x_772_, 1, v___x_770_);
lean_ctor_set(v___x_772_, 2, v___x_771_);
v___x_773_ = l_String_Slice_revPositions(v___x_772_);
lean_dec_ref_known(v___x_772_, 3);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_String_byteIterator(lean_object* v_s_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lean_string_utf8_byte_size(v_s_774_);
v___x_777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_777_, 0, v_s_774_);
lean_ctor_set(v___x_777_, 1, v___x_775_);
lean_ctor_set(v___x_777_, 2, v___x_776_);
v___x_778_ = l_String_Slice_bytes(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_String_revBytes(lean_object* v_s_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_string_utf8_byte_size(v_s_779_);
v___x_782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_782_, 0, v_s_779_);
lean_ctor_set(v___x_782_, 1, v___x_780_);
lean_ctor_set(v___x_782_, 2, v___x_781_);
v___x_783_ = l_String_Slice_revBytes(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__2(lean_object* v___x_784_, lean_object* v_s_785_, lean_object* v_toPure_786_, lean_object* v_f_787_, lean_object* v_toBind_788_, lean_object* v___f_789_, lean_object* v_it_790_, lean_object* v_acc_791_, lean_object* v_hP_792_, lean_object* v_recur_793_){
_start:
{
uint8_t v_decide_794_; 
v_decide_794_ = lean_nat_dec_eq(v_it_790_, v___x_784_);
if (v_decide_794_ == 0)
{
lean_object* v___x_795_; lean_object* v___f_796_; uint32_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_795_ = lean_string_utf8_next_fast(v_s_785_, v_it_790_);
v___f_796_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(v___f_796_, 0, v_toPure_786_);
lean_closure_set(v___f_796_, 1, v_recur_793_);
lean_closure_set(v___f_796_, 2, v___x_795_);
v___x_797_ = lean_string_utf8_get_fast(v_s_785_, v_it_790_);
v___x_798_ = lean_box_uint32(v___x_797_);
v___x_799_ = lean_apply_2(v_f_787_, v___x_798_, v_acc_791_);
lean_inc(v_toBind_788_);
v___x_800_ = lean_apply_4(v_toBind_788_, lean_box(0), lean_box(0), v___x_799_, v___f_789_);
v___x_801_ = lean_apply_4(v_toBind_788_, lean_box(0), lean_box(0), v___x_800_, v___f_796_);
return v___x_801_;
}
else
{
lean_object* v___x_802_; 
lean_dec(v_recur_793_);
lean_dec(v___f_789_);
lean_dec(v_toBind_788_);
lean_dec(v_f_787_);
v___x_802_ = lean_apply_2(v_toPure_786_, lean_box(0), v_acc_791_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__2___boxed(lean_object* v___x_803_, lean_object* v_s_804_, lean_object* v_toPure_805_, lean_object* v_f_806_, lean_object* v_toBind_807_, lean_object* v___f_808_, lean_object* v_it_809_, lean_object* v_acc_810_, lean_object* v_hP_811_, lean_object* v_recur_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_String_instForInCharOfMonad___redArg___lam__2(v___x_803_, v_s_804_, v_toPure_805_, v_f_806_, v_toBind_807_, v___f_808_, v_it_809_, v_acc_810_, v_hP_811_, v_recur_812_);
lean_dec(v_it_809_);
lean_dec_ref(v_s_804_);
lean_dec(v___x_803_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__0(lean_object* v_inst_814_, lean_object* v_00_u03b2_815_, lean_object* v_s_816_, lean_object* v_b_817_, lean_object* v_f_818_){
_start:
{
lean_object* v_toApplicative_819_; lean_object* v_toBind_820_; lean_object* v_toPure_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___f_824_; lean_object* v___f_825_; lean_object* v___x_826_; 
v_toApplicative_819_ = lean_ctor_get(v_inst_814_, 0);
lean_inc_ref(v_toApplicative_819_);
v_toBind_820_ = lean_ctor_get(v_inst_814_, 1);
lean_inc(v_toBind_820_);
lean_dec_ref(v_inst_814_);
v_toPure_821_ = lean_ctor_get(v_toApplicative_819_, 1);
lean_inc_n(v_toPure_821_, 2);
lean_dec_ref(v_toApplicative_819_);
v___x_822_ = lean_string_utf8_byte_size(v_s_816_);
v___x_823_ = lean_unsigned_to_nat(0u);
v___f_824_ = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_824_, 0, v_toPure_821_);
v___f_825_ = lean_alloc_closure((void*)(l_String_instForInCharOfMonad___redArg___lam__2___boxed), 10, 6);
lean_closure_set(v___f_825_, 0, v___x_822_);
lean_closure_set(v___f_825_, 1, v_s_816_);
lean_closure_set(v___f_825_, 2, v_toPure_821_);
lean_closure_set(v___f_825_, 3, v_f_818_);
lean_closure_set(v___f_825_, 4, v_toBind_820_);
lean_closure_set(v___f_825_, 5, v___f_824_);
v___x_826_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_825_, v___x_823_, v_b_817_, lean_box(0));
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg(lean_object* v_inst_827_){
_start:
{
lean_object* v___f_828_; 
v___f_828_ = lean_alloc_closure((void*)(l_String_instForInCharOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_828_, 0, v_inst_827_);
return v___f_828_;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad(lean_object* v_m_829_, lean_object* v_inst_830_){
_start:
{
lean_object* v___f_831_; 
v___f_831_ = lean_alloc_closure((void*)(l_String_instForInCharOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_831_, 0, v_inst_830_);
return v___f_831_;
}
}
LEAN_EXPORT lean_object* l_String_foldl___redArg___lam__0(lean_object* v___x_832_, lean_object* v_s_833_, lean_object* v_f_834_, lean_object* v_it_835_, lean_object* v_acc_836_, lean_object* v_hP_837_, lean_object* v_recur_838_){
_start:
{
uint8_t v_decide_839_; 
v_decide_839_ = lean_nat_dec_eq(v_it_835_, v___x_832_);
if (v_decide_839_ == 0)
{
lean_object* v___x_840_; uint32_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_840_ = lean_string_utf8_next_fast(v_s_833_, v_it_835_);
v___x_841_ = lean_string_utf8_get_fast(v_s_833_, v_it_835_);
v___x_842_ = lean_box_uint32(v___x_841_);
v___x_843_ = lean_apply_2(v_f_834_, v_acc_836_, v___x_842_);
v___x_844_ = lean_apply_4(v_recur_838_, v___x_840_, v___x_843_, lean_box(0), lean_box(0));
return v___x_844_;
}
else
{
lean_dec(v_recur_838_);
lean_dec(v_f_834_);
return v_acc_836_;
}
}
}
LEAN_EXPORT lean_object* l_String_foldl___redArg___lam__0___boxed(lean_object* v___x_845_, lean_object* v_s_846_, lean_object* v_f_847_, lean_object* v_it_848_, lean_object* v_acc_849_, lean_object* v_hP_850_, lean_object* v_recur_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_String_foldl___redArg___lam__0(v___x_845_, v_s_846_, v_f_847_, v_it_848_, v_acc_849_, v_hP_850_, v_recur_851_);
lean_dec(v_it_848_);
lean_dec_ref(v_s_846_);
lean_dec(v___x_845_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_String_foldl___redArg(lean_object* v_f_853_, lean_object* v_init_854_, lean_object* v_s_855_){
_start:
{
lean_object* v___x_856_; lean_object* v___f_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_856_ = lean_string_utf8_byte_size(v_s_855_);
v___f_857_ = lean_alloc_closure((void*)(l_String_foldl___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_857_, 0, v___x_856_);
lean_closure_set(v___f_857_, 1, v_s_855_);
lean_closure_set(v___f_857_, 2, v_f_853_);
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_857_, v___x_858_, v_init_854_, lean_box(0));
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_String_foldl(lean_object* v_00_u03b1_860_, lean_object* v_f_861_, lean_object* v_init_862_, lean_object* v_s_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___f_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_864_ = lean_string_utf8_byte_size(v_s_863_);
v___f_865_ = lean_alloc_closure((void*)(l_String_foldl___redArg___lam__0___boxed), 7, 3);
lean_closure_set(v___f_865_, 0, v___x_864_);
lean_closure_set(v___f_865_, 1, v_s_863_);
lean_closure_set(v___f_865_, 2, v_f_861_);
v___x_866_ = lean_unsigned_to_nat(0u);
v___x_867_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_865_, v___x_866_, v_init_862_, lean_box(0));
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(lean_object* v_f_868_, lean_object* v___x_869_, lean_object* v_s_870_, lean_object* v_a_871_, lean_object* v_b_872_){
_start:
{
uint8_t v_decide_873_; 
v_decide_873_ = lean_nat_dec_eq(v_a_871_, v___x_869_);
if (v_decide_873_ == 0)
{
uint32_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_874_ = lean_string_utf8_get_fast(v_s_870_, v_a_871_);
v___x_875_ = lean_string_utf8_next_fast(v_s_870_, v_a_871_);
lean_dec(v_a_871_);
v___x_876_ = lean_box_uint32(v___x_874_);
lean_inc_ref(v_f_868_);
v___x_877_ = lean_apply_2(v_f_868_, v_b_872_, v___x_876_);
v_a_871_ = v___x_875_;
v_b_872_ = v___x_877_;
goto _start;
}
else
{
lean_dec(v_a_871_);
lean_dec_ref(v_f_868_);
return v_b_872_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg___boxed(lean_object* v_f_879_, lean_object* v___x_880_, lean_object* v_s_881_, lean_object* v_a_882_, lean_object* v_b_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(v_f_879_, v___x_880_, v_s_881_, v_a_882_, v_b_883_);
lean_dec_ref(v_s_881_);
lean_dec(v___x_880_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* lean_string_foldl(lean_object* v_f_885_, lean_object* v_init_886_, lean_object* v_s_887_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_string_utf8_byte_size(v_s_887_);
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(v_f_885_, v___x_888_, v_s_887_, v___x_889_, v_init_886_);
lean_dec_ref(v_s_887_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0(lean_object* v_f_891_, lean_object* v___x_892_, lean_object* v___x_893_, lean_object* v_s_894_, lean_object* v_inst_895_, lean_object* v_R_896_, lean_object* v_a_897_, lean_object* v_b_898_, lean_object* v_c_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(v_f_891_, v___x_893_, v_s_894_, v_a_897_, v_b_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___boxed(lean_object* v_f_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v_s_904_, lean_object* v_inst_905_, lean_object* v_R_906_, lean_object* v_a_907_, lean_object* v_b_908_, lean_object* v_c_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0(v_f_901_, v___x_902_, v___x_903_, v_s_904_, v_inst_905_, v_R_906_, v_a_907_, v_b_908_, v_c_909_);
lean_dec_ref(v_s_904_);
lean_dec(v___x_903_);
lean_dec_ref(v___x_902_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_String_foldr___redArg___lam__0(lean_object* v___x_911_, lean_object* v___x_912_, lean_object* v_s_913_, lean_object* v_f_914_, lean_object* v_it_915_, lean_object* v_acc_916_, lean_object* v_hP_917_, lean_object* v_recur_918_){
_start:
{
uint8_t v_decide_919_; 
v_decide_919_ = lean_nat_dec_eq(v_it_915_, v___x_911_);
if (v_decide_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v_prevPos_922_; uint32_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_920_ = lean_unsigned_to_nat(1u);
v___x_921_ = lean_nat_sub(v_it_915_, v___x_920_);
v_prevPos_922_ = l_String_Slice_posLE(v___x_912_, v___x_921_);
v___x_923_ = lean_string_utf8_get_fast(v_s_913_, v_prevPos_922_);
v___x_924_ = lean_box_uint32(v___x_923_);
v___x_925_ = lean_apply_2(v_f_914_, v___x_924_, v_acc_916_);
v___x_926_ = lean_apply_4(v_recur_918_, v_prevPos_922_, v___x_925_, lean_box(0), lean_box(0));
return v___x_926_;
}
else
{
lean_dec(v_recur_918_);
lean_dec(v_f_914_);
return v_acc_916_;
}
}
}
LEAN_EXPORT lean_object* l_String_foldr___redArg___lam__0___boxed(lean_object* v___x_927_, lean_object* v___x_928_, lean_object* v_s_929_, lean_object* v_f_930_, lean_object* v_it_931_, lean_object* v_acc_932_, lean_object* v_hP_933_, lean_object* v_recur_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_String_foldr___redArg___lam__0(v___x_927_, v___x_928_, v_s_929_, v_f_930_, v_it_931_, v_acc_932_, v_hP_933_, v_recur_934_);
lean_dec(v_it_931_);
lean_dec_ref(v_s_929_);
lean_dec_ref(v___x_928_);
lean_dec(v___x_927_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_String_foldr___redArg(lean_object* v_f_936_, lean_object* v_init_937_, lean_object* v_s_938_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___f_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = lean_string_utf8_byte_size(v_s_938_);
lean_inc_ref(v_s_938_);
v___x_941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_941_, 0, v_s_938_);
lean_ctor_set(v___x_941_, 1, v___x_939_);
lean_ctor_set(v___x_941_, 2, v___x_940_);
lean_inc_ref(v___x_941_);
v___f_942_ = lean_alloc_closure((void*)(l_String_foldr___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_942_, 0, v___x_939_);
lean_closure_set(v___f_942_, 1, v___x_941_);
lean_closure_set(v___f_942_, 2, v_s_938_);
lean_closure_set(v___f_942_, 3, v_f_936_);
v___x_943_ = l_String_Slice_revPositions(v___x_941_);
lean_dec_ref_known(v___x_941_, 3);
v___x_944_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_942_, v___x_943_, v_init_937_, lean_box(0));
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_String_foldr(lean_object* v_00_u03b1_945_, lean_object* v_f_946_, lean_object* v_init_947_, lean_object* v_s_948_){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___f_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = lean_string_utf8_byte_size(v_s_948_);
lean_inc_ref(v_s_948_);
v___x_951_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_951_, 0, v_s_948_);
lean_ctor_set(v___x_951_, 1, v___x_949_);
lean_ctor_set(v___x_951_, 2, v___x_950_);
lean_inc_ref(v___x_951_);
v___f_952_ = lean_alloc_closure((void*)(l_String_foldr___redArg___lam__0___boxed), 8, 4);
lean_closure_set(v___f_952_, 0, v___x_949_);
lean_closure_set(v___f_952_, 1, v___x_951_);
lean_closure_set(v___f_952_, 2, v_s_948_);
lean_closure_set(v___f_952_, 3, v_f_946_);
v___x_953_ = l_String_Slice_revPositions(v___x_951_);
lean_dec_ref_known(v___x_951_, 3);
v___x_954_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_952_, v___x_953_, v_init_947_, lean_box(0));
return v___x_954_;
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
