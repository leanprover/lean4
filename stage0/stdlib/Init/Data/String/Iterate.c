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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
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
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
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
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
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
lean_object* lean_string_utf8_byte_size(lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator_default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_instInhabitedPosIterator_default(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedPosIterator___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_instInhabitedPosIterator(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_positionsFrom___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positionsFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_positionsFrom(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positions(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_positions___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_positions(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_nat_add(x_5, x_3);
x_10 = lean_string_utf8_next_fast(x_4, x_9);
lean_dec(x_9);
x_11 = lean_nat_sub(x_10, x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_apply_2(x_2, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_14 = lean_box(2);
x_15 = lean_apply_2(x_2, lean_box(0), x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_apply_4(x_2, x_3, x_7, lean_box(0), lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_apply_3(x_3, x_8, lean_box(0), x_4);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec_ref(x_6);
x_13 = lean_apply_4(x_2, x_12, x_4, lean_box(0), lean_box(0));
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_2(x_1, lean_box(0), x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_10);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_8);
lean_closure_set(x_14, 4, x_4);
x_15 = lean_nat_sub(x_13, x_12);
x_16 = lean_nat_dec_eq(x_7, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_nat_add(x_12, x_7);
x_18 = lean_string_utf8_next_fast(x_11, x_17);
lean_dec(x_17);
x_19 = lean_nat_sub(x_18, x_12);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
x_21 = lean_apply_2(x_5, lean_box(0), x_20);
x_22 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_14, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
x_23 = lean_box(2);
x_24 = lean_apply_2(x_5, lean_box(0), x_23);
x_25 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_14, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed), 10, 6);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_9);
lean_closure_set(x_13, 3, x_11);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_4);
x_14 = l_WellFounded_opaqueFix_u2083___redArg(x_13, x_7, x_8, lean_box(0));
return x_14;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_chars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_chars___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_chars(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_nat_add(x_5, x_2);
lean_dec(x_2);
x_10 = lean_string_utf8_next_fast(x_4, x_9);
lean_dec(x_9);
x_11 = lean_nat_sub(x_10, x_5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_length(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(x_1, x_2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_length___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_length(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(x_1, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator_default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_instInhabitedRevPosIterator_default(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevPosIterator___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_instInhabitedRevPosIterator(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_revPositionsFrom___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositionsFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_revPositionsFrom(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_sub(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revPositions___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_revPositions(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
x_8 = l_String_Slice_posLE(x_1, x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(2);
x_12 = lean_apply_2(x_2, lean_box(0), x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_alloc_closure((void*)(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_8);
lean_closure_set(x_11, 4, x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_7, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_7, x_14);
x_16 = l_String_Slice_posLE(x_4, x_15);
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_apply_2(x_5, lean_box(0), x_17);
x_19 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_box(2);
x_21 = lean_apply_2(x_5, lean_box(0), x_20);
x_22 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed), 10, 6);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_4);
x_14 = l_WellFounded_opaqueFix_u2083___redArg(x_13, x_7, x_8, lean_box(0));
return x_14;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_alloc_closure((void*)(l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0), 9, 3);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revChars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_revPositions(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revChars___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_revChars(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_bytes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_25; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
x_5 = x_2;
x_6 = x_25;
goto block_24;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
x_10 = lean_nat_sub(x_9, x_8);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_del_object(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_12 = lean_box(2);
x_13 = lean_apply_2(x_1, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_15);
x_16 = x_5;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_15);
x_16 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_nat_add(x_8, x_4);
lean_dec(x_4);
lean_dec(x_8);
x_18 = lean_string_get_byte_fast(x_7, x_17);
lean_dec_ref(x_7);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_apply_2(x_1, lean_box(0), x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorUInt8OfPure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_apply_4(x_2, x_3, x_7, lean_box(0), lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0), 4, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_apply_3(x_3, x_8, lean_box(0), x_4);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec_ref(x_6);
x_13 = lean_apply_4(x_2, x_12, x_4, lean_box(0), lean_box(0));
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_2(x_1, lean_box(0), x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_35; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
x_12 = x_6;
x_13 = x_35;
goto block_34;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 2);
x_17 = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1), 6, 5);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_9);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_7);
lean_closure_set(x_17, 4, x_3);
x_18 = lean_nat_sub(x_16, x_15);
x_19 = lean_nat_dec_lt(x_11, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_del_object(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_20 = lean_box(2);
x_21 = lean_apply_2(x_4, lean_box(0), x_20);
x_22 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_17, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_11, x_23);
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_24);
x_25 = x_12;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_24);
x_25 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_nat_add(x_15, x_11);
lean_dec(x_11);
lean_dec(x_15);
x_27 = lean_string_get_byte_fast(x_14, x_26);
lean_dec_ref(x_14);
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_apply_2(x_4, lean_box(0), x_29);
x_31 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_17, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2), 9, 5);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_2);
lean_closure_set(x_12, 4, x_3);
x_13 = l_WellFounded_opaqueFix_u2083___redArg(x_12, x_6, x_7, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_alloc_closure((void*)(l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3), 8, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revBytes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_sub(x_3, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_24; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
x_5 = x_2;
x_6 = x_24;
goto block_23;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_4, x_11);
lean_dec(x_4);
lean_inc(x_12);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_12);
x_13 = x_5;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_12);
x_13 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_nat_add(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
x_15 = lean_string_get_byte_fast(x_9, x_14);
lean_dec_ref(x_9);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_apply_2(x_1, lean_box(0), x_17);
return x_18;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_del_object(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_21 = lean_box(2);
x_22 = lean_apply_2(x_1, lean_box(0), x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorUInt8OfPure(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_apply_4(x_2, x_3, x_7, lean_box(0), lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0), 4, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_apply_3(x_3, x_8, lean_box(0), x_4);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec_ref(x_6);
x_13 = lean_apply_4(x_2, x_12, x_4, lean_box(0), lean_box(0));
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_apply_2(x_1, lean_box(0), x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_34; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
x_34 = !lean_is_exclusive(x_6);
if (x_34 == 0)
{
x_12 = x_6;
x_13 = x_34;
goto block_33;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1), 6, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_9);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_7);
lean_closure_set(x_14, 4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_11, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_11, x_19);
lean_dec(x_11);
lean_inc(x_20);
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_20);
x_21 = x_12;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_20);
x_21 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_nat_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_23 = lean_string_get_byte_fast(x_17, x_22);
lean_dec_ref(x_17);
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_apply_2(x_4, lean_box(0), x_25);
x_27 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_14, x_26);
return x_27;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_del_object(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_30 = lean_box(2);
x_31 = lean_apply_2(x_4, lean_box(0), x_30);
x_32 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_14, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2), 9, 5);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_2);
lean_closure_set(x_12, 4, x_3);
x_13 = l_WellFounded_opaqueFix_u2083___redArg(x_12, x_6, x_7, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3), 8, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_1, lean_box(0), x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_apply_4(x_2, x_3, x_7, lean_box(0), lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_nat_sub(x_12, x_11);
x_14 = lean_nat_dec_eq(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_nat_add(x_11, x_6);
x_16 = lean_string_utf8_next_fast(x_10, x_15);
x_17 = lean_nat_sub(x_16, x_11);
x_18 = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_9);
lean_closure_set(x_18, 2, x_17);
x_19 = lean_string_utf8_get_fast(x_10, x_15);
lean_dec(x_15);
x_20 = lean_box_uint32(x_19);
x_21 = lean_apply_2(x_3, x_20, x_7);
lean_inc(x_4);
x_22 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_21, x_5);
x_23 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_22, x_18);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_apply_2(x_2, lean_box(0), x_7);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2___boxed), 9, 5);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_5);
lean_closure_set(x_11, 3, x_7);
lean_closure_set(x_11, 4, x_10);
x_12 = l_WellFounded_opaqueFix_u2083___redArg(x_11, x_9, x_4, lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevByteIterator_instForInCharOfMonad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_nat_sub(x_9, x_8);
x_11 = lean_nat_dec_eq(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_nat_add(x_8, x_3);
x_13 = lean_string_utf8_next_fast(x_7, x_12);
x_14 = lean_nat_sub(x_13, x_8);
x_15 = lean_string_utf8_get_fast(x_7, x_12);
lean_dec(x_12);
x_16 = lean_box_uint32(x_15);
x_17 = lean_apply_2(x_2, x_4, x_16);
x_18 = lean_apply_4(x_6, x_14, x_17, lean_box(0), lean_box(0));
return x_18;
}
else
{
lean_dec(x_6);
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_String_Slice_foldl___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_String_Slice_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_WellFounded_opaqueFix_u2083___redArg(x_4, x_5, x_2, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_String_Slice_foldl___redArg___lam__0___boxed), 6, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_WellFounded_opaqueFix_u2083___redArg(x_5, x_6, x_3, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = l_String_Slice_posLE(x_1, x_12);
x_14 = lean_nat_add(x_10, x_13);
x_15 = lean_string_utf8_get_fast(x_9, x_14);
lean_dec(x_14);
x_16 = lean_box_uint32(x_15);
x_17 = lean_apply_2(x_2, x_16, x_4);
x_18 = lean_apply_4(x_6, x_13, x_17, lean_box(0), lean_box(0));
return x_18;
}
else
{
lean_dec(x_6);
lean_dec(x_2);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_String_Slice_foldr___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc_ref(x_3);
x_4 = lean_alloc_closure((void*)(l_String_Slice_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = l_String_Slice_revPositions(x_3);
lean_dec_ref(x_3);
x_6 = l_WellFounded_opaqueFix_u2083___redArg(x_4, x_5, x_2, lean_box(0));
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_Slice_foldr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc_ref(x_4);
x_5 = lean_alloc_closure((void*)(l_String_Slice_foldr___redArg___lam__0___boxed), 6, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_2);
x_6 = l_String_Slice_revPositions(x_4);
lean_dec_ref(x_4);
x_7 = l_WellFounded_opaqueFix_u2083___redArg(x_5, x_6, x_3, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Internal_ofToSliceWithProof___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Internal_ofToSliceWithProof___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Internal_ofToSliceWithProof(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_positionsFrom___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_positionsFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_positionsFrom(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_positions(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_positions___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_positions(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_chars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_chars___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_chars(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_revPositionsFrom___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_revPositionsFrom___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_revPositionsFrom(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_revPositions(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_revPositions___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_revPositions(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_revChars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_revPositions(x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_byteIterator(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_bytes(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_revBytes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_revBytes(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_7, x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_string_utf8_next_fast(x_2, x_7);
x_13 = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1), 4, 3);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_12);
x_14 = lean_string_utf8_get_fast(x_2, x_7);
x_15 = lean_box_uint32(x_14);
x_16 = lean_apply_2(x_4, x_15, x_8);
lean_inc(x_5);
x_17 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_16, x_6);
x_18 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_17, x_13);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_apply_2(x_3, lean_box(0), x_8);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_String_instForInCharOfMonad___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_string_utf8_byte_size(x_3);
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
x_11 = lean_alloc_closure((void*)(l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(x_11, 0, x_8);
x_12 = lean_alloc_closure((void*)(l_String_instForInCharOfMonad___redArg___lam__2___boxed), 10, 6);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_8);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_7);
lean_closure_set(x_12, 5, x_11);
x_13 = l_WellFounded_opaqueFix_u2083___redArg(x_12, x_10, x_4, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_String_instForInCharOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_instForInCharOfMonad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_String_instForInCharOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
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
res = runtime_initialize_Init_Data_String_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_FindPos(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin)
;
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
res = initialize_Init_Data_String_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_FindPos(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_FindPos(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterate(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Iterate(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Iterate(builtin);
}
#ifdef __cplusplus
}
#endif
