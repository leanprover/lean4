// Lean compiler output
// Module: Init.Data.UInt
// Imports: Init.Data.Fin.Basic Init.System.Platform
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
LEAN_EXPORT lean_object* l_instDecidableLt__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instAndOpUInt64;
static lean_object* l_instOrOpUInt16___closed__1;
LEAN_EXPORT size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_instDivUSize;
LEAN_EXPORT lean_object* l_UInt16_modn___boxed(lean_object*, lean_object*);
static lean_object* l_instSubUInt64___closed__1;
static lean_object* l_instSubUInt32___closed__1;
LEAN_EXPORT lean_object* l_UInt8_modn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt16_toUInt32___boxed(lean_object*);
static lean_object* l_instHModUInt32NatUInt32___closed__1;
LEAN_EXPORT size_t l_USize_div(size_t, size_t);
LEAN_EXPORT size_t l_UInt32_toUSize(uint32_t);
static lean_object* l_instShiftRightUInt32___closed__1;
LEAN_EXPORT uint32_t l_UInt16_toUInt32(uint16_t);
static lean_object* l_instAddUInt8___closed__1;
uint32_t lean_uint32_modn(uint32_t, lean_object*);
static lean_object* l_instAddUSize___closed__1;
LEAN_EXPORT uint64_t l_UInt8_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_instComplementUInt8;
static lean_object* l_instDivUInt64___closed__1;
static lean_object* l_instHModUSizeNatUSize___closed__1;
LEAN_EXPORT lean_object* l_UInt64_shiftRight___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_UInt8_toUInt32(uint8_t);
static lean_object* l_instAndOpUInt64___closed__1;
static lean_object* l_instComplementUSize___closed__1;
LEAN_EXPORT uint8_t l_UInt8_decLe(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instAddUInt16;
LEAN_EXPORT lean_object* l_USize_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt64_toUInt32___boxed(lean_object*);
static lean_object* l_instHModUInt8NatUInt8___closed__1;
LEAN_EXPORT uint64_t l_UInt64_add(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_instOfNatUInt16___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Bool_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l_USize_add___boxed(lean_object*, lean_object*);
static lean_object* l_instOrOpUSize___closed__1;
LEAN_EXPORT lean_object* l_instOfNatUInt64___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_toNat___boxed(lean_object*);
static lean_object* l_instXorUInt16___closed__1;
LEAN_EXPORT uint8_t l_UInt8_lor(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt16_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instHModUInt64NatUInt64;
LEAN_EXPORT uint8_t l_UInt32_toUInt8(uint32_t);
LEAN_EXPORT lean_object* l_instDecidableLe__2___boxed(lean_object*, lean_object*);
static lean_object* l_instAndOpUInt16___closed__1;
LEAN_EXPORT size_t l_USize_sub(size_t, size_t);
LEAN_EXPORT size_t l_USize_xor(size_t, size_t);
LEAN_EXPORT lean_object* l_UInt8_lor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instModUInt8;
LEAN_EXPORT uint32_t l_UInt32_land(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_land___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_toUSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instLTUInt8;
LEAN_EXPORT lean_object* l_instAddUSize;
LEAN_EXPORT lean_object* l_instShiftLeftUInt16;
LEAN_EXPORT uint32_t l_UInt32_shiftLeft(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_instSubUInt16;
LEAN_EXPORT uint8_t l_instDecidableLe__2(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_land___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt16_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instModUSize;
LEAN_EXPORT lean_object* l_USize_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_UInt16_land(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt32_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_instOfNatUInt16(lean_object*);
LEAN_EXPORT lean_object* l_USize_land___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instShiftRightUInt32;
LEAN_EXPORT size_t l_USize_complement(size_t);
LEAN_EXPORT lean_object* l_UInt64_land___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_UInt16_toUInt64(uint16_t);
static lean_object* l_instAddUInt32___closed__1;
LEAN_EXPORT lean_object* l_instMulUInt32;
static lean_object* l_instAndOpUInt8___closed__1;
LEAN_EXPORT lean_object* l_UInt16_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instXorUInt8;
LEAN_EXPORT lean_object* l_UInt16_sub___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_USize_shiftRight(size_t, size_t);
LEAN_EXPORT uint8_t l_UInt8_div(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instXorUInt32;
LEAN_EXPORT size_t l_instOfNatUSize(lean_object*);
LEAN_EXPORT lean_object* l_instSubUSize;
static lean_object* l_instModUInt16___closed__1;
LEAN_EXPORT uint8_t l_instDecidableLe__1(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_toUInt32___boxed(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_USize_decLt(size_t, size_t);
static lean_object* l_instXorUSize___closed__1;
static lean_object* l_instAndOpUInt32___closed__1;
LEAN_EXPORT lean_object* l_instSubUInt8;
LEAN_EXPORT lean_object* l_instOrOpUSize;
LEAN_EXPORT uint32_t l_UInt32_shiftRight(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_shiftRight___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt8_decLt(uint8_t, uint8_t);
static lean_object* l_instShiftLeftUInt8___closed__1;
LEAN_EXPORT uint8_t l_UInt8_add(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instXorUInt16;
LEAN_EXPORT uint16_t l_UInt16_add(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_USize_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instShiftRightUSize;
LEAN_EXPORT lean_object* l_instComplementUInt32;
LEAN_EXPORT uint32_t l_UInt32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_instModUInt64;
LEAN_EXPORT lean_object* l_instDecidableLt__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_USize_complement___boxed(lean_object*);
LEAN_EXPORT uint32_t l_UInt32_div(uint32_t, uint32_t);
static lean_object* l_instDivUSize___closed__1;
LEAN_EXPORT lean_object* l_instComplementUSize;
LEAN_EXPORT lean_object* l_instHModUSizeNatUSize;
LEAN_EXPORT lean_object* l_instOfNatUSize___boxed(lean_object*);
static lean_object* l_instComplementUInt8___closed__1;
LEAN_EXPORT lean_object* l_UInt32_ofNat_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instShiftRightUInt16;
LEAN_EXPORT lean_object* l_USize_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt32_toUInt16___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instShiftLeftUSize;
LEAN_EXPORT lean_object* l_USize_shiftRight___boxed(lean_object*, lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_instDivUInt64;
LEAN_EXPORT lean_object* l_UInt64_modn___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_UInt16_xor(uint16_t, uint16_t);
LEAN_EXPORT uint8_t l_instDecidableLt__3(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_instDecidableLt__2(uint16_t, uint16_t);
LEAN_EXPORT uint16_t l_Nat_toUInt16(lean_object*);
LEAN_EXPORT lean_object* l_UInt64_sub___boxed(lean_object*, lean_object*);
static lean_object* l_instDivUInt32___closed__1;
LEAN_EXPORT uint16_t l_UInt16_complement(uint16_t);
LEAN_EXPORT uint16_t l_UInt32_toUInt16(uint32_t);
LEAN_EXPORT uint32_t l_UInt32_complement(uint32_t);
LEAN_EXPORT lean_object* l_instXorUSize;
LEAN_EXPORT uint32_t l_UInt32_sub(uint32_t, uint32_t);
static lean_object* l_instSubUSize___closed__1;
LEAN_EXPORT uint32_t l_UInt32_xor(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt16_xor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_sub___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrOpUInt16;
static lean_object* l_instShiftLeftUInt16___closed__1;
static lean_object* l_instOrOpUInt32___closed__1;
LEAN_EXPORT lean_object* l_UInt32_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_mod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instLTUSize;
LEAN_EXPORT uint32_t l_UInt64_toUInt32(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_toUInt16___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instHModUInt8NatUInt8;
LEAN_EXPORT uint64_t l_instOfNatUInt64(lean_object*);
LEAN_EXPORT lean_object* l_instAndOpUInt32;
static lean_object* l_instSubUInt8___closed__1;
LEAN_EXPORT uint16_t l_UInt8_toUInt16(uint8_t);
LEAN_EXPORT uint8_t l_UInt8_complement(uint8_t);
LEAN_EXPORT lean_object* l_instShiftLeftUInt32;
LEAN_EXPORT lean_object* l_UInt8_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrOpUInt32;
LEAN_EXPORT lean_object* l_instOrOpUInt64;
static lean_object* l_instHModUInt16NatUInt16___closed__1;
static lean_object* l_instXorUInt64___closed__1;
static lean_object* l_instOrOpUInt64___closed__1;
LEAN_EXPORT lean_object* l_UInt32_xor___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt8_shiftRight(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instComplementUInt64;
LEAN_EXPORT lean_object* l_UInt8_complement___boxed(lean_object*);
LEAN_EXPORT uint16_t l_UInt16_shiftLeft(uint16_t, uint16_t);
LEAN_EXPORT uint32_t l_Nat_toUInt32(lean_object*);
static lean_object* l_instAddUInt64___closed__1;
static lean_object* l_instMulUInt8___closed__1;
LEAN_EXPORT lean_object* l_Nat_toUInt16___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt64_decLt(uint64_t, uint64_t);
static lean_object* l_instComplementUInt16___closed__1;
static lean_object* l_instDivUInt16___closed__1;
LEAN_EXPORT uint64_t l_Nat_toUInt64(lean_object*);
LEAN_EXPORT uint8_t l_instOfNatUInt8(lean_object*);
static lean_object* l_instShiftRightUSize___closed__1;
LEAN_EXPORT lean_object* l_UInt64_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_USize_shiftLeft(size_t, size_t);
LEAN_EXPORT lean_object* l_instMulUInt64;
LEAN_EXPORT lean_object* l_instAddUInt32;
LEAN_EXPORT lean_object* l_UInt16_decLt___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
LEAN_EXPORT lean_object* l_instMulUInt16;
LEAN_EXPORT uint16_t l_UInt16_lor(uint16_t, uint16_t);
uint8_t lean_uint8_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_shiftRight___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_ofNat___boxed(lean_object*);
static lean_object* l_instModUSize___closed__1;
LEAN_EXPORT lean_object* l_instShiftRightUInt8;
LEAN_EXPORT lean_object* l_instSubUInt64;
LEAN_EXPORT lean_object* l_USize_shiftLeft___boxed(lean_object*, lean_object*);
static lean_object* l_instShiftLeftUInt64___closed__1;
LEAN_EXPORT lean_object* l_UInt64_xor___boxed(lean_object*, lean_object*);
static lean_object* l_instMulUInt64___closed__1;
LEAN_EXPORT uint8_t l_UInt8_shiftLeft(uint8_t, uint8_t);
LEAN_EXPORT size_t l_USize_mul(size_t, size_t);
LEAN_EXPORT uint64_t l_UInt64_land(uint64_t, uint64_t);
static lean_object* l_instOrOpUInt8___closed__1;
LEAN_EXPORT uint16_t l_UInt16_div(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_instMulUInt8;
LEAN_EXPORT lean_object* l_instLEUInt8;
LEAN_EXPORT uint8_t l_UInt8_land(uint8_t, uint8_t);
LEAN_EXPORT uint16_t l_UInt16_shiftRight(uint16_t, uint16_t);
static lean_object* l_instXorUInt8___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_USize_xor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDivUInt32;
LEAN_EXPORT lean_object* l_UInt64_shiftLeft___boxed(lean_object*, lean_object*);
static lean_object* l_instModUInt32___closed__1;
LEAN_EXPORT lean_object* l_UInt32_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt32_toUInt8___boxed(lean_object*);
LEAN_EXPORT uint64_t l_UInt64_mod(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_instAddUInt8;
LEAN_EXPORT lean_object* l_instMulUSize;
LEAN_EXPORT lean_object* l_UInt16_add___boxed(lean_object*, lean_object*);
static lean_object* l_instComplementUInt32___closed__1;
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT uint64_t l_UInt64_mul(uint64_t, uint64_t);
LEAN_EXPORT size_t l_USize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_UInt8_toUInt16___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_shiftLeft___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_USize_mod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDivUInt16;
LEAN_EXPORT size_t l_USize_mod(size_t, size_t);
LEAN_EXPORT lean_object* l_instModUInt16;
LEAN_EXPORT uint8_t l_UInt8_sub(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_UInt8_xor(uint8_t, uint8_t);
static lean_object* l_instAndOpUSize___closed__1;
LEAN_EXPORT lean_object* l_Nat_toUInt64___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instLEUInt64;
LEAN_EXPORT lean_object* l_instShiftRightUInt64;
LEAN_EXPORT lean_object* l_USize_modn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instLTUInt64;
LEAN_EXPORT lean_object* l_instShiftLeftUInt8;
static lean_object* l_instModUInt64___closed__1;
LEAN_EXPORT uint8_t l_UInt64_toUInt8(uint64_t);
LEAN_EXPORT uint8_t l_USize_decLe(size_t, size_t);
LEAN_EXPORT lean_object* l_UInt64_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instDecidableLt__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt32_mod___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_modn(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_xor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool_toUInt64___boxed(lean_object*);
LEAN_EXPORT uint32_t l_USize_toUInt32(size_t);
LEAN_EXPORT uint16_t l_UInt16_sub(uint16_t, uint16_t);
LEAN_EXPORT uint64_t l_UInt64_shiftLeft(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_instDecidableLe__4(size_t, size_t);
LEAN_EXPORT lean_object* l_UInt64_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_toNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instComplementUInt16;
LEAN_EXPORT lean_object* l_instHModUInt32NatUInt32;
LEAN_EXPORT uint8_t l_instDecidableLt__1(uint8_t, uint8_t);
LEAN_EXPORT uint64_t l_UInt64_lor(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_UInt16_decLt(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt32_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instLTUInt16;
LEAN_EXPORT lean_object* l_instLEUSize;
LEAN_EXPORT lean_object* l_instShiftLeftUInt64;
LEAN_EXPORT uint64_t l_UInt32_toUInt64(uint32_t);
LEAN_EXPORT lean_object* l_instLEUInt16;
uint8_t lean_uint8_modn(uint8_t, lean_object*);
uint16_t lean_uint16_modn(uint16_t, lean_object*);
LEAN_EXPORT lean_object* l_USize_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt32_sub___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instAndOpUInt8;
LEAN_EXPORT uint8_t l_UInt8_mul(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instDivUInt8;
LEAN_EXPORT lean_object* l_USize_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_toUInt8(lean_object*);
LEAN_EXPORT uint8_t l_UInt16_toUInt8(uint16_t);
LEAN_EXPORT uint8_t l_UInt64_decLe(uint64_t, uint64_t);
static lean_object* l_instShiftRightUInt16___closed__1;
LEAN_EXPORT lean_object* l_instAndOpUSize;
LEAN_EXPORT uint32_t l_UInt32_mul(uint32_t, uint32_t);
LEAN_EXPORT size_t l_Nat_toUSize(lean_object*);
LEAN_EXPORT uint32_t l_UInt32_mod(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_complement___boxed(lean_object*);
LEAN_EXPORT size_t l_USize_lor(size_t, size_t);
static lean_object* l_instMulUInt32___closed__1;
static lean_object* l_instMulUSize___closed__1;
LEAN_EXPORT lean_object* l_instDecidableLe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt32_lor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_div___boxed(lean_object*, lean_object*);
static lean_object* l_instHModUInt64NatUInt64___closed__1;
LEAN_EXPORT lean_object* l_instHModUInt16NatUInt16;
LEAN_EXPORT lean_object* l_Nat_toUInt32___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt32_shiftLeft___boxed(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT uint32_t l_instOfNatUInt32(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_complement___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_mod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_USize_toUInt32___boxed(lean_object*);
LEAN_EXPORT uint32_t l_UInt32_lor(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt16_lor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_toUInt64___boxed(lean_object*);
static lean_object* l_instShiftLeftUInt32___closed__1;
LEAN_EXPORT lean_object* l_UInt32_modn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instXorUInt64;
LEAN_EXPORT lean_object* l_UInt8_shiftLeft___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_USize_lor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt16_shiftRight___boxed(lean_object*, lean_object*);
static lean_object* l_instXorUInt32___closed__1;
LEAN_EXPORT lean_object* l_UInt64_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt16_toUInt64___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt64_lor___boxed(lean_object*, lean_object*);
static lean_object* l_instDivUInt8___closed__1;
static lean_object* l_instShiftRightUInt8___closed__1;
LEAN_EXPORT uint16_t l_UInt16_mod(uint16_t, uint16_t);
LEAN_EXPORT uint16_t l_UInt16_mul(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Nat_toUInt8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instModUInt32;
LEAN_EXPORT uint64_t l_UInt64_xor(uint64_t, uint64_t);
LEAN_EXPORT uint16_t l_UInt64_toUInt16(uint64_t);
LEAN_EXPORT lean_object* l_instDecidableLt__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_mod___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_UInt64_sub(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_UInt64_complement(uint64_t);
LEAN_EXPORT lean_object* l_instDecidableLe__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt32_toUSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instDecidableLe__3___boxed(lean_object*, lean_object*);
static lean_object* l_instComplementUInt64___closed__1;
lean_object* lean_uint16_to_nat(uint16_t);
LEAN_EXPORT uint64_t l_UInt64_div(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_UInt64_shiftRight(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt32_toUInt64___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt8_mod(uint8_t, uint8_t);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_instShiftLeftUSize___closed__1;
static lean_object* l_instShiftRightUInt64___closed__1;
static lean_object* l_instSubUInt16___closed__1;
LEAN_EXPORT uint8_t l_UInt16_decLe(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_toUInt8___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableLt__4(size_t, size_t);
LEAN_EXPORT lean_object* l_instSubUInt32;
LEAN_EXPORT lean_object* l_UInt64_toUInt8___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instDecidableLe__3(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_instOrOpUInt8;
LEAN_EXPORT lean_object* l_USize_sub___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOfNatUInt32___boxed(lean_object*);
static lean_object* l_instMulUInt16___closed__1;
LEAN_EXPORT lean_object* l_instAndOpUInt16;
LEAN_EXPORT lean_object* l_instOfNatUInt8___boxed(lean_object*);
static lean_object* l_instAddUInt16___closed__1;
LEAN_EXPORT lean_object* l_instAddUInt64;
lean_object* lean_uint8_to_nat(uint8_t);
LEAN_EXPORT lean_object* l_UInt16_land___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_complement___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_div___boxed(lean_object*, lean_object*);
static lean_object* l_instModUInt8___closed__1;
LEAN_EXPORT lean_object* l_UInt8_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_uint8_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Nat_toUInt8(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_uint8_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Nat_toUInt8(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt8_toNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = lean_uint8_to_nat(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt8_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 + x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 - x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 * x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 / x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? x_3 : x_3 % x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_uint8_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt8_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 & x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 | x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 ^ x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 << x_4 % 8;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 >> x_4 % 8;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instOfNatUInt8(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_uint8_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instOfNatUInt8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_instOfNatUInt8(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_instAddUInt8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_add___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instAddUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_instAddUInt8___closed__1;
return x_1;
}
}
static lean_object* _init_l_instSubUInt8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_sub___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instSubUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_instSubUInt8___closed__1;
return x_1;
}
}
static lean_object* _init_l_instMulUInt8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instMulUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_instMulUInt8___closed__1;
return x_1;
}
}
static lean_object* _init_l_instModUInt8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_mod___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instModUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_instModUInt8___closed__1;
return x_1;
}
}
static lean_object* _init_l_instHModUInt8NatUInt8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_modn___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instHModUInt8NatUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_instHModUInt8NatUInt8___closed__1;
return x_1;
}
}
static lean_object* _init_l_instDivUInt8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_div___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instDivUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_instDivUInt8___closed__1;
return x_1;
}
}
static lean_object* _init_l_instLTUInt8() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instLEUInt8() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt8_complement___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = ~ x_2;
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_instComplementUInt8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_complement___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instComplementUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_instComplementUInt8___closed__1;
return x_1;
}
}
static lean_object* _init_l_instAndOpUInt8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_land___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instAndOpUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_instAndOpUInt8___closed__1;
return x_1;
}
}
static lean_object* _init_l_instOrOpUInt8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_lor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instOrOpUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_instOrOpUInt8___closed__1;
return x_1;
}
}
static lean_object* _init_l_instXorUInt8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_xor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instXorUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_instXorUInt8___closed__1;
return x_1;
}
}
static lean_object* _init_l_instShiftLeftUInt8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_shiftLeft___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instShiftLeftUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_instShiftLeftUInt8___closed__1;
return x_1;
}
}
static lean_object* _init_l_instShiftRightUInt8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt8_shiftRight___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instShiftRightUInt8() {
_start:
{
lean_object* x_1; 
x_1 = l_instShiftRightUInt8___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt8_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 < x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 <= x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instDecidableLt__1(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 < x_2;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableLt__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_instDecidableLt__1(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instDecidableLe__1(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 <= x_2;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableLe__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_instDecidableLe__1(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofNat___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_uint16_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint16_t l_Nat_toUInt16(lean_object* x_1) {
_start:
{
uint16_t x_2; 
x_2 = lean_uint16_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt16___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = l_Nat_toUInt16(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt16_toNat___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = lean_uint16_to_nat(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt16_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 + x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 - x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 * x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 / x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? x_3 : x_3 % x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_uint16_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt16_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 & x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 | x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 ^ x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 << x_4 % 16;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt8___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = ((uint8_t)x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt16___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = ((uint16_t)x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt16_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 >> x_4 % 16;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint16_t l_instOfNatUInt16(lean_object* x_1) {
_start:
{
uint16_t x_2; 
x_2 = lean_uint16_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instOfNatUInt16___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = l_instOfNatUInt16(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_instAddUInt16___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_add___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instAddUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_instAddUInt16___closed__1;
return x_1;
}
}
static lean_object* _init_l_instSubUInt16___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_sub___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instSubUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_instSubUInt16___closed__1;
return x_1;
}
}
static lean_object* _init_l_instMulUInt16___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instMulUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_instMulUInt16___closed__1;
return x_1;
}
}
static lean_object* _init_l_instModUInt16___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_mod___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instModUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_instModUInt16___closed__1;
return x_1;
}
}
static lean_object* _init_l_instHModUInt16NatUInt16___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_modn___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instHModUInt16NatUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_instHModUInt16NatUInt16___closed__1;
return x_1;
}
}
static lean_object* _init_l_instDivUInt16___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_div___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instDivUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_instDivUInt16___closed__1;
return x_1;
}
}
static lean_object* _init_l_instLTUInt16() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instLEUInt16() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt16_complement___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = ~ x_2;
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_instComplementUInt16___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_complement___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instComplementUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_instComplementUInt16___closed__1;
return x_1;
}
}
static lean_object* _init_l_instAndOpUInt16___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_land___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instAndOpUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_instAndOpUInt16___closed__1;
return x_1;
}
}
static lean_object* _init_l_instOrOpUInt16___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_lor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instOrOpUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_instOrOpUInt16___closed__1;
return x_1;
}
}
static lean_object* _init_l_instXorUInt16___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_xor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instXorUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_instXorUInt16___closed__1;
return x_1;
}
}
static lean_object* _init_l_instShiftLeftUInt16___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_shiftLeft___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instShiftLeftUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_instShiftLeftUInt16___closed__1;
return x_1;
}
}
static lean_object* _init_l_instShiftRightUInt16___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt16_shiftRight___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instShiftRightUInt16() {
_start:
{
lean_object* x_1; 
x_1 = l_instShiftRightUInt16___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt16_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 < x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = x_3 <= x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instDecidableLt__2(uint16_t x_1, uint16_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 < x_2;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableLt__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_instDecidableLt__2(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instDecidableLe__2(uint16_t x_1, uint16_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 <= x_2;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableLe__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_instDecidableLe__2(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofNat___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_uint32_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofNat_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_uint32_of_nat(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT uint32_t l_Nat_toUInt32(lean_object* x_1) {
_start:
{
uint32_t x_2; 
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt32___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Nat_toUInt32(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt32_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 + x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 - x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 * x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 / x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? x_3 : x_3 % x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_uint32_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt32_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 & x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 | x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 ^ x_4;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 << x_4 % 32;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = x_3 >> x_4 % 32;
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt8___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = ((uint8_t)x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt16___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = ((uint16_t)x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt32___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = ((uint32_t)x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt32___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = ((uint32_t)x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT uint32_t l_instOfNatUInt32(lean_object* x_1) {
_start:
{
uint32_t x_2; 
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instOfNatUInt32___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_instOfNatUInt32(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
static lean_object* _init_l_instAddUInt32___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_add___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instAddUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_instAddUInt32___closed__1;
return x_1;
}
}
static lean_object* _init_l_instSubUInt32___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_sub___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instSubUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_instSubUInt32___closed__1;
return x_1;
}
}
static lean_object* _init_l_instMulUInt32___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instMulUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_instMulUInt32___closed__1;
return x_1;
}
}
static lean_object* _init_l_instModUInt32___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_mod___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instModUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_instModUInt32___closed__1;
return x_1;
}
}
static lean_object* _init_l_instHModUInt32NatUInt32___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_modn___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instHModUInt32NatUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_instHModUInt32NatUInt32___closed__1;
return x_1;
}
}
static lean_object* _init_l_instDivUInt32___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_div___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instDivUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_instDivUInt32___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt32_complement___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = ~ x_2;
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
static lean_object* _init_l_instComplementUInt32___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_complement___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instComplementUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_instComplementUInt32___closed__1;
return x_1;
}
}
static lean_object* _init_l_instAndOpUInt32___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_land___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instAndOpUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_instAndOpUInt32___closed__1;
return x_1;
}
}
static lean_object* _init_l_instOrOpUInt32___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_lor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instOrOpUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_instOrOpUInt32___closed__1;
return x_1;
}
}
static lean_object* _init_l_instXorUInt32___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_xor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instXorUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_instXorUInt32___closed__1;
return x_1;
}
}
static lean_object* _init_l_instShiftLeftUInt32___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_shiftLeft___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instShiftLeftUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_instShiftLeftUInt32___closed__1;
return x_1;
}
}
static lean_object* _init_l_instShiftRightUInt32___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt32_shiftRight___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instShiftRightUInt32() {
_start:
{
lean_object* x_1; 
x_1 = l_instShiftRightUInt32___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofNat___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_uint64_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Nat_toUInt64(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_toUInt64___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Nat_toUInt64(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt64_toNat___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = lean_uint64_to_nat(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt64_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 + x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 - x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 * x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 / x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? x_3 : x_3 % x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_uint64_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt64_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 & x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 | x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 ^ x_4;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 << x_4 % 64;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 >> x_4 % 64;
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt8___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = ((uint8_t)x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt16___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = ((uint16_t)x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUInt32___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = ((uint32_t)x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUInt64___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = ((uint64_t)x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUInt64___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = ((uint64_t)x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUInt64___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = ((uint64_t)x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_instOfNatUInt64(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instOfNatUInt64___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_instOfNatUInt64(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_instAddUInt64___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_add___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instAddUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_instAddUInt64___closed__1;
return x_1;
}
}
static lean_object* _init_l_instSubUInt64___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_sub___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instSubUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_instSubUInt64___closed__1;
return x_1;
}
}
static lean_object* _init_l_instMulUInt64___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instMulUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_instMulUInt64___closed__1;
return x_1;
}
}
static lean_object* _init_l_instModUInt64___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_mod___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instModUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_instModUInt64___closed__1;
return x_1;
}
}
static lean_object* _init_l_instHModUInt64NatUInt64___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_modn___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instHModUInt64NatUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_instHModUInt64NatUInt64___closed__1;
return x_1;
}
}
static lean_object* _init_l_instDivUInt64___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_div___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instDivUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_instDivUInt64___closed__1;
return x_1;
}
}
static lean_object* _init_l_instLTUInt64() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instLEUInt64() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt64_complement___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = ~ x_2;
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
static lean_object* _init_l_instComplementUInt64___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_complement___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instComplementUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_instComplementUInt64___closed__1;
return x_1;
}
}
static lean_object* _init_l_instAndOpUInt64___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_land___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instAndOpUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_instAndOpUInt64___closed__1;
return x_1;
}
}
static lean_object* _init_l_instOrOpUInt64___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_lor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instOrOpUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_instOrOpUInt64___closed__1;
return x_1;
}
}
static lean_object* _init_l_instXorUInt64___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_xor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instXorUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_instXorUInt64___closed__1;
return x_1;
}
}
static lean_object* _init_l_instShiftLeftUInt64___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_shiftLeft___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instShiftLeftUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_instShiftLeftUInt64___closed__1;
return x_1;
}
}
static lean_object* _init_l_instShiftRightUInt64___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_UInt64_shiftRight___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instShiftRightUInt64() {
_start:
{
lean_object* x_1; 
x_1 = l_instShiftRightUInt64___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Bool_toUInt64___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = (uint64_t)x_2;
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt64_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 < x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = x_3 <= x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instDecidableLt__3(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 < x_2;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableLt__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_instDecidableLt__3(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instDecidableLe__3(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 <= x_2;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableLe__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_instDecidableLe__3(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_ofNat___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_usize_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
LEAN_EXPORT size_t l_Nat_toUSize(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_toUSize___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Nat_toUSize(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_USize_toNat___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_usize_to_nat(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_USize_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 + x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 - x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 * x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? 0 : x_3 / x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_4 == 0 ? x_3 : x_3 % x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_usize_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_usize(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_USize_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 & x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 | x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 ^ x_4;
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 << x_4 % (sizeof(size_t) * 8);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 >> x_4 % (sizeof(size_t) * 8);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUSize___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = x_2;
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt32___boxed(lean_object* x_1) {
_start:
{
size_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = (uint32_t)x_2;
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT size_t l_instOfNatUSize(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instOfNatUSize___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_instOfNatUSize(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l_instAddUSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_add___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instAddUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_instAddUSize___closed__1;
return x_1;
}
}
static lean_object* _init_l_instSubUSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_sub___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instSubUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_instSubUSize___closed__1;
return x_1;
}
}
static lean_object* _init_l_instMulUSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_mul___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instMulUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_instMulUSize___closed__1;
return x_1;
}
}
static lean_object* _init_l_instModUSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_mod___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instModUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_instModUSize___closed__1;
return x_1;
}
}
static lean_object* _init_l_instHModUSizeNatUSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_modn___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instHModUSizeNatUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_instHModUSizeNatUSize___closed__1;
return x_1;
}
}
static lean_object* _init_l_instDivUSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_div___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instDivUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_instDivUSize___closed__1;
return x_1;
}
}
static lean_object* _init_l_instLTUSize() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instLEUSize() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_USize_complement___boxed(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = ~ x_2;
x_4 = lean_box_usize(x_3);
return x_4;
}
}
static lean_object* _init_l_instComplementUSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_complement___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_instComplementUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_instComplementUSize___closed__1;
return x_1;
}
}
static lean_object* _init_l_instAndOpUSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_land___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instAndOpUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_instAndOpUSize___closed__1;
return x_1;
}
}
static lean_object* _init_l_instOrOpUSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_lor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instOrOpUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_instOrOpUSize___closed__1;
return x_1;
}
}
static lean_object* _init_l_instXorUSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_xor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instXorUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_instXorUSize___closed__1;
return x_1;
}
}
static lean_object* _init_l_instShiftLeftUSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_shiftLeft___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instShiftLeftUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_instShiftLeftUSize___closed__1;
return x_1;
}
}
static lean_object* _init_l_instShiftRightUSize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_USize_shiftRight___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_instShiftRightUSize() {
_start:
{
lean_object* x_1; 
x_1 = l_instShiftRightUSize___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_USize_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 < x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = x_3 <= x_4;
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instDecidableLt__4(size_t x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 < x_2;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableLt__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_instDecidableLt__4(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instDecidableLe__4(size_t x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = x_1 <= x_2;
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableLe__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_instDecidableLe__4(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* initialize_Init_Data_Fin_Basic(lean_object*);
lean_object* initialize_Init_System_Platform(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_UInt(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Fin_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instAddUInt8___closed__1 = _init_l_instAddUInt8___closed__1();
lean_mark_persistent(l_instAddUInt8___closed__1);
l_instAddUInt8 = _init_l_instAddUInt8();
lean_mark_persistent(l_instAddUInt8);
l_instSubUInt8___closed__1 = _init_l_instSubUInt8___closed__1();
lean_mark_persistent(l_instSubUInt8___closed__1);
l_instSubUInt8 = _init_l_instSubUInt8();
lean_mark_persistent(l_instSubUInt8);
l_instMulUInt8___closed__1 = _init_l_instMulUInt8___closed__1();
lean_mark_persistent(l_instMulUInt8___closed__1);
l_instMulUInt8 = _init_l_instMulUInt8();
lean_mark_persistent(l_instMulUInt8);
l_instModUInt8___closed__1 = _init_l_instModUInt8___closed__1();
lean_mark_persistent(l_instModUInt8___closed__1);
l_instModUInt8 = _init_l_instModUInt8();
lean_mark_persistent(l_instModUInt8);
l_instHModUInt8NatUInt8___closed__1 = _init_l_instHModUInt8NatUInt8___closed__1();
lean_mark_persistent(l_instHModUInt8NatUInt8___closed__1);
l_instHModUInt8NatUInt8 = _init_l_instHModUInt8NatUInt8();
lean_mark_persistent(l_instHModUInt8NatUInt8);
l_instDivUInt8___closed__1 = _init_l_instDivUInt8___closed__1();
lean_mark_persistent(l_instDivUInt8___closed__1);
l_instDivUInt8 = _init_l_instDivUInt8();
lean_mark_persistent(l_instDivUInt8);
l_instLTUInt8 = _init_l_instLTUInt8();
lean_mark_persistent(l_instLTUInt8);
l_instLEUInt8 = _init_l_instLEUInt8();
lean_mark_persistent(l_instLEUInt8);
l_instComplementUInt8___closed__1 = _init_l_instComplementUInt8___closed__1();
lean_mark_persistent(l_instComplementUInt8___closed__1);
l_instComplementUInt8 = _init_l_instComplementUInt8();
lean_mark_persistent(l_instComplementUInt8);
l_instAndOpUInt8___closed__1 = _init_l_instAndOpUInt8___closed__1();
lean_mark_persistent(l_instAndOpUInt8___closed__1);
l_instAndOpUInt8 = _init_l_instAndOpUInt8();
lean_mark_persistent(l_instAndOpUInt8);
l_instOrOpUInt8___closed__1 = _init_l_instOrOpUInt8___closed__1();
lean_mark_persistent(l_instOrOpUInt8___closed__1);
l_instOrOpUInt8 = _init_l_instOrOpUInt8();
lean_mark_persistent(l_instOrOpUInt8);
l_instXorUInt8___closed__1 = _init_l_instXorUInt8___closed__1();
lean_mark_persistent(l_instXorUInt8___closed__1);
l_instXorUInt8 = _init_l_instXorUInt8();
lean_mark_persistent(l_instXorUInt8);
l_instShiftLeftUInt8___closed__1 = _init_l_instShiftLeftUInt8___closed__1();
lean_mark_persistent(l_instShiftLeftUInt8___closed__1);
l_instShiftLeftUInt8 = _init_l_instShiftLeftUInt8();
lean_mark_persistent(l_instShiftLeftUInt8);
l_instShiftRightUInt8___closed__1 = _init_l_instShiftRightUInt8___closed__1();
lean_mark_persistent(l_instShiftRightUInt8___closed__1);
l_instShiftRightUInt8 = _init_l_instShiftRightUInt8();
lean_mark_persistent(l_instShiftRightUInt8);
l_instAddUInt16___closed__1 = _init_l_instAddUInt16___closed__1();
lean_mark_persistent(l_instAddUInt16___closed__1);
l_instAddUInt16 = _init_l_instAddUInt16();
lean_mark_persistent(l_instAddUInt16);
l_instSubUInt16___closed__1 = _init_l_instSubUInt16___closed__1();
lean_mark_persistent(l_instSubUInt16___closed__1);
l_instSubUInt16 = _init_l_instSubUInt16();
lean_mark_persistent(l_instSubUInt16);
l_instMulUInt16___closed__1 = _init_l_instMulUInt16___closed__1();
lean_mark_persistent(l_instMulUInt16___closed__1);
l_instMulUInt16 = _init_l_instMulUInt16();
lean_mark_persistent(l_instMulUInt16);
l_instModUInt16___closed__1 = _init_l_instModUInt16___closed__1();
lean_mark_persistent(l_instModUInt16___closed__1);
l_instModUInt16 = _init_l_instModUInt16();
lean_mark_persistent(l_instModUInt16);
l_instHModUInt16NatUInt16___closed__1 = _init_l_instHModUInt16NatUInt16___closed__1();
lean_mark_persistent(l_instHModUInt16NatUInt16___closed__1);
l_instHModUInt16NatUInt16 = _init_l_instHModUInt16NatUInt16();
lean_mark_persistent(l_instHModUInt16NatUInt16);
l_instDivUInt16___closed__1 = _init_l_instDivUInt16___closed__1();
lean_mark_persistent(l_instDivUInt16___closed__1);
l_instDivUInt16 = _init_l_instDivUInt16();
lean_mark_persistent(l_instDivUInt16);
l_instLTUInt16 = _init_l_instLTUInt16();
lean_mark_persistent(l_instLTUInt16);
l_instLEUInt16 = _init_l_instLEUInt16();
lean_mark_persistent(l_instLEUInt16);
l_instComplementUInt16___closed__1 = _init_l_instComplementUInt16___closed__1();
lean_mark_persistent(l_instComplementUInt16___closed__1);
l_instComplementUInt16 = _init_l_instComplementUInt16();
lean_mark_persistent(l_instComplementUInt16);
l_instAndOpUInt16___closed__1 = _init_l_instAndOpUInt16___closed__1();
lean_mark_persistent(l_instAndOpUInt16___closed__1);
l_instAndOpUInt16 = _init_l_instAndOpUInt16();
lean_mark_persistent(l_instAndOpUInt16);
l_instOrOpUInt16___closed__1 = _init_l_instOrOpUInt16___closed__1();
lean_mark_persistent(l_instOrOpUInt16___closed__1);
l_instOrOpUInt16 = _init_l_instOrOpUInt16();
lean_mark_persistent(l_instOrOpUInt16);
l_instXorUInt16___closed__1 = _init_l_instXorUInt16___closed__1();
lean_mark_persistent(l_instXorUInt16___closed__1);
l_instXorUInt16 = _init_l_instXorUInt16();
lean_mark_persistent(l_instXorUInt16);
l_instShiftLeftUInt16___closed__1 = _init_l_instShiftLeftUInt16___closed__1();
lean_mark_persistent(l_instShiftLeftUInt16___closed__1);
l_instShiftLeftUInt16 = _init_l_instShiftLeftUInt16();
lean_mark_persistent(l_instShiftLeftUInt16);
l_instShiftRightUInt16___closed__1 = _init_l_instShiftRightUInt16___closed__1();
lean_mark_persistent(l_instShiftRightUInt16___closed__1);
l_instShiftRightUInt16 = _init_l_instShiftRightUInt16();
lean_mark_persistent(l_instShiftRightUInt16);
l_instAddUInt32___closed__1 = _init_l_instAddUInt32___closed__1();
lean_mark_persistent(l_instAddUInt32___closed__1);
l_instAddUInt32 = _init_l_instAddUInt32();
lean_mark_persistent(l_instAddUInt32);
l_instSubUInt32___closed__1 = _init_l_instSubUInt32___closed__1();
lean_mark_persistent(l_instSubUInt32___closed__1);
l_instSubUInt32 = _init_l_instSubUInt32();
lean_mark_persistent(l_instSubUInt32);
l_instMulUInt32___closed__1 = _init_l_instMulUInt32___closed__1();
lean_mark_persistent(l_instMulUInt32___closed__1);
l_instMulUInt32 = _init_l_instMulUInt32();
lean_mark_persistent(l_instMulUInt32);
l_instModUInt32___closed__1 = _init_l_instModUInt32___closed__1();
lean_mark_persistent(l_instModUInt32___closed__1);
l_instModUInt32 = _init_l_instModUInt32();
lean_mark_persistent(l_instModUInt32);
l_instHModUInt32NatUInt32___closed__1 = _init_l_instHModUInt32NatUInt32___closed__1();
lean_mark_persistent(l_instHModUInt32NatUInt32___closed__1);
l_instHModUInt32NatUInt32 = _init_l_instHModUInt32NatUInt32();
lean_mark_persistent(l_instHModUInt32NatUInt32);
l_instDivUInt32___closed__1 = _init_l_instDivUInt32___closed__1();
lean_mark_persistent(l_instDivUInt32___closed__1);
l_instDivUInt32 = _init_l_instDivUInt32();
lean_mark_persistent(l_instDivUInt32);
l_instComplementUInt32___closed__1 = _init_l_instComplementUInt32___closed__1();
lean_mark_persistent(l_instComplementUInt32___closed__1);
l_instComplementUInt32 = _init_l_instComplementUInt32();
lean_mark_persistent(l_instComplementUInt32);
l_instAndOpUInt32___closed__1 = _init_l_instAndOpUInt32___closed__1();
lean_mark_persistent(l_instAndOpUInt32___closed__1);
l_instAndOpUInt32 = _init_l_instAndOpUInt32();
lean_mark_persistent(l_instAndOpUInt32);
l_instOrOpUInt32___closed__1 = _init_l_instOrOpUInt32___closed__1();
lean_mark_persistent(l_instOrOpUInt32___closed__1);
l_instOrOpUInt32 = _init_l_instOrOpUInt32();
lean_mark_persistent(l_instOrOpUInt32);
l_instXorUInt32___closed__1 = _init_l_instXorUInt32___closed__1();
lean_mark_persistent(l_instXorUInt32___closed__1);
l_instXorUInt32 = _init_l_instXorUInt32();
lean_mark_persistent(l_instXorUInt32);
l_instShiftLeftUInt32___closed__1 = _init_l_instShiftLeftUInt32___closed__1();
lean_mark_persistent(l_instShiftLeftUInt32___closed__1);
l_instShiftLeftUInt32 = _init_l_instShiftLeftUInt32();
lean_mark_persistent(l_instShiftLeftUInt32);
l_instShiftRightUInt32___closed__1 = _init_l_instShiftRightUInt32___closed__1();
lean_mark_persistent(l_instShiftRightUInt32___closed__1);
l_instShiftRightUInt32 = _init_l_instShiftRightUInt32();
lean_mark_persistent(l_instShiftRightUInt32);
l_instAddUInt64___closed__1 = _init_l_instAddUInt64___closed__1();
lean_mark_persistent(l_instAddUInt64___closed__1);
l_instAddUInt64 = _init_l_instAddUInt64();
lean_mark_persistent(l_instAddUInt64);
l_instSubUInt64___closed__1 = _init_l_instSubUInt64___closed__1();
lean_mark_persistent(l_instSubUInt64___closed__1);
l_instSubUInt64 = _init_l_instSubUInt64();
lean_mark_persistent(l_instSubUInt64);
l_instMulUInt64___closed__1 = _init_l_instMulUInt64___closed__1();
lean_mark_persistent(l_instMulUInt64___closed__1);
l_instMulUInt64 = _init_l_instMulUInt64();
lean_mark_persistent(l_instMulUInt64);
l_instModUInt64___closed__1 = _init_l_instModUInt64___closed__1();
lean_mark_persistent(l_instModUInt64___closed__1);
l_instModUInt64 = _init_l_instModUInt64();
lean_mark_persistent(l_instModUInt64);
l_instHModUInt64NatUInt64___closed__1 = _init_l_instHModUInt64NatUInt64___closed__1();
lean_mark_persistent(l_instHModUInt64NatUInt64___closed__1);
l_instHModUInt64NatUInt64 = _init_l_instHModUInt64NatUInt64();
lean_mark_persistent(l_instHModUInt64NatUInt64);
l_instDivUInt64___closed__1 = _init_l_instDivUInt64___closed__1();
lean_mark_persistent(l_instDivUInt64___closed__1);
l_instDivUInt64 = _init_l_instDivUInt64();
lean_mark_persistent(l_instDivUInt64);
l_instLTUInt64 = _init_l_instLTUInt64();
lean_mark_persistent(l_instLTUInt64);
l_instLEUInt64 = _init_l_instLEUInt64();
lean_mark_persistent(l_instLEUInt64);
l_instComplementUInt64___closed__1 = _init_l_instComplementUInt64___closed__1();
lean_mark_persistent(l_instComplementUInt64___closed__1);
l_instComplementUInt64 = _init_l_instComplementUInt64();
lean_mark_persistent(l_instComplementUInt64);
l_instAndOpUInt64___closed__1 = _init_l_instAndOpUInt64___closed__1();
lean_mark_persistent(l_instAndOpUInt64___closed__1);
l_instAndOpUInt64 = _init_l_instAndOpUInt64();
lean_mark_persistent(l_instAndOpUInt64);
l_instOrOpUInt64___closed__1 = _init_l_instOrOpUInt64___closed__1();
lean_mark_persistent(l_instOrOpUInt64___closed__1);
l_instOrOpUInt64 = _init_l_instOrOpUInt64();
lean_mark_persistent(l_instOrOpUInt64);
l_instXorUInt64___closed__1 = _init_l_instXorUInt64___closed__1();
lean_mark_persistent(l_instXorUInt64___closed__1);
l_instXorUInt64 = _init_l_instXorUInt64();
lean_mark_persistent(l_instXorUInt64);
l_instShiftLeftUInt64___closed__1 = _init_l_instShiftLeftUInt64___closed__1();
lean_mark_persistent(l_instShiftLeftUInt64___closed__1);
l_instShiftLeftUInt64 = _init_l_instShiftLeftUInt64();
lean_mark_persistent(l_instShiftLeftUInt64);
l_instShiftRightUInt64___closed__1 = _init_l_instShiftRightUInt64___closed__1();
lean_mark_persistent(l_instShiftRightUInt64___closed__1);
l_instShiftRightUInt64 = _init_l_instShiftRightUInt64();
lean_mark_persistent(l_instShiftRightUInt64);
l_instAddUSize___closed__1 = _init_l_instAddUSize___closed__1();
lean_mark_persistent(l_instAddUSize___closed__1);
l_instAddUSize = _init_l_instAddUSize();
lean_mark_persistent(l_instAddUSize);
l_instSubUSize___closed__1 = _init_l_instSubUSize___closed__1();
lean_mark_persistent(l_instSubUSize___closed__1);
l_instSubUSize = _init_l_instSubUSize();
lean_mark_persistent(l_instSubUSize);
l_instMulUSize___closed__1 = _init_l_instMulUSize___closed__1();
lean_mark_persistent(l_instMulUSize___closed__1);
l_instMulUSize = _init_l_instMulUSize();
lean_mark_persistent(l_instMulUSize);
l_instModUSize___closed__1 = _init_l_instModUSize___closed__1();
lean_mark_persistent(l_instModUSize___closed__1);
l_instModUSize = _init_l_instModUSize();
lean_mark_persistent(l_instModUSize);
l_instHModUSizeNatUSize___closed__1 = _init_l_instHModUSizeNatUSize___closed__1();
lean_mark_persistent(l_instHModUSizeNatUSize___closed__1);
l_instHModUSizeNatUSize = _init_l_instHModUSizeNatUSize();
lean_mark_persistent(l_instHModUSizeNatUSize);
l_instDivUSize___closed__1 = _init_l_instDivUSize___closed__1();
lean_mark_persistent(l_instDivUSize___closed__1);
l_instDivUSize = _init_l_instDivUSize();
lean_mark_persistent(l_instDivUSize);
l_instLTUSize = _init_l_instLTUSize();
lean_mark_persistent(l_instLTUSize);
l_instLEUSize = _init_l_instLEUSize();
lean_mark_persistent(l_instLEUSize);
l_instComplementUSize___closed__1 = _init_l_instComplementUSize___closed__1();
lean_mark_persistent(l_instComplementUSize___closed__1);
l_instComplementUSize = _init_l_instComplementUSize();
lean_mark_persistent(l_instComplementUSize);
l_instAndOpUSize___closed__1 = _init_l_instAndOpUSize___closed__1();
lean_mark_persistent(l_instAndOpUSize___closed__1);
l_instAndOpUSize = _init_l_instAndOpUSize();
lean_mark_persistent(l_instAndOpUSize);
l_instOrOpUSize___closed__1 = _init_l_instOrOpUSize___closed__1();
lean_mark_persistent(l_instOrOpUSize___closed__1);
l_instOrOpUSize = _init_l_instOrOpUSize();
lean_mark_persistent(l_instOrOpUSize);
l_instXorUSize___closed__1 = _init_l_instXorUSize___closed__1();
lean_mark_persistent(l_instXorUSize___closed__1);
l_instXorUSize = _init_l_instXorUSize();
lean_mark_persistent(l_instXorUSize);
l_instShiftLeftUSize___closed__1 = _init_l_instShiftLeftUSize___closed__1();
lean_mark_persistent(l_instShiftLeftUSize___closed__1);
l_instShiftLeftUSize = _init_l_instShiftLeftUSize();
lean_mark_persistent(l_instShiftLeftUSize);
l_instShiftRightUSize___closed__1 = _init_l_instShiftRightUSize___closed__1();
lean_mark_persistent(l_instShiftRightUSize___closed__1);
l_instShiftRightUSize = _init_l_instShiftRightUSize();
lean_mark_persistent(l_instShiftRightUSize);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
