// Lean compiler output
// Module: Init.Data.SInt.Basic
// Imports: public import Init.Data.UInt.Basic public import Init.Data.ToString.Extra
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
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint16_t lean_uint16_of_nat_mk(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_UInt32_toUInt64___boxed(lean_object*);
size_t lean_usize_of_nat_mk(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint32_t lean_uint32_of_nat_mk(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_USize_toUInt64___boxed(lean_object*);
lean_object* l_UInt16_toUInt64___boxed(lean_object*);
uint8_t lean_uint8_of_nat_mk(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_uint8_to_nat(uint8_t);
uint64_t lean_uint64_of_nat_mk(lean_object*);
lean_object* l_UInt8_toUInt64___boxed(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int8_size;
LEAN_EXPORT lean_object* l_Int8_toBitVec(uint8_t);
LEAN_EXPORT lean_object* l_Int8_toBitVec___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt8_toInt8(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_toInt8___boxed(lean_object*);
uint8_t lean_int8_of_int(lean_object*);
LEAN_EXPORT lean_object* l_Int8_ofInt___boxed(lean_object*);
uint8_t lean_int8_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Int8_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int_toInt8(lean_object*);
LEAN_EXPORT lean_object* l_Int_toInt8___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Nat_toInt8(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toInt8___boxed(lean_object*);
lean_object* lean_int8_to_int(uint8_t);
LEAN_EXPORT lean_object* l_Int8_toInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int8_toNatClampNeg(uint8_t);
LEAN_EXPORT lean_object* l_Int8_toNatClampNeg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int8_ofBitVec(lean_object*);
LEAN_EXPORT lean_object* l_Int8_ofBitVec___boxed(lean_object*);
uint8_t lean_int8_neg(uint8_t);
LEAN_EXPORT lean_object* l_Int8_neg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringInt8___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToStringInt8___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringInt8___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringInt8___closed__0 = (const lean_object*)&l_instToStringInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringInt8 = (const lean_object*)&l_instToStringInt8___closed__0_value;
static lean_once_cell_t l_instReprInt8___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprInt8___lam__0___closed__0;
LEAN_EXPORT lean_object* l_instReprInt8___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprInt8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprInt8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprInt8___closed__0 = (const lean_object*)&l_instReprInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprInt8 = (const lean_object*)&l_instReprInt8___closed__0_value;
LEAN_EXPORT lean_object* l_instReprAtomInt8;
static const lean_closure_object l_instHashableInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableInt8___closed__0 = (const lean_object*)&l_instHashableInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableInt8 = (const lean_object*)&l_instHashableInt8___closed__0_value;
LEAN_EXPORT uint8_t l_Int8_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Int8_instOfNat___boxed(lean_object*);
static const lean_closure_object l_Int8_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int8_instNeg___closed__0 = (const lean_object*)&l_Int8_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Int8_instNeg = (const lean_object*)&l_Int8_instNeg___closed__0_value;
static lean_once_cell_t l_Int8_maxValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Int8_maxValue___closed__0;
LEAN_EXPORT uint8_t l_Int8_maxValue;
static lean_once_cell_t l_Int8_minValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Int8_minValue___closed__0;
static lean_once_cell_t l_Int8_minValue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Int8_minValue___closed__1;
LEAN_EXPORT uint8_t l_Int8_minValue;
LEAN_EXPORT uint8_t l_Int8_ofIntLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int8_ofIntLE___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int8_ofIntLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int8_ofIntLE___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Int8_ofIntTruncate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int8_ofIntTruncate___closed__0;
static lean_once_cell_t l_Int8_ofIntTruncate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int8_ofIntTruncate___closed__1;
LEAN_EXPORT uint8_t l_Int8_ofIntTruncate(lean_object*);
LEAN_EXPORT lean_object* l_Int8_ofIntTruncate___boxed(lean_object*);
uint8_t lean_int8_add(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_add___boxed(lean_object*, lean_object*);
uint8_t lean_int8_sub(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_sub___boxed(lean_object*, lean_object*);
uint8_t lean_int8_mul(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_mul___boxed(lean_object*, lean_object*);
uint8_t lean_int8_div(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_div___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Int8_pow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Int8_pow___closed__0;
LEAN_EXPORT uint8_t l_Int8_pow(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Int8_pow___boxed(lean_object*, lean_object*);
uint8_t lean_int8_mod(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_mod___boxed(lean_object*, lean_object*);
uint8_t lean_int8_land(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_land___boxed(lean_object*, lean_object*);
uint8_t lean_int8_lor(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_lor___boxed(lean_object*, lean_object*);
uint8_t lean_int8_xor(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_xor___boxed(lean_object*, lean_object*);
uint8_t lean_int8_shift_left(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_shiftLeft___boxed(lean_object*, lean_object*);
uint8_t lean_int8_shift_right(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_shiftRight___boxed(lean_object*, lean_object*);
uint8_t lean_int8_complement(uint8_t);
LEAN_EXPORT lean_object* l_Int8_complement___boxed(lean_object*);
uint8_t lean_int8_abs(uint8_t);
LEAN_EXPORT lean_object* l_Int8_abs___boxed(lean_object*);
uint8_t lean_int8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_decEq___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_instInhabitedInt8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_instInhabitedInt8___closed__0;
LEAN_EXPORT uint8_t l_instInhabitedInt8;
static const lean_closure_object l_instAddInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAddInt8___closed__0 = (const lean_object*)&l_instAddInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instAddInt8 = (const lean_object*)&l_instAddInt8___closed__0_value;
static const lean_closure_object l_instSubInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSubInt8___closed__0 = (const lean_object*)&l_instSubInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instSubInt8 = (const lean_object*)&l_instSubInt8___closed__0_value;
static const lean_closure_object l_instMulInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMulInt8___closed__0 = (const lean_object*)&l_instMulInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instMulInt8 = (const lean_object*)&l_instMulInt8___closed__0_value;
static const lean_closure_object l_instPowInt8Nat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instPowInt8Nat___closed__0 = (const lean_object*)&l_instPowInt8Nat___closed__0_value;
LEAN_EXPORT const lean_object* l_instPowInt8Nat = (const lean_object*)&l_instPowInt8Nat___closed__0_value;
static const lean_closure_object l_instModInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_mod___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instModInt8___closed__0 = (const lean_object*)&l_instModInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instModInt8 = (const lean_object*)&l_instModInt8___closed__0_value;
static const lean_closure_object l_instDivInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instDivInt8___closed__0 = (const lean_object*)&l_instDivInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instDivInt8 = (const lean_object*)&l_instDivInt8___closed__0_value;
LEAN_EXPORT lean_object* l_instLTInt8;
LEAN_EXPORT lean_object* l_instLEInt8;
static const lean_closure_object l_instComplementInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_complement___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instComplementInt8___closed__0 = (const lean_object*)&l_instComplementInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instComplementInt8 = (const lean_object*)&l_instComplementInt8___closed__0_value;
static const lean_closure_object l_instAndOpInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_land___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAndOpInt8___closed__0 = (const lean_object*)&l_instAndOpInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instAndOpInt8 = (const lean_object*)&l_instAndOpInt8___closed__0_value;
static const lean_closure_object l_instOrOpInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_lor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrOpInt8___closed__0 = (const lean_object*)&l_instOrOpInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrOpInt8 = (const lean_object*)&l_instOrOpInt8___closed__0_value;
static const lean_closure_object l_instXorOpInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_xor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instXorOpInt8___closed__0 = (const lean_object*)&l_instXorOpInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instXorOpInt8 = (const lean_object*)&l_instXorOpInt8___closed__0_value;
static const lean_closure_object l_instShiftLeftInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftLeftInt8___closed__0 = (const lean_object*)&l_instShiftLeftInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftLeftInt8 = (const lean_object*)&l_instShiftLeftInt8___closed__0_value;
static const lean_closure_object l_instShiftRightInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftRightInt8___closed__0 = (const lean_object*)&l_instShiftRightInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftRightInt8 = (const lean_object*)&l_instShiftRightInt8___closed__0_value;
LEAN_EXPORT uint8_t l_instDecidableEqInt8(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instDecidableEqInt8___boxed(lean_object*, lean_object*);
uint8_t lean_bool_to_int8(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toInt8___boxed(lean_object*);
uint8_t lean_int8_dec_lt(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_decLt___boxed(lean_object*, lean_object*);
uint8_t lean_int8_dec_le(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instMaxInt8___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instMaxInt8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMaxInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMaxInt8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMaxInt8___closed__0 = (const lean_object*)&l_instMaxInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instMaxInt8 = (const lean_object*)&l_instMaxInt8___closed__0_value;
LEAN_EXPORT uint8_t l_instMinInt8___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instMinInt8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMinInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMinInt8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMinInt8___closed__0 = (const lean_object*)&l_instMinInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instMinInt8 = (const lean_object*)&l_instMinInt8___closed__0_value;
LEAN_EXPORT lean_object* l_Int16_size;
LEAN_EXPORT lean_object* l_Int16_toBitVec(uint16_t);
LEAN_EXPORT lean_object* l_Int16_toBitVec___boxed(lean_object*);
LEAN_EXPORT uint16_t l_UInt16_toInt16(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_toInt16___boxed(lean_object*);
uint16_t lean_int16_of_int(lean_object*);
LEAN_EXPORT lean_object* l_Int16_ofInt___boxed(lean_object*);
uint16_t lean_int16_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Int16_ofNat___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Int_toInt16(lean_object*);
LEAN_EXPORT lean_object* l_Int_toInt16___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Nat_toInt16(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toInt16___boxed(lean_object*);
lean_object* lean_int16_to_int(uint16_t);
LEAN_EXPORT lean_object* l_Int16_toInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg(uint16_t);
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Int16_ofBitVec(lean_object*);
LEAN_EXPORT lean_object* l_Int16_ofBitVec___boxed(lean_object*);
uint8_t lean_int16_to_int8(uint16_t);
LEAN_EXPORT lean_object* l_Int16_toInt8___boxed(lean_object*);
uint16_t lean_int8_to_int16(uint8_t);
LEAN_EXPORT lean_object* l_Int8_toInt16___boxed(lean_object*);
uint16_t lean_int16_neg(uint16_t);
LEAN_EXPORT lean_object* l_Int16_neg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringInt16___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringInt16___closed__0 = (const lean_object*)&l_instToStringInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringInt16 = (const lean_object*)&l_instToStringInt16___closed__0_value;
LEAN_EXPORT lean_object* l_instReprInt16___lam__0(uint16_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprInt16___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprInt16___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprInt16___closed__0 = (const lean_object*)&l_instReprInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprInt16 = (const lean_object*)&l_instReprInt16___closed__0_value;
LEAN_EXPORT lean_object* l_instReprAtomInt16;
static const lean_closure_object l_instHashableInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableInt16___closed__0 = (const lean_object*)&l_instHashableInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableInt16 = (const lean_object*)&l_instHashableInt16___closed__0_value;
LEAN_EXPORT uint16_t l_Int16_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Int16_instOfNat___boxed(lean_object*);
static const lean_closure_object l_Int16_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int16_instNeg___closed__0 = (const lean_object*)&l_Int16_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Int16_instNeg = (const lean_object*)&l_Int16_instNeg___closed__0_value;
static lean_once_cell_t l_Int16_maxValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Int16_maxValue___closed__0;
LEAN_EXPORT uint16_t l_Int16_maxValue;
static lean_once_cell_t l_Int16_minValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Int16_minValue___closed__0;
static lean_once_cell_t l_Int16_minValue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Int16_minValue___closed__1;
LEAN_EXPORT uint16_t l_Int16_minValue;
LEAN_EXPORT uint16_t l_Int16_ofIntLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int16_ofIntLE___redArg___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Int16_ofIntLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int16_ofIntLE___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Int16_ofIntTruncate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int16_ofIntTruncate___closed__0;
static lean_once_cell_t l_Int16_ofIntTruncate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int16_ofIntTruncate___closed__1;
LEAN_EXPORT uint16_t l_Int16_ofIntTruncate(lean_object*);
LEAN_EXPORT lean_object* l_Int16_ofIntTruncate___boxed(lean_object*);
uint16_t lean_int16_add(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_add___boxed(lean_object*, lean_object*);
uint16_t lean_int16_sub(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_sub___boxed(lean_object*, lean_object*);
uint16_t lean_int16_mul(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_mul___boxed(lean_object*, lean_object*);
uint16_t lean_int16_div(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_div___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Int16_pow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Int16_pow___closed__0;
LEAN_EXPORT uint16_t l_Int16_pow(uint16_t, lean_object*);
LEAN_EXPORT lean_object* l_Int16_pow___boxed(lean_object*, lean_object*);
uint16_t lean_int16_mod(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_mod___boxed(lean_object*, lean_object*);
uint16_t lean_int16_land(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_land___boxed(lean_object*, lean_object*);
uint16_t lean_int16_lor(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_lor___boxed(lean_object*, lean_object*);
uint16_t lean_int16_xor(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_xor___boxed(lean_object*, lean_object*);
uint16_t lean_int16_shift_left(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_shiftLeft___boxed(lean_object*, lean_object*);
uint16_t lean_int16_shift_right(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_shiftRight___boxed(lean_object*, lean_object*);
uint16_t lean_int16_complement(uint16_t);
LEAN_EXPORT lean_object* l_Int16_complement___boxed(lean_object*);
uint16_t lean_int16_abs(uint16_t);
LEAN_EXPORT lean_object* l_Int16_abs___boxed(lean_object*);
uint8_t lean_int16_dec_eq(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_decEq___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_instInhabitedInt16___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_instInhabitedInt16___closed__0;
LEAN_EXPORT uint16_t l_instInhabitedInt16;
static const lean_closure_object l_instAddInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAddInt16___closed__0 = (const lean_object*)&l_instAddInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instAddInt16 = (const lean_object*)&l_instAddInt16___closed__0_value;
static const lean_closure_object l_instSubInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSubInt16___closed__0 = (const lean_object*)&l_instSubInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instSubInt16 = (const lean_object*)&l_instSubInt16___closed__0_value;
static const lean_closure_object l_instMulInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMulInt16___closed__0 = (const lean_object*)&l_instMulInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instMulInt16 = (const lean_object*)&l_instMulInt16___closed__0_value;
static const lean_closure_object l_instPowInt16Nat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instPowInt16Nat___closed__0 = (const lean_object*)&l_instPowInt16Nat___closed__0_value;
LEAN_EXPORT const lean_object* l_instPowInt16Nat = (const lean_object*)&l_instPowInt16Nat___closed__0_value;
static const lean_closure_object l_instModInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_mod___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instModInt16___closed__0 = (const lean_object*)&l_instModInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instModInt16 = (const lean_object*)&l_instModInt16___closed__0_value;
static const lean_closure_object l_instDivInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instDivInt16___closed__0 = (const lean_object*)&l_instDivInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instDivInt16 = (const lean_object*)&l_instDivInt16___closed__0_value;
LEAN_EXPORT lean_object* l_instLTInt16;
LEAN_EXPORT lean_object* l_instLEInt16;
static const lean_closure_object l_instComplementInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_complement___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instComplementInt16___closed__0 = (const lean_object*)&l_instComplementInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instComplementInt16 = (const lean_object*)&l_instComplementInt16___closed__0_value;
static const lean_closure_object l_instAndOpInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_land___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAndOpInt16___closed__0 = (const lean_object*)&l_instAndOpInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instAndOpInt16 = (const lean_object*)&l_instAndOpInt16___closed__0_value;
static const lean_closure_object l_instOrOpInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_lor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrOpInt16___closed__0 = (const lean_object*)&l_instOrOpInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrOpInt16 = (const lean_object*)&l_instOrOpInt16___closed__0_value;
static const lean_closure_object l_instXorOpInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_xor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instXorOpInt16___closed__0 = (const lean_object*)&l_instXorOpInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instXorOpInt16 = (const lean_object*)&l_instXorOpInt16___closed__0_value;
static const lean_closure_object l_instShiftLeftInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftLeftInt16___closed__0 = (const lean_object*)&l_instShiftLeftInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftLeftInt16 = (const lean_object*)&l_instShiftLeftInt16___closed__0_value;
static const lean_closure_object l_instShiftRightInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftRightInt16___closed__0 = (const lean_object*)&l_instShiftRightInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftRightInt16 = (const lean_object*)&l_instShiftRightInt16___closed__0_value;
LEAN_EXPORT uint8_t l_instDecidableEqInt16(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_instDecidableEqInt16___boxed(lean_object*, lean_object*);
uint16_t lean_bool_to_int16(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toInt16___boxed(lean_object*);
uint8_t lean_int16_dec_lt(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_decLt___boxed(lean_object*, lean_object*);
uint8_t lean_int16_dec_le(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_instMaxInt16___lam__0(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_instMaxInt16___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMaxInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMaxInt16___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMaxInt16___closed__0 = (const lean_object*)&l_instMaxInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instMaxInt16 = (const lean_object*)&l_instMaxInt16___closed__0_value;
LEAN_EXPORT uint16_t l_instMinInt16___lam__0(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_instMinInt16___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMinInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMinInt16___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMinInt16___closed__0 = (const lean_object*)&l_instMinInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instMinInt16 = (const lean_object*)&l_instMinInt16___closed__0_value;
LEAN_EXPORT lean_object* l_Int32_size;
LEAN_EXPORT lean_object* l_Int32_toBitVec(uint32_t);
LEAN_EXPORT lean_object* l_Int32_toBitVec___boxed(lean_object*);
LEAN_EXPORT uint32_t l_UInt32_toInt32(uint32_t);
LEAN_EXPORT lean_object* l_UInt32_toInt32___boxed(lean_object*);
uint32_t lean_int32_of_int(lean_object*);
LEAN_EXPORT lean_object* l_Int32_ofInt___boxed(lean_object*);
uint32_t lean_int32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Int32_ofNat___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Int_toInt32(lean_object*);
LEAN_EXPORT lean_object* l_Int_toInt32___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Nat_toInt32(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toInt32___boxed(lean_object*);
lean_object* lean_int32_to_int(uint32_t);
LEAN_EXPORT lean_object* l_Int32_toInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg(uint32_t);
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Int32_ofBitVec(lean_object*);
LEAN_EXPORT lean_object* l_Int32_ofBitVec___boxed(lean_object*);
uint8_t lean_int32_to_int8(uint32_t);
LEAN_EXPORT lean_object* l_Int32_toInt8___boxed(lean_object*);
uint16_t lean_int32_to_int16(uint32_t);
LEAN_EXPORT lean_object* l_Int32_toInt16___boxed(lean_object*);
uint32_t lean_int8_to_int32(uint8_t);
LEAN_EXPORT lean_object* l_Int8_toInt32___boxed(lean_object*);
uint32_t lean_int16_to_int32(uint16_t);
LEAN_EXPORT lean_object* l_Int16_toInt32___boxed(lean_object*);
uint32_t lean_int32_neg(uint32_t);
LEAN_EXPORT lean_object* l_Int32_neg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringInt32___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringInt32___closed__0 = (const lean_object*)&l_instToStringInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringInt32 = (const lean_object*)&l_instToStringInt32___closed__0_value;
LEAN_EXPORT lean_object* l_instReprInt32___lam__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprInt32___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprInt32___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprInt32___closed__0 = (const lean_object*)&l_instReprInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprInt32 = (const lean_object*)&l_instReprInt32___closed__0_value;
LEAN_EXPORT lean_object* l_instReprAtomInt32;
static const lean_closure_object l_instHashableInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableInt32___closed__0 = (const lean_object*)&l_instHashableInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableInt32 = (const lean_object*)&l_instHashableInt32___closed__0_value;
LEAN_EXPORT uint32_t l_Int32_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Int32_instOfNat___boxed(lean_object*);
static const lean_closure_object l_Int32_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int32_instNeg___closed__0 = (const lean_object*)&l_Int32_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Int32_instNeg = (const lean_object*)&l_Int32_instNeg___closed__0_value;
static lean_once_cell_t l_Int32_maxValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Int32_maxValue___closed__0;
LEAN_EXPORT uint32_t l_Int32_maxValue;
static lean_once_cell_t l_Int32_minValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Int32_minValue___closed__0;
static lean_once_cell_t l_Int32_minValue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Int32_minValue___closed__1;
LEAN_EXPORT uint32_t l_Int32_minValue;
LEAN_EXPORT uint32_t l_Int32_ofIntLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int32_ofIntLE___redArg___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Int32_ofIntLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int32_ofIntLE___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Int32_ofIntTruncate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int32_ofIntTruncate___closed__0;
static lean_once_cell_t l_Int32_ofIntTruncate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int32_ofIntTruncate___closed__1;
LEAN_EXPORT uint32_t l_Int32_ofIntTruncate(lean_object*);
LEAN_EXPORT lean_object* l_Int32_ofIntTruncate___boxed(lean_object*);
uint32_t lean_int32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_add___boxed(lean_object*, lean_object*);
uint32_t lean_int32_sub(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_sub___boxed(lean_object*, lean_object*);
uint32_t lean_int32_mul(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_mul___boxed(lean_object*, lean_object*);
uint32_t lean_int32_div(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_div___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Int32_pow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Int32_pow___closed__0;
LEAN_EXPORT uint32_t l_Int32_pow(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Int32_pow___boxed(lean_object*, lean_object*);
uint32_t lean_int32_mod(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_mod___boxed(lean_object*, lean_object*);
uint32_t lean_int32_land(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_land___boxed(lean_object*, lean_object*);
uint32_t lean_int32_lor(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_lor___boxed(lean_object*, lean_object*);
uint32_t lean_int32_xor(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_xor___boxed(lean_object*, lean_object*);
uint32_t lean_int32_shift_left(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_shiftLeft___boxed(lean_object*, lean_object*);
uint32_t lean_int32_shift_right(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_shiftRight___boxed(lean_object*, lean_object*);
uint32_t lean_int32_complement(uint32_t);
LEAN_EXPORT lean_object* l_Int32_complement___boxed(lean_object*);
uint32_t lean_int32_abs(uint32_t);
LEAN_EXPORT lean_object* l_Int32_abs___boxed(lean_object*);
uint8_t lean_int32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_decEq___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_instInhabitedInt32___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_instInhabitedInt32___closed__0;
LEAN_EXPORT uint32_t l_instInhabitedInt32;
static const lean_closure_object l_instAddInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAddInt32___closed__0 = (const lean_object*)&l_instAddInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instAddInt32 = (const lean_object*)&l_instAddInt32___closed__0_value;
static const lean_closure_object l_instSubInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSubInt32___closed__0 = (const lean_object*)&l_instSubInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instSubInt32 = (const lean_object*)&l_instSubInt32___closed__0_value;
static const lean_closure_object l_instMulInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMulInt32___closed__0 = (const lean_object*)&l_instMulInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instMulInt32 = (const lean_object*)&l_instMulInt32___closed__0_value;
static const lean_closure_object l_instPowInt32Nat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instPowInt32Nat___closed__0 = (const lean_object*)&l_instPowInt32Nat___closed__0_value;
LEAN_EXPORT const lean_object* l_instPowInt32Nat = (const lean_object*)&l_instPowInt32Nat___closed__0_value;
static const lean_closure_object l_instModInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_mod___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instModInt32___closed__0 = (const lean_object*)&l_instModInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instModInt32 = (const lean_object*)&l_instModInt32___closed__0_value;
static const lean_closure_object l_instDivInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instDivInt32___closed__0 = (const lean_object*)&l_instDivInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instDivInt32 = (const lean_object*)&l_instDivInt32___closed__0_value;
LEAN_EXPORT lean_object* l_instLTInt32;
LEAN_EXPORT lean_object* l_instLEInt32;
static const lean_closure_object l_instComplementInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_complement___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instComplementInt32___closed__0 = (const lean_object*)&l_instComplementInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instComplementInt32 = (const lean_object*)&l_instComplementInt32___closed__0_value;
static const lean_closure_object l_instAndOpInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_land___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAndOpInt32___closed__0 = (const lean_object*)&l_instAndOpInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instAndOpInt32 = (const lean_object*)&l_instAndOpInt32___closed__0_value;
static const lean_closure_object l_instOrOpInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_lor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrOpInt32___closed__0 = (const lean_object*)&l_instOrOpInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrOpInt32 = (const lean_object*)&l_instOrOpInt32___closed__0_value;
static const lean_closure_object l_instXorOpInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_xor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instXorOpInt32___closed__0 = (const lean_object*)&l_instXorOpInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instXorOpInt32 = (const lean_object*)&l_instXorOpInt32___closed__0_value;
static const lean_closure_object l_instShiftLeftInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftLeftInt32___closed__0 = (const lean_object*)&l_instShiftLeftInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftLeftInt32 = (const lean_object*)&l_instShiftLeftInt32___closed__0_value;
static const lean_closure_object l_instShiftRightInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftRightInt32___closed__0 = (const lean_object*)&l_instShiftRightInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftRightInt32 = (const lean_object*)&l_instShiftRightInt32___closed__0_value;
LEAN_EXPORT uint8_t l_instDecidableEqInt32(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_instDecidableEqInt32___boxed(lean_object*, lean_object*);
uint32_t lean_bool_to_int32(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toInt32___boxed(lean_object*);
uint8_t lean_int32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_decLt___boxed(lean_object*, lean_object*);
uint8_t lean_int32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_instMaxInt32___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_instMaxInt32___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMaxInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMaxInt32___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMaxInt32___closed__0 = (const lean_object*)&l_instMaxInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instMaxInt32 = (const lean_object*)&l_instMaxInt32___closed__0_value;
LEAN_EXPORT uint32_t l_instMinInt32___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_instMinInt32___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMinInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMinInt32___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMinInt32___closed__0 = (const lean_object*)&l_instMinInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instMinInt32 = (const lean_object*)&l_instMinInt32___closed__0_value;
static lean_once_cell_t l_Int64_size___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int64_size___closed__0;
LEAN_EXPORT lean_object* l_Int64_size;
LEAN_EXPORT lean_object* l_Int64_toBitVec(uint64_t);
LEAN_EXPORT lean_object* l_Int64_toBitVec___boxed(lean_object*);
LEAN_EXPORT uint64_t l_UInt64_toInt64(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_toInt64___boxed(lean_object*);
uint64_t lean_int64_of_int(lean_object*);
LEAN_EXPORT lean_object* l_Int64_ofInt___boxed(lean_object*);
uint64_t lean_int64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Int64_ofNat___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Int_toInt64(lean_object*);
LEAN_EXPORT lean_object* l_Int_toInt64___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Nat_toInt64(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toInt64___boxed(lean_object*);
lean_object* lean_int64_to_int_sint(uint64_t);
LEAN_EXPORT lean_object* l_Int64_toInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg(uint64_t);
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Int64_ofBitVec(lean_object*);
LEAN_EXPORT lean_object* l_Int64_ofBitVec___boxed(lean_object*);
uint8_t lean_int64_to_int8(uint64_t);
LEAN_EXPORT lean_object* l_Int64_toInt8___boxed(lean_object*);
uint16_t lean_int64_to_int16(uint64_t);
LEAN_EXPORT lean_object* l_Int64_toInt16___boxed(lean_object*);
uint32_t lean_int64_to_int32(uint64_t);
LEAN_EXPORT lean_object* l_Int64_toInt32___boxed(lean_object*);
uint64_t lean_int8_to_int64(uint8_t);
LEAN_EXPORT lean_object* l_Int8_toInt64___boxed(lean_object*);
uint64_t lean_int16_to_int64(uint16_t);
LEAN_EXPORT lean_object* l_Int16_toInt64___boxed(lean_object*);
uint64_t lean_int32_to_int64(uint32_t);
LEAN_EXPORT lean_object* l_Int32_toInt64___boxed(lean_object*);
uint64_t lean_int64_neg(uint64_t);
LEAN_EXPORT lean_object* l_Int64_neg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringInt64___closed__0 = (const lean_object*)&l_instToStringInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringInt64 = (const lean_object*)&l_instToStringInt64___closed__0_value;
LEAN_EXPORT lean_object* l_instReprInt64___lam__0(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprInt64___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprInt64___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprInt64___closed__0 = (const lean_object*)&l_instReprInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprInt64 = (const lean_object*)&l_instReprInt64___closed__0_value;
LEAN_EXPORT lean_object* l_instReprAtomInt64;
LEAN_EXPORT uint64_t l_instHashableInt64___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_instHashableInt64___lam__0___boxed(lean_object*);
static const lean_closure_object l_instHashableInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableInt64___closed__0 = (const lean_object*)&l_instHashableInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableInt64 = (const lean_object*)&l_instHashableInt64___closed__0_value;
LEAN_EXPORT uint64_t l_Int64_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Int64_instOfNat___boxed(lean_object*);
static const lean_closure_object l_Int64_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int64_instNeg___closed__0 = (const lean_object*)&l_Int64_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Int64_instNeg = (const lean_object*)&l_Int64_instNeg___closed__0_value;
static lean_once_cell_t l_Int64_maxValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Int64_maxValue___closed__0;
LEAN_EXPORT uint64_t l_Int64_maxValue;
static lean_once_cell_t l_Int64_minValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int64_minValue___closed__0;
static lean_once_cell_t l_Int64_minValue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Int64_minValue___closed__1;
static lean_once_cell_t l_Int64_minValue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Int64_minValue___closed__2;
LEAN_EXPORT uint64_t l_Int64_minValue;
LEAN_EXPORT uint64_t l_Int64_ofIntLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int64_ofIntLE___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Int64_ofIntLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int64_ofIntLE___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Int64_ofIntTruncate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int64_ofIntTruncate___closed__0;
static lean_once_cell_t l_Int64_ofIntTruncate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int64_ofIntTruncate___closed__1;
LEAN_EXPORT uint64_t l_Int64_ofIntTruncate(lean_object*);
LEAN_EXPORT lean_object* l_Int64_ofIntTruncate___boxed(lean_object*);
uint64_t lean_int64_add(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_add___boxed(lean_object*, lean_object*);
uint64_t lean_int64_sub(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_sub___boxed(lean_object*, lean_object*);
uint64_t lean_int64_mul(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_mul___boxed(lean_object*, lean_object*);
uint64_t lean_int64_div(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_div___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Int64_pow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Int64_pow___closed__0;
LEAN_EXPORT uint64_t l_Int64_pow(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Int64_pow___boxed(lean_object*, lean_object*);
uint64_t lean_int64_mod(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_mod___boxed(lean_object*, lean_object*);
uint64_t lean_int64_land(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_land___boxed(lean_object*, lean_object*);
uint64_t lean_int64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_lor___boxed(lean_object*, lean_object*);
uint64_t lean_int64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_xor___boxed(lean_object*, lean_object*);
uint64_t lean_int64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_shiftLeft___boxed(lean_object*, lean_object*);
uint64_t lean_int64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_shiftRight___boxed(lean_object*, lean_object*);
uint64_t lean_int64_complement(uint64_t);
LEAN_EXPORT lean_object* l_Int64_complement___boxed(lean_object*);
uint64_t lean_int64_abs(uint64_t);
LEAN_EXPORT lean_object* l_Int64_abs___boxed(lean_object*);
uint8_t lean_int64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_decEq___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_instInhabitedInt64___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_instInhabitedInt64___closed__0;
LEAN_EXPORT uint64_t l_instInhabitedInt64;
static const lean_closure_object l_instAddInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAddInt64___closed__0 = (const lean_object*)&l_instAddInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instAddInt64 = (const lean_object*)&l_instAddInt64___closed__0_value;
static const lean_closure_object l_instSubInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSubInt64___closed__0 = (const lean_object*)&l_instSubInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instSubInt64 = (const lean_object*)&l_instSubInt64___closed__0_value;
static const lean_closure_object l_instMulInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMulInt64___closed__0 = (const lean_object*)&l_instMulInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instMulInt64 = (const lean_object*)&l_instMulInt64___closed__0_value;
static const lean_closure_object l_instPowInt64Nat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instPowInt64Nat___closed__0 = (const lean_object*)&l_instPowInt64Nat___closed__0_value;
LEAN_EXPORT const lean_object* l_instPowInt64Nat = (const lean_object*)&l_instPowInt64Nat___closed__0_value;
static const lean_closure_object l_instModInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_mod___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instModInt64___closed__0 = (const lean_object*)&l_instModInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instModInt64 = (const lean_object*)&l_instModInt64___closed__0_value;
static const lean_closure_object l_instDivInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instDivInt64___closed__0 = (const lean_object*)&l_instDivInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instDivInt64 = (const lean_object*)&l_instDivInt64___closed__0_value;
LEAN_EXPORT lean_object* l_instLTInt64;
LEAN_EXPORT lean_object* l_instLEInt64;
static const lean_closure_object l_instComplementInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_complement___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instComplementInt64___closed__0 = (const lean_object*)&l_instComplementInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instComplementInt64 = (const lean_object*)&l_instComplementInt64___closed__0_value;
static const lean_closure_object l_instAndOpInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_land___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAndOpInt64___closed__0 = (const lean_object*)&l_instAndOpInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instAndOpInt64 = (const lean_object*)&l_instAndOpInt64___closed__0_value;
static const lean_closure_object l_instOrOpInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_lor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrOpInt64___closed__0 = (const lean_object*)&l_instOrOpInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrOpInt64 = (const lean_object*)&l_instOrOpInt64___closed__0_value;
static const lean_closure_object l_instXorOpInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_xor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instXorOpInt64___closed__0 = (const lean_object*)&l_instXorOpInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instXorOpInt64 = (const lean_object*)&l_instXorOpInt64___closed__0_value;
static const lean_closure_object l_instShiftLeftInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftLeftInt64___closed__0 = (const lean_object*)&l_instShiftLeftInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftLeftInt64 = (const lean_object*)&l_instShiftLeftInt64___closed__0_value;
static const lean_closure_object l_instShiftRightInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftRightInt64___closed__0 = (const lean_object*)&l_instShiftRightInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftRightInt64 = (const lean_object*)&l_instShiftRightInt64___closed__0_value;
LEAN_EXPORT uint8_t l_instDecidableEqInt64(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_instDecidableEqInt64___boxed(lean_object*, lean_object*);
uint64_t lean_bool_to_int64(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toInt64___boxed(lean_object*);
uint8_t lean_int64_dec_lt(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_decLt___boxed(lean_object*, lean_object*);
uint8_t lean_int64_dec_le(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instMaxInt64___lam__0(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_instMaxInt64___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMaxInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMaxInt64___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMaxInt64___closed__0 = (const lean_object*)&l_instMaxInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instMaxInt64 = (const lean_object*)&l_instMaxInt64___closed__0_value;
LEAN_EXPORT uint64_t l_instMinInt64___lam__0(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_instMinInt64___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMinInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMinInt64___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMinInt64___closed__0 = (const lean_object*)&l_instMinInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instMinInt64 = (const lean_object*)&l_instMinInt64___closed__0_value;
static lean_once_cell_t l_ISize_size___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ISize_size___closed__0;
LEAN_EXPORT lean_object* l_ISize_size;
LEAN_EXPORT lean_object* l_ISize_toBitVec(size_t);
LEAN_EXPORT lean_object* l_ISize_toBitVec___boxed(lean_object*);
LEAN_EXPORT size_t l_USize_toISize(size_t);
LEAN_EXPORT lean_object* l_USize_toISize___boxed(lean_object*);
size_t lean_isize_of_int(lean_object*);
LEAN_EXPORT lean_object* l_ISize_ofInt___boxed(lean_object*);
size_t lean_isize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_ISize_ofNat___boxed(lean_object*);
LEAN_EXPORT size_t l_Int_toISize(lean_object*);
LEAN_EXPORT lean_object* l_Int_toISize___boxed(lean_object*);
LEAN_EXPORT size_t l_Nat_toISize(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toISize___boxed(lean_object*);
lean_object* lean_isize_to_int(size_t);
LEAN_EXPORT lean_object* l_ISize_toInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg(size_t);
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg___boxed(lean_object*);
LEAN_EXPORT size_t l_ISize_ofBitVec(lean_object*);
LEAN_EXPORT lean_object* l_ISize_ofBitVec___boxed(lean_object*);
uint8_t lean_isize_to_int8(size_t);
LEAN_EXPORT lean_object* l_ISize_toInt8___boxed(lean_object*);
uint16_t lean_isize_to_int16(size_t);
LEAN_EXPORT lean_object* l_ISize_toInt16___boxed(lean_object*);
uint32_t lean_isize_to_int32(size_t);
LEAN_EXPORT lean_object* l_ISize_toInt32___boxed(lean_object*);
uint64_t lean_isize_to_int64(size_t);
LEAN_EXPORT lean_object* l_ISize_toInt64___boxed(lean_object*);
size_t lean_int8_to_isize(uint8_t);
LEAN_EXPORT lean_object* l_Int8_toISize___boxed(lean_object*);
size_t lean_int16_to_isize(uint16_t);
LEAN_EXPORT lean_object* l_Int16_toISize___boxed(lean_object*);
size_t lean_int32_to_isize(uint32_t);
LEAN_EXPORT lean_object* l_Int32_toISize___boxed(lean_object*);
size_t lean_int64_to_isize(uint64_t);
LEAN_EXPORT lean_object* l_Int64_toISize___boxed(lean_object*);
size_t lean_isize_neg(size_t);
LEAN_EXPORT lean_object* l_ISize_neg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instToStringISize___lam__0(size_t);
LEAN_EXPORT lean_object* l_instToStringISize___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringISize___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringISize___closed__0 = (const lean_object*)&l_instToStringISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringISize = (const lean_object*)&l_instToStringISize___closed__0_value;
LEAN_EXPORT lean_object* l_instReprISize___lam__0(size_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprISize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprISize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprISize___closed__0 = (const lean_object*)&l_instReprISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprISize = (const lean_object*)&l_instReprISize___closed__0_value;
LEAN_EXPORT lean_object* l_instReprAtomISize;
static const lean_closure_object l_instHashableISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableISize___closed__0 = (const lean_object*)&l_instHashableISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableISize = (const lean_object*)&l_instHashableISize___closed__0_value;
LEAN_EXPORT size_t l_ISize_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_ISize_instOfNat___boxed(lean_object*);
static const lean_closure_object l_ISize_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ISize_instNeg___closed__0 = (const lean_object*)&l_ISize_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_ISize_instNeg = (const lean_object*)&l_ISize_instNeg___closed__0_value;
static lean_once_cell_t l_ISize_maxValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ISize_maxValue___closed__0;
static lean_once_cell_t l_ISize_maxValue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ISize_maxValue___closed__1;
static lean_once_cell_t l_ISize_maxValue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ISize_maxValue___closed__2;
static lean_once_cell_t l_ISize_maxValue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ISize_maxValue___closed__3;
static lean_once_cell_t l_ISize_maxValue___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ISize_maxValue___closed__4;
static lean_once_cell_t l_ISize_maxValue___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_ISize_maxValue___closed__5;
LEAN_EXPORT size_t l_ISize_maxValue;
static lean_once_cell_t l_ISize_minValue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ISize_minValue___closed__0;
static lean_once_cell_t l_ISize_minValue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_ISize_minValue___closed__1;
LEAN_EXPORT size_t l_ISize_minValue;
LEAN_EXPORT size_t l_ISize_ofIntLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ISize_ofIntLE___redArg___boxed(lean_object*);
LEAN_EXPORT size_t l_ISize_ofIntLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ISize_ofIntLE___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_ISize_ofIntTruncate___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ISize_ofIntTruncate___closed__0;
static lean_once_cell_t l_ISize_ofIntTruncate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ISize_ofIntTruncate___closed__1;
LEAN_EXPORT size_t l_ISize_ofIntTruncate(lean_object*);
LEAN_EXPORT lean_object* l_ISize_ofIntTruncate___boxed(lean_object*);
size_t lean_isize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_add___boxed(lean_object*, lean_object*);
size_t lean_isize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_sub___boxed(lean_object*, lean_object*);
size_t lean_isize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_mul___boxed(lean_object*, lean_object*);
size_t lean_isize_div(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_div___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_ISize_pow___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_ISize_pow___closed__0;
LEAN_EXPORT size_t l_ISize_pow(size_t, lean_object*);
LEAN_EXPORT lean_object* l_ISize_pow___boxed(lean_object*, lean_object*);
size_t lean_isize_mod(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_mod___boxed(lean_object*, lean_object*);
size_t lean_isize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_land___boxed(lean_object*, lean_object*);
size_t lean_isize_lor(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_lor___boxed(lean_object*, lean_object*);
size_t lean_isize_xor(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_xor___boxed(lean_object*, lean_object*);
size_t lean_isize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_shiftLeft___boxed(lean_object*, lean_object*);
size_t lean_isize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_shiftRight___boxed(lean_object*, lean_object*);
size_t lean_isize_complement(size_t);
LEAN_EXPORT lean_object* l_ISize_complement___boxed(lean_object*);
size_t lean_isize_abs(size_t);
LEAN_EXPORT lean_object* l_ISize_abs___boxed(lean_object*);
uint8_t lean_isize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_decEq___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_instInhabitedISize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_instInhabitedISize___closed__0;
LEAN_EXPORT size_t l_instInhabitedISize;
static const lean_closure_object l_instAddISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAddISize___closed__0 = (const lean_object*)&l_instAddISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instAddISize = (const lean_object*)&l_instAddISize___closed__0_value;
static const lean_closure_object l_instSubISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSubISize___closed__0 = (const lean_object*)&l_instSubISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instSubISize = (const lean_object*)&l_instSubISize___closed__0_value;
static const lean_closure_object l_instMulISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMulISize___closed__0 = (const lean_object*)&l_instMulISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instMulISize = (const lean_object*)&l_instMulISize___closed__0_value;
static const lean_closure_object l_instPowISizeNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instPowISizeNat___closed__0 = (const lean_object*)&l_instPowISizeNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instPowISizeNat = (const lean_object*)&l_instPowISizeNat___closed__0_value;
static const lean_closure_object l_instModISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_mod___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instModISize___closed__0 = (const lean_object*)&l_instModISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instModISize = (const lean_object*)&l_instModISize___closed__0_value;
static const lean_closure_object l_instDivISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instDivISize___closed__0 = (const lean_object*)&l_instDivISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instDivISize = (const lean_object*)&l_instDivISize___closed__0_value;
LEAN_EXPORT lean_object* l_instLTISize;
LEAN_EXPORT lean_object* l_instLEISize;
static const lean_closure_object l_instComplementISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_complement___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instComplementISize___closed__0 = (const lean_object*)&l_instComplementISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instComplementISize = (const lean_object*)&l_instComplementISize___closed__0_value;
static const lean_closure_object l_instAndOpISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_land___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAndOpISize___closed__0 = (const lean_object*)&l_instAndOpISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instAndOpISize = (const lean_object*)&l_instAndOpISize___closed__0_value;
static const lean_closure_object l_instOrOpISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_lor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrOpISize___closed__0 = (const lean_object*)&l_instOrOpISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrOpISize = (const lean_object*)&l_instOrOpISize___closed__0_value;
static const lean_closure_object l_instXorOpISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_xor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instXorOpISize___closed__0 = (const lean_object*)&l_instXorOpISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instXorOpISize = (const lean_object*)&l_instXorOpISize___closed__0_value;
static const lean_closure_object l_instShiftLeftISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftLeftISize___closed__0 = (const lean_object*)&l_instShiftLeftISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftLeftISize = (const lean_object*)&l_instShiftLeftISize___closed__0_value;
static const lean_closure_object l_instShiftRightISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftRightISize___closed__0 = (const lean_object*)&l_instShiftRightISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftRightISize = (const lean_object*)&l_instShiftRightISize___closed__0_value;
LEAN_EXPORT uint8_t l_instDecidableEqISize(size_t, size_t);
LEAN_EXPORT lean_object* l_instDecidableEqISize___boxed(lean_object*, lean_object*);
size_t lean_bool_to_isize(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toISize___boxed(lean_object*);
uint8_t lean_isize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_decLt___boxed(lean_object*, lean_object*);
uint8_t lean_isize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_instMaxISize___lam__0(size_t, size_t);
LEAN_EXPORT lean_object* l_instMaxISize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMaxISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMaxISize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMaxISize___closed__0 = (const lean_object*)&l_instMaxISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instMaxISize = (const lean_object*)&l_instMaxISize___closed__0_value;
LEAN_EXPORT size_t l_instMinISize___lam__0(size_t, size_t);
LEAN_EXPORT lean_object* l_instMinISize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMinISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMinISize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMinISize___closed__0 = (const lean_object*)&l_instMinISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instMinISize = (const lean_object*)&l_instMinISize___closed__0_value;
static lean_object* _init_l_Int8_size(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(256u);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Int8_toBitVec(uint8_t v_x_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_uint8_to_nat(v_x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Int8_toBitVec___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_boxed_5_; lean_object* v_res_6_; 
v_x_boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Int8_toBitVec(v_x_boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT uint8_t l_UInt8_toInt8(uint8_t v_i_7_){
_start:
{
return v_i_7_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toInt8___boxed(lean_object* v_i_8_){
_start:
{
uint8_t v_i_boxed_9_; uint8_t v_res_10_; lean_object* v_r_11_; 
v_i_boxed_9_ = lean_unbox(v_i_8_);
v_res_10_ = l_UInt8_toInt8(v_i_boxed_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* l_Int8_ofInt___boxed(lean_object* v_i_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = lean_int8_of_int(v_i_13_);
lean_dec(v_i_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT lean_object* l_Int8_ofNat___boxed(lean_object* v_n_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = lean_int8_of_nat(v_n_17_);
lean_dec(v_n_17_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l_Int_toInt8(lean_object* v_i_20_){
_start:
{
uint8_t v___x_21_; 
v___x_21_ = lean_int8_of_int(v_i_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt8___boxed(lean_object* v_i_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Int_toInt8(v_i_22_);
lean_dec(v_i_22_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT uint8_t l_Nat_toInt8(lean_object* v_n_25_){
_start:
{
uint8_t v___x_26_; 
v___x_26_ = lean_int8_of_nat(v_n_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt8___boxed(lean_object* v_n_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Nat_toInt8(v_n_27_);
lean_dec(v_n_27_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt___boxed(lean_object* v_i_31_){
_start:
{
uint8_t v_i_boxed_32_; lean_object* v_res_33_; 
v_i_boxed_32_ = lean_unbox(v_i_31_);
v_res_33_ = lean_int8_to_int(v_i_boxed_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Int8_toNatClampNeg(uint8_t v_i_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_int8_to_int(v_i_34_);
v___x_36_ = l_Int_toNat(v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Int8_toNatClampNeg___boxed(lean_object* v_i_37_){
_start:
{
uint8_t v_i_boxed_38_; lean_object* v_res_39_; 
v_i_boxed_38_ = lean_unbox(v_i_37_);
v_res_39_ = l_Int8_toNatClampNeg(v_i_boxed_38_);
return v_res_39_;
}
}
LEAN_EXPORT uint8_t l_Int8_ofBitVec(lean_object* v_b_40_){
_start:
{
uint8_t v___x_41_; 
v___x_41_ = lean_uint8_of_nat_mk(v_b_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Int8_ofBitVec___boxed(lean_object* v_b_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_Int8_ofBitVec(v_b_42_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
LEAN_EXPORT lean_object* l_Int8_neg___boxed(lean_object* v_i_46_){
_start:
{
uint8_t v_i_boxed_47_; uint8_t v_res_48_; lean_object* v_r_49_; 
v_i_boxed_47_ = lean_unbox(v_i_46_);
v_res_48_ = lean_int8_neg(v_i_boxed_47_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt8___lam__0(uint8_t v_i_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_int8_to_int(v_i_50_);
v___x_52_ = l_Int_repr(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt8___lam__0___boxed(lean_object* v_i_53_){
_start:
{
uint8_t v_i_boxed_54_; lean_object* v_res_55_; 
v_i_boxed_54_ = lean_unbox(v_i_53_);
v_res_55_ = l_instToStringInt8___lam__0(v_i_boxed_54_);
return v_res_55_;
}
}
static lean_object* _init_l_instReprInt8___lam__0___closed__0(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_nat_to_int(v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_instReprInt8___lam__0(uint8_t v_i_60_, lean_object* v_prec_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_62_ = lean_int8_to_int(v_i_60_);
v___x_63_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_64_ = lean_int_dec_lt(v___x_62_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = l_Int_repr(v___x_62_);
v___x_66_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = l_Int_repr(v___x_62_);
v___x_68_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
v___x_69_ = l_Repr_addAppParen(v___x_68_, v_prec_61_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt8___lam__0___boxed(lean_object* v_i_70_, lean_object* v_prec_71_){
_start:
{
uint8_t v_i_boxed_72_; lean_object* v_res_73_; 
v_i_boxed_72_ = lean_unbox(v_i_70_);
v_res_73_ = l_instReprInt8___lam__0(v_i_boxed_72_, v_prec_71_);
lean_dec(v_prec_71_);
return v_res_73_;
}
}
static lean_object* _init_l_instReprAtomInt8(void){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(0);
return v___x_76_;
}
}
LEAN_EXPORT uint8_t l_Int8_instOfNat(lean_object* v_n_79_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = lean_int8_of_nat(v_n_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Int8_instOfNat___boxed(lean_object* v_n_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Int8_instOfNat(v_n_81_);
lean_dec(v_n_81_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
static uint8_t _init_l_Int8_maxValue___closed__0(void){
_start:
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(127u);
v___x_87_ = lean_int8_of_nat(v___x_86_);
return v___x_87_;
}
}
static uint8_t _init_l_Int8_maxValue(void){
_start:
{
uint8_t v___x_88_; 
v___x_88_ = lean_uint8_once(&l_Int8_maxValue___closed__0, &l_Int8_maxValue___closed__0_once, _init_l_Int8_maxValue___closed__0);
return v___x_88_;
}
}
static uint8_t _init_l_Int8_minValue___closed__0(void){
_start:
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(128u);
v___x_90_ = lean_int8_of_nat(v___x_89_);
return v___x_90_;
}
}
static uint8_t _init_l_Int8_minValue___closed__1(void){
_start:
{
uint8_t v___x_91_; uint8_t v___x_92_; 
v___x_91_ = lean_uint8_once(&l_Int8_minValue___closed__0, &l_Int8_minValue___closed__0_once, _init_l_Int8_minValue___closed__0);
v___x_92_ = lean_int8_neg(v___x_91_);
return v___x_92_;
}
}
static uint8_t _init_l_Int8_minValue(void){
_start:
{
uint8_t v___x_93_; 
v___x_93_ = lean_uint8_once(&l_Int8_minValue___closed__1, &l_Int8_minValue___closed__1_once, _init_l_Int8_minValue___closed__1);
return v___x_93_;
}
}
LEAN_EXPORT uint8_t l_Int8_ofIntLE___redArg(lean_object* v_i_94_){
_start:
{
uint8_t v___x_95_; 
v___x_95_ = lean_int8_of_int(v_i_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Int8_ofIntLE___redArg___boxed(lean_object* v_i_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Int8_ofIntLE___redArg(v_i_96_);
lean_dec(v_i_96_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT uint8_t l_Int8_ofIntLE(lean_object* v_i_99_, lean_object* v___hl_100_, lean_object* v___hr_101_){
_start:
{
uint8_t v___x_102_; 
v___x_102_ = lean_int8_of_int(v_i_99_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Int8_ofIntLE___boxed(lean_object* v_i_103_, lean_object* v___hl_104_, lean_object* v___hr_105_){
_start:
{
uint8_t v_res_106_; lean_object* v_r_107_; 
v_res_106_ = l_Int8_ofIntLE(v_i_103_, v___hl_104_, v___hr_105_);
lean_dec(v_i_103_);
v_r_107_ = lean_box(v_res_106_);
return v_r_107_;
}
}
static lean_object* _init_l_Int8_ofIntTruncate___closed__0(void){
_start:
{
uint8_t v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_uint8_once(&l_Int8_minValue___closed__1, &l_Int8_minValue___closed__1_once, _init_l_Int8_minValue___closed__1);
v___x_109_ = lean_int8_to_int(v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l_Int8_ofIntTruncate___closed__1(void){
_start:
{
uint8_t v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_uint8_once(&l_Int8_maxValue___closed__0, &l_Int8_maxValue___closed__0_once, _init_l_Int8_maxValue___closed__0);
v___x_111_ = lean_int8_to_int(v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT uint8_t l_Int8_ofIntTruncate(lean_object* v_i_112_){
_start:
{
uint8_t v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_113_ = lean_uint8_once(&l_Int8_minValue___closed__1, &l_Int8_minValue___closed__1_once, _init_l_Int8_minValue___closed__1);
v___x_114_ = lean_obj_once(&l_Int8_ofIntTruncate___closed__0, &l_Int8_ofIntTruncate___closed__0_once, _init_l_Int8_ofIntTruncate___closed__0);
v___x_115_ = lean_int_dec_le(v___x_114_, v_i_112_);
if (v___x_115_ == 0)
{
return v___x_113_;
}
else
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_obj_once(&l_Int8_ofIntTruncate___closed__1, &l_Int8_ofIntTruncate___closed__1_once, _init_l_Int8_ofIntTruncate___closed__1);
v___x_117_ = lean_int_dec_le(v_i_112_, v___x_116_);
if (v___x_117_ == 0)
{
return v___x_113_;
}
else
{
uint8_t v___x_118_; 
v___x_118_ = lean_int8_of_int(v_i_112_);
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int8_ofIntTruncate___boxed(lean_object* v_i_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Int8_ofIntTruncate(v_i_119_);
lean_dec(v_i_119_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT lean_object* l_Int8_add___boxed(lean_object* v_a_124_, lean_object* v_b_125_){
_start:
{
uint8_t v_a_boxed_126_; uint8_t v_b_boxed_127_; uint8_t v_res_128_; lean_object* v_r_129_; 
v_a_boxed_126_ = lean_unbox(v_a_124_);
v_b_boxed_127_ = lean_unbox(v_b_125_);
v_res_128_ = lean_int8_add(v_a_boxed_126_, v_b_boxed_127_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT lean_object* l_Int8_sub___boxed(lean_object* v_a_132_, lean_object* v_b_133_){
_start:
{
uint8_t v_a_boxed_134_; uint8_t v_b_boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v_a_boxed_134_ = lean_unbox(v_a_132_);
v_b_boxed_135_ = lean_unbox(v_b_133_);
v_res_136_ = lean_int8_sub(v_a_boxed_134_, v_b_boxed_135_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_Int8_mul___boxed(lean_object* v_a_140_, lean_object* v_b_141_){
_start:
{
uint8_t v_a_boxed_142_; uint8_t v_b_boxed_143_; uint8_t v_res_144_; lean_object* v_r_145_; 
v_a_boxed_142_ = lean_unbox(v_a_140_);
v_b_boxed_143_ = lean_unbox(v_b_141_);
v_res_144_ = lean_int8_mul(v_a_boxed_142_, v_b_boxed_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
LEAN_EXPORT lean_object* l_Int8_div___boxed(lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
uint8_t v_a_boxed_150_; uint8_t v_b_boxed_151_; uint8_t v_res_152_; lean_object* v_r_153_; 
v_a_boxed_150_ = lean_unbox(v_a_148_);
v_b_boxed_151_ = lean_unbox(v_b_149_);
v_res_152_ = lean_int8_div(v_a_boxed_150_, v_b_boxed_151_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
static uint8_t _init_l_Int8_pow___closed__0(void){
_start:
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_int8_of_nat(v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT uint8_t l_Int8_pow(uint8_t v_x_156_, lean_object* v_n_157_){
_start:
{
lean_object* v_zero_158_; uint8_t v_isZero_159_; 
v_zero_158_ = lean_unsigned_to_nat(0u);
v_isZero_159_ = lean_nat_dec_eq(v_n_157_, v_zero_158_);
if (v_isZero_159_ == 1)
{
uint8_t v___x_160_; 
v___x_160_ = lean_uint8_once(&l_Int8_pow___closed__0, &l_Int8_pow___closed__0_once, _init_l_Int8_pow___closed__0);
return v___x_160_;
}
else
{
lean_object* v_one_161_; lean_object* v_n_162_; uint8_t v___x_163_; uint8_t v___x_164_; 
v_one_161_ = lean_unsigned_to_nat(1u);
v_n_162_ = lean_nat_sub(v_n_157_, v_one_161_);
v___x_163_ = l_Int8_pow(v_x_156_, v_n_162_);
lean_dec(v_n_162_);
v___x_164_ = lean_int8_mul(v___x_163_, v_x_156_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Int8_pow___boxed(lean_object* v_x_165_, lean_object* v_n_166_){
_start:
{
uint8_t v_x_boxed_167_; uint8_t v_res_168_; lean_object* v_r_169_; 
v_x_boxed_167_ = lean_unbox(v_x_165_);
v_res_168_ = l_Int8_pow(v_x_boxed_167_, v_n_166_);
lean_dec(v_n_166_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT lean_object* l_Int8_mod___boxed(lean_object* v_a_172_, lean_object* v_b_173_){
_start:
{
uint8_t v_a_boxed_174_; uint8_t v_b_boxed_175_; uint8_t v_res_176_; lean_object* v_r_177_; 
v_a_boxed_174_ = lean_unbox(v_a_172_);
v_b_boxed_175_ = lean_unbox(v_b_173_);
v_res_176_ = lean_int8_mod(v_a_boxed_174_, v_b_boxed_175_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT lean_object* l_Int8_land___boxed(lean_object* v_a_180_, lean_object* v_b_181_){
_start:
{
uint8_t v_a_boxed_182_; uint8_t v_b_boxed_183_; uint8_t v_res_184_; lean_object* v_r_185_; 
v_a_boxed_182_ = lean_unbox(v_a_180_);
v_b_boxed_183_ = lean_unbox(v_b_181_);
v_res_184_ = lean_int8_land(v_a_boxed_182_, v_b_boxed_183_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT lean_object* l_Int8_lor___boxed(lean_object* v_a_188_, lean_object* v_b_189_){
_start:
{
uint8_t v_a_boxed_190_; uint8_t v_b_boxed_191_; uint8_t v_res_192_; lean_object* v_r_193_; 
v_a_boxed_190_ = lean_unbox(v_a_188_);
v_b_boxed_191_ = lean_unbox(v_b_189_);
v_res_192_ = lean_int8_lor(v_a_boxed_190_, v_b_boxed_191_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT lean_object* l_Int8_xor___boxed(lean_object* v_a_196_, lean_object* v_b_197_){
_start:
{
uint8_t v_a_boxed_198_; uint8_t v_b_boxed_199_; uint8_t v_res_200_; lean_object* v_r_201_; 
v_a_boxed_198_ = lean_unbox(v_a_196_);
v_b_boxed_199_ = lean_unbox(v_b_197_);
v_res_200_ = lean_int8_xor(v_a_boxed_198_, v_b_boxed_199_);
v_r_201_ = lean_box(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT lean_object* l_Int8_shiftLeft___boxed(lean_object* v_a_204_, lean_object* v_b_205_){
_start:
{
uint8_t v_a_boxed_206_; uint8_t v_b_boxed_207_; uint8_t v_res_208_; lean_object* v_r_209_; 
v_a_boxed_206_ = lean_unbox(v_a_204_);
v_b_boxed_207_ = lean_unbox(v_b_205_);
v_res_208_ = lean_int8_shift_left(v_a_boxed_206_, v_b_boxed_207_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT lean_object* l_Int8_shiftRight___boxed(lean_object* v_a_212_, lean_object* v_b_213_){
_start:
{
uint8_t v_a_boxed_214_; uint8_t v_b_boxed_215_; uint8_t v_res_216_; lean_object* v_r_217_; 
v_a_boxed_214_ = lean_unbox(v_a_212_);
v_b_boxed_215_ = lean_unbox(v_b_213_);
v_res_216_ = lean_int8_shift_right(v_a_boxed_214_, v_b_boxed_215_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT lean_object* l_Int8_complement___boxed(lean_object* v_a_219_){
_start:
{
uint8_t v_a_boxed_220_; uint8_t v_res_221_; lean_object* v_r_222_; 
v_a_boxed_220_ = lean_unbox(v_a_219_);
v_res_221_ = lean_int8_complement(v_a_boxed_220_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT lean_object* l_Int8_abs___boxed(lean_object* v_a_224_){
_start:
{
uint8_t v_a_boxed_225_; uint8_t v_res_226_; lean_object* v_r_227_; 
v_a_boxed_225_ = lean_unbox(v_a_224_);
v_res_226_ = lean_int8_abs(v_a_boxed_225_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l_Int8_decEq___boxed(lean_object* v_a_230_, lean_object* v_b_231_){
_start:
{
uint8_t v_a_boxed_232_; uint8_t v_b_boxed_233_; uint8_t v_res_234_; lean_object* v_r_235_; 
v_a_boxed_232_ = lean_unbox(v_a_230_);
v_b_boxed_233_ = lean_unbox(v_b_231_);
v_res_234_ = lean_int8_dec_eq(v_a_boxed_232_, v_b_boxed_233_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
static uint8_t _init_l_instInhabitedInt8___closed__0(void){
_start:
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(0u);
v___x_237_ = lean_int8_of_nat(v___x_236_);
return v___x_237_;
}
}
static uint8_t _init_l_instInhabitedInt8(void){
_start:
{
uint8_t v___x_238_; 
v___x_238_ = lean_uint8_once(&l_instInhabitedInt8___closed__0, &l_instInhabitedInt8___closed__0_once, _init_l_instInhabitedInt8___closed__0);
return v___x_238_;
}
}
static lean_object* _init_l_instLTInt8(void){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = lean_box(0);
return v___x_251_;
}
}
static lean_object* _init_l_instLEInt8(void){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_box(0);
return v___x_252_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt8(uint8_t v_a_265_, uint8_t v_b_266_){
_start:
{
uint8_t v___x_267_; 
v___x_267_ = lean_int8_dec_eq(v_a_265_, v_b_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt8___boxed(lean_object* v_a_268_, lean_object* v_b_269_){
_start:
{
uint8_t v_a_boxed_270_; uint8_t v_b_boxed_271_; uint8_t v_res_272_; lean_object* v_r_273_; 
v_a_boxed_270_ = lean_unbox(v_a_268_);
v_b_boxed_271_ = lean_unbox(v_b_269_);
v_res_272_ = l_instDecidableEqInt8(v_a_boxed_270_, v_b_boxed_271_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt8___boxed(lean_object* v_b_275_){
_start:
{
uint8_t v_b_boxed_276_; uint8_t v_res_277_; lean_object* v_r_278_; 
v_b_boxed_276_ = lean_unbox(v_b_275_);
v_res_277_ = lean_bool_to_int8(v_b_boxed_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLt___boxed(lean_object* v_a_281_, lean_object* v_b_282_){
_start:
{
uint8_t v_a_boxed_283_; uint8_t v_b_boxed_284_; uint8_t v_res_285_; lean_object* v_r_286_; 
v_a_boxed_283_ = lean_unbox(v_a_281_);
v_b_boxed_284_ = lean_unbox(v_b_282_);
v_res_285_ = lean_int8_dec_lt(v_a_boxed_283_, v_b_boxed_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLe___boxed(lean_object* v_a_289_, lean_object* v_b_290_){
_start:
{
uint8_t v_a_boxed_291_; uint8_t v_b_boxed_292_; uint8_t v_res_293_; lean_object* v_r_294_; 
v_a_boxed_291_ = lean_unbox(v_a_289_);
v_b_boxed_292_ = lean_unbox(v_b_290_);
v_res_293_ = lean_int8_dec_le(v_a_boxed_291_, v_b_boxed_292_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT uint8_t l_instMaxInt8___lam__0(uint8_t v_x_295_, uint8_t v_y_296_){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = lean_int8_dec_le(v_x_295_, v_y_296_);
if (v___x_297_ == 0)
{
return v_x_295_;
}
else
{
return v_y_296_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt8___lam__0___boxed(lean_object* v_x_298_, lean_object* v_y_299_){
_start:
{
uint8_t v_x_boxed_300_; uint8_t v_y_boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_x_boxed_300_ = lean_unbox(v_x_298_);
v_y_boxed_301_ = lean_unbox(v_y_299_);
v_res_302_ = l_instMaxInt8___lam__0(v_x_boxed_300_, v_y_boxed_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT uint8_t l_instMinInt8___lam__0(uint8_t v_x_306_, uint8_t v_y_307_){
_start:
{
uint8_t v___x_308_; 
v___x_308_ = lean_int8_dec_le(v_x_306_, v_y_307_);
if (v___x_308_ == 0)
{
return v_y_307_;
}
else
{
return v_x_306_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt8___lam__0___boxed(lean_object* v_x_309_, lean_object* v_y_310_){
_start:
{
uint8_t v_x_boxed_311_; uint8_t v_y_boxed_312_; uint8_t v_res_313_; lean_object* v_r_314_; 
v_x_boxed_311_ = lean_unbox(v_x_309_);
v_y_boxed_312_ = lean_unbox(v_y_310_);
v_res_313_ = l_instMinInt8___lam__0(v_x_boxed_311_, v_y_boxed_312_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
static lean_object* _init_l_Int16_size(void){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_unsigned_to_nat(65536u);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Int16_toBitVec(uint16_t v_x_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_uint16_to_nat(v_x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Int16_toBitVec___boxed(lean_object* v_x_320_){
_start:
{
uint16_t v_x_boxed_321_; lean_object* v_res_322_; 
v_x_boxed_321_ = lean_unbox(v_x_320_);
v_res_322_ = l_Int16_toBitVec(v_x_boxed_321_);
return v_res_322_;
}
}
LEAN_EXPORT uint16_t l_UInt16_toInt16(uint16_t v_i_323_){
_start:
{
return v_i_323_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toInt16___boxed(lean_object* v_i_324_){
_start:
{
uint16_t v_i_boxed_325_; uint16_t v_res_326_; lean_object* v_r_327_; 
v_i_boxed_325_ = lean_unbox(v_i_324_);
v_res_326_ = l_UInt16_toInt16(v_i_boxed_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofInt___boxed(lean_object* v_i_329_){
_start:
{
uint16_t v_res_330_; lean_object* v_r_331_; 
v_res_330_ = lean_int16_of_int(v_i_329_);
lean_dec(v_i_329_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofNat___boxed(lean_object* v_n_333_){
_start:
{
uint16_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = lean_int16_of_nat(v_n_333_);
lean_dec(v_n_333_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT uint16_t l_Int_toInt16(lean_object* v_i_336_){
_start:
{
uint16_t v___x_337_; 
v___x_337_ = lean_int16_of_int(v_i_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt16___boxed(lean_object* v_i_338_){
_start:
{
uint16_t v_res_339_; lean_object* v_r_340_; 
v_res_339_ = l_Int_toInt16(v_i_338_);
lean_dec(v_i_338_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint16_t l_Nat_toInt16(lean_object* v_n_341_){
_start:
{
uint16_t v___x_342_; 
v___x_342_ = lean_int16_of_nat(v_n_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt16___boxed(lean_object* v_n_343_){
_start:
{
uint16_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_Nat_toInt16(v_n_343_);
lean_dec(v_n_343_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt___boxed(lean_object* v_i_347_){
_start:
{
uint16_t v_i_boxed_348_; lean_object* v_res_349_; 
v_i_boxed_348_ = lean_unbox(v_i_347_);
v_res_349_ = lean_int16_to_int(v_i_boxed_348_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg(uint16_t v_i_350_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_int16_to_int(v_i_350_);
v___x_352_ = l_Int_toNat(v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg___boxed(lean_object* v_i_353_){
_start:
{
uint16_t v_i_boxed_354_; lean_object* v_res_355_; 
v_i_boxed_354_ = lean_unbox(v_i_353_);
v_res_355_ = l_Int16_toNatClampNeg(v_i_boxed_354_);
return v_res_355_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofBitVec(lean_object* v_b_356_){
_start:
{
uint16_t v___x_357_; 
v___x_357_ = lean_uint16_of_nat_mk(v_b_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofBitVec___boxed(lean_object* v_b_358_){
_start:
{
uint16_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Int16_ofBitVec(v_b_358_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt8___boxed(lean_object* v_a_362_){
_start:
{
uint16_t v_a_boxed_363_; uint8_t v_res_364_; lean_object* v_r_365_; 
v_a_boxed_363_ = lean_unbox(v_a_362_);
v_res_364_ = lean_int16_to_int8(v_a_boxed_363_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt16___boxed(lean_object* v_a_367_){
_start:
{
uint8_t v_a_boxed_368_; uint16_t v_res_369_; lean_object* v_r_370_; 
v_a_boxed_368_ = lean_unbox(v_a_367_);
v_res_369_ = lean_int8_to_int16(v_a_boxed_368_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT lean_object* l_Int16_neg___boxed(lean_object* v_i_372_){
_start:
{
uint16_t v_i_boxed_373_; uint16_t v_res_374_; lean_object* v_r_375_; 
v_i_boxed_373_ = lean_unbox(v_i_372_);
v_res_374_ = lean_int16_neg(v_i_boxed_373_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0(uint16_t v_i_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_int16_to_int(v_i_376_);
v___x_378_ = l_Int_repr(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0___boxed(lean_object* v_i_379_){
_start:
{
uint16_t v_i_boxed_380_; lean_object* v_res_381_; 
v_i_boxed_380_ = lean_unbox(v_i_379_);
v_res_381_ = l_instToStringInt16___lam__0(v_i_boxed_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_instReprInt16___lam__0(uint16_t v_i_384_, lean_object* v_prec_385_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_386_ = lean_int16_to_int(v_i_384_);
v___x_387_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_388_ = lean_int_dec_lt(v___x_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = l_Int_repr(v___x_386_);
v___x_390_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = l_Int_repr(v___x_386_);
v___x_392_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
v___x_393_ = l_Repr_addAppParen(v___x_392_, v_prec_385_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt16___lam__0___boxed(lean_object* v_i_394_, lean_object* v_prec_395_){
_start:
{
uint16_t v_i_boxed_396_; lean_object* v_res_397_; 
v_i_boxed_396_ = lean_unbox(v_i_394_);
v_res_397_ = l_instReprInt16___lam__0(v_i_boxed_396_, v_prec_395_);
lean_dec(v_prec_395_);
return v_res_397_;
}
}
static lean_object* _init_l_instReprAtomInt16(void){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_box(0);
return v___x_400_;
}
}
LEAN_EXPORT uint16_t l_Int16_instOfNat(lean_object* v_n_403_){
_start:
{
uint16_t v___x_404_; 
v___x_404_ = lean_int16_of_nat(v_n_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Int16_instOfNat___boxed(lean_object* v_n_405_){
_start:
{
uint16_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_Int16_instOfNat(v_n_405_);
lean_dec(v_n_405_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
static uint16_t _init_l_Int16_maxValue___closed__0(void){
_start:
{
lean_object* v___x_410_; uint16_t v___x_411_; 
v___x_410_ = lean_unsigned_to_nat(32767u);
v___x_411_ = lean_int16_of_nat(v___x_410_);
return v___x_411_;
}
}
static uint16_t _init_l_Int16_maxValue(void){
_start:
{
uint16_t v___x_412_; 
v___x_412_ = lean_uint16_once(&l_Int16_maxValue___closed__0, &l_Int16_maxValue___closed__0_once, _init_l_Int16_maxValue___closed__0);
return v___x_412_;
}
}
static uint16_t _init_l_Int16_minValue___closed__0(void){
_start:
{
lean_object* v___x_413_; uint16_t v___x_414_; 
v___x_413_ = lean_unsigned_to_nat(32768u);
v___x_414_ = lean_int16_of_nat(v___x_413_);
return v___x_414_;
}
}
static uint16_t _init_l_Int16_minValue___closed__1(void){
_start:
{
uint16_t v___x_415_; uint16_t v___x_416_; 
v___x_415_ = lean_uint16_once(&l_Int16_minValue___closed__0, &l_Int16_minValue___closed__0_once, _init_l_Int16_minValue___closed__0);
v___x_416_ = lean_int16_neg(v___x_415_);
return v___x_416_;
}
}
static uint16_t _init_l_Int16_minValue(void){
_start:
{
uint16_t v___x_417_; 
v___x_417_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
return v___x_417_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntLE___redArg(lean_object* v_i_418_){
_start:
{
uint16_t v___x_419_; 
v___x_419_ = lean_int16_of_int(v_i_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntLE___redArg___boxed(lean_object* v_i_420_){
_start:
{
uint16_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_Int16_ofIntLE___redArg(v_i_420_);
lean_dec(v_i_420_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntLE(lean_object* v_i_423_, lean_object* v___hl_424_, lean_object* v___hr_425_){
_start:
{
uint16_t v___x_426_; 
v___x_426_ = lean_int16_of_int(v_i_423_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntLE___boxed(lean_object* v_i_427_, lean_object* v___hl_428_, lean_object* v___hr_429_){
_start:
{
uint16_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l_Int16_ofIntLE(v_i_427_, v___hl_428_, v___hr_429_);
lean_dec(v_i_427_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
static lean_object* _init_l_Int16_ofIntTruncate___closed__0(void){
_start:
{
uint16_t v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
v___x_433_ = lean_int16_to_int(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Int16_ofIntTruncate___closed__1(void){
_start:
{
uint16_t v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_uint16_once(&l_Int16_maxValue___closed__0, &l_Int16_maxValue___closed__0_once, _init_l_Int16_maxValue___closed__0);
v___x_435_ = lean_int16_to_int(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntTruncate(lean_object* v_i_436_){
_start:
{
uint16_t v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_437_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
v___x_438_ = lean_obj_once(&l_Int16_ofIntTruncate___closed__0, &l_Int16_ofIntTruncate___closed__0_once, _init_l_Int16_ofIntTruncate___closed__0);
v___x_439_ = lean_int_dec_le(v___x_438_, v_i_436_);
if (v___x_439_ == 0)
{
return v___x_437_;
}
else
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = lean_obj_once(&l_Int16_ofIntTruncate___closed__1, &l_Int16_ofIntTruncate___closed__1_once, _init_l_Int16_ofIntTruncate___closed__1);
v___x_441_ = lean_int_dec_le(v_i_436_, v___x_440_);
if (v___x_441_ == 0)
{
return v___x_437_;
}
else
{
uint16_t v___x_442_; 
v___x_442_ = lean_int16_of_int(v_i_436_);
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntTruncate___boxed(lean_object* v_i_443_){
_start:
{
uint16_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Int16_ofIntTruncate(v_i_443_);
lean_dec(v_i_443_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT lean_object* l_Int16_add___boxed(lean_object* v_a_448_, lean_object* v_b_449_){
_start:
{
uint16_t v_a_boxed_450_; uint16_t v_b_boxed_451_; uint16_t v_res_452_; lean_object* v_r_453_; 
v_a_boxed_450_ = lean_unbox(v_a_448_);
v_b_boxed_451_ = lean_unbox(v_b_449_);
v_res_452_ = lean_int16_add(v_a_boxed_450_, v_b_boxed_451_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT lean_object* l_Int16_sub___boxed(lean_object* v_a_456_, lean_object* v_b_457_){
_start:
{
uint16_t v_a_boxed_458_; uint16_t v_b_boxed_459_; uint16_t v_res_460_; lean_object* v_r_461_; 
v_a_boxed_458_ = lean_unbox(v_a_456_);
v_b_boxed_459_ = lean_unbox(v_b_457_);
v_res_460_ = lean_int16_sub(v_a_boxed_458_, v_b_boxed_459_);
v_r_461_ = lean_box(v_res_460_);
return v_r_461_;
}
}
LEAN_EXPORT lean_object* l_Int16_mul___boxed(lean_object* v_a_464_, lean_object* v_b_465_){
_start:
{
uint16_t v_a_boxed_466_; uint16_t v_b_boxed_467_; uint16_t v_res_468_; lean_object* v_r_469_; 
v_a_boxed_466_ = lean_unbox(v_a_464_);
v_b_boxed_467_ = lean_unbox(v_b_465_);
v_res_468_ = lean_int16_mul(v_a_boxed_466_, v_b_boxed_467_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT lean_object* l_Int16_div___boxed(lean_object* v_a_472_, lean_object* v_b_473_){
_start:
{
uint16_t v_a_boxed_474_; uint16_t v_b_boxed_475_; uint16_t v_res_476_; lean_object* v_r_477_; 
v_a_boxed_474_ = lean_unbox(v_a_472_);
v_b_boxed_475_ = lean_unbox(v_b_473_);
v_res_476_ = lean_int16_div(v_a_boxed_474_, v_b_boxed_475_);
v_r_477_ = lean_box(v_res_476_);
return v_r_477_;
}
}
static uint16_t _init_l_Int16_pow___closed__0(void){
_start:
{
lean_object* v___x_478_; uint16_t v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = lean_int16_of_nat(v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT uint16_t l_Int16_pow(uint16_t v_x_480_, lean_object* v_n_481_){
_start:
{
lean_object* v_zero_482_; uint8_t v_isZero_483_; 
v_zero_482_ = lean_unsigned_to_nat(0u);
v_isZero_483_ = lean_nat_dec_eq(v_n_481_, v_zero_482_);
if (v_isZero_483_ == 1)
{
uint16_t v___x_484_; 
v___x_484_ = lean_uint16_once(&l_Int16_pow___closed__0, &l_Int16_pow___closed__0_once, _init_l_Int16_pow___closed__0);
return v___x_484_;
}
else
{
lean_object* v_one_485_; lean_object* v_n_486_; uint16_t v___x_487_; uint16_t v___x_488_; 
v_one_485_ = lean_unsigned_to_nat(1u);
v_n_486_ = lean_nat_sub(v_n_481_, v_one_485_);
v___x_487_ = l_Int16_pow(v_x_480_, v_n_486_);
lean_dec(v_n_486_);
v___x_488_ = lean_int16_mul(v___x_487_, v_x_480_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Int16_pow___boxed(lean_object* v_x_489_, lean_object* v_n_490_){
_start:
{
uint16_t v_x_boxed_491_; uint16_t v_res_492_; lean_object* v_r_493_; 
v_x_boxed_491_ = lean_unbox(v_x_489_);
v_res_492_ = l_Int16_pow(v_x_boxed_491_, v_n_490_);
lean_dec(v_n_490_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l_Int16_mod___boxed(lean_object* v_a_496_, lean_object* v_b_497_){
_start:
{
uint16_t v_a_boxed_498_; uint16_t v_b_boxed_499_; uint16_t v_res_500_; lean_object* v_r_501_; 
v_a_boxed_498_ = lean_unbox(v_a_496_);
v_b_boxed_499_ = lean_unbox(v_b_497_);
v_res_500_ = lean_int16_mod(v_a_boxed_498_, v_b_boxed_499_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT lean_object* l_Int16_land___boxed(lean_object* v_a_504_, lean_object* v_b_505_){
_start:
{
uint16_t v_a_boxed_506_; uint16_t v_b_boxed_507_; uint16_t v_res_508_; lean_object* v_r_509_; 
v_a_boxed_506_ = lean_unbox(v_a_504_);
v_b_boxed_507_ = lean_unbox(v_b_505_);
v_res_508_ = lean_int16_land(v_a_boxed_506_, v_b_boxed_507_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
LEAN_EXPORT lean_object* l_Int16_lor___boxed(lean_object* v_a_512_, lean_object* v_b_513_){
_start:
{
uint16_t v_a_boxed_514_; uint16_t v_b_boxed_515_; uint16_t v_res_516_; lean_object* v_r_517_; 
v_a_boxed_514_ = lean_unbox(v_a_512_);
v_b_boxed_515_ = lean_unbox(v_b_513_);
v_res_516_ = lean_int16_lor(v_a_boxed_514_, v_b_boxed_515_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT lean_object* l_Int16_xor___boxed(lean_object* v_a_520_, lean_object* v_b_521_){
_start:
{
uint16_t v_a_boxed_522_; uint16_t v_b_boxed_523_; uint16_t v_res_524_; lean_object* v_r_525_; 
v_a_boxed_522_ = lean_unbox(v_a_520_);
v_b_boxed_523_ = lean_unbox(v_b_521_);
v_res_524_ = lean_int16_xor(v_a_boxed_522_, v_b_boxed_523_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT lean_object* l_Int16_shiftLeft___boxed(lean_object* v_a_528_, lean_object* v_b_529_){
_start:
{
uint16_t v_a_boxed_530_; uint16_t v_b_boxed_531_; uint16_t v_res_532_; lean_object* v_r_533_; 
v_a_boxed_530_ = lean_unbox(v_a_528_);
v_b_boxed_531_ = lean_unbox(v_b_529_);
v_res_532_ = lean_int16_shift_left(v_a_boxed_530_, v_b_boxed_531_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT lean_object* l_Int16_shiftRight___boxed(lean_object* v_a_536_, lean_object* v_b_537_){
_start:
{
uint16_t v_a_boxed_538_; uint16_t v_b_boxed_539_; uint16_t v_res_540_; lean_object* v_r_541_; 
v_a_boxed_538_ = lean_unbox(v_a_536_);
v_b_boxed_539_ = lean_unbox(v_b_537_);
v_res_540_ = lean_int16_shift_right(v_a_boxed_538_, v_b_boxed_539_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT lean_object* l_Int16_complement___boxed(lean_object* v_a_543_){
_start:
{
uint16_t v_a_boxed_544_; uint16_t v_res_545_; lean_object* v_r_546_; 
v_a_boxed_544_ = lean_unbox(v_a_543_);
v_res_545_ = lean_int16_complement(v_a_boxed_544_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT lean_object* l_Int16_abs___boxed(lean_object* v_a_548_){
_start:
{
uint16_t v_a_boxed_549_; uint16_t v_res_550_; lean_object* v_r_551_; 
v_a_boxed_549_ = lean_unbox(v_a_548_);
v_res_550_ = lean_int16_abs(v_a_boxed_549_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT lean_object* l_Int16_decEq___boxed(lean_object* v_a_554_, lean_object* v_b_555_){
_start:
{
uint16_t v_a_boxed_556_; uint16_t v_b_boxed_557_; uint8_t v_res_558_; lean_object* v_r_559_; 
v_a_boxed_556_ = lean_unbox(v_a_554_);
v_b_boxed_557_ = lean_unbox(v_b_555_);
v_res_558_ = lean_int16_dec_eq(v_a_boxed_556_, v_b_boxed_557_);
v_r_559_ = lean_box(v_res_558_);
return v_r_559_;
}
}
static uint16_t _init_l_instInhabitedInt16___closed__0(void){
_start:
{
lean_object* v___x_560_; uint16_t v___x_561_; 
v___x_560_ = lean_unsigned_to_nat(0u);
v___x_561_ = lean_int16_of_nat(v___x_560_);
return v___x_561_;
}
}
static uint16_t _init_l_instInhabitedInt16(void){
_start:
{
uint16_t v___x_562_; 
v___x_562_ = lean_uint16_once(&l_instInhabitedInt16___closed__0, &l_instInhabitedInt16___closed__0_once, _init_l_instInhabitedInt16___closed__0);
return v___x_562_;
}
}
static lean_object* _init_l_instLTInt16(void){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_box(0);
return v___x_575_;
}
}
static lean_object* _init_l_instLEInt16(void){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = lean_box(0);
return v___x_576_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt16(uint16_t v_a_589_, uint16_t v_b_590_){
_start:
{
uint8_t v___x_591_; 
v___x_591_ = lean_int16_dec_eq(v_a_589_, v_b_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt16___boxed(lean_object* v_a_592_, lean_object* v_b_593_){
_start:
{
uint16_t v_a_boxed_594_; uint16_t v_b_boxed_595_; uint8_t v_res_596_; lean_object* v_r_597_; 
v_a_boxed_594_ = lean_unbox(v_a_592_);
v_b_boxed_595_ = lean_unbox(v_b_593_);
v_res_596_ = l_instDecidableEqInt16(v_a_boxed_594_, v_b_boxed_595_);
v_r_597_ = lean_box(v_res_596_);
return v_r_597_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt16___boxed(lean_object* v_b_599_){
_start:
{
uint8_t v_b_boxed_600_; uint16_t v_res_601_; lean_object* v_r_602_; 
v_b_boxed_600_ = lean_unbox(v_b_599_);
v_res_601_ = lean_bool_to_int16(v_b_boxed_600_);
v_r_602_ = lean_box(v_res_601_);
return v_r_602_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLt___boxed(lean_object* v_a_605_, lean_object* v_b_606_){
_start:
{
uint16_t v_a_boxed_607_; uint16_t v_b_boxed_608_; uint8_t v_res_609_; lean_object* v_r_610_; 
v_a_boxed_607_ = lean_unbox(v_a_605_);
v_b_boxed_608_ = lean_unbox(v_b_606_);
v_res_609_ = lean_int16_dec_lt(v_a_boxed_607_, v_b_boxed_608_);
v_r_610_ = lean_box(v_res_609_);
return v_r_610_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLe___boxed(lean_object* v_a_613_, lean_object* v_b_614_){
_start:
{
uint16_t v_a_boxed_615_; uint16_t v_b_boxed_616_; uint8_t v_res_617_; lean_object* v_r_618_; 
v_a_boxed_615_ = lean_unbox(v_a_613_);
v_b_boxed_616_ = lean_unbox(v_b_614_);
v_res_617_ = lean_int16_dec_le(v_a_boxed_615_, v_b_boxed_616_);
v_r_618_ = lean_box(v_res_617_);
return v_r_618_;
}
}
LEAN_EXPORT uint16_t l_instMaxInt16___lam__0(uint16_t v_x_619_, uint16_t v_y_620_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = lean_int16_dec_le(v_x_619_, v_y_620_);
if (v___x_621_ == 0)
{
return v_x_619_;
}
else
{
return v_y_620_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt16___lam__0___boxed(lean_object* v_x_622_, lean_object* v_y_623_){
_start:
{
uint16_t v_x_boxed_624_; uint16_t v_y_boxed_625_; uint16_t v_res_626_; lean_object* v_r_627_; 
v_x_boxed_624_ = lean_unbox(v_x_622_);
v_y_boxed_625_ = lean_unbox(v_y_623_);
v_res_626_ = l_instMaxInt16___lam__0(v_x_boxed_624_, v_y_boxed_625_);
v_r_627_ = lean_box(v_res_626_);
return v_r_627_;
}
}
LEAN_EXPORT uint16_t l_instMinInt16___lam__0(uint16_t v_x_630_, uint16_t v_y_631_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = lean_int16_dec_le(v_x_630_, v_y_631_);
if (v___x_632_ == 0)
{
return v_y_631_;
}
else
{
return v_x_630_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt16___lam__0___boxed(lean_object* v_x_633_, lean_object* v_y_634_){
_start:
{
uint16_t v_x_boxed_635_; uint16_t v_y_boxed_636_; uint16_t v_res_637_; lean_object* v_r_638_; 
v_x_boxed_635_ = lean_unbox(v_x_633_);
v_y_boxed_636_ = lean_unbox(v_y_634_);
v_res_637_ = l_instMinInt16___lam__0(v_x_boxed_635_, v_y_boxed_636_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
static lean_object* _init_l_Int32_size(void){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = lean_cstr_to_nat("4294967296");
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Int32_toBitVec(uint32_t v_x_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = lean_uint32_to_nat(v_x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Int32_toBitVec___boxed(lean_object* v_x_644_){
_start:
{
uint32_t v_x_boxed_645_; lean_object* v_res_646_; 
v_x_boxed_645_ = lean_unbox_uint32(v_x_644_);
lean_dec(v_x_644_);
v_res_646_ = l_Int32_toBitVec(v_x_boxed_645_);
return v_res_646_;
}
}
LEAN_EXPORT uint32_t l_UInt32_toInt32(uint32_t v_i_647_){
_start:
{
return v_i_647_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toInt32___boxed(lean_object* v_i_648_){
_start:
{
uint32_t v_i_boxed_649_; uint32_t v_res_650_; lean_object* v_r_651_; 
v_i_boxed_649_ = lean_unbox_uint32(v_i_648_);
lean_dec(v_i_648_);
v_res_650_ = l_UInt32_toInt32(v_i_boxed_649_);
v_r_651_ = lean_box_uint32(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofInt___boxed(lean_object* v_i_653_){
_start:
{
uint32_t v_res_654_; lean_object* v_r_655_; 
v_res_654_ = lean_int32_of_int(v_i_653_);
lean_dec(v_i_653_);
v_r_655_ = lean_box_uint32(v_res_654_);
return v_r_655_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofNat___boxed(lean_object* v_n_657_){
_start:
{
uint32_t v_res_658_; lean_object* v_r_659_; 
v_res_658_ = lean_int32_of_nat(v_n_657_);
lean_dec(v_n_657_);
v_r_659_ = lean_box_uint32(v_res_658_);
return v_r_659_;
}
}
LEAN_EXPORT uint32_t l_Int_toInt32(lean_object* v_i_660_){
_start:
{
uint32_t v___x_661_; 
v___x_661_ = lean_int32_of_int(v_i_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt32___boxed(lean_object* v_i_662_){
_start:
{
uint32_t v_res_663_; lean_object* v_r_664_; 
v_res_663_ = l_Int_toInt32(v_i_662_);
lean_dec(v_i_662_);
v_r_664_ = lean_box_uint32(v_res_663_);
return v_r_664_;
}
}
LEAN_EXPORT uint32_t l_Nat_toInt32(lean_object* v_n_665_){
_start:
{
uint32_t v___x_666_; 
v___x_666_ = lean_int32_of_nat(v_n_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt32___boxed(lean_object* v_n_667_){
_start:
{
uint32_t v_res_668_; lean_object* v_r_669_; 
v_res_668_ = l_Nat_toInt32(v_n_667_);
lean_dec(v_n_667_);
v_r_669_ = lean_box_uint32(v_res_668_);
return v_r_669_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt___boxed(lean_object* v_i_671_){
_start:
{
uint32_t v_i_boxed_672_; lean_object* v_res_673_; 
v_i_boxed_672_ = lean_unbox_uint32(v_i_671_);
lean_dec(v_i_671_);
v_res_673_ = lean_int32_to_int(v_i_boxed_672_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg(uint32_t v_i_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_int32_to_int(v_i_674_);
v___x_676_ = l_Int_toNat(v___x_675_);
lean_dec(v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg___boxed(lean_object* v_i_677_){
_start:
{
uint32_t v_i_boxed_678_; lean_object* v_res_679_; 
v_i_boxed_678_ = lean_unbox_uint32(v_i_677_);
lean_dec(v_i_677_);
v_res_679_ = l_Int32_toNatClampNeg(v_i_boxed_678_);
return v_res_679_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofBitVec(lean_object* v_b_680_){
_start:
{
uint32_t v___x_681_; 
v___x_681_ = lean_uint32_of_nat_mk(v_b_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofBitVec___boxed(lean_object* v_b_682_){
_start:
{
uint32_t v_res_683_; lean_object* v_r_684_; 
v_res_683_ = l_Int32_ofBitVec(v_b_682_);
v_r_684_ = lean_box_uint32(v_res_683_);
return v_r_684_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt8___boxed(lean_object* v_a_686_){
_start:
{
uint32_t v_a_boxed_687_; uint8_t v_res_688_; lean_object* v_r_689_; 
v_a_boxed_687_ = lean_unbox_uint32(v_a_686_);
lean_dec(v_a_686_);
v_res_688_ = lean_int32_to_int8(v_a_boxed_687_);
v_r_689_ = lean_box(v_res_688_);
return v_r_689_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt16___boxed(lean_object* v_a_691_){
_start:
{
uint32_t v_a_boxed_692_; uint16_t v_res_693_; lean_object* v_r_694_; 
v_a_boxed_692_ = lean_unbox_uint32(v_a_691_);
lean_dec(v_a_691_);
v_res_693_ = lean_int32_to_int16(v_a_boxed_692_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt32___boxed(lean_object* v_a_696_){
_start:
{
uint8_t v_a_boxed_697_; uint32_t v_res_698_; lean_object* v_r_699_; 
v_a_boxed_697_ = lean_unbox(v_a_696_);
v_res_698_ = lean_int8_to_int32(v_a_boxed_697_);
v_r_699_ = lean_box_uint32(v_res_698_);
return v_r_699_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt32___boxed(lean_object* v_a_701_){
_start:
{
uint16_t v_a_boxed_702_; uint32_t v_res_703_; lean_object* v_r_704_; 
v_a_boxed_702_ = lean_unbox(v_a_701_);
v_res_703_ = lean_int16_to_int32(v_a_boxed_702_);
v_r_704_ = lean_box_uint32(v_res_703_);
return v_r_704_;
}
}
LEAN_EXPORT lean_object* l_Int32_neg___boxed(lean_object* v_i_706_){
_start:
{
uint32_t v_i_boxed_707_; uint32_t v_res_708_; lean_object* v_r_709_; 
v_i_boxed_707_ = lean_unbox_uint32(v_i_706_);
lean_dec(v_i_706_);
v_res_708_ = lean_int32_neg(v_i_boxed_707_);
v_r_709_ = lean_box_uint32(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0(uint32_t v_i_710_){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_int32_to_int(v_i_710_);
v___x_712_ = l_Int_repr(v___x_711_);
lean_dec(v___x_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0___boxed(lean_object* v_i_713_){
_start:
{
uint32_t v_i_boxed_714_; lean_object* v_res_715_; 
v_i_boxed_714_ = lean_unbox_uint32(v_i_713_);
lean_dec(v_i_713_);
v_res_715_ = l_instToStringInt32___lam__0(v_i_boxed_714_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_instReprInt32___lam__0(uint32_t v_i_718_, lean_object* v_prec_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_720_ = lean_int32_to_int(v_i_718_);
v___x_721_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_722_ = lean_int_dec_lt(v___x_720_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = l_Int_repr(v___x_720_);
lean_dec(v___x_720_);
v___x_724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = l_Int_repr(v___x_720_);
lean_dec(v___x_720_);
v___x_726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
v___x_727_ = l_Repr_addAppParen(v___x_726_, v_prec_719_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt32___lam__0___boxed(lean_object* v_i_728_, lean_object* v_prec_729_){
_start:
{
uint32_t v_i_boxed_730_; lean_object* v_res_731_; 
v_i_boxed_730_ = lean_unbox_uint32(v_i_728_);
lean_dec(v_i_728_);
v_res_731_ = l_instReprInt32___lam__0(v_i_boxed_730_, v_prec_729_);
lean_dec(v_prec_729_);
return v_res_731_;
}
}
static lean_object* _init_l_instReprAtomInt32(void){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_box(0);
return v___x_734_;
}
}
LEAN_EXPORT uint32_t l_Int32_instOfNat(lean_object* v_n_737_){
_start:
{
uint32_t v___x_738_; 
v___x_738_ = lean_int32_of_nat(v_n_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Int32_instOfNat___boxed(lean_object* v_n_739_){
_start:
{
uint32_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = l_Int32_instOfNat(v_n_739_);
lean_dec(v_n_739_);
v_r_741_ = lean_box_uint32(v_res_740_);
return v_r_741_;
}
}
static uint32_t _init_l_Int32_maxValue___closed__0(void){
_start:
{
lean_object* v___x_744_; uint32_t v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(2147483647u);
v___x_745_ = lean_int32_of_nat(v___x_744_);
return v___x_745_;
}
}
static uint32_t _init_l_Int32_maxValue(void){
_start:
{
uint32_t v___x_746_; 
v___x_746_ = lean_uint32_once(&l_Int32_maxValue___closed__0, &l_Int32_maxValue___closed__0_once, _init_l_Int32_maxValue___closed__0);
return v___x_746_;
}
}
static uint32_t _init_l_Int32_minValue___closed__0(void){
_start:
{
lean_object* v___x_747_; uint32_t v___x_748_; 
v___x_747_ = lean_unsigned_to_nat(2147483648u);
v___x_748_ = lean_int32_of_nat(v___x_747_);
return v___x_748_;
}
}
static uint32_t _init_l_Int32_minValue___closed__1(void){
_start:
{
uint32_t v___x_749_; uint32_t v___x_750_; 
v___x_749_ = lean_uint32_once(&l_Int32_minValue___closed__0, &l_Int32_minValue___closed__0_once, _init_l_Int32_minValue___closed__0);
v___x_750_ = lean_int32_neg(v___x_749_);
return v___x_750_;
}
}
static uint32_t _init_l_Int32_minValue(void){
_start:
{
uint32_t v___x_751_; 
v___x_751_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
return v___x_751_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntLE___redArg(lean_object* v_i_752_){
_start:
{
uint32_t v___x_753_; 
v___x_753_ = lean_int32_of_int(v_i_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntLE___redArg___boxed(lean_object* v_i_754_){
_start:
{
uint32_t v_res_755_; lean_object* v_r_756_; 
v_res_755_ = l_Int32_ofIntLE___redArg(v_i_754_);
lean_dec(v_i_754_);
v_r_756_ = lean_box_uint32(v_res_755_);
return v_r_756_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntLE(lean_object* v_i_757_, lean_object* v___hl_758_, lean_object* v___hr_759_){
_start:
{
uint32_t v___x_760_; 
v___x_760_ = lean_int32_of_int(v_i_757_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntLE___boxed(lean_object* v_i_761_, lean_object* v___hl_762_, lean_object* v___hr_763_){
_start:
{
uint32_t v_res_764_; lean_object* v_r_765_; 
v_res_764_ = l_Int32_ofIntLE(v_i_761_, v___hl_762_, v___hr_763_);
lean_dec(v_i_761_);
v_r_765_ = lean_box_uint32(v_res_764_);
return v_r_765_;
}
}
static lean_object* _init_l_Int32_ofIntTruncate___closed__0(void){
_start:
{
uint32_t v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
v___x_767_ = lean_int32_to_int(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_Int32_ofIntTruncate___closed__1(void){
_start:
{
uint32_t v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_uint32_once(&l_Int32_maxValue___closed__0, &l_Int32_maxValue___closed__0_once, _init_l_Int32_maxValue___closed__0);
v___x_769_ = lean_int32_to_int(v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntTruncate(lean_object* v_i_770_){
_start:
{
uint32_t v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_771_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
v___x_772_ = lean_obj_once(&l_Int32_ofIntTruncate___closed__0, &l_Int32_ofIntTruncate___closed__0_once, _init_l_Int32_ofIntTruncate___closed__0);
v___x_773_ = lean_int_dec_le(v___x_772_, v_i_770_);
if (v___x_773_ == 0)
{
return v___x_771_;
}
else
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_obj_once(&l_Int32_ofIntTruncate___closed__1, &l_Int32_ofIntTruncate___closed__1_once, _init_l_Int32_ofIntTruncate___closed__1);
v___x_775_ = lean_int_dec_le(v_i_770_, v___x_774_);
if (v___x_775_ == 0)
{
return v___x_771_;
}
else
{
uint32_t v___x_776_; 
v___x_776_ = lean_int32_of_int(v_i_770_);
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntTruncate___boxed(lean_object* v_i_777_){
_start:
{
uint32_t v_res_778_; lean_object* v_r_779_; 
v_res_778_ = l_Int32_ofIntTruncate(v_i_777_);
lean_dec(v_i_777_);
v_r_779_ = lean_box_uint32(v_res_778_);
return v_r_779_;
}
}
LEAN_EXPORT lean_object* l_Int32_add___boxed(lean_object* v_a_782_, lean_object* v_b_783_){
_start:
{
uint32_t v_a_boxed_784_; uint32_t v_b_boxed_785_; uint32_t v_res_786_; lean_object* v_r_787_; 
v_a_boxed_784_ = lean_unbox_uint32(v_a_782_);
lean_dec(v_a_782_);
v_b_boxed_785_ = lean_unbox_uint32(v_b_783_);
lean_dec(v_b_783_);
v_res_786_ = lean_int32_add(v_a_boxed_784_, v_b_boxed_785_);
v_r_787_ = lean_box_uint32(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT lean_object* l_Int32_sub___boxed(lean_object* v_a_790_, lean_object* v_b_791_){
_start:
{
uint32_t v_a_boxed_792_; uint32_t v_b_boxed_793_; uint32_t v_res_794_; lean_object* v_r_795_; 
v_a_boxed_792_ = lean_unbox_uint32(v_a_790_);
lean_dec(v_a_790_);
v_b_boxed_793_ = lean_unbox_uint32(v_b_791_);
lean_dec(v_b_791_);
v_res_794_ = lean_int32_sub(v_a_boxed_792_, v_b_boxed_793_);
v_r_795_ = lean_box_uint32(v_res_794_);
return v_r_795_;
}
}
LEAN_EXPORT lean_object* l_Int32_mul___boxed(lean_object* v_a_798_, lean_object* v_b_799_){
_start:
{
uint32_t v_a_boxed_800_; uint32_t v_b_boxed_801_; uint32_t v_res_802_; lean_object* v_r_803_; 
v_a_boxed_800_ = lean_unbox_uint32(v_a_798_);
lean_dec(v_a_798_);
v_b_boxed_801_ = lean_unbox_uint32(v_b_799_);
lean_dec(v_b_799_);
v_res_802_ = lean_int32_mul(v_a_boxed_800_, v_b_boxed_801_);
v_r_803_ = lean_box_uint32(v_res_802_);
return v_r_803_;
}
}
LEAN_EXPORT lean_object* l_Int32_div___boxed(lean_object* v_a_806_, lean_object* v_b_807_){
_start:
{
uint32_t v_a_boxed_808_; uint32_t v_b_boxed_809_; uint32_t v_res_810_; lean_object* v_r_811_; 
v_a_boxed_808_ = lean_unbox_uint32(v_a_806_);
lean_dec(v_a_806_);
v_b_boxed_809_ = lean_unbox_uint32(v_b_807_);
lean_dec(v_b_807_);
v_res_810_ = lean_int32_div(v_a_boxed_808_, v_b_boxed_809_);
v_r_811_ = lean_box_uint32(v_res_810_);
return v_r_811_;
}
}
static uint32_t _init_l_Int32_pow___closed__0(void){
_start:
{
lean_object* v___x_812_; uint32_t v___x_813_; 
v___x_812_ = lean_unsigned_to_nat(1u);
v___x_813_ = lean_int32_of_nat(v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT uint32_t l_Int32_pow(uint32_t v_x_814_, lean_object* v_n_815_){
_start:
{
lean_object* v_zero_816_; uint8_t v_isZero_817_; 
v_zero_816_ = lean_unsigned_to_nat(0u);
v_isZero_817_ = lean_nat_dec_eq(v_n_815_, v_zero_816_);
if (v_isZero_817_ == 1)
{
uint32_t v___x_818_; 
v___x_818_ = lean_uint32_once(&l_Int32_pow___closed__0, &l_Int32_pow___closed__0_once, _init_l_Int32_pow___closed__0);
return v___x_818_;
}
else
{
lean_object* v_one_819_; lean_object* v_n_820_; uint32_t v___x_821_; uint32_t v___x_822_; 
v_one_819_ = lean_unsigned_to_nat(1u);
v_n_820_ = lean_nat_sub(v_n_815_, v_one_819_);
v___x_821_ = l_Int32_pow(v_x_814_, v_n_820_);
lean_dec(v_n_820_);
v___x_822_ = lean_int32_mul(v___x_821_, v_x_814_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Int32_pow___boxed(lean_object* v_x_823_, lean_object* v_n_824_){
_start:
{
uint32_t v_x_boxed_825_; uint32_t v_res_826_; lean_object* v_r_827_; 
v_x_boxed_825_ = lean_unbox_uint32(v_x_823_);
lean_dec(v_x_823_);
v_res_826_ = l_Int32_pow(v_x_boxed_825_, v_n_824_);
lean_dec(v_n_824_);
v_r_827_ = lean_box_uint32(v_res_826_);
return v_r_827_;
}
}
LEAN_EXPORT lean_object* l_Int32_mod___boxed(lean_object* v_a_830_, lean_object* v_b_831_){
_start:
{
uint32_t v_a_boxed_832_; uint32_t v_b_boxed_833_; uint32_t v_res_834_; lean_object* v_r_835_; 
v_a_boxed_832_ = lean_unbox_uint32(v_a_830_);
lean_dec(v_a_830_);
v_b_boxed_833_ = lean_unbox_uint32(v_b_831_);
lean_dec(v_b_831_);
v_res_834_ = lean_int32_mod(v_a_boxed_832_, v_b_boxed_833_);
v_r_835_ = lean_box_uint32(v_res_834_);
return v_r_835_;
}
}
LEAN_EXPORT lean_object* l_Int32_land___boxed(lean_object* v_a_838_, lean_object* v_b_839_){
_start:
{
uint32_t v_a_boxed_840_; uint32_t v_b_boxed_841_; uint32_t v_res_842_; lean_object* v_r_843_; 
v_a_boxed_840_ = lean_unbox_uint32(v_a_838_);
lean_dec(v_a_838_);
v_b_boxed_841_ = lean_unbox_uint32(v_b_839_);
lean_dec(v_b_839_);
v_res_842_ = lean_int32_land(v_a_boxed_840_, v_b_boxed_841_);
v_r_843_ = lean_box_uint32(v_res_842_);
return v_r_843_;
}
}
LEAN_EXPORT lean_object* l_Int32_lor___boxed(lean_object* v_a_846_, lean_object* v_b_847_){
_start:
{
uint32_t v_a_boxed_848_; uint32_t v_b_boxed_849_; uint32_t v_res_850_; lean_object* v_r_851_; 
v_a_boxed_848_ = lean_unbox_uint32(v_a_846_);
lean_dec(v_a_846_);
v_b_boxed_849_ = lean_unbox_uint32(v_b_847_);
lean_dec(v_b_847_);
v_res_850_ = lean_int32_lor(v_a_boxed_848_, v_b_boxed_849_);
v_r_851_ = lean_box_uint32(v_res_850_);
return v_r_851_;
}
}
LEAN_EXPORT lean_object* l_Int32_xor___boxed(lean_object* v_a_854_, lean_object* v_b_855_){
_start:
{
uint32_t v_a_boxed_856_; uint32_t v_b_boxed_857_; uint32_t v_res_858_; lean_object* v_r_859_; 
v_a_boxed_856_ = lean_unbox_uint32(v_a_854_);
lean_dec(v_a_854_);
v_b_boxed_857_ = lean_unbox_uint32(v_b_855_);
lean_dec(v_b_855_);
v_res_858_ = lean_int32_xor(v_a_boxed_856_, v_b_boxed_857_);
v_r_859_ = lean_box_uint32(v_res_858_);
return v_r_859_;
}
}
LEAN_EXPORT lean_object* l_Int32_shiftLeft___boxed(lean_object* v_a_862_, lean_object* v_b_863_){
_start:
{
uint32_t v_a_boxed_864_; uint32_t v_b_boxed_865_; uint32_t v_res_866_; lean_object* v_r_867_; 
v_a_boxed_864_ = lean_unbox_uint32(v_a_862_);
lean_dec(v_a_862_);
v_b_boxed_865_ = lean_unbox_uint32(v_b_863_);
lean_dec(v_b_863_);
v_res_866_ = lean_int32_shift_left(v_a_boxed_864_, v_b_boxed_865_);
v_r_867_ = lean_box_uint32(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT lean_object* l_Int32_shiftRight___boxed(lean_object* v_a_870_, lean_object* v_b_871_){
_start:
{
uint32_t v_a_boxed_872_; uint32_t v_b_boxed_873_; uint32_t v_res_874_; lean_object* v_r_875_; 
v_a_boxed_872_ = lean_unbox_uint32(v_a_870_);
lean_dec(v_a_870_);
v_b_boxed_873_ = lean_unbox_uint32(v_b_871_);
lean_dec(v_b_871_);
v_res_874_ = lean_int32_shift_right(v_a_boxed_872_, v_b_boxed_873_);
v_r_875_ = lean_box_uint32(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l_Int32_complement___boxed(lean_object* v_a_877_){
_start:
{
uint32_t v_a_boxed_878_; uint32_t v_res_879_; lean_object* v_r_880_; 
v_a_boxed_878_ = lean_unbox_uint32(v_a_877_);
lean_dec(v_a_877_);
v_res_879_ = lean_int32_complement(v_a_boxed_878_);
v_r_880_ = lean_box_uint32(v_res_879_);
return v_r_880_;
}
}
LEAN_EXPORT lean_object* l_Int32_abs___boxed(lean_object* v_a_882_){
_start:
{
uint32_t v_a_boxed_883_; uint32_t v_res_884_; lean_object* v_r_885_; 
v_a_boxed_883_ = lean_unbox_uint32(v_a_882_);
lean_dec(v_a_882_);
v_res_884_ = lean_int32_abs(v_a_boxed_883_);
v_r_885_ = lean_box_uint32(v_res_884_);
return v_r_885_;
}
}
LEAN_EXPORT lean_object* l_Int32_decEq___boxed(lean_object* v_a_888_, lean_object* v_b_889_){
_start:
{
uint32_t v_a_boxed_890_; uint32_t v_b_boxed_891_; uint8_t v_res_892_; lean_object* v_r_893_; 
v_a_boxed_890_ = lean_unbox_uint32(v_a_888_);
lean_dec(v_a_888_);
v_b_boxed_891_ = lean_unbox_uint32(v_b_889_);
lean_dec(v_b_889_);
v_res_892_ = lean_int32_dec_eq(v_a_boxed_890_, v_b_boxed_891_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
static uint32_t _init_l_instInhabitedInt32___closed__0(void){
_start:
{
lean_object* v___x_894_; uint32_t v___x_895_; 
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_int32_of_nat(v___x_894_);
return v___x_895_;
}
}
static uint32_t _init_l_instInhabitedInt32(void){
_start:
{
uint32_t v___x_896_; 
v___x_896_ = lean_uint32_once(&l_instInhabitedInt32___closed__0, &l_instInhabitedInt32___closed__0_once, _init_l_instInhabitedInt32___closed__0);
return v___x_896_;
}
}
static lean_object* _init_l_instLTInt32(void){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = lean_box(0);
return v___x_909_;
}
}
static lean_object* _init_l_instLEInt32(void){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = lean_box(0);
return v___x_910_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt32(uint32_t v_a_923_, uint32_t v_b_924_){
_start:
{
uint8_t v___x_925_; 
v___x_925_ = lean_int32_dec_eq(v_a_923_, v_b_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt32___boxed(lean_object* v_a_926_, lean_object* v_b_927_){
_start:
{
uint32_t v_a_boxed_928_; uint32_t v_b_boxed_929_; uint8_t v_res_930_; lean_object* v_r_931_; 
v_a_boxed_928_ = lean_unbox_uint32(v_a_926_);
lean_dec(v_a_926_);
v_b_boxed_929_ = lean_unbox_uint32(v_b_927_);
lean_dec(v_b_927_);
v_res_930_ = l_instDecidableEqInt32(v_a_boxed_928_, v_b_boxed_929_);
v_r_931_ = lean_box(v_res_930_);
return v_r_931_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt32___boxed(lean_object* v_b_933_){
_start:
{
uint8_t v_b_boxed_934_; uint32_t v_res_935_; lean_object* v_r_936_; 
v_b_boxed_934_ = lean_unbox(v_b_933_);
v_res_935_ = lean_bool_to_int32(v_b_boxed_934_);
v_r_936_ = lean_box_uint32(v_res_935_);
return v_r_936_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLt___boxed(lean_object* v_a_939_, lean_object* v_b_940_){
_start:
{
uint32_t v_a_boxed_941_; uint32_t v_b_boxed_942_; uint8_t v_res_943_; lean_object* v_r_944_; 
v_a_boxed_941_ = lean_unbox_uint32(v_a_939_);
lean_dec(v_a_939_);
v_b_boxed_942_ = lean_unbox_uint32(v_b_940_);
lean_dec(v_b_940_);
v_res_943_ = lean_int32_dec_lt(v_a_boxed_941_, v_b_boxed_942_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLe___boxed(lean_object* v_a_947_, lean_object* v_b_948_){
_start:
{
uint32_t v_a_boxed_949_; uint32_t v_b_boxed_950_; uint8_t v_res_951_; lean_object* v_r_952_; 
v_a_boxed_949_ = lean_unbox_uint32(v_a_947_);
lean_dec(v_a_947_);
v_b_boxed_950_ = lean_unbox_uint32(v_b_948_);
lean_dec(v_b_948_);
v_res_951_ = lean_int32_dec_le(v_a_boxed_949_, v_b_boxed_950_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT uint32_t l_instMaxInt32___lam__0(uint32_t v_x_953_, uint32_t v_y_954_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = lean_int32_dec_le(v_x_953_, v_y_954_);
if (v___x_955_ == 0)
{
return v_x_953_;
}
else
{
return v_y_954_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt32___lam__0___boxed(lean_object* v_x_956_, lean_object* v_y_957_){
_start:
{
uint32_t v_x_boxed_958_; uint32_t v_y_boxed_959_; uint32_t v_res_960_; lean_object* v_r_961_; 
v_x_boxed_958_ = lean_unbox_uint32(v_x_956_);
lean_dec(v_x_956_);
v_y_boxed_959_ = lean_unbox_uint32(v_y_957_);
lean_dec(v_y_957_);
v_res_960_ = l_instMaxInt32___lam__0(v_x_boxed_958_, v_y_boxed_959_);
v_r_961_ = lean_box_uint32(v_res_960_);
return v_r_961_;
}
}
LEAN_EXPORT uint32_t l_instMinInt32___lam__0(uint32_t v_x_964_, uint32_t v_y_965_){
_start:
{
uint8_t v___x_966_; 
v___x_966_ = lean_int32_dec_le(v_x_964_, v_y_965_);
if (v___x_966_ == 0)
{
return v_y_965_;
}
else
{
return v_x_964_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt32___lam__0___boxed(lean_object* v_x_967_, lean_object* v_y_968_){
_start:
{
uint32_t v_x_boxed_969_; uint32_t v_y_boxed_970_; uint32_t v_res_971_; lean_object* v_r_972_; 
v_x_boxed_969_ = lean_unbox_uint32(v_x_967_);
lean_dec(v_x_967_);
v_y_boxed_970_ = lean_unbox_uint32(v_y_968_);
lean_dec(v_y_968_);
v_res_971_ = l_instMinInt32___lam__0(v_x_boxed_969_, v_y_boxed_970_);
v_r_972_ = lean_box_uint32(v_res_971_);
return v_r_972_;
}
}
static lean_object* _init_l_Int64_size___closed__0(void){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = lean_cstr_to_nat("18446744073709551616");
return v___x_975_;
}
}
static lean_object* _init_l_Int64_size(void){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = lean_obj_once(&l_Int64_size___closed__0, &l_Int64_size___closed__0_once, _init_l_Int64_size___closed__0);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Int64_toBitVec(uint64_t v_x_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = lean_uint64_to_nat(v_x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Int64_toBitVec___boxed(lean_object* v_x_979_){
_start:
{
uint64_t v_x_boxed_980_; lean_object* v_res_981_; 
v_x_boxed_980_ = lean_unbox_uint64(v_x_979_);
lean_dec_ref(v_x_979_);
v_res_981_ = l_Int64_toBitVec(v_x_boxed_980_);
return v_res_981_;
}
}
LEAN_EXPORT uint64_t l_UInt64_toInt64(uint64_t v_i_982_){
_start:
{
return v_i_982_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toInt64___boxed(lean_object* v_i_983_){
_start:
{
uint64_t v_i_boxed_984_; uint64_t v_res_985_; lean_object* v_r_986_; 
v_i_boxed_984_ = lean_unbox_uint64(v_i_983_);
lean_dec_ref(v_i_983_);
v_res_985_ = l_UInt64_toInt64(v_i_boxed_984_);
v_r_986_ = lean_box_uint64(v_res_985_);
return v_r_986_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofInt___boxed(lean_object* v_i_988_){
_start:
{
uint64_t v_res_989_; lean_object* v_r_990_; 
v_res_989_ = lean_int64_of_int(v_i_988_);
lean_dec(v_i_988_);
v_r_990_ = lean_box_uint64(v_res_989_);
return v_r_990_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofNat___boxed(lean_object* v_n_992_){
_start:
{
uint64_t v_res_993_; lean_object* v_r_994_; 
v_res_993_ = lean_int64_of_nat(v_n_992_);
lean_dec(v_n_992_);
v_r_994_ = lean_box_uint64(v_res_993_);
return v_r_994_;
}
}
LEAN_EXPORT uint64_t l_Int_toInt64(lean_object* v_i_995_){
_start:
{
uint64_t v___x_996_; 
v___x_996_ = lean_int64_of_int(v_i_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt64___boxed(lean_object* v_i_997_){
_start:
{
uint64_t v_res_998_; lean_object* v_r_999_; 
v_res_998_ = l_Int_toInt64(v_i_997_);
lean_dec(v_i_997_);
v_r_999_ = lean_box_uint64(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT uint64_t l_Nat_toInt64(lean_object* v_n_1000_){
_start:
{
uint64_t v___x_1001_; 
v___x_1001_ = lean_int64_of_nat(v_n_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt64___boxed(lean_object* v_n_1002_){
_start:
{
uint64_t v_res_1003_; lean_object* v_r_1004_; 
v_res_1003_ = l_Nat_toInt64(v_n_1002_);
lean_dec(v_n_1002_);
v_r_1004_ = lean_box_uint64(v_res_1003_);
return v_r_1004_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt___boxed(lean_object* v_i_1006_){
_start:
{
uint64_t v_i_boxed_1007_; lean_object* v_res_1008_; 
v_i_boxed_1007_ = lean_unbox_uint64(v_i_1006_);
lean_dec_ref(v_i_1006_);
v_res_1008_ = lean_int64_to_int_sint(v_i_boxed_1007_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg(uint64_t v_i_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_int64_to_int_sint(v_i_1009_);
v___x_1011_ = l_Int_toNat(v___x_1010_);
lean_dec(v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg___boxed(lean_object* v_i_1012_){
_start:
{
uint64_t v_i_boxed_1013_; lean_object* v_res_1014_; 
v_i_boxed_1013_ = lean_unbox_uint64(v_i_1012_);
lean_dec_ref(v_i_1012_);
v_res_1014_ = l_Int64_toNatClampNeg(v_i_boxed_1013_);
return v_res_1014_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofBitVec(lean_object* v_b_1015_){
_start:
{
uint64_t v___x_1016_; 
v___x_1016_ = lean_uint64_of_nat_mk(v_b_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofBitVec___boxed(lean_object* v_b_1017_){
_start:
{
uint64_t v_res_1018_; lean_object* v_r_1019_; 
v_res_1018_ = l_Int64_ofBitVec(v_b_1017_);
v_r_1019_ = lean_box_uint64(v_res_1018_);
return v_r_1019_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt8___boxed(lean_object* v_a_1021_){
_start:
{
uint64_t v_a_boxed_1022_; uint8_t v_res_1023_; lean_object* v_r_1024_; 
v_a_boxed_1022_ = lean_unbox_uint64(v_a_1021_);
lean_dec_ref(v_a_1021_);
v_res_1023_ = lean_int64_to_int8(v_a_boxed_1022_);
v_r_1024_ = lean_box(v_res_1023_);
return v_r_1024_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt16___boxed(lean_object* v_a_1026_){
_start:
{
uint64_t v_a_boxed_1027_; uint16_t v_res_1028_; lean_object* v_r_1029_; 
v_a_boxed_1027_ = lean_unbox_uint64(v_a_1026_);
lean_dec_ref(v_a_1026_);
v_res_1028_ = lean_int64_to_int16(v_a_boxed_1027_);
v_r_1029_ = lean_box(v_res_1028_);
return v_r_1029_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt32___boxed(lean_object* v_a_1031_){
_start:
{
uint64_t v_a_boxed_1032_; uint32_t v_res_1033_; lean_object* v_r_1034_; 
v_a_boxed_1032_ = lean_unbox_uint64(v_a_1031_);
lean_dec_ref(v_a_1031_);
v_res_1033_ = lean_int64_to_int32(v_a_boxed_1032_);
v_r_1034_ = lean_box_uint32(v_res_1033_);
return v_r_1034_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt64___boxed(lean_object* v_a_1036_){
_start:
{
uint8_t v_a_boxed_1037_; uint64_t v_res_1038_; lean_object* v_r_1039_; 
v_a_boxed_1037_ = lean_unbox(v_a_1036_);
v_res_1038_ = lean_int8_to_int64(v_a_boxed_1037_);
v_r_1039_ = lean_box_uint64(v_res_1038_);
return v_r_1039_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt64___boxed(lean_object* v_a_1041_){
_start:
{
uint16_t v_a_boxed_1042_; uint64_t v_res_1043_; lean_object* v_r_1044_; 
v_a_boxed_1042_ = lean_unbox(v_a_1041_);
v_res_1043_ = lean_int16_to_int64(v_a_boxed_1042_);
v_r_1044_ = lean_box_uint64(v_res_1043_);
return v_r_1044_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt64___boxed(lean_object* v_a_1046_){
_start:
{
uint32_t v_a_boxed_1047_; uint64_t v_res_1048_; lean_object* v_r_1049_; 
v_a_boxed_1047_ = lean_unbox_uint32(v_a_1046_);
lean_dec(v_a_1046_);
v_res_1048_ = lean_int32_to_int64(v_a_boxed_1047_);
v_r_1049_ = lean_box_uint64(v_res_1048_);
return v_r_1049_;
}
}
LEAN_EXPORT lean_object* l_Int64_neg___boxed(lean_object* v_i_1051_){
_start:
{
uint64_t v_i_boxed_1052_; uint64_t v_res_1053_; lean_object* v_r_1054_; 
v_i_boxed_1052_ = lean_unbox_uint64(v_i_1051_);
lean_dec_ref(v_i_1051_);
v_res_1053_ = lean_int64_neg(v_i_boxed_1052_);
v_r_1054_ = lean_box_uint64(v_res_1053_);
return v_r_1054_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0(uint64_t v_i_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_int64_to_int_sint(v_i_1055_);
v___x_1057_ = l_Int_repr(v___x_1056_);
lean_dec(v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0___boxed(lean_object* v_i_1058_){
_start:
{
uint64_t v_i_boxed_1059_; lean_object* v_res_1060_; 
v_i_boxed_1059_ = lean_unbox_uint64(v_i_1058_);
lean_dec_ref(v_i_1058_);
v_res_1060_ = l_instToStringInt64___lam__0(v_i_boxed_1059_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_instReprInt64___lam__0(uint64_t v_i_1063_, lean_object* v_prec_1064_){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1065_ = lean_int64_to_int_sint(v_i_1063_);
v___x_1066_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_1067_ = lean_int_dec_lt(v___x_1065_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = l_Int_repr(v___x_1065_);
lean_dec(v___x_1065_);
v___x_1069_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
else
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = l_Int_repr(v___x_1065_);
lean_dec(v___x_1065_);
v___x_1071_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
v___x_1072_ = l_Repr_addAppParen(v___x_1071_, v_prec_1064_);
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt64___lam__0___boxed(lean_object* v_i_1073_, lean_object* v_prec_1074_){
_start:
{
uint64_t v_i_boxed_1075_; lean_object* v_res_1076_; 
v_i_boxed_1075_ = lean_unbox_uint64(v_i_1073_);
lean_dec_ref(v_i_1073_);
v_res_1076_ = l_instReprInt64___lam__0(v_i_boxed_1075_, v_prec_1074_);
lean_dec(v_prec_1074_);
return v_res_1076_;
}
}
static lean_object* _init_l_instReprAtomInt64(void){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_box(0);
return v___x_1079_;
}
}
LEAN_EXPORT uint64_t l_instHashableInt64___lam__0(uint64_t v_i_1080_){
_start:
{
return v_i_1080_;
}
}
LEAN_EXPORT lean_object* l_instHashableInt64___lam__0___boxed(lean_object* v_i_1081_){
_start:
{
uint64_t v_i_boxed_1082_; uint64_t v_res_1083_; lean_object* v_r_1084_; 
v_i_boxed_1082_ = lean_unbox_uint64(v_i_1081_);
lean_dec_ref(v_i_1081_);
v_res_1083_ = l_instHashableInt64___lam__0(v_i_boxed_1082_);
v_r_1084_ = lean_box_uint64(v_res_1083_);
return v_r_1084_;
}
}
LEAN_EXPORT uint64_t l_Int64_instOfNat(lean_object* v_n_1087_){
_start:
{
uint64_t v___x_1088_; 
v___x_1088_ = lean_int64_of_nat(v_n_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Int64_instOfNat___boxed(lean_object* v_n_1089_){
_start:
{
uint64_t v_res_1090_; lean_object* v_r_1091_; 
v_res_1090_ = l_Int64_instOfNat(v_n_1089_);
lean_dec(v_n_1089_);
v_r_1091_ = lean_box_uint64(v_res_1090_);
return v_r_1091_;
}
}
static uint64_t _init_l_Int64_maxValue___closed__0(void){
_start:
{
lean_object* v___x_1094_; uint64_t v___x_1095_; 
v___x_1094_ = lean_cstr_to_nat("9223372036854775807");
v___x_1095_ = lean_int64_of_nat(v___x_1094_);
return v___x_1095_;
}
}
static uint64_t _init_l_Int64_maxValue(void){
_start:
{
uint64_t v___x_1096_; 
v___x_1096_ = lean_uint64_once(&l_Int64_maxValue___closed__0, &l_Int64_maxValue___closed__0_once, _init_l_Int64_maxValue___closed__0);
return v___x_1096_;
}
}
static lean_object* _init_l_Int64_minValue___closed__0(void){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_cstr_to_nat("9223372036854775808");
return v___x_1097_;
}
}
static uint64_t _init_l_Int64_minValue___closed__1(void){
_start:
{
lean_object* v___x_1098_; uint64_t v___x_1099_; 
v___x_1098_ = lean_obj_once(&l_Int64_minValue___closed__0, &l_Int64_minValue___closed__0_once, _init_l_Int64_minValue___closed__0);
v___x_1099_ = lean_int64_of_nat(v___x_1098_);
return v___x_1099_;
}
}
static uint64_t _init_l_Int64_minValue___closed__2(void){
_start:
{
uint64_t v___x_1100_; uint64_t v___x_1101_; 
v___x_1100_ = lean_uint64_once(&l_Int64_minValue___closed__1, &l_Int64_minValue___closed__1_once, _init_l_Int64_minValue___closed__1);
v___x_1101_ = lean_int64_neg(v___x_1100_);
return v___x_1101_;
}
}
static uint64_t _init_l_Int64_minValue(void){
_start:
{
uint64_t v___x_1102_; 
v___x_1102_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
return v___x_1102_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntLE___redArg(lean_object* v_i_1103_){
_start:
{
uint64_t v___x_1104_; 
v___x_1104_ = lean_int64_of_int(v_i_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntLE___redArg___boxed(lean_object* v_i_1105_){
_start:
{
uint64_t v_res_1106_; lean_object* v_r_1107_; 
v_res_1106_ = l_Int64_ofIntLE___redArg(v_i_1105_);
lean_dec(v_i_1105_);
v_r_1107_ = lean_box_uint64(v_res_1106_);
return v_r_1107_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntLE(lean_object* v_i_1108_, lean_object* v___hl_1109_, lean_object* v___hr_1110_){
_start:
{
uint64_t v___x_1111_; 
v___x_1111_ = lean_int64_of_int(v_i_1108_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntLE___boxed(lean_object* v_i_1112_, lean_object* v___hl_1113_, lean_object* v___hr_1114_){
_start:
{
uint64_t v_res_1115_; lean_object* v_r_1116_; 
v_res_1115_ = l_Int64_ofIntLE(v_i_1112_, v___hl_1113_, v___hr_1114_);
lean_dec(v_i_1112_);
v_r_1116_ = lean_box_uint64(v_res_1115_);
return v_r_1116_;
}
}
static lean_object* _init_l_Int64_ofIntTruncate___closed__0(void){
_start:
{
uint64_t v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
v___x_1118_ = lean_int64_to_int_sint(v___x_1117_);
return v___x_1118_;
}
}
static lean_object* _init_l_Int64_ofIntTruncate___closed__1(void){
_start:
{
uint64_t v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = lean_uint64_once(&l_Int64_maxValue___closed__0, &l_Int64_maxValue___closed__0_once, _init_l_Int64_maxValue___closed__0);
v___x_1120_ = lean_int64_to_int_sint(v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntTruncate(lean_object* v_i_1121_){
_start:
{
uint64_t v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1122_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
v___x_1123_ = lean_obj_once(&l_Int64_ofIntTruncate___closed__0, &l_Int64_ofIntTruncate___closed__0_once, _init_l_Int64_ofIntTruncate___closed__0);
v___x_1124_ = lean_int_dec_le(v___x_1123_, v_i_1121_);
if (v___x_1124_ == 0)
{
return v___x_1122_;
}
else
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = lean_obj_once(&l_Int64_ofIntTruncate___closed__1, &l_Int64_ofIntTruncate___closed__1_once, _init_l_Int64_ofIntTruncate___closed__1);
v___x_1126_ = lean_int_dec_le(v_i_1121_, v___x_1125_);
if (v___x_1126_ == 0)
{
return v___x_1122_;
}
else
{
uint64_t v___x_1127_; 
v___x_1127_ = lean_int64_of_int(v_i_1121_);
return v___x_1127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntTruncate___boxed(lean_object* v_i_1128_){
_start:
{
uint64_t v_res_1129_; lean_object* v_r_1130_; 
v_res_1129_ = l_Int64_ofIntTruncate(v_i_1128_);
lean_dec(v_i_1128_);
v_r_1130_ = lean_box_uint64(v_res_1129_);
return v_r_1130_;
}
}
LEAN_EXPORT lean_object* l_Int64_add___boxed(lean_object* v_a_1133_, lean_object* v_b_1134_){
_start:
{
uint64_t v_a_boxed_1135_; uint64_t v_b_boxed_1136_; uint64_t v_res_1137_; lean_object* v_r_1138_; 
v_a_boxed_1135_ = lean_unbox_uint64(v_a_1133_);
lean_dec_ref(v_a_1133_);
v_b_boxed_1136_ = lean_unbox_uint64(v_b_1134_);
lean_dec_ref(v_b_1134_);
v_res_1137_ = lean_int64_add(v_a_boxed_1135_, v_b_boxed_1136_);
v_r_1138_ = lean_box_uint64(v_res_1137_);
return v_r_1138_;
}
}
LEAN_EXPORT lean_object* l_Int64_sub___boxed(lean_object* v_a_1141_, lean_object* v_b_1142_){
_start:
{
uint64_t v_a_boxed_1143_; uint64_t v_b_boxed_1144_; uint64_t v_res_1145_; lean_object* v_r_1146_; 
v_a_boxed_1143_ = lean_unbox_uint64(v_a_1141_);
lean_dec_ref(v_a_1141_);
v_b_boxed_1144_ = lean_unbox_uint64(v_b_1142_);
lean_dec_ref(v_b_1142_);
v_res_1145_ = lean_int64_sub(v_a_boxed_1143_, v_b_boxed_1144_);
v_r_1146_ = lean_box_uint64(v_res_1145_);
return v_r_1146_;
}
}
LEAN_EXPORT lean_object* l_Int64_mul___boxed(lean_object* v_a_1149_, lean_object* v_b_1150_){
_start:
{
uint64_t v_a_boxed_1151_; uint64_t v_b_boxed_1152_; uint64_t v_res_1153_; lean_object* v_r_1154_; 
v_a_boxed_1151_ = lean_unbox_uint64(v_a_1149_);
lean_dec_ref(v_a_1149_);
v_b_boxed_1152_ = lean_unbox_uint64(v_b_1150_);
lean_dec_ref(v_b_1150_);
v_res_1153_ = lean_int64_mul(v_a_boxed_1151_, v_b_boxed_1152_);
v_r_1154_ = lean_box_uint64(v_res_1153_);
return v_r_1154_;
}
}
LEAN_EXPORT lean_object* l_Int64_div___boxed(lean_object* v_a_1157_, lean_object* v_b_1158_){
_start:
{
uint64_t v_a_boxed_1159_; uint64_t v_b_boxed_1160_; uint64_t v_res_1161_; lean_object* v_r_1162_; 
v_a_boxed_1159_ = lean_unbox_uint64(v_a_1157_);
lean_dec_ref(v_a_1157_);
v_b_boxed_1160_ = lean_unbox_uint64(v_b_1158_);
lean_dec_ref(v_b_1158_);
v_res_1161_ = lean_int64_div(v_a_boxed_1159_, v_b_boxed_1160_);
v_r_1162_ = lean_box_uint64(v_res_1161_);
return v_r_1162_;
}
}
static uint64_t _init_l_Int64_pow___closed__0(void){
_start:
{
lean_object* v___x_1163_; uint64_t v___x_1164_; 
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_int64_of_nat(v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT uint64_t l_Int64_pow(uint64_t v_x_1165_, lean_object* v_n_1166_){
_start:
{
lean_object* v_zero_1167_; uint8_t v_isZero_1168_; 
v_zero_1167_ = lean_unsigned_to_nat(0u);
v_isZero_1168_ = lean_nat_dec_eq(v_n_1166_, v_zero_1167_);
if (v_isZero_1168_ == 1)
{
uint64_t v___x_1169_; 
v___x_1169_ = lean_uint64_once(&l_Int64_pow___closed__0, &l_Int64_pow___closed__0_once, _init_l_Int64_pow___closed__0);
return v___x_1169_;
}
else
{
lean_object* v_one_1170_; lean_object* v_n_1171_; uint64_t v___x_1172_; uint64_t v___x_1173_; 
v_one_1170_ = lean_unsigned_to_nat(1u);
v_n_1171_ = lean_nat_sub(v_n_1166_, v_one_1170_);
v___x_1172_ = l_Int64_pow(v_x_1165_, v_n_1171_);
lean_dec(v_n_1171_);
v___x_1173_ = lean_int64_mul(v___x_1172_, v_x_1165_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_Int64_pow___boxed(lean_object* v_x_1174_, lean_object* v_n_1175_){
_start:
{
uint64_t v_x_boxed_1176_; uint64_t v_res_1177_; lean_object* v_r_1178_; 
v_x_boxed_1176_ = lean_unbox_uint64(v_x_1174_);
lean_dec_ref(v_x_1174_);
v_res_1177_ = l_Int64_pow(v_x_boxed_1176_, v_n_1175_);
lean_dec(v_n_1175_);
v_r_1178_ = lean_box_uint64(v_res_1177_);
return v_r_1178_;
}
}
LEAN_EXPORT lean_object* l_Int64_mod___boxed(lean_object* v_a_1181_, lean_object* v_b_1182_){
_start:
{
uint64_t v_a_boxed_1183_; uint64_t v_b_boxed_1184_; uint64_t v_res_1185_; lean_object* v_r_1186_; 
v_a_boxed_1183_ = lean_unbox_uint64(v_a_1181_);
lean_dec_ref(v_a_1181_);
v_b_boxed_1184_ = lean_unbox_uint64(v_b_1182_);
lean_dec_ref(v_b_1182_);
v_res_1185_ = lean_int64_mod(v_a_boxed_1183_, v_b_boxed_1184_);
v_r_1186_ = lean_box_uint64(v_res_1185_);
return v_r_1186_;
}
}
LEAN_EXPORT lean_object* l_Int64_land___boxed(lean_object* v_a_1189_, lean_object* v_b_1190_){
_start:
{
uint64_t v_a_boxed_1191_; uint64_t v_b_boxed_1192_; uint64_t v_res_1193_; lean_object* v_r_1194_; 
v_a_boxed_1191_ = lean_unbox_uint64(v_a_1189_);
lean_dec_ref(v_a_1189_);
v_b_boxed_1192_ = lean_unbox_uint64(v_b_1190_);
lean_dec_ref(v_b_1190_);
v_res_1193_ = lean_int64_land(v_a_boxed_1191_, v_b_boxed_1192_);
v_r_1194_ = lean_box_uint64(v_res_1193_);
return v_r_1194_;
}
}
LEAN_EXPORT lean_object* l_Int64_lor___boxed(lean_object* v_a_1197_, lean_object* v_b_1198_){
_start:
{
uint64_t v_a_boxed_1199_; uint64_t v_b_boxed_1200_; uint64_t v_res_1201_; lean_object* v_r_1202_; 
v_a_boxed_1199_ = lean_unbox_uint64(v_a_1197_);
lean_dec_ref(v_a_1197_);
v_b_boxed_1200_ = lean_unbox_uint64(v_b_1198_);
lean_dec_ref(v_b_1198_);
v_res_1201_ = lean_int64_lor(v_a_boxed_1199_, v_b_boxed_1200_);
v_r_1202_ = lean_box_uint64(v_res_1201_);
return v_r_1202_;
}
}
LEAN_EXPORT lean_object* l_Int64_xor___boxed(lean_object* v_a_1205_, lean_object* v_b_1206_){
_start:
{
uint64_t v_a_boxed_1207_; uint64_t v_b_boxed_1208_; uint64_t v_res_1209_; lean_object* v_r_1210_; 
v_a_boxed_1207_ = lean_unbox_uint64(v_a_1205_);
lean_dec_ref(v_a_1205_);
v_b_boxed_1208_ = lean_unbox_uint64(v_b_1206_);
lean_dec_ref(v_b_1206_);
v_res_1209_ = lean_int64_xor(v_a_boxed_1207_, v_b_boxed_1208_);
v_r_1210_ = lean_box_uint64(v_res_1209_);
return v_r_1210_;
}
}
LEAN_EXPORT lean_object* l_Int64_shiftLeft___boxed(lean_object* v_a_1213_, lean_object* v_b_1214_){
_start:
{
uint64_t v_a_boxed_1215_; uint64_t v_b_boxed_1216_; uint64_t v_res_1217_; lean_object* v_r_1218_; 
v_a_boxed_1215_ = lean_unbox_uint64(v_a_1213_);
lean_dec_ref(v_a_1213_);
v_b_boxed_1216_ = lean_unbox_uint64(v_b_1214_);
lean_dec_ref(v_b_1214_);
v_res_1217_ = lean_int64_shift_left(v_a_boxed_1215_, v_b_boxed_1216_);
v_r_1218_ = lean_box_uint64(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT lean_object* l_Int64_shiftRight___boxed(lean_object* v_a_1221_, lean_object* v_b_1222_){
_start:
{
uint64_t v_a_boxed_1223_; uint64_t v_b_boxed_1224_; uint64_t v_res_1225_; lean_object* v_r_1226_; 
v_a_boxed_1223_ = lean_unbox_uint64(v_a_1221_);
lean_dec_ref(v_a_1221_);
v_b_boxed_1224_ = lean_unbox_uint64(v_b_1222_);
lean_dec_ref(v_b_1222_);
v_res_1225_ = lean_int64_shift_right(v_a_boxed_1223_, v_b_boxed_1224_);
v_r_1226_ = lean_box_uint64(v_res_1225_);
return v_r_1226_;
}
}
LEAN_EXPORT lean_object* l_Int64_complement___boxed(lean_object* v_a_1228_){
_start:
{
uint64_t v_a_boxed_1229_; uint64_t v_res_1230_; lean_object* v_r_1231_; 
v_a_boxed_1229_ = lean_unbox_uint64(v_a_1228_);
lean_dec_ref(v_a_1228_);
v_res_1230_ = lean_int64_complement(v_a_boxed_1229_);
v_r_1231_ = lean_box_uint64(v_res_1230_);
return v_r_1231_;
}
}
LEAN_EXPORT lean_object* l_Int64_abs___boxed(lean_object* v_a_1233_){
_start:
{
uint64_t v_a_boxed_1234_; uint64_t v_res_1235_; lean_object* v_r_1236_; 
v_a_boxed_1234_ = lean_unbox_uint64(v_a_1233_);
lean_dec_ref(v_a_1233_);
v_res_1235_ = lean_int64_abs(v_a_boxed_1234_);
v_r_1236_ = lean_box_uint64(v_res_1235_);
return v_r_1236_;
}
}
LEAN_EXPORT lean_object* l_Int64_decEq___boxed(lean_object* v_a_1239_, lean_object* v_b_1240_){
_start:
{
uint64_t v_a_boxed_1241_; uint64_t v_b_boxed_1242_; uint8_t v_res_1243_; lean_object* v_r_1244_; 
v_a_boxed_1241_ = lean_unbox_uint64(v_a_1239_);
lean_dec_ref(v_a_1239_);
v_b_boxed_1242_ = lean_unbox_uint64(v_b_1240_);
lean_dec_ref(v_b_1240_);
v_res_1243_ = lean_int64_dec_eq(v_a_boxed_1241_, v_b_boxed_1242_);
v_r_1244_ = lean_box(v_res_1243_);
return v_r_1244_;
}
}
static uint64_t _init_l_instInhabitedInt64___closed__0(void){
_start:
{
lean_object* v___x_1245_; uint64_t v___x_1246_; 
v___x_1245_ = lean_unsigned_to_nat(0u);
v___x_1246_ = lean_int64_of_nat(v___x_1245_);
return v___x_1246_;
}
}
static uint64_t _init_l_instInhabitedInt64(void){
_start:
{
uint64_t v___x_1247_; 
v___x_1247_ = lean_uint64_once(&l_instInhabitedInt64___closed__0, &l_instInhabitedInt64___closed__0_once, _init_l_instInhabitedInt64___closed__0);
return v___x_1247_;
}
}
static lean_object* _init_l_instLTInt64(void){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_box(0);
return v___x_1260_;
}
}
static lean_object* _init_l_instLEInt64(void){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_box(0);
return v___x_1261_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt64(uint64_t v_a_1274_, uint64_t v_b_1275_){
_start:
{
uint8_t v___x_1276_; 
v___x_1276_ = lean_int64_dec_eq(v_a_1274_, v_b_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt64___boxed(lean_object* v_a_1277_, lean_object* v_b_1278_){
_start:
{
uint64_t v_a_boxed_1279_; uint64_t v_b_boxed_1280_; uint8_t v_res_1281_; lean_object* v_r_1282_; 
v_a_boxed_1279_ = lean_unbox_uint64(v_a_1277_);
lean_dec_ref(v_a_1277_);
v_b_boxed_1280_ = lean_unbox_uint64(v_b_1278_);
lean_dec_ref(v_b_1278_);
v_res_1281_ = l_instDecidableEqInt64(v_a_boxed_1279_, v_b_boxed_1280_);
v_r_1282_ = lean_box(v_res_1281_);
return v_r_1282_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt64___boxed(lean_object* v_b_1284_){
_start:
{
uint8_t v_b_boxed_1285_; uint64_t v_res_1286_; lean_object* v_r_1287_; 
v_b_boxed_1285_ = lean_unbox(v_b_1284_);
v_res_1286_ = lean_bool_to_int64(v_b_boxed_1285_);
v_r_1287_ = lean_box_uint64(v_res_1286_);
return v_r_1287_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLt___boxed(lean_object* v_a_1290_, lean_object* v_b_1291_){
_start:
{
uint64_t v_a_boxed_1292_; uint64_t v_b_boxed_1293_; uint8_t v_res_1294_; lean_object* v_r_1295_; 
v_a_boxed_1292_ = lean_unbox_uint64(v_a_1290_);
lean_dec_ref(v_a_1290_);
v_b_boxed_1293_ = lean_unbox_uint64(v_b_1291_);
lean_dec_ref(v_b_1291_);
v_res_1294_ = lean_int64_dec_lt(v_a_boxed_1292_, v_b_boxed_1293_);
v_r_1295_ = lean_box(v_res_1294_);
return v_r_1295_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLe___boxed(lean_object* v_a_1298_, lean_object* v_b_1299_){
_start:
{
uint64_t v_a_boxed_1300_; uint64_t v_b_boxed_1301_; uint8_t v_res_1302_; lean_object* v_r_1303_; 
v_a_boxed_1300_ = lean_unbox_uint64(v_a_1298_);
lean_dec_ref(v_a_1298_);
v_b_boxed_1301_ = lean_unbox_uint64(v_b_1299_);
lean_dec_ref(v_b_1299_);
v_res_1302_ = lean_int64_dec_le(v_a_boxed_1300_, v_b_boxed_1301_);
v_r_1303_ = lean_box(v_res_1302_);
return v_r_1303_;
}
}
LEAN_EXPORT uint64_t l_instMaxInt64___lam__0(uint64_t v_x_1304_, uint64_t v_y_1305_){
_start:
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_int64_dec_le(v_x_1304_, v_y_1305_);
if (v___x_1306_ == 0)
{
return v_x_1304_;
}
else
{
return v_y_1305_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt64___lam__0___boxed(lean_object* v_x_1307_, lean_object* v_y_1308_){
_start:
{
uint64_t v_x_boxed_1309_; uint64_t v_y_boxed_1310_; uint64_t v_res_1311_; lean_object* v_r_1312_; 
v_x_boxed_1309_ = lean_unbox_uint64(v_x_1307_);
lean_dec_ref(v_x_1307_);
v_y_boxed_1310_ = lean_unbox_uint64(v_y_1308_);
lean_dec_ref(v_y_1308_);
v_res_1311_ = l_instMaxInt64___lam__0(v_x_boxed_1309_, v_y_boxed_1310_);
v_r_1312_ = lean_box_uint64(v_res_1311_);
return v_r_1312_;
}
}
LEAN_EXPORT uint64_t l_instMinInt64___lam__0(uint64_t v_x_1315_, uint64_t v_y_1316_){
_start:
{
uint8_t v___x_1317_; 
v___x_1317_ = lean_int64_dec_le(v_x_1315_, v_y_1316_);
if (v___x_1317_ == 0)
{
return v_y_1316_;
}
else
{
return v_x_1315_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt64___lam__0___boxed(lean_object* v_x_1318_, lean_object* v_y_1319_){
_start:
{
uint64_t v_x_boxed_1320_; uint64_t v_y_boxed_1321_; uint64_t v_res_1322_; lean_object* v_r_1323_; 
v_x_boxed_1320_ = lean_unbox_uint64(v_x_1318_);
lean_dec_ref(v_x_1318_);
v_y_boxed_1321_ = lean_unbox_uint64(v_y_1319_);
lean_dec_ref(v_y_1319_);
v_res_1322_ = l_instMinInt64___lam__0(v_x_boxed_1320_, v_y_boxed_1321_);
v_r_1323_ = lean_box_uint64(v_res_1322_);
return v_r_1323_;
}
}
static lean_object* _init_l_ISize_size___closed__0(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1326_ = l_System_Platform_numBits;
v___x_1327_ = lean_unsigned_to_nat(2u);
v___x_1328_ = lean_nat_pow(v___x_1327_, v___x_1326_);
return v___x_1328_;
}
}
static lean_object* _init_l_ISize_size(void){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_obj_once(&l_ISize_size___closed__0, &l_ISize_size___closed__0_once, _init_l_ISize_size___closed__0);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_ISize_toBitVec(size_t v_x_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_usize_to_nat(v_x_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_ISize_toBitVec___boxed(lean_object* v_x_1332_){
_start:
{
size_t v_x_boxed_1333_; lean_object* v_res_1334_; 
v_x_boxed_1333_ = lean_unbox_usize(v_x_1332_);
lean_dec(v_x_1332_);
v_res_1334_ = l_ISize_toBitVec(v_x_boxed_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT size_t l_USize_toISize(size_t v_i_1335_){
_start:
{
return v_i_1335_;
}
}
LEAN_EXPORT lean_object* l_USize_toISize___boxed(lean_object* v_i_1336_){
_start:
{
size_t v_i_boxed_1337_; size_t v_res_1338_; lean_object* v_r_1339_; 
v_i_boxed_1337_ = lean_unbox_usize(v_i_1336_);
lean_dec(v_i_1336_);
v_res_1338_ = l_USize_toISize(v_i_boxed_1337_);
v_r_1339_ = lean_box_usize(v_res_1338_);
return v_r_1339_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofInt___boxed(lean_object* v_i_1341_){
_start:
{
size_t v_res_1342_; lean_object* v_r_1343_; 
v_res_1342_ = lean_isize_of_int(v_i_1341_);
lean_dec(v_i_1341_);
v_r_1343_ = lean_box_usize(v_res_1342_);
return v_r_1343_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofNat___boxed(lean_object* v_n_1345_){
_start:
{
size_t v_res_1346_; lean_object* v_r_1347_; 
v_res_1346_ = lean_isize_of_nat(v_n_1345_);
lean_dec(v_n_1345_);
v_r_1347_ = lean_box_usize(v_res_1346_);
return v_r_1347_;
}
}
LEAN_EXPORT size_t l_Int_toISize(lean_object* v_i_1348_){
_start:
{
size_t v___x_1349_; 
v___x_1349_ = lean_isize_of_int(v_i_1348_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Int_toISize___boxed(lean_object* v_i_1350_){
_start:
{
size_t v_res_1351_; lean_object* v_r_1352_; 
v_res_1351_ = l_Int_toISize(v_i_1350_);
lean_dec(v_i_1350_);
v_r_1352_ = lean_box_usize(v_res_1351_);
return v_r_1352_;
}
}
LEAN_EXPORT size_t l_Nat_toISize(lean_object* v_n_1353_){
_start:
{
size_t v___x_1354_; 
v___x_1354_ = lean_isize_of_nat(v_n_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Nat_toISize___boxed(lean_object* v_n_1355_){
_start:
{
size_t v_res_1356_; lean_object* v_r_1357_; 
v_res_1356_ = l_Nat_toISize(v_n_1355_);
lean_dec(v_n_1355_);
v_r_1357_ = lean_box_usize(v_res_1356_);
return v_r_1357_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt___boxed(lean_object* v_i_1359_){
_start:
{
size_t v_i_boxed_1360_; lean_object* v_res_1361_; 
v_i_boxed_1360_ = lean_unbox_usize(v_i_1359_);
lean_dec(v_i_1359_);
v_res_1361_ = lean_isize_to_int(v_i_boxed_1360_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg(size_t v_i_1362_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_isize_to_int(v_i_1362_);
v___x_1364_ = l_Int_toNat(v___x_1363_);
lean_dec(v___x_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg___boxed(lean_object* v_i_1365_){
_start:
{
size_t v_i_boxed_1366_; lean_object* v_res_1367_; 
v_i_boxed_1366_ = lean_unbox_usize(v_i_1365_);
lean_dec(v_i_1365_);
v_res_1367_ = l_ISize_toNatClampNeg(v_i_boxed_1366_);
return v_res_1367_;
}
}
LEAN_EXPORT size_t l_ISize_ofBitVec(lean_object* v_b_1368_){
_start:
{
size_t v___x_1369_; 
v___x_1369_ = lean_usize_of_nat_mk(v_b_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofBitVec___boxed(lean_object* v_b_1370_){
_start:
{
size_t v_res_1371_; lean_object* v_r_1372_; 
v_res_1371_ = l_ISize_ofBitVec(v_b_1370_);
v_r_1372_ = lean_box_usize(v_res_1371_);
return v_r_1372_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt8___boxed(lean_object* v_a_1374_){
_start:
{
size_t v_a_boxed_1375_; uint8_t v_res_1376_; lean_object* v_r_1377_; 
v_a_boxed_1375_ = lean_unbox_usize(v_a_1374_);
lean_dec(v_a_1374_);
v_res_1376_ = lean_isize_to_int8(v_a_boxed_1375_);
v_r_1377_ = lean_box(v_res_1376_);
return v_r_1377_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt16___boxed(lean_object* v_a_1379_){
_start:
{
size_t v_a_boxed_1380_; uint16_t v_res_1381_; lean_object* v_r_1382_; 
v_a_boxed_1380_ = lean_unbox_usize(v_a_1379_);
lean_dec(v_a_1379_);
v_res_1381_ = lean_isize_to_int16(v_a_boxed_1380_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt32___boxed(lean_object* v_a_1384_){
_start:
{
size_t v_a_boxed_1385_; uint32_t v_res_1386_; lean_object* v_r_1387_; 
v_a_boxed_1385_ = lean_unbox_usize(v_a_1384_);
lean_dec(v_a_1384_);
v_res_1386_ = lean_isize_to_int32(v_a_boxed_1385_);
v_r_1387_ = lean_box_uint32(v_res_1386_);
return v_r_1387_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt64___boxed(lean_object* v_a_1389_){
_start:
{
size_t v_a_boxed_1390_; uint64_t v_res_1391_; lean_object* v_r_1392_; 
v_a_boxed_1390_ = lean_unbox_usize(v_a_1389_);
lean_dec(v_a_1389_);
v_res_1391_ = lean_isize_to_int64(v_a_boxed_1390_);
v_r_1392_ = lean_box_uint64(v_res_1391_);
return v_r_1392_;
}
}
LEAN_EXPORT lean_object* l_Int8_toISize___boxed(lean_object* v_a_1394_){
_start:
{
uint8_t v_a_boxed_1395_; size_t v_res_1396_; lean_object* v_r_1397_; 
v_a_boxed_1395_ = lean_unbox(v_a_1394_);
v_res_1396_ = lean_int8_to_isize(v_a_boxed_1395_);
v_r_1397_ = lean_box_usize(v_res_1396_);
return v_r_1397_;
}
}
LEAN_EXPORT lean_object* l_Int16_toISize___boxed(lean_object* v_a_1399_){
_start:
{
uint16_t v_a_boxed_1400_; size_t v_res_1401_; lean_object* v_r_1402_; 
v_a_boxed_1400_ = lean_unbox(v_a_1399_);
v_res_1401_ = lean_int16_to_isize(v_a_boxed_1400_);
v_r_1402_ = lean_box_usize(v_res_1401_);
return v_r_1402_;
}
}
LEAN_EXPORT lean_object* l_Int32_toISize___boxed(lean_object* v_a_1404_){
_start:
{
uint32_t v_a_boxed_1405_; size_t v_res_1406_; lean_object* v_r_1407_; 
v_a_boxed_1405_ = lean_unbox_uint32(v_a_1404_);
lean_dec(v_a_1404_);
v_res_1406_ = lean_int32_to_isize(v_a_boxed_1405_);
v_r_1407_ = lean_box_usize(v_res_1406_);
return v_r_1407_;
}
}
LEAN_EXPORT lean_object* l_Int64_toISize___boxed(lean_object* v_a_1409_){
_start:
{
uint64_t v_a_boxed_1410_; size_t v_res_1411_; lean_object* v_r_1412_; 
v_a_boxed_1410_ = lean_unbox_uint64(v_a_1409_);
lean_dec_ref(v_a_1409_);
v_res_1411_ = lean_int64_to_isize(v_a_boxed_1410_);
v_r_1412_ = lean_box_usize(v_res_1411_);
return v_r_1412_;
}
}
LEAN_EXPORT lean_object* l_ISize_neg___boxed(lean_object* v_i_1414_){
_start:
{
size_t v_i_boxed_1415_; size_t v_res_1416_; lean_object* v_r_1417_; 
v_i_boxed_1415_ = lean_unbox_usize(v_i_1414_);
lean_dec(v_i_1414_);
v_res_1416_ = lean_isize_neg(v_i_boxed_1415_);
v_r_1417_ = lean_box_usize(v_res_1416_);
return v_r_1417_;
}
}
LEAN_EXPORT lean_object* l_instToStringISize___lam__0(size_t v_i_1418_){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_isize_to_int(v_i_1418_);
v___x_1420_ = l_Int_repr(v___x_1419_);
lean_dec(v___x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_instToStringISize___lam__0___boxed(lean_object* v_i_1421_){
_start:
{
size_t v_i_boxed_1422_; lean_object* v_res_1423_; 
v_i_boxed_1422_ = lean_unbox_usize(v_i_1421_);
lean_dec(v_i_1421_);
v_res_1423_ = l_instToStringISize___lam__0(v_i_boxed_1422_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_instReprISize___lam__0(size_t v_i_1426_, lean_object* v_prec_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1428_ = lean_isize_to_int(v_i_1426_);
v___x_1429_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_1430_ = lean_int_dec_lt(v___x_1428_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = l_Int_repr(v___x_1428_);
lean_dec(v___x_1428_);
v___x_1432_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = l_Int_repr(v___x_1428_);
lean_dec(v___x_1428_);
v___x_1434_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
v___x_1435_ = l_Repr_addAppParen(v___x_1434_, v_prec_1427_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l_instReprISize___lam__0___boxed(lean_object* v_i_1436_, lean_object* v_prec_1437_){
_start:
{
size_t v_i_boxed_1438_; lean_object* v_res_1439_; 
v_i_boxed_1438_ = lean_unbox_usize(v_i_1436_);
lean_dec(v_i_1436_);
v_res_1439_ = l_instReprISize___lam__0(v_i_boxed_1438_, v_prec_1437_);
lean_dec(v_prec_1437_);
return v_res_1439_;
}
}
static lean_object* _init_l_instReprAtomISize(void){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_box(0);
return v___x_1442_;
}
}
LEAN_EXPORT size_t l_ISize_instOfNat(lean_object* v_n_1445_){
_start:
{
size_t v___x_1446_; 
v___x_1446_ = lean_isize_of_nat(v_n_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_ISize_instOfNat___boxed(lean_object* v_n_1447_){
_start:
{
size_t v_res_1448_; lean_object* v_r_1449_; 
v_res_1448_ = l_ISize_instOfNat(v_n_1447_);
lean_dec(v_n_1447_);
v_r_1449_ = lean_box_usize(v_res_1448_);
return v_r_1449_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__0(void){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_unsigned_to_nat(2u);
v___x_1453_ = lean_nat_to_int(v___x_1452_);
return v___x_1453_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__1(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = lean_unsigned_to_nat(1u);
v___x_1455_ = l_System_Platform_numBits;
v___x_1456_ = lean_nat_sub(v___x_1455_, v___x_1454_);
return v___x_1456_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__2(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = lean_obj_once(&l_ISize_maxValue___closed__1, &l_ISize_maxValue___closed__1_once, _init_l_ISize_maxValue___closed__1);
v___x_1458_ = lean_obj_once(&l_ISize_maxValue___closed__0, &l_ISize_maxValue___closed__0_once, _init_l_ISize_maxValue___closed__0);
v___x_1459_ = l_Int_pow(v___x_1458_, v___x_1457_);
return v___x_1459_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__3(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_unsigned_to_nat(1u);
v___x_1461_ = lean_nat_to_int(v___x_1460_);
return v___x_1461_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__4(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = lean_obj_once(&l_ISize_maxValue___closed__3, &l_ISize_maxValue___closed__3_once, _init_l_ISize_maxValue___closed__3);
v___x_1463_ = lean_obj_once(&l_ISize_maxValue___closed__2, &l_ISize_maxValue___closed__2_once, _init_l_ISize_maxValue___closed__2);
v___x_1464_ = lean_int_sub(v___x_1463_, v___x_1462_);
return v___x_1464_;
}
}
static size_t _init_l_ISize_maxValue___closed__5(void){
_start:
{
lean_object* v___x_1465_; size_t v___x_1466_; 
v___x_1465_ = lean_obj_once(&l_ISize_maxValue___closed__4, &l_ISize_maxValue___closed__4_once, _init_l_ISize_maxValue___closed__4);
v___x_1466_ = lean_isize_of_int(v___x_1465_);
return v___x_1466_;
}
}
static size_t _init_l_ISize_maxValue(void){
_start:
{
size_t v___x_1467_; 
v___x_1467_ = lean_usize_once(&l_ISize_maxValue___closed__5, &l_ISize_maxValue___closed__5_once, _init_l_ISize_maxValue___closed__5);
return v___x_1467_;
}
}
static lean_object* _init_l_ISize_minValue___closed__0(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_obj_once(&l_ISize_maxValue___closed__2, &l_ISize_maxValue___closed__2_once, _init_l_ISize_maxValue___closed__2);
v___x_1469_ = lean_int_neg(v___x_1468_);
return v___x_1469_;
}
}
static size_t _init_l_ISize_minValue___closed__1(void){
_start:
{
lean_object* v___x_1470_; size_t v___x_1471_; 
v___x_1470_ = lean_obj_once(&l_ISize_minValue___closed__0, &l_ISize_minValue___closed__0_once, _init_l_ISize_minValue___closed__0);
v___x_1471_ = lean_isize_of_int(v___x_1470_);
return v___x_1471_;
}
}
static size_t _init_l_ISize_minValue(void){
_start:
{
size_t v___x_1472_; 
v___x_1472_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
return v___x_1472_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntLE___redArg(lean_object* v_i_1473_){
_start:
{
size_t v___x_1474_; 
v___x_1474_ = lean_isize_of_int(v_i_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntLE___redArg___boxed(lean_object* v_i_1475_){
_start:
{
size_t v_res_1476_; lean_object* v_r_1477_; 
v_res_1476_ = l_ISize_ofIntLE___redArg(v_i_1475_);
lean_dec(v_i_1475_);
v_r_1477_ = lean_box_usize(v_res_1476_);
return v_r_1477_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntLE(lean_object* v_i_1478_, lean_object* v___hl_1479_, lean_object* v___hr_1480_){
_start:
{
size_t v___x_1481_; 
v___x_1481_ = lean_isize_of_int(v_i_1478_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntLE___boxed(lean_object* v_i_1482_, lean_object* v___hl_1483_, lean_object* v___hr_1484_){
_start:
{
size_t v_res_1485_; lean_object* v_r_1486_; 
v_res_1485_ = l_ISize_ofIntLE(v_i_1482_, v___hl_1483_, v___hr_1484_);
lean_dec(v_i_1482_);
v_r_1486_ = lean_box_usize(v_res_1485_);
return v_r_1486_;
}
}
static lean_object* _init_l_ISize_ofIntTruncate___closed__0(void){
_start:
{
size_t v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
v___x_1488_ = lean_isize_to_int(v___x_1487_);
return v___x_1488_;
}
}
static lean_object* _init_l_ISize_ofIntTruncate___closed__1(void){
_start:
{
size_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_usize_once(&l_ISize_maxValue___closed__5, &l_ISize_maxValue___closed__5_once, _init_l_ISize_maxValue___closed__5);
v___x_1490_ = lean_isize_to_int(v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntTruncate(lean_object* v_i_1491_){
_start:
{
size_t v___x_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1492_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
v___x_1493_ = lean_obj_once(&l_ISize_ofIntTruncate___closed__0, &l_ISize_ofIntTruncate___closed__0_once, _init_l_ISize_ofIntTruncate___closed__0);
v___x_1494_ = lean_int_dec_le(v___x_1493_, v_i_1491_);
if (v___x_1494_ == 0)
{
return v___x_1492_;
}
else
{
lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1495_ = lean_obj_once(&l_ISize_ofIntTruncate___closed__1, &l_ISize_ofIntTruncate___closed__1_once, _init_l_ISize_ofIntTruncate___closed__1);
v___x_1496_ = lean_int_dec_le(v_i_1491_, v___x_1495_);
if (v___x_1496_ == 0)
{
return v___x_1492_;
}
else
{
size_t v___x_1497_; 
v___x_1497_ = lean_isize_of_int(v_i_1491_);
return v___x_1497_;
}
}
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntTruncate___boxed(lean_object* v_i_1498_){
_start:
{
size_t v_res_1499_; lean_object* v_r_1500_; 
v_res_1499_ = l_ISize_ofIntTruncate(v_i_1498_);
lean_dec(v_i_1498_);
v_r_1500_ = lean_box_usize(v_res_1499_);
return v_r_1500_;
}
}
LEAN_EXPORT lean_object* l_ISize_add___boxed(lean_object* v_a_1503_, lean_object* v_b_1504_){
_start:
{
size_t v_a_boxed_1505_; size_t v_b_boxed_1506_; size_t v_res_1507_; lean_object* v_r_1508_; 
v_a_boxed_1505_ = lean_unbox_usize(v_a_1503_);
lean_dec(v_a_1503_);
v_b_boxed_1506_ = lean_unbox_usize(v_b_1504_);
lean_dec(v_b_1504_);
v_res_1507_ = lean_isize_add(v_a_boxed_1505_, v_b_boxed_1506_);
v_r_1508_ = lean_box_usize(v_res_1507_);
return v_r_1508_;
}
}
LEAN_EXPORT lean_object* l_ISize_sub___boxed(lean_object* v_a_1511_, lean_object* v_b_1512_){
_start:
{
size_t v_a_boxed_1513_; size_t v_b_boxed_1514_; size_t v_res_1515_; lean_object* v_r_1516_; 
v_a_boxed_1513_ = lean_unbox_usize(v_a_1511_);
lean_dec(v_a_1511_);
v_b_boxed_1514_ = lean_unbox_usize(v_b_1512_);
lean_dec(v_b_1512_);
v_res_1515_ = lean_isize_sub(v_a_boxed_1513_, v_b_boxed_1514_);
v_r_1516_ = lean_box_usize(v_res_1515_);
return v_r_1516_;
}
}
LEAN_EXPORT lean_object* l_ISize_mul___boxed(lean_object* v_a_1519_, lean_object* v_b_1520_){
_start:
{
size_t v_a_boxed_1521_; size_t v_b_boxed_1522_; size_t v_res_1523_; lean_object* v_r_1524_; 
v_a_boxed_1521_ = lean_unbox_usize(v_a_1519_);
lean_dec(v_a_1519_);
v_b_boxed_1522_ = lean_unbox_usize(v_b_1520_);
lean_dec(v_b_1520_);
v_res_1523_ = lean_isize_mul(v_a_boxed_1521_, v_b_boxed_1522_);
v_r_1524_ = lean_box_usize(v_res_1523_);
return v_r_1524_;
}
}
LEAN_EXPORT lean_object* l_ISize_div___boxed(lean_object* v_a_1527_, lean_object* v_b_1528_){
_start:
{
size_t v_a_boxed_1529_; size_t v_b_boxed_1530_; size_t v_res_1531_; lean_object* v_r_1532_; 
v_a_boxed_1529_ = lean_unbox_usize(v_a_1527_);
lean_dec(v_a_1527_);
v_b_boxed_1530_ = lean_unbox_usize(v_b_1528_);
lean_dec(v_b_1528_);
v_res_1531_ = lean_isize_div(v_a_boxed_1529_, v_b_boxed_1530_);
v_r_1532_ = lean_box_usize(v_res_1531_);
return v_r_1532_;
}
}
static size_t _init_l_ISize_pow___closed__0(void){
_start:
{
lean_object* v___x_1533_; size_t v___x_1534_; 
v___x_1533_ = lean_unsigned_to_nat(1u);
v___x_1534_ = lean_isize_of_nat(v___x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT size_t l_ISize_pow(size_t v_x_1535_, lean_object* v_n_1536_){
_start:
{
lean_object* v_zero_1537_; uint8_t v_isZero_1538_; 
v_zero_1537_ = lean_unsigned_to_nat(0u);
v_isZero_1538_ = lean_nat_dec_eq(v_n_1536_, v_zero_1537_);
if (v_isZero_1538_ == 1)
{
size_t v___x_1539_; 
v___x_1539_ = lean_usize_once(&l_ISize_pow___closed__0, &l_ISize_pow___closed__0_once, _init_l_ISize_pow___closed__0);
return v___x_1539_;
}
else
{
lean_object* v_one_1540_; lean_object* v_n_1541_; size_t v___x_1542_; size_t v___x_1543_; 
v_one_1540_ = lean_unsigned_to_nat(1u);
v_n_1541_ = lean_nat_sub(v_n_1536_, v_one_1540_);
v___x_1542_ = l_ISize_pow(v_x_1535_, v_n_1541_);
lean_dec(v_n_1541_);
v___x_1543_ = lean_isize_mul(v___x_1542_, v_x_1535_);
return v___x_1543_;
}
}
}
LEAN_EXPORT lean_object* l_ISize_pow___boxed(lean_object* v_x_1544_, lean_object* v_n_1545_){
_start:
{
size_t v_x_boxed_1546_; size_t v_res_1547_; lean_object* v_r_1548_; 
v_x_boxed_1546_ = lean_unbox_usize(v_x_1544_);
lean_dec(v_x_1544_);
v_res_1547_ = l_ISize_pow(v_x_boxed_1546_, v_n_1545_);
lean_dec(v_n_1545_);
v_r_1548_ = lean_box_usize(v_res_1547_);
return v_r_1548_;
}
}
LEAN_EXPORT lean_object* l_ISize_mod___boxed(lean_object* v_a_1551_, lean_object* v_b_1552_){
_start:
{
size_t v_a_boxed_1553_; size_t v_b_boxed_1554_; size_t v_res_1555_; lean_object* v_r_1556_; 
v_a_boxed_1553_ = lean_unbox_usize(v_a_1551_);
lean_dec(v_a_1551_);
v_b_boxed_1554_ = lean_unbox_usize(v_b_1552_);
lean_dec(v_b_1552_);
v_res_1555_ = lean_isize_mod(v_a_boxed_1553_, v_b_boxed_1554_);
v_r_1556_ = lean_box_usize(v_res_1555_);
return v_r_1556_;
}
}
LEAN_EXPORT lean_object* l_ISize_land___boxed(lean_object* v_a_1559_, lean_object* v_b_1560_){
_start:
{
size_t v_a_boxed_1561_; size_t v_b_boxed_1562_; size_t v_res_1563_; lean_object* v_r_1564_; 
v_a_boxed_1561_ = lean_unbox_usize(v_a_1559_);
lean_dec(v_a_1559_);
v_b_boxed_1562_ = lean_unbox_usize(v_b_1560_);
lean_dec(v_b_1560_);
v_res_1563_ = lean_isize_land(v_a_boxed_1561_, v_b_boxed_1562_);
v_r_1564_ = lean_box_usize(v_res_1563_);
return v_r_1564_;
}
}
LEAN_EXPORT lean_object* l_ISize_lor___boxed(lean_object* v_a_1567_, lean_object* v_b_1568_){
_start:
{
size_t v_a_boxed_1569_; size_t v_b_boxed_1570_; size_t v_res_1571_; lean_object* v_r_1572_; 
v_a_boxed_1569_ = lean_unbox_usize(v_a_1567_);
lean_dec(v_a_1567_);
v_b_boxed_1570_ = lean_unbox_usize(v_b_1568_);
lean_dec(v_b_1568_);
v_res_1571_ = lean_isize_lor(v_a_boxed_1569_, v_b_boxed_1570_);
v_r_1572_ = lean_box_usize(v_res_1571_);
return v_r_1572_;
}
}
LEAN_EXPORT lean_object* l_ISize_xor___boxed(lean_object* v_a_1575_, lean_object* v_b_1576_){
_start:
{
size_t v_a_boxed_1577_; size_t v_b_boxed_1578_; size_t v_res_1579_; lean_object* v_r_1580_; 
v_a_boxed_1577_ = lean_unbox_usize(v_a_1575_);
lean_dec(v_a_1575_);
v_b_boxed_1578_ = lean_unbox_usize(v_b_1576_);
lean_dec(v_b_1576_);
v_res_1579_ = lean_isize_xor(v_a_boxed_1577_, v_b_boxed_1578_);
v_r_1580_ = lean_box_usize(v_res_1579_);
return v_r_1580_;
}
}
LEAN_EXPORT lean_object* l_ISize_shiftLeft___boxed(lean_object* v_a_1583_, lean_object* v_b_1584_){
_start:
{
size_t v_a_boxed_1585_; size_t v_b_boxed_1586_; size_t v_res_1587_; lean_object* v_r_1588_; 
v_a_boxed_1585_ = lean_unbox_usize(v_a_1583_);
lean_dec(v_a_1583_);
v_b_boxed_1586_ = lean_unbox_usize(v_b_1584_);
lean_dec(v_b_1584_);
v_res_1587_ = lean_isize_shift_left(v_a_boxed_1585_, v_b_boxed_1586_);
v_r_1588_ = lean_box_usize(v_res_1587_);
return v_r_1588_;
}
}
LEAN_EXPORT lean_object* l_ISize_shiftRight___boxed(lean_object* v_a_1591_, lean_object* v_b_1592_){
_start:
{
size_t v_a_boxed_1593_; size_t v_b_boxed_1594_; size_t v_res_1595_; lean_object* v_r_1596_; 
v_a_boxed_1593_ = lean_unbox_usize(v_a_1591_);
lean_dec(v_a_1591_);
v_b_boxed_1594_ = lean_unbox_usize(v_b_1592_);
lean_dec(v_b_1592_);
v_res_1595_ = lean_isize_shift_right(v_a_boxed_1593_, v_b_boxed_1594_);
v_r_1596_ = lean_box_usize(v_res_1595_);
return v_r_1596_;
}
}
LEAN_EXPORT lean_object* l_ISize_complement___boxed(lean_object* v_a_1598_){
_start:
{
size_t v_a_boxed_1599_; size_t v_res_1600_; lean_object* v_r_1601_; 
v_a_boxed_1599_ = lean_unbox_usize(v_a_1598_);
lean_dec(v_a_1598_);
v_res_1600_ = lean_isize_complement(v_a_boxed_1599_);
v_r_1601_ = lean_box_usize(v_res_1600_);
return v_r_1601_;
}
}
LEAN_EXPORT lean_object* l_ISize_abs___boxed(lean_object* v_a_1603_){
_start:
{
size_t v_a_boxed_1604_; size_t v_res_1605_; lean_object* v_r_1606_; 
v_a_boxed_1604_ = lean_unbox_usize(v_a_1603_);
lean_dec(v_a_1603_);
v_res_1605_ = lean_isize_abs(v_a_boxed_1604_);
v_r_1606_ = lean_box_usize(v_res_1605_);
return v_r_1606_;
}
}
LEAN_EXPORT lean_object* l_ISize_decEq___boxed(lean_object* v_a_1609_, lean_object* v_b_1610_){
_start:
{
size_t v_a_boxed_1611_; size_t v_b_boxed_1612_; uint8_t v_res_1613_; lean_object* v_r_1614_; 
v_a_boxed_1611_ = lean_unbox_usize(v_a_1609_);
lean_dec(v_a_1609_);
v_b_boxed_1612_ = lean_unbox_usize(v_b_1610_);
lean_dec(v_b_1610_);
v_res_1613_ = lean_isize_dec_eq(v_a_boxed_1611_, v_b_boxed_1612_);
v_r_1614_ = lean_box(v_res_1613_);
return v_r_1614_;
}
}
static size_t _init_l_instInhabitedISize___closed__0(void){
_start:
{
lean_object* v___x_1615_; size_t v___x_1616_; 
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = lean_isize_of_nat(v___x_1615_);
return v___x_1616_;
}
}
static size_t _init_l_instInhabitedISize(void){
_start:
{
size_t v___x_1617_; 
v___x_1617_ = lean_usize_once(&l_instInhabitedISize___closed__0, &l_instInhabitedISize___closed__0_once, _init_l_instInhabitedISize___closed__0);
return v___x_1617_;
}
}
static lean_object* _init_l_instLTISize(void){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = lean_box(0);
return v___x_1630_;
}
}
static lean_object* _init_l_instLEISize(void){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = lean_box(0);
return v___x_1631_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqISize(size_t v_a_1644_, size_t v_b_1645_){
_start:
{
uint8_t v___x_1646_; 
v___x_1646_ = lean_isize_dec_eq(v_a_1644_, v_b_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqISize___boxed(lean_object* v_a_1647_, lean_object* v_b_1648_){
_start:
{
size_t v_a_boxed_1649_; size_t v_b_boxed_1650_; uint8_t v_res_1651_; lean_object* v_r_1652_; 
v_a_boxed_1649_ = lean_unbox_usize(v_a_1647_);
lean_dec(v_a_1647_);
v_b_boxed_1650_ = lean_unbox_usize(v_b_1648_);
lean_dec(v_b_1648_);
v_res_1651_ = l_instDecidableEqISize(v_a_boxed_1649_, v_b_boxed_1650_);
v_r_1652_ = lean_box(v_res_1651_);
return v_r_1652_;
}
}
LEAN_EXPORT lean_object* l_Bool_toISize___boxed(lean_object* v_b_1654_){
_start:
{
uint8_t v_b_boxed_1655_; size_t v_res_1656_; lean_object* v_r_1657_; 
v_b_boxed_1655_ = lean_unbox(v_b_1654_);
v_res_1656_ = lean_bool_to_isize(v_b_boxed_1655_);
v_r_1657_ = lean_box_usize(v_res_1656_);
return v_r_1657_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLt___boxed(lean_object* v_a_1660_, lean_object* v_b_1661_){
_start:
{
size_t v_a_boxed_1662_; size_t v_b_boxed_1663_; uint8_t v_res_1664_; lean_object* v_r_1665_; 
v_a_boxed_1662_ = lean_unbox_usize(v_a_1660_);
lean_dec(v_a_1660_);
v_b_boxed_1663_ = lean_unbox_usize(v_b_1661_);
lean_dec(v_b_1661_);
v_res_1664_ = lean_isize_dec_lt(v_a_boxed_1662_, v_b_boxed_1663_);
v_r_1665_ = lean_box(v_res_1664_);
return v_r_1665_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLe___boxed(lean_object* v_a_1668_, lean_object* v_b_1669_){
_start:
{
size_t v_a_boxed_1670_; size_t v_b_boxed_1671_; uint8_t v_res_1672_; lean_object* v_r_1673_; 
v_a_boxed_1670_ = lean_unbox_usize(v_a_1668_);
lean_dec(v_a_1668_);
v_b_boxed_1671_ = lean_unbox_usize(v_b_1669_);
lean_dec(v_b_1669_);
v_res_1672_ = lean_isize_dec_le(v_a_boxed_1670_, v_b_boxed_1671_);
v_r_1673_ = lean_box(v_res_1672_);
return v_r_1673_;
}
}
LEAN_EXPORT size_t l_instMaxISize___lam__0(size_t v_x_1674_, size_t v_y_1675_){
_start:
{
uint8_t v___x_1676_; 
v___x_1676_ = lean_isize_dec_le(v_x_1674_, v_y_1675_);
if (v___x_1676_ == 0)
{
return v_x_1674_;
}
else
{
return v_y_1675_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxISize___lam__0___boxed(lean_object* v_x_1677_, lean_object* v_y_1678_){
_start:
{
size_t v_x_boxed_1679_; size_t v_y_boxed_1680_; size_t v_res_1681_; lean_object* v_r_1682_; 
v_x_boxed_1679_ = lean_unbox_usize(v_x_1677_);
lean_dec(v_x_1677_);
v_y_boxed_1680_ = lean_unbox_usize(v_y_1678_);
lean_dec(v_y_1678_);
v_res_1681_ = l_instMaxISize___lam__0(v_x_boxed_1679_, v_y_boxed_1680_);
v_r_1682_ = lean_box_usize(v_res_1681_);
return v_r_1682_;
}
}
LEAN_EXPORT size_t l_instMinISize___lam__0(size_t v_x_1685_, size_t v_y_1686_){
_start:
{
uint8_t v___x_1687_; 
v___x_1687_ = lean_isize_dec_le(v_x_1685_, v_y_1686_);
if (v___x_1687_ == 0)
{
return v_y_1686_;
}
else
{
return v_x_1685_;
}
}
}
LEAN_EXPORT lean_object* l_instMinISize___lam__0___boxed(lean_object* v_x_1688_, lean_object* v_y_1689_){
_start:
{
size_t v_x_boxed_1690_; size_t v_y_boxed_1691_; size_t v_res_1692_; lean_object* v_r_1693_; 
v_x_boxed_1690_ = lean_unbox_usize(v_x_1688_);
lean_dec(v_x_1688_);
v_y_boxed_1691_ = lean_unbox_usize(v_y_1689_);
lean_dec(v_y_1689_);
v_res_1692_ = l_instMinISize___lam__0(v_x_boxed_1690_, v_y_boxed_1691_);
v_r_1693_ = lean_box_usize(v_res_1692_);
return v_r_1693_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Extra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int8_size = _init_l_Int8_size();
lean_mark_persistent(l_Int8_size);
l_instReprAtomInt8 = _init_l_instReprAtomInt8();
lean_mark_persistent(l_instReprAtomInt8);
l_Int8_maxValue = _init_l_Int8_maxValue();
l_Int8_minValue = _init_l_Int8_minValue();
l_instInhabitedInt8 = _init_l_instInhabitedInt8();
l_instLTInt8 = _init_l_instLTInt8();
lean_mark_persistent(l_instLTInt8);
l_instLEInt8 = _init_l_instLEInt8();
lean_mark_persistent(l_instLEInt8);
l_Int16_size = _init_l_Int16_size();
lean_mark_persistent(l_Int16_size);
l_instReprAtomInt16 = _init_l_instReprAtomInt16();
lean_mark_persistent(l_instReprAtomInt16);
l_Int16_maxValue = _init_l_Int16_maxValue();
l_Int16_minValue = _init_l_Int16_minValue();
l_instInhabitedInt16 = _init_l_instInhabitedInt16();
l_instLTInt16 = _init_l_instLTInt16();
lean_mark_persistent(l_instLTInt16);
l_instLEInt16 = _init_l_instLEInt16();
lean_mark_persistent(l_instLEInt16);
l_Int32_size = _init_l_Int32_size();
lean_mark_persistent(l_Int32_size);
l_instReprAtomInt32 = _init_l_instReprAtomInt32();
lean_mark_persistent(l_instReprAtomInt32);
l_Int32_maxValue = _init_l_Int32_maxValue();
l_Int32_minValue = _init_l_Int32_minValue();
l_instInhabitedInt32 = _init_l_instInhabitedInt32();
l_instLTInt32 = _init_l_instLTInt32();
lean_mark_persistent(l_instLTInt32);
l_instLEInt32 = _init_l_instLEInt32();
lean_mark_persistent(l_instLEInt32);
l_Int64_size = _init_l_Int64_size();
lean_mark_persistent(l_Int64_size);
l_instReprAtomInt64 = _init_l_instReprAtomInt64();
lean_mark_persistent(l_instReprAtomInt64);
l_Int64_maxValue = _init_l_Int64_maxValue();
l_Int64_minValue = _init_l_Int64_minValue();
l_instInhabitedInt64 = _init_l_instInhabitedInt64();
l_instLTInt64 = _init_l_instLTInt64();
lean_mark_persistent(l_instLTInt64);
l_instLEInt64 = _init_l_instLEInt64();
lean_mark_persistent(l_instLEInt64);
l_ISize_size = _init_l_ISize_size();
lean_mark_persistent(l_ISize_size);
l_instReprAtomISize = _init_l_instReprAtomISize();
lean_mark_persistent(l_instReprAtomISize);
l_ISize_maxValue = _init_l_ISize_maxValue();
l_ISize_minValue = _init_l_ISize_minValue();
l_instInhabitedISize = _init_l_instInhabitedISize();
l_instLTISize = _init_l_instLTISize();
lean_mark_persistent(l_instLTISize);
l_instLEISize = _init_l_instLEISize();
lean_mark_persistent(l_instLEISize);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_SInt_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_SInt_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
