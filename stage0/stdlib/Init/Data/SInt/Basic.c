// Lean compiler output
// Module: Init.Data.SInt.Basic
// Imports: public import Init.Data.UInt.Basic
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
LEAN_EXPORT lean_object* l_Int8_size;
lean_object* lean_uint8_to_nat(uint8_t);
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
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Int8_toNatClampNeg(uint8_t);
LEAN_EXPORT lean_object* l_Int8_toNatClampNeg___boxed(lean_object*);
uint8_t lean_uint8_of_nat_mk(lean_object*);
LEAN_EXPORT uint8_t l_Int8_ofBitVec(lean_object*);
LEAN_EXPORT lean_object* l_Int8_ofBitVec___boxed(lean_object*);
uint8_t lean_int8_neg(uint8_t);
LEAN_EXPORT lean_object* l_Int8_neg___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_instToStringInt8___lam__0___closed__0;
static const lean_string_object l_instToStringInt8___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_instToStringInt8___lam__0___closed__1 = (const lean_object*)&l_instToStringInt8___lam__0___closed__1_value;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instToStringInt8___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToStringInt8___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringInt8___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringInt8___closed__0 = (const lean_object*)&l_instToStringInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringInt8 = (const lean_object*)&l_instToStringInt8___closed__0_value;
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprInt8___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_instReprInt8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprInt8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprInt8___closed__0 = (const lean_object*)&l_instReprInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprInt8 = (const lean_object*)&l_instReprInt8___closed__0_value;
LEAN_EXPORT lean_object* l_instReprAtomInt8;
lean_object* l_UInt8_toUInt64___boxed(lean_object*);
static const lean_closure_object l_instHashableInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableInt8___closed__0 = (const lean_object*)&l_instHashableInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableInt8 = (const lean_object*)&l_instHashableInt8___closed__0_value;
LEAN_EXPORT uint8_t l_Int8_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Int8_instOfNat___boxed(lean_object*);
static const lean_closure_object l_Int8_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int8_instNeg___closed__0 = (const lean_object*)&l_Int8_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Int8_instNeg = (const lean_object*)&l_Int8_instNeg___closed__0_value;
static uint8_t l_Int8_maxValue___closed__0;
LEAN_EXPORT uint8_t l_Int8_maxValue;
static uint8_t l_Int8_minValue___closed__0;
static uint8_t l_Int8_minValue___closed__1;
LEAN_EXPORT uint8_t l_Int8_minValue;
LEAN_EXPORT uint8_t l_Int8_ofIntLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int8_ofIntLE___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Int8_ofIntLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int8_ofIntLE___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int8_ofIntTruncate___closed__0;
static lean_object* l_Int8_ofIntTruncate___closed__1;
uint8_t lean_int_dec_le(lean_object*, lean_object*);
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
static uint8_t l_Int8_pow___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* lean_uint16_to_nat(uint16_t);
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
uint16_t lean_uint16_of_nat_mk(lean_object*);
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
lean_object* l_UInt16_toUInt64___boxed(lean_object*);
static const lean_closure_object l_instHashableInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableInt16___closed__0 = (const lean_object*)&l_instHashableInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableInt16 = (const lean_object*)&l_instHashableInt16___closed__0_value;
LEAN_EXPORT uint16_t l_Int16_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Int16_instOfNat___boxed(lean_object*);
static const lean_closure_object l_Int16_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int16_instNeg___closed__0 = (const lean_object*)&l_Int16_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Int16_instNeg = (const lean_object*)&l_Int16_instNeg___closed__0_value;
static uint16_t l_Int16_maxValue___closed__0;
LEAN_EXPORT uint16_t l_Int16_maxValue;
static uint16_t l_Int16_minValue___closed__0;
static uint16_t l_Int16_minValue___closed__1;
LEAN_EXPORT uint16_t l_Int16_minValue;
LEAN_EXPORT uint16_t l_Int16_ofIntLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int16_ofIntLE___redArg___boxed(lean_object*);
LEAN_EXPORT uint16_t l_Int16_ofIntLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int16_ofIntLE___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int16_ofIntTruncate___closed__0;
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
lean_object* lean_uint32_to_nat(uint32_t);
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
uint32_t lean_uint32_of_nat_mk(lean_object*);
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
lean_object* l_UInt32_toUInt64___boxed(lean_object*);
static const lean_closure_object l_instHashableInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableInt32___closed__0 = (const lean_object*)&l_instHashableInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableInt32 = (const lean_object*)&l_instHashableInt32___closed__0_value;
LEAN_EXPORT uint32_t l_Int32_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Int32_instOfNat___boxed(lean_object*);
static const lean_closure_object l_Int32_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int32_instNeg___closed__0 = (const lean_object*)&l_Int32_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Int32_instNeg = (const lean_object*)&l_Int32_instNeg___closed__0_value;
static uint32_t l_Int32_maxValue___closed__0;
LEAN_EXPORT uint32_t l_Int32_maxValue;
static uint32_t l_Int32_minValue___closed__0;
static uint32_t l_Int32_minValue___closed__1;
LEAN_EXPORT uint32_t l_Int32_minValue;
LEAN_EXPORT uint32_t l_Int32_ofIntLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int32_ofIntLE___redArg___boxed(lean_object*);
LEAN_EXPORT uint32_t l_Int32_ofIntLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int32_ofIntLE___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int32_ofIntTruncate___closed__0;
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
static lean_object* l_Int64_size___closed__0;
LEAN_EXPORT lean_object* l_Int64_size;
lean_object* lean_uint64_to_nat(uint64_t);
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
uint64_t lean_uint64_of_nat_mk(lean_object*);
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
static uint64_t l_Int64_maxValue___closed__0;
LEAN_EXPORT uint64_t l_Int64_maxValue;
static lean_object* l_Int64_minValue___closed__0;
static uint64_t l_Int64_minValue___closed__1;
static uint64_t l_Int64_minValue___closed__2;
LEAN_EXPORT uint64_t l_Int64_minValue;
LEAN_EXPORT uint64_t l_Int64_ofIntLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Int64_ofIntLE___redArg___boxed(lean_object*);
LEAN_EXPORT uint64_t l_Int64_ofIntLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int64_ofIntLE___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int64_ofIntTruncate___closed__0;
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
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
static lean_object* l_ISize_size___closed__0;
LEAN_EXPORT lean_object* l_ISize_size;
lean_object* lean_usize_to_nat(size_t);
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
size_t lean_usize_of_nat_mk(lean_object*);
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
lean_object* l_USize_toUInt64___boxed(lean_object*);
static const lean_closure_object l_instHashableISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableISize___closed__0 = (const lean_object*)&l_instHashableISize___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableISize = (const lean_object*)&l_instHashableISize___closed__0_value;
LEAN_EXPORT size_t l_ISize_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_ISize_instOfNat___boxed(lean_object*);
static const lean_closure_object l_ISize_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ISize_instNeg___closed__0 = (const lean_object*)&l_ISize_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_ISize_instNeg = (const lean_object*)&l_ISize_instNeg___closed__0_value;
static lean_object* l_ISize_maxValue___closed__0;
static lean_object* l_ISize_maxValue___closed__1;
lean_object* l_Int_pow(lean_object*, lean_object*);
static lean_object* l_ISize_maxValue___closed__2;
static lean_object* l_ISize_maxValue___closed__3;
lean_object* lean_int_sub(lean_object*, lean_object*);
static lean_object* l_ISize_maxValue___closed__4;
static size_t l_ISize_maxValue___closed__5;
LEAN_EXPORT size_t l_ISize_maxValue;
lean_object* lean_int_neg(lean_object*);
static lean_object* l_ISize_minValue___closed__0;
static size_t l_ISize_minValue___closed__1;
LEAN_EXPORT size_t l_ISize_minValue;
LEAN_EXPORT size_t l_ISize_ofIntLE___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ISize_ofIntLE___redArg___boxed(lean_object*);
LEAN_EXPORT size_t l_ISize_ofIntLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ISize_ofIntLE___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_ISize_ofIntTruncate___closed__0;
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
static lean_object* _init_l_Int8_size() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(256u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Int8_toBitVec(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uint8_to_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int8_toBitVec___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Int8_toBitVec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_UInt8_toInt8(uint8_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt8_toInt8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_UInt8_toInt8(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int8_ofInt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_int8_of_int(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int8_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_int8_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Int_toInt8(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_int8_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_toInt8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Int_toInt8(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Nat_toInt8(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_int8_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Nat_toInt8(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lean_int8_to_int(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int8_toNatClampNeg(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_int8_to_int(x_1);
x_3 = l_Int_toNat(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int8_toNatClampNeg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Int8_toNatClampNeg(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Int8_ofBitVec(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_uint8_of_nat_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int8_ofBitVec___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Int8_ofBitVec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int8_neg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_int8_neg(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_instToStringInt8___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_instToStringInt8___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_int8_to_int(x_1);
x_3 = l_instToStringInt8___lam__0___closed__0;
x_4 = lean_int_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_nat_abs(x_2);
x_6 = l_Nat_reprFast(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_nat_abs(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = ((lean_object*)(l_instToStringInt8___lam__0___closed__1));
x_11 = lean_nat_add(x_9, x_8);
lean_dec(x_9);
x_12 = l_Nat_reprFast(x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec_ref(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_instToStringInt8___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_instToStringInt8___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprInt8___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_int8_to_int(x_1);
x_4 = l_instToStringInt8___lam__0___closed__0;
x_5 = lean_int_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Int_repr(x_3);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Int_repr(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Repr_addAppParen(x_9, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt8___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_instReprInt8___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_instReprAtomInt8() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Int8_instOfNat(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_int8_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int8_instOfNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Int8_instOfNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static uint8_t _init_l_Int8_maxValue___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_unsigned_to_nat(127u);
x_2 = lean_int8_of_nat(x_1);
return x_2;
}
}
static uint8_t _init_l_Int8_maxValue() {
_start:
{
uint8_t x_1; 
x_1 = l_Int8_maxValue___closed__0;
return x_1;
}
}
static uint8_t _init_l_Int8_minValue___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_unsigned_to_nat(128u);
x_2 = lean_int8_of_nat(x_1);
return x_2;
}
}
static uint8_t _init_l_Int8_minValue___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = l_Int8_minValue___closed__0;
x_2 = lean_int8_neg(x_1);
return x_2;
}
}
static uint8_t _init_l_Int8_minValue() {
_start:
{
uint8_t x_1; 
x_1 = l_Int8_minValue___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Int8_ofIntLE___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_int8_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int8_ofIntLE___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Int8_ofIntLE___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Int8_ofIntLE(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_int8_of_int(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int8_ofIntLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Int8_ofIntLE(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Int8_ofIntTruncate___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = l_Int8_minValue___closed__1;
x_2 = lean_int8_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int8_ofIntTruncate___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = l_Int8_maxValue___closed__0;
x_2 = lean_int8_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Int8_ofIntTruncate(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Int8_minValue___closed__1;
x_3 = l_Int8_ofIntTruncate___closed__0;
x_4 = lean_int_dec_le(x_3, x_1);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Int8_ofIntTruncate___closed__1;
x_6 = lean_int_dec_le(x_1, x_5);
if (x_6 == 0)
{
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_int8_of_int(x_1);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Int8_ofIntTruncate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Int8_ofIntTruncate(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int8_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int8_add(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int8_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int8_sub(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int8_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int8_mul(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int8_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int8_div(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint8_t _init_l_Int8_pow___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_int8_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Int8_pow(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
uint8_t x_5; 
x_5 = l_Int8_pow___closed__0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = l_Int8_pow(x_1, x_7);
lean_dec(x_7);
x_9 = lean_int8_mul(x_8, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Int8_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Int8_pow(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int8_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int8_mod(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int8_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int8_land(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int8_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int8_lor(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int8_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int8_xor(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int8_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int8_shift_left(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int8_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int8_shift_right(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int8_complement___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_int8_complement(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int8_abs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_int8_abs(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int8_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int8_dec_eq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint8_t _init_l_instInhabitedInt8___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_int8_of_nat(x_1);
return x_2;
}
}
static uint8_t _init_l_instInhabitedInt8() {
_start:
{
uint8_t x_1; 
x_1 = l_instInhabitedInt8___closed__0;
return x_1;
}
}
static lean_object* _init_l_instLTInt8() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instLEInt8() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt8(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int8_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_instDecidableEqInt8(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_bool_to_int8(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int8_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int8_dec_lt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int8_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int8_dec_le(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instMaxInt8___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int8_dec_le(x_1, x_2);
if (x_3 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt8___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_instMaxInt8___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instMinInt8___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int8_dec_le(x_1, x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt8___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_instMinInt8___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Int16_size() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(65536u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Int16_toBitVec(uint16_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uint16_to_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int16_toBitVec___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Int16_toBitVec(x_2);
return x_3;
}
}
LEAN_EXPORT uint16_t l_UInt16_toInt16(uint16_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt16_toInt16___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_UInt16_toInt16(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int16_ofInt___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_int16_of_int(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int16_ofNat___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_int16_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint16_t l_Int_toInt16(lean_object* x_1) {
_start:
{
uint16_t x_2; 
x_2 = lean_int16_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_toInt16___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = l_Int_toInt16(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint16_t l_Nat_toInt16(lean_object* x_1) {
_start:
{
uint16_t x_2; 
x_2 = lean_int16_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt16___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = l_Nat_toInt16(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lean_int16_to_int(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg(uint16_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_int16_to_int(x_1);
x_3 = l_Int_toNat(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Int16_toNatClampNeg(x_2);
return x_3;
}
}
LEAN_EXPORT uint16_t l_Int16_ofBitVec(lean_object* x_1) {
_start:
{
uint16_t x_2; 
x_2 = lean_uint16_of_nat_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int16_ofBitVec___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = l_Int16_ofBitVec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt8___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_int16_to_int8(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt16___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_int8_to_int16(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int16_neg___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_int16_neg(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0(uint16_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_int16_to_int(x_1);
x_3 = l_instToStringInt8___lam__0___closed__0;
x_4 = lean_int_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_nat_abs(x_2);
x_6 = l_Nat_reprFast(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_nat_abs(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = ((lean_object*)(l_instToStringInt8___lam__0___closed__1));
x_11 = lean_nat_add(x_9, x_8);
lean_dec(x_9);
x_12 = l_Nat_reprFast(x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec_ref(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_instToStringInt16___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprInt16___lam__0(uint16_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_int16_to_int(x_1);
x_4 = l_instToStringInt8___lam__0___closed__0;
x_5 = lean_int_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Int_repr(x_3);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Int_repr(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Repr_addAppParen(x_9, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt16___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_instReprInt16___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_instReprAtomInt16() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint16_t l_Int16_instOfNat(lean_object* x_1) {
_start:
{
uint16_t x_2; 
x_2 = lean_int16_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int16_instOfNat___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = l_Int16_instOfNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static uint16_t _init_l_Int16_maxValue___closed__0() {
_start:
{
lean_object* x_1; uint16_t x_2; 
x_1 = lean_unsigned_to_nat(32767u);
x_2 = lean_int16_of_nat(x_1);
return x_2;
}
}
static uint16_t _init_l_Int16_maxValue() {
_start:
{
uint16_t x_1; 
x_1 = l_Int16_maxValue___closed__0;
return x_1;
}
}
static uint16_t _init_l_Int16_minValue___closed__0() {
_start:
{
lean_object* x_1; uint16_t x_2; 
x_1 = lean_unsigned_to_nat(32768u);
x_2 = lean_int16_of_nat(x_1);
return x_2;
}
}
static uint16_t _init_l_Int16_minValue___closed__1() {
_start:
{
uint16_t x_1; uint16_t x_2; 
x_1 = l_Int16_minValue___closed__0;
x_2 = lean_int16_neg(x_1);
return x_2;
}
}
static uint16_t _init_l_Int16_minValue() {
_start:
{
uint16_t x_1; 
x_1 = l_Int16_minValue___closed__1;
return x_1;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntLE___redArg(lean_object* x_1) {
_start:
{
uint16_t x_2; 
x_2 = lean_int16_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntLE___redArg___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = l_Int16_ofIntLE___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntLE(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint16_t x_4; 
x_4 = lean_int16_of_int(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint16_t x_4; lean_object* x_5; 
x_4 = l_Int16_ofIntLE(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Int16_ofIntTruncate___closed__0() {
_start:
{
uint16_t x_1; lean_object* x_2; 
x_1 = l_Int16_minValue___closed__1;
x_2 = lean_int16_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int16_ofIntTruncate___closed__1() {
_start:
{
uint16_t x_1; lean_object* x_2; 
x_1 = l_Int16_maxValue___closed__0;
x_2 = lean_int16_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntTruncate(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Int16_minValue___closed__1;
x_3 = l_Int16_ofIntTruncate___closed__0;
x_4 = lean_int_dec_le(x_3, x_1);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Int16_ofIntTruncate___closed__1;
x_6 = lean_int_dec_le(x_1, x_5);
if (x_6 == 0)
{
return x_2;
}
else
{
uint16_t x_7; 
x_7 = lean_int16_of_int(x_1);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntTruncate___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = l_Int16_ofIntTruncate(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int16_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int16_add(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int16_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int16_sub(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int16_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int16_mul(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int16_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int16_div(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint16_t _init_l_Int16_pow___closed__0() {
_start:
{
lean_object* x_1; uint16_t x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_int16_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT uint16_t l_Int16_pow(uint16_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
uint16_t x_5; 
x_5 = l_Int16_pow___closed__0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint16_t x_8; uint16_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = l_Int16_pow(x_1, x_7);
lean_dec(x_7);
x_9 = lean_int16_mul(x_8, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Int16_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Int16_pow(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int16_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int16_mod(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int16_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int16_land(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int16_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int16_lor(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int16_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int16_xor(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int16_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int16_shift_left(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int16_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int16_shift_right(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int16_complement___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_int16_complement(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int16_abs___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_int16_abs(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int16_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int16_dec_eq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint16_t _init_l_instInhabitedInt16___closed__0() {
_start:
{
lean_object* x_1; uint16_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_int16_of_nat(x_1);
return x_2;
}
}
static uint16_t _init_l_instInhabitedInt16() {
_start:
{
uint16_t x_1; 
x_1 = l_instInhabitedInt16___closed__0;
return x_1;
}
}
static lean_object* _init_l_instLTInt16() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instLEInt16() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt16(uint16_t x_1, uint16_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int16_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt16___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_instDecidableEqInt16(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt16___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_bool_to_int16(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int16_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int16_dec_lt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int16_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_int16_dec_le(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint16_t l_instMaxInt16___lam__0(uint16_t x_1, uint16_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int16_dec_le(x_1, x_2);
if (x_3 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt16___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_instMaxInt16___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint16_t l_instMinInt16___lam__0(uint16_t x_1, uint16_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int16_dec_le(x_1, x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt16___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_instMinInt16___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Int32_size() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("4294967296");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Int32_toBitVec(uint32_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uint32_to_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int32_toBitVec___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Int32_toBitVec(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_UInt32_toInt32(uint32_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt32_toInt32___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_UInt32_toInt32(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int32_ofInt___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_int32_of_int(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int32_ofNat___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_int32_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_Int_toInt32(lean_object* x_1) {
_start:
{
uint32_t x_2; 
x_2 = lean_int32_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_toInt32___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Int_toInt32(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_Nat_toInt32(lean_object* x_1) {
_start:
{
uint32_t x_2; 
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt32___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Nat_toInt32(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = lean_int32_to_int(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_int32_to_int(x_1);
x_3 = l_Int_toNat(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Int32_toNatClampNeg(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_Int32_ofBitVec(lean_object* x_1) {
_start:
{
uint32_t x_2; 
x_2 = lean_uint32_of_nat_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int32_ofBitVec___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Int32_ofBitVec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt8___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = lean_int32_to_int8(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt16___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = lean_int32_to_int16(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt32___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_int8_to_int32(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt32___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_int16_to_int32(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int32_neg___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = lean_int32_neg(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_int32_to_int(x_1);
x_3 = l_instToStringInt8___lam__0___closed__0;
x_4 = lean_int_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_nat_abs(x_2);
lean_dec(x_2);
x_6 = l_Nat_reprFast(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_nat_abs(x_2);
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = ((lean_object*)(l_instToStringInt8___lam__0___closed__1));
x_11 = lean_nat_add(x_9, x_8);
lean_dec(x_9);
x_12 = l_Nat_reprFast(x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec_ref(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_instToStringInt32___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprInt32___lam__0(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_int32_to_int(x_1);
x_4 = l_instToStringInt8___lam__0___closed__0;
x_5 = lean_int_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Int_repr(x_3);
lean_dec(x_3);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Int_repr(x_3);
lean_dec(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Repr_addAppParen(x_9, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt32___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_instReprInt32___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_instReprAtomInt32() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint32_t l_Int32_instOfNat(lean_object* x_1) {
_start:
{
uint32_t x_2; 
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int32_instOfNat___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Int32_instOfNat(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
static uint32_t _init_l_Int32_maxValue___closed__0() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(2147483647u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Int32_maxValue() {
_start:
{
uint32_t x_1; 
x_1 = l_Int32_maxValue___closed__0;
return x_1;
}
}
static uint32_t _init_l_Int32_minValue___closed__0() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(2147483648u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_Int32_minValue___closed__1() {
_start:
{
uint32_t x_1; uint32_t x_2; 
x_1 = l_Int32_minValue___closed__0;
x_2 = lean_int32_neg(x_1);
return x_2;
}
}
static uint32_t _init_l_Int32_minValue() {
_start:
{
uint32_t x_1; 
x_1 = l_Int32_minValue___closed__1;
return x_1;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntLE___redArg(lean_object* x_1) {
_start:
{
uint32_t x_2; 
x_2 = lean_int32_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntLE___redArg___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Int32_ofIntLE___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntLE(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; 
x_4 = lean_int32_of_int(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = l_Int32_ofIntLE(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
static lean_object* _init_l_Int32_ofIntTruncate___closed__0() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = l_Int32_minValue___closed__1;
x_2 = lean_int32_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int32_ofIntTruncate___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = l_Int32_maxValue___closed__0;
x_2 = lean_int32_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntTruncate(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Int32_minValue___closed__1;
x_3 = l_Int32_ofIntTruncate___closed__0;
x_4 = lean_int_dec_le(x_3, x_1);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Int32_ofIntTruncate___closed__1;
x_6 = lean_int_dec_le(x_1, x_5);
if (x_6 == 0)
{
return x_2;
}
else
{
uint32_t x_7; 
x_7 = lean_int32_of_int(x_1);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntTruncate___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Int32_ofIntTruncate(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int32_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_int32_add(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int32_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_int32_sub(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int32_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_int32_mul(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int32_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_int32_div(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
static uint32_t _init_l_Int32_pow___closed__0() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT uint32_t l_Int32_pow(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
uint32_t x_5; 
x_5 = l_Int32_pow___closed__0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint32_t x_8; uint32_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = l_Int32_pow(x_1, x_7);
lean_dec(x_7);
x_9 = lean_int32_mul(x_8, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Int32_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Int32_pow(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int32_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_int32_mod(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int32_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_int32_land(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int32_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_int32_lor(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int32_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_int32_xor(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int32_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_int32_shift_left(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int32_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_int32_shift_right(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int32_complement___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = lean_int32_complement(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int32_abs___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = lean_int32_abs(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int32_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_int32_dec_eq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint32_t _init_l_instInhabitedInt32___closed__0() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static uint32_t _init_l_instInhabitedInt32() {
_start:
{
uint32_t x_1; 
x_1 = l_instInhabitedInt32___closed__0;
return x_1;
}
}
static lean_object* _init_l_instLTInt32() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instLEInt32() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt32(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int32_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt32___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_instDecidableEqInt32(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt32___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_bool_to_int32(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int32_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_int32_dec_lt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int32_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_int32_dec_le(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint32_t l_instMaxInt32___lam__0(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int32_dec_le(x_1, x_2);
if (x_3 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt32___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_instMaxInt32___lam__0(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT uint32_t l_instMinInt32___lam__0(uint32_t x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int32_dec_le(x_1, x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt32___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_instMinInt32___lam__0(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
static lean_object* _init_l_Int64_size___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("18446744073709551616");
return x_1;
}
}
static lean_object* _init_l_Int64_size() {
_start:
{
lean_object* x_1; 
x_1 = l_Int64_size___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Int64_toBitVec(uint64_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_uint64_to_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int64_toBitVec___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Int64_toBitVec(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_UInt64_toInt64(uint64_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt64_toInt64___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_UInt64_toInt64(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int64_ofInt___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_int64_of_int(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int64_ofNat___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_int64_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Int_toInt64(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_int64_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_toInt64___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Int_toInt64(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Nat_toInt64(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt64___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Nat_toInt64(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = lean_int64_to_int_sint(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_int64_to_int_sint(x_1);
x_3 = l_Int_toNat(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Int64_toNatClampNeg(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Int64_ofBitVec(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_uint64_of_nat_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int64_ofBitVec___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Int64_ofBitVec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt8___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = lean_int64_to_int8(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt16___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = lean_int64_to_int16(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt32___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = lean_int64_to_int32(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt64___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_int8_to_int64(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt64___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_int16_to_int64(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt64___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = lean_int32_to_int64(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int64_neg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = lean_int64_neg(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_int64_to_int_sint(x_1);
x_3 = l_instToStringInt8___lam__0___closed__0;
x_4 = lean_int_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_nat_abs(x_2);
lean_dec(x_2);
x_6 = l_Nat_reprFast(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_nat_abs(x_2);
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = ((lean_object*)(l_instToStringInt8___lam__0___closed__1));
x_11 = lean_nat_add(x_9, x_8);
lean_dec(x_9);
x_12 = l_Nat_reprFast(x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec_ref(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_instToStringInt64___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprInt64___lam__0(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_int64_to_int_sint(x_1);
x_4 = l_instToStringInt8___lam__0___closed__0;
x_5 = lean_int_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Int_repr(x_3);
lean_dec(x_3);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Int_repr(x_3);
lean_dec(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Repr_addAppParen(x_9, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt64___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_instReprInt64___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_instReprAtomInt64() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_instHashableInt64___lam__0(uint64_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_instHashableInt64___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_instHashableInt64___lam__0(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Int64_instOfNat(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int64_instOfNat___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Int64_instOfNat(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static uint64_t _init_l_Int64_maxValue___closed__0() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_cstr_to_nat("9223372036854775807");
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
static uint64_t _init_l_Int64_maxValue() {
_start:
{
uint64_t x_1; 
x_1 = l_Int64_maxValue___closed__0;
return x_1;
}
}
static lean_object* _init_l_Int64_minValue___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("9223372036854775808");
return x_1;
}
}
static uint64_t _init_l_Int64_minValue___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Int64_minValue___closed__0;
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
static uint64_t _init_l_Int64_minValue___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; 
x_1 = l_Int64_minValue___closed__1;
x_2 = lean_int64_neg(x_1);
return x_2;
}
}
static uint64_t _init_l_Int64_minValue() {
_start:
{
uint64_t x_1; 
x_1 = l_Int64_minValue___closed__2;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntLE___redArg(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_int64_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntLE___redArg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Int64_ofIntLE___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntLE(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; 
x_4 = lean_int64_of_int(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = l_Int64_ofIntLE(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
static lean_object* _init_l_Int64_ofIntTruncate___closed__0() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Int64_minValue___closed__2;
x_2 = lean_int64_to_int_sint(x_1);
return x_2;
}
}
static lean_object* _init_l_Int64_ofIntTruncate___closed__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Int64_maxValue___closed__0;
x_2 = lean_int64_to_int_sint(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntTruncate(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Int64_minValue___closed__2;
x_3 = l_Int64_ofIntTruncate___closed__0;
x_4 = lean_int_dec_le(x_3, x_1);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Int64_ofIntTruncate___closed__1;
x_6 = lean_int_dec_le(x_1, x_5);
if (x_6 == 0)
{
return x_2;
}
else
{
uint64_t x_7; 
x_7 = lean_int64_of_int(x_1);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntTruncate___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Int64_ofIntTruncate(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int64_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_int64_add(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int64_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_int64_sub(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int64_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_int64_mul(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int64_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_int64_div(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
static uint64_t _init_l_Int64_pow___closed__0() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_Int64_pow(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
uint64_t x_5; 
x_5 = l_Int64_pow___closed__0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = l_Int64_pow(x_1, x_7);
lean_dec(x_7);
x_9 = lean_int64_mul(x_8, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Int64_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Int64_pow(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Int64_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_int64_mod(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int64_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_int64_land(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int64_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_int64_lor(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int64_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_int64_xor(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int64_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_int64_shift_left(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int64_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_int64_shift_right(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int64_complement___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = lean_int64_complement(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int64_abs___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = lean_int64_abs(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int64_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_int64_dec_eq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint64_t _init_l_instInhabitedInt64___closed__0() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
static uint64_t _init_l_instInhabitedInt64() {
_start:
{
uint64_t x_1; 
x_1 = l_instInhabitedInt64___closed__0;
return x_1;
}
}
static lean_object* _init_l_instLTInt64() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instLEInt64() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt64(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int64_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt64___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_instDecidableEqInt64(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt64___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_bool_to_int64(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int64_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_int64_dec_lt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Int64_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_int64_dec_le(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint64_t l_instMaxInt64___lam__0(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int64_dec_le(x_1, x_2);
if (x_3 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt64___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_instMaxInt64___lam__0(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT uint64_t l_instMinInt64___lam__0(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_int64_dec_le(x_1, x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt64___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_instMinInt64___lam__0(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
static lean_object* _init_l_ISize_size___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_Platform_numBits;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_pow(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_ISize_size() {
_start:
{
lean_object* x_1; 
x_1 = l_ISize_size___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_ISize_toBitVec(size_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_usize_to_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ISize_toBitVec___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_ISize_toBitVec(x_2);
return x_3;
}
}
LEAN_EXPORT size_t l_USize_toISize(size_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_USize_toISize___boxed(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_USize_toISize(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ISize_ofInt___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_isize_of_int(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ISize_ofNat___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_isize_of_nat(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
LEAN_EXPORT size_t l_Int_toISize(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_isize_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_toISize___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Int_toISize(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
LEAN_EXPORT size_t l_Nat_toISize(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_isize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_toISize___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Nat_toISize(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_isize_to_int(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg(size_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_isize_to_int(x_1);
x_3 = l_Int_toNat(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_ISize_toNatClampNeg(x_2);
return x_3;
}
}
LEAN_EXPORT size_t l_ISize_ofBitVec(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_usize_of_nat_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ISize_ofBitVec___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_ISize_ofBitVec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt8___boxed(lean_object* x_1) {
_start:
{
size_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_isize_to_int8(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt16___boxed(lean_object* x_1) {
_start:
{
size_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_isize_to_int16(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt32___boxed(lean_object* x_1) {
_start:
{
size_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_isize_to_int32(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt64___boxed(lean_object* x_1) {
_start:
{
size_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_isize_to_int64(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int8_toISize___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_int8_to_isize(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int16_toISize___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_int16_to_isize(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int32_toISize___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = lean_int32_to_isize(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int64_toISize___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = lean_int64_to_isize(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ISize_neg___boxed(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_isize_neg(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_instToStringISize___lam__0(size_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_isize_to_int(x_1);
x_3 = l_instToStringInt8___lam__0___closed__0;
x_4 = lean_int_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_nat_abs(x_2);
lean_dec(x_2);
x_6 = l_Nat_reprFast(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_nat_abs(x_2);
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_7);
x_10 = ((lean_object*)(l_instToStringInt8___lam__0___closed__1));
x_11 = lean_nat_add(x_9, x_8);
lean_dec(x_9);
x_12 = l_Nat_reprFast(x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec_ref(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_instToStringISize___lam__0___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_instToStringISize___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instReprISize___lam__0(size_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_isize_to_int(x_1);
x_4 = l_instToStringInt8___lam__0___closed__0;
x_5 = lean_int_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Int_repr(x_3);
lean_dec(x_3);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Int_repr(x_3);
lean_dec(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Repr_addAppParen(x_9, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_instReprISize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_instReprISize___lam__0(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_instReprAtomISize() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT size_t l_ISize_instOfNat(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_isize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ISize_instOfNat___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_ISize_instOfNat(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l_ISize_maxValue___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_ISize_maxValue___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_System_Platform_numBits;
x_3 = lean_nat_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_ISize_maxValue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ISize_maxValue___closed__1;
x_2 = l_ISize_maxValue___closed__0;
x_3 = l_Int_pow(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_ISize_maxValue___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_ISize_maxValue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ISize_maxValue___closed__3;
x_2 = l_ISize_maxValue___closed__2;
x_3 = lean_int_sub(x_2, x_1);
return x_3;
}
}
static size_t _init_l_ISize_maxValue___closed__5() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_ISize_maxValue___closed__4;
x_2 = lean_isize_of_int(x_1);
return x_2;
}
}
static size_t _init_l_ISize_maxValue() {
_start:
{
size_t x_1; 
x_1 = l_ISize_maxValue___closed__5;
return x_1;
}
}
static lean_object* _init_l_ISize_minValue___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_ISize_maxValue___closed__2;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static size_t _init_l_ISize_minValue___closed__1() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_ISize_minValue___closed__0;
x_2 = lean_isize_of_int(x_1);
return x_2;
}
}
static size_t _init_l_ISize_minValue() {
_start:
{
size_t x_1; 
x_1 = l_ISize_minValue___closed__1;
return x_1;
}
}
LEAN_EXPORT size_t l_ISize_ofIntLE___redArg(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_isize_of_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntLE___redArg___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_ISize_ofIntLE___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
LEAN_EXPORT size_t l_ISize_ofIntLE(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; 
x_4 = lean_isize_of_int(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = l_ISize_ofIntLE(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box_usize(x_4);
return x_5;
}
}
static lean_object* _init_l_ISize_ofIntTruncate___closed__0() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = l_ISize_minValue___closed__1;
x_2 = lean_isize_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_ISize_ofIntTruncate___closed__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = l_ISize_maxValue___closed__5;
x_2 = lean_isize_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT size_t l_ISize_ofIntTruncate(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_ISize_minValue___closed__1;
x_3 = l_ISize_ofIntTruncate___closed__0;
x_4 = lean_int_dec_le(x_3, x_1);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_ISize_ofIntTruncate___closed__1;
x_6 = lean_int_dec_le(x_1, x_5);
if (x_6 == 0)
{
return x_2;
}
else
{
size_t x_7; 
x_7 = lean_isize_of_int(x_1);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntTruncate___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_ISize_ofIntTruncate(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ISize_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_isize_add(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ISize_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_isize_sub(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ISize_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_isize_mul(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ISize_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_isize_div(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
static size_t _init_l_ISize_pow___closed__0() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_isize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT size_t l_ISize_pow(size_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
size_t x_5; 
x_5 = l_ISize_pow___closed__0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = l_ISize_pow(x_1, x_7);
lean_dec(x_7);
x_9 = lean_isize_mul(x_8, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_ISize_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_ISize_pow(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_usize(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ISize_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_isize_mod(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ISize_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_isize_land(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ISize_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_isize_lor(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ISize_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_isize_xor(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ISize_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_isize_shift_left(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ISize_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_isize_shift_right(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ISize_complement___boxed(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_isize_complement(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ISize_abs___boxed(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_isize_abs(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ISize_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_isize_dec_eq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static size_t _init_l_instInhabitedISize___closed__0() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_isize_of_nat(x_1);
return x_2;
}
}
static size_t _init_l_instInhabitedISize() {
_start:
{
size_t x_1; 
x_1 = l_instInhabitedISize___closed__0;
return x_1;
}
}
static lean_object* _init_l_instLTISize() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instLEISize() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqISize(size_t x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_isize_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqISize___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_instDecidableEqISize(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Bool_toISize___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_bool_to_isize(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ISize_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_isize_dec_lt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_ISize_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_isize_dec_le(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT size_t l_instMaxISize___lam__0(size_t x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_isize_dec_le(x_1, x_2);
if (x_3 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_instMaxISize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_instMaxISize___lam__0(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT size_t l_instMinISize___lam__0(size_t x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_isize_dec_le(x_1, x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_instMinISize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_instMinISize___lam__0(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int8_size = _init_l_Int8_size();
lean_mark_persistent(l_Int8_size);
l_instToStringInt8___lam__0___closed__0 = _init_l_instToStringInt8___lam__0___closed__0();
lean_mark_persistent(l_instToStringInt8___lam__0___closed__0);
l_instReprAtomInt8 = _init_l_instReprAtomInt8();
lean_mark_persistent(l_instReprAtomInt8);
l_Int8_maxValue___closed__0 = _init_l_Int8_maxValue___closed__0();
l_Int8_maxValue = _init_l_Int8_maxValue();
l_Int8_minValue___closed__0 = _init_l_Int8_minValue___closed__0();
l_Int8_minValue___closed__1 = _init_l_Int8_minValue___closed__1();
l_Int8_minValue = _init_l_Int8_minValue();
l_Int8_ofIntTruncate___closed__0 = _init_l_Int8_ofIntTruncate___closed__0();
lean_mark_persistent(l_Int8_ofIntTruncate___closed__0);
l_Int8_ofIntTruncate___closed__1 = _init_l_Int8_ofIntTruncate___closed__1();
lean_mark_persistent(l_Int8_ofIntTruncate___closed__1);
l_Int8_pow___closed__0 = _init_l_Int8_pow___closed__0();
l_instInhabitedInt8___closed__0 = _init_l_instInhabitedInt8___closed__0();
l_instInhabitedInt8 = _init_l_instInhabitedInt8();
l_instLTInt8 = _init_l_instLTInt8();
lean_mark_persistent(l_instLTInt8);
l_instLEInt8 = _init_l_instLEInt8();
lean_mark_persistent(l_instLEInt8);
l_Int16_size = _init_l_Int16_size();
lean_mark_persistent(l_Int16_size);
l_instReprAtomInt16 = _init_l_instReprAtomInt16();
lean_mark_persistent(l_instReprAtomInt16);
l_Int16_maxValue___closed__0 = _init_l_Int16_maxValue___closed__0();
l_Int16_maxValue = _init_l_Int16_maxValue();
l_Int16_minValue___closed__0 = _init_l_Int16_minValue___closed__0();
l_Int16_minValue___closed__1 = _init_l_Int16_minValue___closed__1();
l_Int16_minValue = _init_l_Int16_minValue();
l_Int16_ofIntTruncate___closed__0 = _init_l_Int16_ofIntTruncate___closed__0();
lean_mark_persistent(l_Int16_ofIntTruncate___closed__0);
l_Int16_ofIntTruncate___closed__1 = _init_l_Int16_ofIntTruncate___closed__1();
lean_mark_persistent(l_Int16_ofIntTruncate___closed__1);
l_Int16_pow___closed__0 = _init_l_Int16_pow___closed__0();
l_instInhabitedInt16___closed__0 = _init_l_instInhabitedInt16___closed__0();
l_instInhabitedInt16 = _init_l_instInhabitedInt16();
l_instLTInt16 = _init_l_instLTInt16();
lean_mark_persistent(l_instLTInt16);
l_instLEInt16 = _init_l_instLEInt16();
lean_mark_persistent(l_instLEInt16);
l_Int32_size = _init_l_Int32_size();
lean_mark_persistent(l_Int32_size);
l_instReprAtomInt32 = _init_l_instReprAtomInt32();
lean_mark_persistent(l_instReprAtomInt32);
l_Int32_maxValue___closed__0 = _init_l_Int32_maxValue___closed__0();
l_Int32_maxValue = _init_l_Int32_maxValue();
l_Int32_minValue___closed__0 = _init_l_Int32_minValue___closed__0();
l_Int32_minValue___closed__1 = _init_l_Int32_minValue___closed__1();
l_Int32_minValue = _init_l_Int32_minValue();
l_Int32_ofIntTruncate___closed__0 = _init_l_Int32_ofIntTruncate___closed__0();
lean_mark_persistent(l_Int32_ofIntTruncate___closed__0);
l_Int32_ofIntTruncate___closed__1 = _init_l_Int32_ofIntTruncate___closed__1();
lean_mark_persistent(l_Int32_ofIntTruncate___closed__1);
l_Int32_pow___closed__0 = _init_l_Int32_pow___closed__0();
l_instInhabitedInt32___closed__0 = _init_l_instInhabitedInt32___closed__0();
l_instInhabitedInt32 = _init_l_instInhabitedInt32();
l_instLTInt32 = _init_l_instLTInt32();
lean_mark_persistent(l_instLTInt32);
l_instLEInt32 = _init_l_instLEInt32();
lean_mark_persistent(l_instLEInt32);
l_Int64_size___closed__0 = _init_l_Int64_size___closed__0();
lean_mark_persistent(l_Int64_size___closed__0);
l_Int64_size = _init_l_Int64_size();
lean_mark_persistent(l_Int64_size);
l_instReprAtomInt64 = _init_l_instReprAtomInt64();
lean_mark_persistent(l_instReprAtomInt64);
l_Int64_maxValue___closed__0 = _init_l_Int64_maxValue___closed__0();
l_Int64_maxValue = _init_l_Int64_maxValue();
l_Int64_minValue___closed__0 = _init_l_Int64_minValue___closed__0();
lean_mark_persistent(l_Int64_minValue___closed__0);
l_Int64_minValue___closed__1 = _init_l_Int64_minValue___closed__1();
l_Int64_minValue___closed__2 = _init_l_Int64_minValue___closed__2();
l_Int64_minValue = _init_l_Int64_minValue();
l_Int64_ofIntTruncate___closed__0 = _init_l_Int64_ofIntTruncate___closed__0();
lean_mark_persistent(l_Int64_ofIntTruncate___closed__0);
l_Int64_ofIntTruncate___closed__1 = _init_l_Int64_ofIntTruncate___closed__1();
lean_mark_persistent(l_Int64_ofIntTruncate___closed__1);
l_Int64_pow___closed__0 = _init_l_Int64_pow___closed__0();
l_instInhabitedInt64___closed__0 = _init_l_instInhabitedInt64___closed__0();
l_instInhabitedInt64 = _init_l_instInhabitedInt64();
l_instLTInt64 = _init_l_instLTInt64();
lean_mark_persistent(l_instLTInt64);
l_instLEInt64 = _init_l_instLEInt64();
lean_mark_persistent(l_instLEInt64);
l_ISize_size___closed__0 = _init_l_ISize_size___closed__0();
lean_mark_persistent(l_ISize_size___closed__0);
l_ISize_size = _init_l_ISize_size();
lean_mark_persistent(l_ISize_size);
l_instReprAtomISize = _init_l_instReprAtomISize();
lean_mark_persistent(l_instReprAtomISize);
l_ISize_maxValue___closed__0 = _init_l_ISize_maxValue___closed__0();
lean_mark_persistent(l_ISize_maxValue___closed__0);
l_ISize_maxValue___closed__1 = _init_l_ISize_maxValue___closed__1();
lean_mark_persistent(l_ISize_maxValue___closed__1);
l_ISize_maxValue___closed__2 = _init_l_ISize_maxValue___closed__2();
lean_mark_persistent(l_ISize_maxValue___closed__2);
l_ISize_maxValue___closed__3 = _init_l_ISize_maxValue___closed__3();
lean_mark_persistent(l_ISize_maxValue___closed__3);
l_ISize_maxValue___closed__4 = _init_l_ISize_maxValue___closed__4();
lean_mark_persistent(l_ISize_maxValue___closed__4);
l_ISize_maxValue___closed__5 = _init_l_ISize_maxValue___closed__5();
l_ISize_maxValue = _init_l_ISize_maxValue();
l_ISize_minValue___closed__0 = _init_l_ISize_minValue___closed__0();
lean_mark_persistent(l_ISize_minValue___closed__0);
l_ISize_minValue___closed__1 = _init_l_ISize_minValue___closed__1();
l_ISize_minValue = _init_l_ISize_minValue();
l_ISize_ofIntTruncate___closed__0 = _init_l_ISize_ofIntTruncate___closed__0();
lean_mark_persistent(l_ISize_ofIntTruncate___closed__0);
l_ISize_ofIntTruncate___closed__1 = _init_l_ISize_ofIntTruncate___closed__1();
lean_mark_persistent(l_ISize_ofIntTruncate___closed__1);
l_ISize_pow___closed__0 = _init_l_ISize_pow___closed__0();
l_instInhabitedISize___closed__0 = _init_l_instInhabitedISize___closed__0();
l_instInhabitedISize = _init_l_instInhabitedISize();
l_instLTISize = _init_l_instLTISize();
lean_mark_persistent(l_instLTISize);
l_instLEISize = _init_l_instLEISize();
lean_mark_persistent(l_instLEISize);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
