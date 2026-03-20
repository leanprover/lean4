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
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
static lean_once_cell_t l_instToStringInt8___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instToStringInt8___lam__0___closed__0;
static const lean_string_object l_instToStringInt8___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_instToStringInt8___lam__0___closed__1 = (const lean_object*)&l_instToStringInt8___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instToStringInt8___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToStringInt8___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToStringInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringInt8___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToStringInt8___closed__0 = (const lean_object*)&l_instToStringInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instToStringInt8 = (const lean_object*)&l_instToStringInt8___closed__0_value;
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
static lean_object* _init_l_instToStringInt8___lam__0___closed__0(void){
_start:
{
lean_object* v_natZero_50_; lean_object* v_intZero_51_; 
v_natZero_50_ = lean_unsigned_to_nat(0u);
v_intZero_51_ = lean_nat_to_int(v_natZero_50_);
return v_intZero_51_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt8___lam__0(uint8_t v_i_53_){
_start:
{
lean_object* v___x_54_; lean_object* v_intZero_55_; uint8_t v_isNeg_56_; 
v___x_54_ = lean_int8_to_int(v_i_53_);
v_intZero_55_ = lean_obj_once(&l_instToStringInt8___lam__0___closed__0, &l_instToStringInt8___lam__0___closed__0_once, _init_l_instToStringInt8___lam__0___closed__0);
v_isNeg_56_ = lean_int_dec_lt(v___x_54_, v_intZero_55_);
if (v_isNeg_56_ == 0)
{
lean_object* v_a_57_; lean_object* v___x_58_; 
v_a_57_ = lean_nat_abs(v___x_54_);
v___x_58_ = l_Nat_reprFast(v_a_57_);
return v___x_58_;
}
else
{
lean_object* v_abs_59_; lean_object* v_one_60_; lean_object* v_a_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_abs_59_ = lean_nat_abs(v___x_54_);
v_one_60_ = lean_unsigned_to_nat(1u);
v_a_61_ = lean_nat_sub(v_abs_59_, v_one_60_);
lean_dec(v_abs_59_);
v___x_62_ = ((lean_object*)(l_instToStringInt8___lam__0___closed__1));
v___x_63_ = lean_nat_add(v_a_61_, v_one_60_);
lean_dec(v_a_61_);
v___x_64_ = l_Nat_reprFast(v___x_63_);
v___x_65_ = lean_string_append(v___x_62_, v___x_64_);
lean_dec_ref(v___x_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringInt8___lam__0___boxed(lean_object* v_i_66_){
_start:
{
uint8_t v_i_boxed_67_; lean_object* v_res_68_; 
v_i_boxed_67_ = lean_unbox(v_i_66_);
v_res_68_ = l_instToStringInt8___lam__0(v_i_boxed_67_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_instReprInt8___lam__0(uint8_t v_i_71_, lean_object* v_prec_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_73_ = lean_int8_to_int(v_i_71_);
v___x_74_ = lean_obj_once(&l_instToStringInt8___lam__0___closed__0, &l_instToStringInt8___lam__0___closed__0_once, _init_l_instToStringInt8___lam__0___closed__0);
v___x_75_ = lean_int_dec_lt(v___x_73_, v___x_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = l_Int_repr(v___x_73_);
v___x_77_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = l_Int_repr(v___x_73_);
v___x_79_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
v___x_80_ = l_Repr_addAppParen(v___x_79_, v_prec_72_);
return v___x_80_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt8___lam__0___boxed(lean_object* v_i_81_, lean_object* v_prec_82_){
_start:
{
uint8_t v_i_boxed_83_; lean_object* v_res_84_; 
v_i_boxed_83_ = lean_unbox(v_i_81_);
v_res_84_ = l_instReprInt8___lam__0(v_i_boxed_83_, v_prec_82_);
lean_dec(v_prec_82_);
return v_res_84_;
}
}
static lean_object* _init_l_instReprAtomInt8(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = lean_box(0);
return v___x_87_;
}
}
LEAN_EXPORT uint8_t l_Int8_instOfNat(lean_object* v_n_90_){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = lean_int8_of_nat(v_n_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Int8_instOfNat___boxed(lean_object* v_n_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_Int8_instOfNat(v_n_92_);
lean_dec(v_n_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
static uint8_t _init_l_Int8_maxValue___closed__0(void){
_start:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(127u);
v___x_98_ = lean_int8_of_nat(v___x_97_);
return v___x_98_;
}
}
static uint8_t _init_l_Int8_maxValue(void){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = lean_uint8_once(&l_Int8_maxValue___closed__0, &l_Int8_maxValue___closed__0_once, _init_l_Int8_maxValue___closed__0);
return v___x_99_;
}
}
static uint8_t _init_l_Int8_minValue___closed__0(void){
_start:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(128u);
v___x_101_ = lean_int8_of_nat(v___x_100_);
return v___x_101_;
}
}
static uint8_t _init_l_Int8_minValue___closed__1(void){
_start:
{
uint8_t v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_uint8_once(&l_Int8_minValue___closed__0, &l_Int8_minValue___closed__0_once, _init_l_Int8_minValue___closed__0);
v___x_103_ = lean_int8_neg(v___x_102_);
return v___x_103_;
}
}
static uint8_t _init_l_Int8_minValue(void){
_start:
{
uint8_t v___x_104_; 
v___x_104_ = lean_uint8_once(&l_Int8_minValue___closed__1, &l_Int8_minValue___closed__1_once, _init_l_Int8_minValue___closed__1);
return v___x_104_;
}
}
LEAN_EXPORT uint8_t l_Int8_ofIntLE___redArg(lean_object* v_i_105_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = lean_int8_of_int(v_i_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Int8_ofIntLE___redArg___boxed(lean_object* v_i_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Int8_ofIntLE___redArg(v_i_107_);
lean_dec(v_i_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT uint8_t l_Int8_ofIntLE(lean_object* v_i_110_, lean_object* v___hl_111_, lean_object* v___hr_112_){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = lean_int8_of_int(v_i_110_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Int8_ofIntLE___boxed(lean_object* v_i_114_, lean_object* v___hl_115_, lean_object* v___hr_116_){
_start:
{
uint8_t v_res_117_; lean_object* v_r_118_; 
v_res_117_ = l_Int8_ofIntLE(v_i_114_, v___hl_115_, v___hr_116_);
lean_dec(v_i_114_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
static lean_object* _init_l_Int8_ofIntTruncate___closed__0(void){
_start:
{
uint8_t v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_uint8_once(&l_Int8_minValue___closed__1, &l_Int8_minValue___closed__1_once, _init_l_Int8_minValue___closed__1);
v___x_120_ = lean_int8_to_int(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l_Int8_ofIntTruncate___closed__1(void){
_start:
{
uint8_t v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_uint8_once(&l_Int8_maxValue___closed__0, &l_Int8_maxValue___closed__0_once, _init_l_Int8_maxValue___closed__0);
v___x_122_ = lean_int8_to_int(v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT uint8_t l_Int8_ofIntTruncate(lean_object* v_i_123_){
_start:
{
uint8_t v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_124_ = lean_uint8_once(&l_Int8_minValue___closed__1, &l_Int8_minValue___closed__1_once, _init_l_Int8_minValue___closed__1);
v___x_125_ = lean_obj_once(&l_Int8_ofIntTruncate___closed__0, &l_Int8_ofIntTruncate___closed__0_once, _init_l_Int8_ofIntTruncate___closed__0);
v___x_126_ = lean_int_dec_le(v___x_125_, v_i_123_);
if (v___x_126_ == 0)
{
return v___x_124_;
}
else
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = lean_obj_once(&l_Int8_ofIntTruncate___closed__1, &l_Int8_ofIntTruncate___closed__1_once, _init_l_Int8_ofIntTruncate___closed__1);
v___x_128_ = lean_int_dec_le(v_i_123_, v___x_127_);
if (v___x_128_ == 0)
{
return v___x_124_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = lean_int8_of_int(v_i_123_);
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int8_ofIntTruncate___boxed(lean_object* v_i_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Int8_ofIntTruncate(v_i_130_);
lean_dec(v_i_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT lean_object* l_Int8_add___boxed(lean_object* v_a_135_, lean_object* v_b_136_){
_start:
{
uint8_t v_a_boxed_137_; uint8_t v_b_boxed_138_; uint8_t v_res_139_; lean_object* v_r_140_; 
v_a_boxed_137_ = lean_unbox(v_a_135_);
v_b_boxed_138_ = lean_unbox(v_b_136_);
v_res_139_ = lean_int8_add(v_a_boxed_137_, v_b_boxed_138_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT lean_object* l_Int8_sub___boxed(lean_object* v_a_143_, lean_object* v_b_144_){
_start:
{
uint8_t v_a_boxed_145_; uint8_t v_b_boxed_146_; uint8_t v_res_147_; lean_object* v_r_148_; 
v_a_boxed_145_ = lean_unbox(v_a_143_);
v_b_boxed_146_ = lean_unbox(v_b_144_);
v_res_147_ = lean_int8_sub(v_a_boxed_145_, v_b_boxed_146_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT lean_object* l_Int8_mul___boxed(lean_object* v_a_151_, lean_object* v_b_152_){
_start:
{
uint8_t v_a_boxed_153_; uint8_t v_b_boxed_154_; uint8_t v_res_155_; lean_object* v_r_156_; 
v_a_boxed_153_ = lean_unbox(v_a_151_);
v_b_boxed_154_ = lean_unbox(v_b_152_);
v_res_155_ = lean_int8_mul(v_a_boxed_153_, v_b_boxed_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT lean_object* l_Int8_div___boxed(lean_object* v_a_159_, lean_object* v_b_160_){
_start:
{
uint8_t v_a_boxed_161_; uint8_t v_b_boxed_162_; uint8_t v_res_163_; lean_object* v_r_164_; 
v_a_boxed_161_ = lean_unbox(v_a_159_);
v_b_boxed_162_ = lean_unbox(v_b_160_);
v_res_163_ = lean_int8_div(v_a_boxed_161_, v_b_boxed_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
static uint8_t _init_l_Int8_pow___closed__0(void){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_int8_of_nat(v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT uint8_t l_Int8_pow(uint8_t v_x_167_, lean_object* v_n_168_){
_start:
{
lean_object* v_zero_169_; uint8_t v_isZero_170_; 
v_zero_169_ = lean_unsigned_to_nat(0u);
v_isZero_170_ = lean_nat_dec_eq(v_n_168_, v_zero_169_);
if (v_isZero_170_ == 1)
{
uint8_t v___x_171_; 
v___x_171_ = lean_uint8_once(&l_Int8_pow___closed__0, &l_Int8_pow___closed__0_once, _init_l_Int8_pow___closed__0);
return v___x_171_;
}
else
{
lean_object* v_one_172_; lean_object* v_n_173_; uint8_t v___x_174_; uint8_t v___x_175_; 
v_one_172_ = lean_unsigned_to_nat(1u);
v_n_173_ = lean_nat_sub(v_n_168_, v_one_172_);
v___x_174_ = l_Int8_pow(v_x_167_, v_n_173_);
lean_dec(v_n_173_);
v___x_175_ = lean_int8_mul(v___x_174_, v_x_167_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Int8_pow___boxed(lean_object* v_x_176_, lean_object* v_n_177_){
_start:
{
uint8_t v_x_boxed_178_; uint8_t v_res_179_; lean_object* v_r_180_; 
v_x_boxed_178_ = lean_unbox(v_x_176_);
v_res_179_ = l_Int8_pow(v_x_boxed_178_, v_n_177_);
lean_dec(v_n_177_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT lean_object* l_Int8_mod___boxed(lean_object* v_a_183_, lean_object* v_b_184_){
_start:
{
uint8_t v_a_boxed_185_; uint8_t v_b_boxed_186_; uint8_t v_res_187_; lean_object* v_r_188_; 
v_a_boxed_185_ = lean_unbox(v_a_183_);
v_b_boxed_186_ = lean_unbox(v_b_184_);
v_res_187_ = lean_int8_mod(v_a_boxed_185_, v_b_boxed_186_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT lean_object* l_Int8_land___boxed(lean_object* v_a_191_, lean_object* v_b_192_){
_start:
{
uint8_t v_a_boxed_193_; uint8_t v_b_boxed_194_; uint8_t v_res_195_; lean_object* v_r_196_; 
v_a_boxed_193_ = lean_unbox(v_a_191_);
v_b_boxed_194_ = lean_unbox(v_b_192_);
v_res_195_ = lean_int8_land(v_a_boxed_193_, v_b_boxed_194_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Int8_lor___boxed(lean_object* v_a_199_, lean_object* v_b_200_){
_start:
{
uint8_t v_a_boxed_201_; uint8_t v_b_boxed_202_; uint8_t v_res_203_; lean_object* v_r_204_; 
v_a_boxed_201_ = lean_unbox(v_a_199_);
v_b_boxed_202_ = lean_unbox(v_b_200_);
v_res_203_ = lean_int8_lor(v_a_boxed_201_, v_b_boxed_202_);
v_r_204_ = lean_box(v_res_203_);
return v_r_204_;
}
}
LEAN_EXPORT lean_object* l_Int8_xor___boxed(lean_object* v_a_207_, lean_object* v_b_208_){
_start:
{
uint8_t v_a_boxed_209_; uint8_t v_b_boxed_210_; uint8_t v_res_211_; lean_object* v_r_212_; 
v_a_boxed_209_ = lean_unbox(v_a_207_);
v_b_boxed_210_ = lean_unbox(v_b_208_);
v_res_211_ = lean_int8_xor(v_a_boxed_209_, v_b_boxed_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT lean_object* l_Int8_shiftLeft___boxed(lean_object* v_a_215_, lean_object* v_b_216_){
_start:
{
uint8_t v_a_boxed_217_; uint8_t v_b_boxed_218_; uint8_t v_res_219_; lean_object* v_r_220_; 
v_a_boxed_217_ = lean_unbox(v_a_215_);
v_b_boxed_218_ = lean_unbox(v_b_216_);
v_res_219_ = lean_int8_shift_left(v_a_boxed_217_, v_b_boxed_218_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT lean_object* l_Int8_shiftRight___boxed(lean_object* v_a_223_, lean_object* v_b_224_){
_start:
{
uint8_t v_a_boxed_225_; uint8_t v_b_boxed_226_; uint8_t v_res_227_; lean_object* v_r_228_; 
v_a_boxed_225_ = lean_unbox(v_a_223_);
v_b_boxed_226_ = lean_unbox(v_b_224_);
v_res_227_ = lean_int8_shift_right(v_a_boxed_225_, v_b_boxed_226_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT lean_object* l_Int8_complement___boxed(lean_object* v_a_230_){
_start:
{
uint8_t v_a_boxed_231_; uint8_t v_res_232_; lean_object* v_r_233_; 
v_a_boxed_231_ = lean_unbox(v_a_230_);
v_res_232_ = lean_int8_complement(v_a_boxed_231_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT lean_object* l_Int8_abs___boxed(lean_object* v_a_235_){
_start:
{
uint8_t v_a_boxed_236_; uint8_t v_res_237_; lean_object* v_r_238_; 
v_a_boxed_236_ = lean_unbox(v_a_235_);
v_res_237_ = lean_int8_abs(v_a_boxed_236_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT lean_object* l_Int8_decEq___boxed(lean_object* v_a_241_, lean_object* v_b_242_){
_start:
{
uint8_t v_a_boxed_243_; uint8_t v_b_boxed_244_; uint8_t v_res_245_; lean_object* v_r_246_; 
v_a_boxed_243_ = lean_unbox(v_a_241_);
v_b_boxed_244_ = lean_unbox(v_b_242_);
v_res_245_ = lean_int8_dec_eq(v_a_boxed_243_, v_b_boxed_244_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
static uint8_t _init_l_instInhabitedInt8___closed__0(void){
_start:
{
lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_int8_of_nat(v___x_247_);
return v___x_248_;
}
}
static uint8_t _init_l_instInhabitedInt8(void){
_start:
{
uint8_t v___x_249_; 
v___x_249_ = lean_uint8_once(&l_instInhabitedInt8___closed__0, &l_instInhabitedInt8___closed__0_once, _init_l_instInhabitedInt8___closed__0);
return v___x_249_;
}
}
static lean_object* _init_l_instLTInt8(void){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = lean_box(0);
return v___x_262_;
}
}
static lean_object* _init_l_instLEInt8(void){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = lean_box(0);
return v___x_263_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt8(uint8_t v_a_276_, uint8_t v_b_277_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = lean_int8_dec_eq(v_a_276_, v_b_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt8___boxed(lean_object* v_a_279_, lean_object* v_b_280_){
_start:
{
uint8_t v_a_boxed_281_; uint8_t v_b_boxed_282_; uint8_t v_res_283_; lean_object* v_r_284_; 
v_a_boxed_281_ = lean_unbox(v_a_279_);
v_b_boxed_282_ = lean_unbox(v_b_280_);
v_res_283_ = l_instDecidableEqInt8(v_a_boxed_281_, v_b_boxed_282_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt8___boxed(lean_object* v_b_286_){
_start:
{
uint8_t v_b_boxed_287_; uint8_t v_res_288_; lean_object* v_r_289_; 
v_b_boxed_287_ = lean_unbox(v_b_286_);
v_res_288_ = lean_bool_to_int8(v_b_boxed_287_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLt___boxed(lean_object* v_a_292_, lean_object* v_b_293_){
_start:
{
uint8_t v_a_boxed_294_; uint8_t v_b_boxed_295_; uint8_t v_res_296_; lean_object* v_r_297_; 
v_a_boxed_294_ = lean_unbox(v_a_292_);
v_b_boxed_295_ = lean_unbox(v_b_293_);
v_res_296_ = lean_int8_dec_lt(v_a_boxed_294_, v_b_boxed_295_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLe___boxed(lean_object* v_a_300_, lean_object* v_b_301_){
_start:
{
uint8_t v_a_boxed_302_; uint8_t v_b_boxed_303_; uint8_t v_res_304_; lean_object* v_r_305_; 
v_a_boxed_302_ = lean_unbox(v_a_300_);
v_b_boxed_303_ = lean_unbox(v_b_301_);
v_res_304_ = lean_int8_dec_le(v_a_boxed_302_, v_b_boxed_303_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT uint8_t l_instMaxInt8___lam__0(uint8_t v_x_306_, uint8_t v_y_307_){
_start:
{
uint8_t v___x_308_; 
v___x_308_ = lean_int8_dec_le(v_x_306_, v_y_307_);
if (v___x_308_ == 0)
{
return v_x_306_;
}
else
{
return v_y_307_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt8___lam__0___boxed(lean_object* v_x_309_, lean_object* v_y_310_){
_start:
{
uint8_t v_x_boxed_311_; uint8_t v_y_boxed_312_; uint8_t v_res_313_; lean_object* v_r_314_; 
v_x_boxed_311_ = lean_unbox(v_x_309_);
v_y_boxed_312_ = lean_unbox(v_y_310_);
v_res_313_ = l_instMaxInt8___lam__0(v_x_boxed_311_, v_y_boxed_312_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT uint8_t l_instMinInt8___lam__0(uint8_t v_x_317_, uint8_t v_y_318_){
_start:
{
uint8_t v___x_319_; 
v___x_319_ = lean_int8_dec_le(v_x_317_, v_y_318_);
if (v___x_319_ == 0)
{
return v_y_318_;
}
else
{
return v_x_317_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt8___lam__0___boxed(lean_object* v_x_320_, lean_object* v_y_321_){
_start:
{
uint8_t v_x_boxed_322_; uint8_t v_y_boxed_323_; uint8_t v_res_324_; lean_object* v_r_325_; 
v_x_boxed_322_ = lean_unbox(v_x_320_);
v_y_boxed_323_ = lean_unbox(v_y_321_);
v_res_324_ = l_instMinInt8___lam__0(v_x_boxed_322_, v_y_boxed_323_);
v_r_325_ = lean_box(v_res_324_);
return v_r_325_;
}
}
static lean_object* _init_l_Int16_size(void){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_unsigned_to_nat(65536u);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Int16_toBitVec(uint16_t v_x_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = lean_uint16_to_nat(v_x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Int16_toBitVec___boxed(lean_object* v_x_331_){
_start:
{
uint16_t v_x_boxed_332_; lean_object* v_res_333_; 
v_x_boxed_332_ = lean_unbox(v_x_331_);
v_res_333_ = l_Int16_toBitVec(v_x_boxed_332_);
return v_res_333_;
}
}
LEAN_EXPORT uint16_t l_UInt16_toInt16(uint16_t v_i_334_){
_start:
{
return v_i_334_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toInt16___boxed(lean_object* v_i_335_){
_start:
{
uint16_t v_i_boxed_336_; uint16_t v_res_337_; lean_object* v_r_338_; 
v_i_boxed_336_ = lean_unbox(v_i_335_);
v_res_337_ = l_UInt16_toInt16(v_i_boxed_336_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofInt___boxed(lean_object* v_i_340_){
_start:
{
uint16_t v_res_341_; lean_object* v_r_342_; 
v_res_341_ = lean_int16_of_int(v_i_340_);
lean_dec(v_i_340_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofNat___boxed(lean_object* v_n_344_){
_start:
{
uint16_t v_res_345_; lean_object* v_r_346_; 
v_res_345_ = lean_int16_of_nat(v_n_344_);
lean_dec(v_n_344_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT uint16_t l_Int_toInt16(lean_object* v_i_347_){
_start:
{
uint16_t v___x_348_; 
v___x_348_ = lean_int16_of_int(v_i_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt16___boxed(lean_object* v_i_349_){
_start:
{
uint16_t v_res_350_; lean_object* v_r_351_; 
v_res_350_ = l_Int_toInt16(v_i_349_);
lean_dec(v_i_349_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT uint16_t l_Nat_toInt16(lean_object* v_n_352_){
_start:
{
uint16_t v___x_353_; 
v___x_353_ = lean_int16_of_nat(v_n_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt16___boxed(lean_object* v_n_354_){
_start:
{
uint16_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Nat_toInt16(v_n_354_);
lean_dec(v_n_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt___boxed(lean_object* v_i_358_){
_start:
{
uint16_t v_i_boxed_359_; lean_object* v_res_360_; 
v_i_boxed_359_ = lean_unbox(v_i_358_);
v_res_360_ = lean_int16_to_int(v_i_boxed_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg(uint16_t v_i_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_int16_to_int(v_i_361_);
v___x_363_ = l_Int_toNat(v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg___boxed(lean_object* v_i_364_){
_start:
{
uint16_t v_i_boxed_365_; lean_object* v_res_366_; 
v_i_boxed_365_ = lean_unbox(v_i_364_);
v_res_366_ = l_Int16_toNatClampNeg(v_i_boxed_365_);
return v_res_366_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofBitVec(lean_object* v_b_367_){
_start:
{
uint16_t v___x_368_; 
v___x_368_ = lean_uint16_of_nat_mk(v_b_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofBitVec___boxed(lean_object* v_b_369_){
_start:
{
uint16_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_Int16_ofBitVec(v_b_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt8___boxed(lean_object* v_a_373_){
_start:
{
uint16_t v_a_boxed_374_; uint8_t v_res_375_; lean_object* v_r_376_; 
v_a_boxed_374_ = lean_unbox(v_a_373_);
v_res_375_ = lean_int16_to_int8(v_a_boxed_374_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt16___boxed(lean_object* v_a_378_){
_start:
{
uint8_t v_a_boxed_379_; uint16_t v_res_380_; lean_object* v_r_381_; 
v_a_boxed_379_ = lean_unbox(v_a_378_);
v_res_380_ = lean_int8_to_int16(v_a_boxed_379_);
v_r_381_ = lean_box(v_res_380_);
return v_r_381_;
}
}
LEAN_EXPORT lean_object* l_Int16_neg___boxed(lean_object* v_i_383_){
_start:
{
uint16_t v_i_boxed_384_; uint16_t v_res_385_; lean_object* v_r_386_; 
v_i_boxed_384_ = lean_unbox(v_i_383_);
v_res_385_ = lean_int16_neg(v_i_boxed_384_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0(uint16_t v_i_387_){
_start:
{
lean_object* v___x_388_; lean_object* v_intZero_389_; uint8_t v_isNeg_390_; 
v___x_388_ = lean_int16_to_int(v_i_387_);
v_intZero_389_ = lean_obj_once(&l_instToStringInt8___lam__0___closed__0, &l_instToStringInt8___lam__0___closed__0_once, _init_l_instToStringInt8___lam__0___closed__0);
v_isNeg_390_ = lean_int_dec_lt(v___x_388_, v_intZero_389_);
if (v_isNeg_390_ == 0)
{
lean_object* v_a_391_; lean_object* v___x_392_; 
v_a_391_ = lean_nat_abs(v___x_388_);
v___x_392_ = l_Nat_reprFast(v_a_391_);
return v___x_392_;
}
else
{
lean_object* v_abs_393_; lean_object* v_one_394_; lean_object* v_a_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_abs_393_ = lean_nat_abs(v___x_388_);
v_one_394_ = lean_unsigned_to_nat(1u);
v_a_395_ = lean_nat_sub(v_abs_393_, v_one_394_);
lean_dec(v_abs_393_);
v___x_396_ = ((lean_object*)(l_instToStringInt8___lam__0___closed__1));
v___x_397_ = lean_nat_add(v_a_395_, v_one_394_);
lean_dec(v_a_395_);
v___x_398_ = l_Nat_reprFast(v___x_397_);
v___x_399_ = lean_string_append(v___x_396_, v___x_398_);
lean_dec_ref(v___x_398_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0___boxed(lean_object* v_i_400_){
_start:
{
uint16_t v_i_boxed_401_; lean_object* v_res_402_; 
v_i_boxed_401_ = lean_unbox(v_i_400_);
v_res_402_ = l_instToStringInt16___lam__0(v_i_boxed_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_instReprInt16___lam__0(uint16_t v_i_405_, lean_object* v_prec_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_407_ = lean_int16_to_int(v_i_405_);
v___x_408_ = lean_obj_once(&l_instToStringInt8___lam__0___closed__0, &l_instToStringInt8___lam__0___closed__0_once, _init_l_instToStringInt8___lam__0___closed__0);
v___x_409_ = lean_int_dec_lt(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = l_Int_repr(v___x_407_);
v___x_411_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = l_Int_repr(v___x_407_);
v___x_413_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
v___x_414_ = l_Repr_addAppParen(v___x_413_, v_prec_406_);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt16___lam__0___boxed(lean_object* v_i_415_, lean_object* v_prec_416_){
_start:
{
uint16_t v_i_boxed_417_; lean_object* v_res_418_; 
v_i_boxed_417_ = lean_unbox(v_i_415_);
v_res_418_ = l_instReprInt16___lam__0(v_i_boxed_417_, v_prec_416_);
lean_dec(v_prec_416_);
return v_res_418_;
}
}
static lean_object* _init_l_instReprAtomInt16(void){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = lean_box(0);
return v___x_421_;
}
}
LEAN_EXPORT uint16_t l_Int16_instOfNat(lean_object* v_n_424_){
_start:
{
uint16_t v___x_425_; 
v___x_425_ = lean_int16_of_nat(v_n_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Int16_instOfNat___boxed(lean_object* v_n_426_){
_start:
{
uint16_t v_res_427_; lean_object* v_r_428_; 
v_res_427_ = l_Int16_instOfNat(v_n_426_);
lean_dec(v_n_426_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
static uint16_t _init_l_Int16_maxValue___closed__0(void){
_start:
{
lean_object* v___x_431_; uint16_t v___x_432_; 
v___x_431_ = lean_unsigned_to_nat(32767u);
v___x_432_ = lean_int16_of_nat(v___x_431_);
return v___x_432_;
}
}
static uint16_t _init_l_Int16_maxValue(void){
_start:
{
uint16_t v___x_433_; 
v___x_433_ = lean_uint16_once(&l_Int16_maxValue___closed__0, &l_Int16_maxValue___closed__0_once, _init_l_Int16_maxValue___closed__0);
return v___x_433_;
}
}
static uint16_t _init_l_Int16_minValue___closed__0(void){
_start:
{
lean_object* v___x_434_; uint16_t v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(32768u);
v___x_435_ = lean_int16_of_nat(v___x_434_);
return v___x_435_;
}
}
static uint16_t _init_l_Int16_minValue___closed__1(void){
_start:
{
uint16_t v___x_436_; uint16_t v___x_437_; 
v___x_436_ = lean_uint16_once(&l_Int16_minValue___closed__0, &l_Int16_minValue___closed__0_once, _init_l_Int16_minValue___closed__0);
v___x_437_ = lean_int16_neg(v___x_436_);
return v___x_437_;
}
}
static uint16_t _init_l_Int16_minValue(void){
_start:
{
uint16_t v___x_438_; 
v___x_438_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
return v___x_438_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntLE___redArg(lean_object* v_i_439_){
_start:
{
uint16_t v___x_440_; 
v___x_440_ = lean_int16_of_int(v_i_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntLE___redArg___boxed(lean_object* v_i_441_){
_start:
{
uint16_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_Int16_ofIntLE___redArg(v_i_441_);
lean_dec(v_i_441_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntLE(lean_object* v_i_444_, lean_object* v___hl_445_, lean_object* v___hr_446_){
_start:
{
uint16_t v___x_447_; 
v___x_447_ = lean_int16_of_int(v_i_444_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntLE___boxed(lean_object* v_i_448_, lean_object* v___hl_449_, lean_object* v___hr_450_){
_start:
{
uint16_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l_Int16_ofIntLE(v_i_448_, v___hl_449_, v___hr_450_);
lean_dec(v_i_448_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
static lean_object* _init_l_Int16_ofIntTruncate___closed__0(void){
_start:
{
uint16_t v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
v___x_454_ = lean_int16_to_int(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_l_Int16_ofIntTruncate___closed__1(void){
_start:
{
uint16_t v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_uint16_once(&l_Int16_maxValue___closed__0, &l_Int16_maxValue___closed__0_once, _init_l_Int16_maxValue___closed__0);
v___x_456_ = lean_int16_to_int(v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntTruncate(lean_object* v_i_457_){
_start:
{
uint16_t v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_458_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
v___x_459_ = lean_obj_once(&l_Int16_ofIntTruncate___closed__0, &l_Int16_ofIntTruncate___closed__0_once, _init_l_Int16_ofIntTruncate___closed__0);
v___x_460_ = lean_int_dec_le(v___x_459_, v_i_457_);
if (v___x_460_ == 0)
{
return v___x_458_;
}
else
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_obj_once(&l_Int16_ofIntTruncate___closed__1, &l_Int16_ofIntTruncate___closed__1_once, _init_l_Int16_ofIntTruncate___closed__1);
v___x_462_ = lean_int_dec_le(v_i_457_, v___x_461_);
if (v___x_462_ == 0)
{
return v___x_458_;
}
else
{
uint16_t v___x_463_; 
v___x_463_ = lean_int16_of_int(v_i_457_);
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntTruncate___boxed(lean_object* v_i_464_){
_start:
{
uint16_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Int16_ofIntTruncate(v_i_464_);
lean_dec(v_i_464_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT lean_object* l_Int16_add___boxed(lean_object* v_a_469_, lean_object* v_b_470_){
_start:
{
uint16_t v_a_boxed_471_; uint16_t v_b_boxed_472_; uint16_t v_res_473_; lean_object* v_r_474_; 
v_a_boxed_471_ = lean_unbox(v_a_469_);
v_b_boxed_472_ = lean_unbox(v_b_470_);
v_res_473_ = lean_int16_add(v_a_boxed_471_, v_b_boxed_472_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT lean_object* l_Int16_sub___boxed(lean_object* v_a_477_, lean_object* v_b_478_){
_start:
{
uint16_t v_a_boxed_479_; uint16_t v_b_boxed_480_; uint16_t v_res_481_; lean_object* v_r_482_; 
v_a_boxed_479_ = lean_unbox(v_a_477_);
v_b_boxed_480_ = lean_unbox(v_b_478_);
v_res_481_ = lean_int16_sub(v_a_boxed_479_, v_b_boxed_480_);
v_r_482_ = lean_box(v_res_481_);
return v_r_482_;
}
}
LEAN_EXPORT lean_object* l_Int16_mul___boxed(lean_object* v_a_485_, lean_object* v_b_486_){
_start:
{
uint16_t v_a_boxed_487_; uint16_t v_b_boxed_488_; uint16_t v_res_489_; lean_object* v_r_490_; 
v_a_boxed_487_ = lean_unbox(v_a_485_);
v_b_boxed_488_ = lean_unbox(v_b_486_);
v_res_489_ = lean_int16_mul(v_a_boxed_487_, v_b_boxed_488_);
v_r_490_ = lean_box(v_res_489_);
return v_r_490_;
}
}
LEAN_EXPORT lean_object* l_Int16_div___boxed(lean_object* v_a_493_, lean_object* v_b_494_){
_start:
{
uint16_t v_a_boxed_495_; uint16_t v_b_boxed_496_; uint16_t v_res_497_; lean_object* v_r_498_; 
v_a_boxed_495_ = lean_unbox(v_a_493_);
v_b_boxed_496_ = lean_unbox(v_b_494_);
v_res_497_ = lean_int16_div(v_a_boxed_495_, v_b_boxed_496_);
v_r_498_ = lean_box(v_res_497_);
return v_r_498_;
}
}
static uint16_t _init_l_Int16_pow___closed__0(void){
_start:
{
lean_object* v___x_499_; uint16_t v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_int16_of_nat(v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT uint16_t l_Int16_pow(uint16_t v_x_501_, lean_object* v_n_502_){
_start:
{
lean_object* v_zero_503_; uint8_t v_isZero_504_; 
v_zero_503_ = lean_unsigned_to_nat(0u);
v_isZero_504_ = lean_nat_dec_eq(v_n_502_, v_zero_503_);
if (v_isZero_504_ == 1)
{
uint16_t v___x_505_; 
v___x_505_ = lean_uint16_once(&l_Int16_pow___closed__0, &l_Int16_pow___closed__0_once, _init_l_Int16_pow___closed__0);
return v___x_505_;
}
else
{
lean_object* v_one_506_; lean_object* v_n_507_; uint16_t v___x_508_; uint16_t v___x_509_; 
v_one_506_ = lean_unsigned_to_nat(1u);
v_n_507_ = lean_nat_sub(v_n_502_, v_one_506_);
v___x_508_ = l_Int16_pow(v_x_501_, v_n_507_);
lean_dec(v_n_507_);
v___x_509_ = lean_int16_mul(v___x_508_, v_x_501_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l_Int16_pow___boxed(lean_object* v_x_510_, lean_object* v_n_511_){
_start:
{
uint16_t v_x_boxed_512_; uint16_t v_res_513_; lean_object* v_r_514_; 
v_x_boxed_512_ = lean_unbox(v_x_510_);
v_res_513_ = l_Int16_pow(v_x_boxed_512_, v_n_511_);
lean_dec(v_n_511_);
v_r_514_ = lean_box(v_res_513_);
return v_r_514_;
}
}
LEAN_EXPORT lean_object* l_Int16_mod___boxed(lean_object* v_a_517_, lean_object* v_b_518_){
_start:
{
uint16_t v_a_boxed_519_; uint16_t v_b_boxed_520_; uint16_t v_res_521_; lean_object* v_r_522_; 
v_a_boxed_519_ = lean_unbox(v_a_517_);
v_b_boxed_520_ = lean_unbox(v_b_518_);
v_res_521_ = lean_int16_mod(v_a_boxed_519_, v_b_boxed_520_);
v_r_522_ = lean_box(v_res_521_);
return v_r_522_;
}
}
LEAN_EXPORT lean_object* l_Int16_land___boxed(lean_object* v_a_525_, lean_object* v_b_526_){
_start:
{
uint16_t v_a_boxed_527_; uint16_t v_b_boxed_528_; uint16_t v_res_529_; lean_object* v_r_530_; 
v_a_boxed_527_ = lean_unbox(v_a_525_);
v_b_boxed_528_ = lean_unbox(v_b_526_);
v_res_529_ = lean_int16_land(v_a_boxed_527_, v_b_boxed_528_);
v_r_530_ = lean_box(v_res_529_);
return v_r_530_;
}
}
LEAN_EXPORT lean_object* l_Int16_lor___boxed(lean_object* v_a_533_, lean_object* v_b_534_){
_start:
{
uint16_t v_a_boxed_535_; uint16_t v_b_boxed_536_; uint16_t v_res_537_; lean_object* v_r_538_; 
v_a_boxed_535_ = lean_unbox(v_a_533_);
v_b_boxed_536_ = lean_unbox(v_b_534_);
v_res_537_ = lean_int16_lor(v_a_boxed_535_, v_b_boxed_536_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT lean_object* l_Int16_xor___boxed(lean_object* v_a_541_, lean_object* v_b_542_){
_start:
{
uint16_t v_a_boxed_543_; uint16_t v_b_boxed_544_; uint16_t v_res_545_; lean_object* v_r_546_; 
v_a_boxed_543_ = lean_unbox(v_a_541_);
v_b_boxed_544_ = lean_unbox(v_b_542_);
v_res_545_ = lean_int16_xor(v_a_boxed_543_, v_b_boxed_544_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT lean_object* l_Int16_shiftLeft___boxed(lean_object* v_a_549_, lean_object* v_b_550_){
_start:
{
uint16_t v_a_boxed_551_; uint16_t v_b_boxed_552_; uint16_t v_res_553_; lean_object* v_r_554_; 
v_a_boxed_551_ = lean_unbox(v_a_549_);
v_b_boxed_552_ = lean_unbox(v_b_550_);
v_res_553_ = lean_int16_shift_left(v_a_boxed_551_, v_b_boxed_552_);
v_r_554_ = lean_box(v_res_553_);
return v_r_554_;
}
}
LEAN_EXPORT lean_object* l_Int16_shiftRight___boxed(lean_object* v_a_557_, lean_object* v_b_558_){
_start:
{
uint16_t v_a_boxed_559_; uint16_t v_b_boxed_560_; uint16_t v_res_561_; lean_object* v_r_562_; 
v_a_boxed_559_ = lean_unbox(v_a_557_);
v_b_boxed_560_ = lean_unbox(v_b_558_);
v_res_561_ = lean_int16_shift_right(v_a_boxed_559_, v_b_boxed_560_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
LEAN_EXPORT lean_object* l_Int16_complement___boxed(lean_object* v_a_564_){
_start:
{
uint16_t v_a_boxed_565_; uint16_t v_res_566_; lean_object* v_r_567_; 
v_a_boxed_565_ = lean_unbox(v_a_564_);
v_res_566_ = lean_int16_complement(v_a_boxed_565_);
v_r_567_ = lean_box(v_res_566_);
return v_r_567_;
}
}
LEAN_EXPORT lean_object* l_Int16_abs___boxed(lean_object* v_a_569_){
_start:
{
uint16_t v_a_boxed_570_; uint16_t v_res_571_; lean_object* v_r_572_; 
v_a_boxed_570_ = lean_unbox(v_a_569_);
v_res_571_ = lean_int16_abs(v_a_boxed_570_);
v_r_572_ = lean_box(v_res_571_);
return v_r_572_;
}
}
LEAN_EXPORT lean_object* l_Int16_decEq___boxed(lean_object* v_a_575_, lean_object* v_b_576_){
_start:
{
uint16_t v_a_boxed_577_; uint16_t v_b_boxed_578_; uint8_t v_res_579_; lean_object* v_r_580_; 
v_a_boxed_577_ = lean_unbox(v_a_575_);
v_b_boxed_578_ = lean_unbox(v_b_576_);
v_res_579_ = lean_int16_dec_eq(v_a_boxed_577_, v_b_boxed_578_);
v_r_580_ = lean_box(v_res_579_);
return v_r_580_;
}
}
static uint16_t _init_l_instInhabitedInt16___closed__0(void){
_start:
{
lean_object* v___x_581_; uint16_t v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_int16_of_nat(v___x_581_);
return v___x_582_;
}
}
static uint16_t _init_l_instInhabitedInt16(void){
_start:
{
uint16_t v___x_583_; 
v___x_583_ = lean_uint16_once(&l_instInhabitedInt16___closed__0, &l_instInhabitedInt16___closed__0_once, _init_l_instInhabitedInt16___closed__0);
return v___x_583_;
}
}
static lean_object* _init_l_instLTInt16(void){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = lean_box(0);
return v___x_596_;
}
}
static lean_object* _init_l_instLEInt16(void){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = lean_box(0);
return v___x_597_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt16(uint16_t v_a_610_, uint16_t v_b_611_){
_start:
{
uint8_t v___x_612_; 
v___x_612_ = lean_int16_dec_eq(v_a_610_, v_b_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt16___boxed(lean_object* v_a_613_, lean_object* v_b_614_){
_start:
{
uint16_t v_a_boxed_615_; uint16_t v_b_boxed_616_; uint8_t v_res_617_; lean_object* v_r_618_; 
v_a_boxed_615_ = lean_unbox(v_a_613_);
v_b_boxed_616_ = lean_unbox(v_b_614_);
v_res_617_ = l_instDecidableEqInt16(v_a_boxed_615_, v_b_boxed_616_);
v_r_618_ = lean_box(v_res_617_);
return v_r_618_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt16___boxed(lean_object* v_b_620_){
_start:
{
uint8_t v_b_boxed_621_; uint16_t v_res_622_; lean_object* v_r_623_; 
v_b_boxed_621_ = lean_unbox(v_b_620_);
v_res_622_ = lean_bool_to_int16(v_b_boxed_621_);
v_r_623_ = lean_box(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLt___boxed(lean_object* v_a_626_, lean_object* v_b_627_){
_start:
{
uint16_t v_a_boxed_628_; uint16_t v_b_boxed_629_; uint8_t v_res_630_; lean_object* v_r_631_; 
v_a_boxed_628_ = lean_unbox(v_a_626_);
v_b_boxed_629_ = lean_unbox(v_b_627_);
v_res_630_ = lean_int16_dec_lt(v_a_boxed_628_, v_b_boxed_629_);
v_r_631_ = lean_box(v_res_630_);
return v_r_631_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLe___boxed(lean_object* v_a_634_, lean_object* v_b_635_){
_start:
{
uint16_t v_a_boxed_636_; uint16_t v_b_boxed_637_; uint8_t v_res_638_; lean_object* v_r_639_; 
v_a_boxed_636_ = lean_unbox(v_a_634_);
v_b_boxed_637_ = lean_unbox(v_b_635_);
v_res_638_ = lean_int16_dec_le(v_a_boxed_636_, v_b_boxed_637_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT uint16_t l_instMaxInt16___lam__0(uint16_t v_x_640_, uint16_t v_y_641_){
_start:
{
uint8_t v___x_642_; 
v___x_642_ = lean_int16_dec_le(v_x_640_, v_y_641_);
if (v___x_642_ == 0)
{
return v_x_640_;
}
else
{
return v_y_641_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt16___lam__0___boxed(lean_object* v_x_643_, lean_object* v_y_644_){
_start:
{
uint16_t v_x_boxed_645_; uint16_t v_y_boxed_646_; uint16_t v_res_647_; lean_object* v_r_648_; 
v_x_boxed_645_ = lean_unbox(v_x_643_);
v_y_boxed_646_ = lean_unbox(v_y_644_);
v_res_647_ = l_instMaxInt16___lam__0(v_x_boxed_645_, v_y_boxed_646_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
LEAN_EXPORT uint16_t l_instMinInt16___lam__0(uint16_t v_x_651_, uint16_t v_y_652_){
_start:
{
uint8_t v___x_653_; 
v___x_653_ = lean_int16_dec_le(v_x_651_, v_y_652_);
if (v___x_653_ == 0)
{
return v_y_652_;
}
else
{
return v_x_651_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt16___lam__0___boxed(lean_object* v_x_654_, lean_object* v_y_655_){
_start:
{
uint16_t v_x_boxed_656_; uint16_t v_y_boxed_657_; uint16_t v_res_658_; lean_object* v_r_659_; 
v_x_boxed_656_ = lean_unbox(v_x_654_);
v_y_boxed_657_ = lean_unbox(v_y_655_);
v_res_658_ = l_instMinInt16___lam__0(v_x_boxed_656_, v_y_boxed_657_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
static lean_object* _init_l_Int32_size(void){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = lean_cstr_to_nat("4294967296");
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Int32_toBitVec(uint32_t v_x_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = lean_uint32_to_nat(v_x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Int32_toBitVec___boxed(lean_object* v_x_665_){
_start:
{
uint32_t v_x_boxed_666_; lean_object* v_res_667_; 
v_x_boxed_666_ = lean_unbox_uint32(v_x_665_);
lean_dec(v_x_665_);
v_res_667_ = l_Int32_toBitVec(v_x_boxed_666_);
return v_res_667_;
}
}
LEAN_EXPORT uint32_t l_UInt32_toInt32(uint32_t v_i_668_){
_start:
{
return v_i_668_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toInt32___boxed(lean_object* v_i_669_){
_start:
{
uint32_t v_i_boxed_670_; uint32_t v_res_671_; lean_object* v_r_672_; 
v_i_boxed_670_ = lean_unbox_uint32(v_i_669_);
lean_dec(v_i_669_);
v_res_671_ = l_UInt32_toInt32(v_i_boxed_670_);
v_r_672_ = lean_box_uint32(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofInt___boxed(lean_object* v_i_674_){
_start:
{
uint32_t v_res_675_; lean_object* v_r_676_; 
v_res_675_ = lean_int32_of_int(v_i_674_);
lean_dec(v_i_674_);
v_r_676_ = lean_box_uint32(v_res_675_);
return v_r_676_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofNat___boxed(lean_object* v_n_678_){
_start:
{
uint32_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = lean_int32_of_nat(v_n_678_);
lean_dec(v_n_678_);
v_r_680_ = lean_box_uint32(v_res_679_);
return v_r_680_;
}
}
LEAN_EXPORT uint32_t l_Int_toInt32(lean_object* v_i_681_){
_start:
{
uint32_t v___x_682_; 
v___x_682_ = lean_int32_of_int(v_i_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt32___boxed(lean_object* v_i_683_){
_start:
{
uint32_t v_res_684_; lean_object* v_r_685_; 
v_res_684_ = l_Int_toInt32(v_i_683_);
lean_dec(v_i_683_);
v_r_685_ = lean_box_uint32(v_res_684_);
return v_r_685_;
}
}
LEAN_EXPORT uint32_t l_Nat_toInt32(lean_object* v_n_686_){
_start:
{
uint32_t v___x_687_; 
v___x_687_ = lean_int32_of_nat(v_n_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt32___boxed(lean_object* v_n_688_){
_start:
{
uint32_t v_res_689_; lean_object* v_r_690_; 
v_res_689_ = l_Nat_toInt32(v_n_688_);
lean_dec(v_n_688_);
v_r_690_ = lean_box_uint32(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt___boxed(lean_object* v_i_692_){
_start:
{
uint32_t v_i_boxed_693_; lean_object* v_res_694_; 
v_i_boxed_693_ = lean_unbox_uint32(v_i_692_);
lean_dec(v_i_692_);
v_res_694_ = lean_int32_to_int(v_i_boxed_693_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg(uint32_t v_i_695_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_int32_to_int(v_i_695_);
v___x_697_ = l_Int_toNat(v___x_696_);
lean_dec(v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg___boxed(lean_object* v_i_698_){
_start:
{
uint32_t v_i_boxed_699_; lean_object* v_res_700_; 
v_i_boxed_699_ = lean_unbox_uint32(v_i_698_);
lean_dec(v_i_698_);
v_res_700_ = l_Int32_toNatClampNeg(v_i_boxed_699_);
return v_res_700_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofBitVec(lean_object* v_b_701_){
_start:
{
uint32_t v___x_702_; 
v___x_702_ = lean_uint32_of_nat_mk(v_b_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofBitVec___boxed(lean_object* v_b_703_){
_start:
{
uint32_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = l_Int32_ofBitVec(v_b_703_);
v_r_705_ = lean_box_uint32(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt8___boxed(lean_object* v_a_707_){
_start:
{
uint32_t v_a_boxed_708_; uint8_t v_res_709_; lean_object* v_r_710_; 
v_a_boxed_708_ = lean_unbox_uint32(v_a_707_);
lean_dec(v_a_707_);
v_res_709_ = lean_int32_to_int8(v_a_boxed_708_);
v_r_710_ = lean_box(v_res_709_);
return v_r_710_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt16___boxed(lean_object* v_a_712_){
_start:
{
uint32_t v_a_boxed_713_; uint16_t v_res_714_; lean_object* v_r_715_; 
v_a_boxed_713_ = lean_unbox_uint32(v_a_712_);
lean_dec(v_a_712_);
v_res_714_ = lean_int32_to_int16(v_a_boxed_713_);
v_r_715_ = lean_box(v_res_714_);
return v_r_715_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt32___boxed(lean_object* v_a_717_){
_start:
{
uint8_t v_a_boxed_718_; uint32_t v_res_719_; lean_object* v_r_720_; 
v_a_boxed_718_ = lean_unbox(v_a_717_);
v_res_719_ = lean_int8_to_int32(v_a_boxed_718_);
v_r_720_ = lean_box_uint32(v_res_719_);
return v_r_720_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt32___boxed(lean_object* v_a_722_){
_start:
{
uint16_t v_a_boxed_723_; uint32_t v_res_724_; lean_object* v_r_725_; 
v_a_boxed_723_ = lean_unbox(v_a_722_);
v_res_724_ = lean_int16_to_int32(v_a_boxed_723_);
v_r_725_ = lean_box_uint32(v_res_724_);
return v_r_725_;
}
}
LEAN_EXPORT lean_object* l_Int32_neg___boxed(lean_object* v_i_727_){
_start:
{
uint32_t v_i_boxed_728_; uint32_t v_res_729_; lean_object* v_r_730_; 
v_i_boxed_728_ = lean_unbox_uint32(v_i_727_);
lean_dec(v_i_727_);
v_res_729_ = lean_int32_neg(v_i_boxed_728_);
v_r_730_ = lean_box_uint32(v_res_729_);
return v_r_730_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0(uint32_t v_i_731_){
_start:
{
lean_object* v___x_732_; lean_object* v_intZero_733_; uint8_t v_isNeg_734_; 
v___x_732_ = lean_int32_to_int(v_i_731_);
v_intZero_733_ = lean_obj_once(&l_instToStringInt8___lam__0___closed__0, &l_instToStringInt8___lam__0___closed__0_once, _init_l_instToStringInt8___lam__0___closed__0);
v_isNeg_734_ = lean_int_dec_lt(v___x_732_, v_intZero_733_);
if (v_isNeg_734_ == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; 
v_a_735_ = lean_nat_abs(v___x_732_);
lean_dec(v___x_732_);
v___x_736_ = l_Nat_reprFast(v_a_735_);
return v___x_736_;
}
else
{
lean_object* v_abs_737_; lean_object* v_one_738_; lean_object* v_a_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_abs_737_ = lean_nat_abs(v___x_732_);
lean_dec(v___x_732_);
v_one_738_ = lean_unsigned_to_nat(1u);
v_a_739_ = lean_nat_sub(v_abs_737_, v_one_738_);
lean_dec(v_abs_737_);
v___x_740_ = ((lean_object*)(l_instToStringInt8___lam__0___closed__1));
v___x_741_ = lean_nat_add(v_a_739_, v_one_738_);
lean_dec(v_a_739_);
v___x_742_ = l_Nat_reprFast(v___x_741_);
v___x_743_ = lean_string_append(v___x_740_, v___x_742_);
lean_dec_ref(v___x_742_);
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0___boxed(lean_object* v_i_744_){
_start:
{
uint32_t v_i_boxed_745_; lean_object* v_res_746_; 
v_i_boxed_745_ = lean_unbox_uint32(v_i_744_);
lean_dec(v_i_744_);
v_res_746_ = l_instToStringInt32___lam__0(v_i_boxed_745_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_instReprInt32___lam__0(uint32_t v_i_749_, lean_object* v_prec_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_751_ = lean_int32_to_int(v_i_749_);
v___x_752_ = lean_obj_once(&l_instToStringInt8___lam__0___closed__0, &l_instToStringInt8___lam__0___closed__0_once, _init_l_instToStringInt8___lam__0___closed__0);
v___x_753_ = lean_int_dec_lt(v___x_751_, v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = l_Int_repr(v___x_751_);
lean_dec(v___x_751_);
v___x_755_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = l_Int_repr(v___x_751_);
lean_dec(v___x_751_);
v___x_757_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___x_758_ = l_Repr_addAppParen(v___x_757_, v_prec_750_);
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt32___lam__0___boxed(lean_object* v_i_759_, lean_object* v_prec_760_){
_start:
{
uint32_t v_i_boxed_761_; lean_object* v_res_762_; 
v_i_boxed_761_ = lean_unbox_uint32(v_i_759_);
lean_dec(v_i_759_);
v_res_762_ = l_instReprInt32___lam__0(v_i_boxed_761_, v_prec_760_);
lean_dec(v_prec_760_);
return v_res_762_;
}
}
static lean_object* _init_l_instReprAtomInt32(void){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = lean_box(0);
return v___x_765_;
}
}
LEAN_EXPORT uint32_t l_Int32_instOfNat(lean_object* v_n_768_){
_start:
{
uint32_t v___x_769_; 
v___x_769_ = lean_int32_of_nat(v_n_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Int32_instOfNat___boxed(lean_object* v_n_770_){
_start:
{
uint32_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l_Int32_instOfNat(v_n_770_);
lean_dec(v_n_770_);
v_r_772_ = lean_box_uint32(v_res_771_);
return v_r_772_;
}
}
static uint32_t _init_l_Int32_maxValue___closed__0(void){
_start:
{
lean_object* v___x_775_; uint32_t v___x_776_; 
v___x_775_ = lean_unsigned_to_nat(2147483647u);
v___x_776_ = lean_int32_of_nat(v___x_775_);
return v___x_776_;
}
}
static uint32_t _init_l_Int32_maxValue(void){
_start:
{
uint32_t v___x_777_; 
v___x_777_ = lean_uint32_once(&l_Int32_maxValue___closed__0, &l_Int32_maxValue___closed__0_once, _init_l_Int32_maxValue___closed__0);
return v___x_777_;
}
}
static uint32_t _init_l_Int32_minValue___closed__0(void){
_start:
{
lean_object* v___x_778_; uint32_t v___x_779_; 
v___x_778_ = lean_unsigned_to_nat(2147483648u);
v___x_779_ = lean_int32_of_nat(v___x_778_);
return v___x_779_;
}
}
static uint32_t _init_l_Int32_minValue___closed__1(void){
_start:
{
uint32_t v___x_780_; uint32_t v___x_781_; 
v___x_780_ = lean_uint32_once(&l_Int32_minValue___closed__0, &l_Int32_minValue___closed__0_once, _init_l_Int32_minValue___closed__0);
v___x_781_ = lean_int32_neg(v___x_780_);
return v___x_781_;
}
}
static uint32_t _init_l_Int32_minValue(void){
_start:
{
uint32_t v___x_782_; 
v___x_782_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
return v___x_782_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntLE___redArg(lean_object* v_i_783_){
_start:
{
uint32_t v___x_784_; 
v___x_784_ = lean_int32_of_int(v_i_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntLE___redArg___boxed(lean_object* v_i_785_){
_start:
{
uint32_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_Int32_ofIntLE___redArg(v_i_785_);
lean_dec(v_i_785_);
v_r_787_ = lean_box_uint32(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntLE(lean_object* v_i_788_, lean_object* v___hl_789_, lean_object* v___hr_790_){
_start:
{
uint32_t v___x_791_; 
v___x_791_ = lean_int32_of_int(v_i_788_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntLE___boxed(lean_object* v_i_792_, lean_object* v___hl_793_, lean_object* v___hr_794_){
_start:
{
uint32_t v_res_795_; lean_object* v_r_796_; 
v_res_795_ = l_Int32_ofIntLE(v_i_792_, v___hl_793_, v___hr_794_);
lean_dec(v_i_792_);
v_r_796_ = lean_box_uint32(v_res_795_);
return v_r_796_;
}
}
static lean_object* _init_l_Int32_ofIntTruncate___closed__0(void){
_start:
{
uint32_t v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
v___x_798_ = lean_int32_to_int(v___x_797_);
return v___x_798_;
}
}
static lean_object* _init_l_Int32_ofIntTruncate___closed__1(void){
_start:
{
uint32_t v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_uint32_once(&l_Int32_maxValue___closed__0, &l_Int32_maxValue___closed__0_once, _init_l_Int32_maxValue___closed__0);
v___x_800_ = lean_int32_to_int(v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntTruncate(lean_object* v_i_801_){
_start:
{
uint32_t v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_802_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
v___x_803_ = lean_obj_once(&l_Int32_ofIntTruncate___closed__0, &l_Int32_ofIntTruncate___closed__0_once, _init_l_Int32_ofIntTruncate___closed__0);
v___x_804_ = lean_int_dec_le(v___x_803_, v_i_801_);
if (v___x_804_ == 0)
{
return v___x_802_;
}
else
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = lean_obj_once(&l_Int32_ofIntTruncate___closed__1, &l_Int32_ofIntTruncate___closed__1_once, _init_l_Int32_ofIntTruncate___closed__1);
v___x_806_ = lean_int_dec_le(v_i_801_, v___x_805_);
if (v___x_806_ == 0)
{
return v___x_802_;
}
else
{
uint32_t v___x_807_; 
v___x_807_ = lean_int32_of_int(v_i_801_);
return v___x_807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntTruncate___boxed(lean_object* v_i_808_){
_start:
{
uint32_t v_res_809_; lean_object* v_r_810_; 
v_res_809_ = l_Int32_ofIntTruncate(v_i_808_);
lean_dec(v_i_808_);
v_r_810_ = lean_box_uint32(v_res_809_);
return v_r_810_;
}
}
LEAN_EXPORT lean_object* l_Int32_add___boxed(lean_object* v_a_813_, lean_object* v_b_814_){
_start:
{
uint32_t v_a_boxed_815_; uint32_t v_b_boxed_816_; uint32_t v_res_817_; lean_object* v_r_818_; 
v_a_boxed_815_ = lean_unbox_uint32(v_a_813_);
lean_dec(v_a_813_);
v_b_boxed_816_ = lean_unbox_uint32(v_b_814_);
lean_dec(v_b_814_);
v_res_817_ = lean_int32_add(v_a_boxed_815_, v_b_boxed_816_);
v_r_818_ = lean_box_uint32(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT lean_object* l_Int32_sub___boxed(lean_object* v_a_821_, lean_object* v_b_822_){
_start:
{
uint32_t v_a_boxed_823_; uint32_t v_b_boxed_824_; uint32_t v_res_825_; lean_object* v_r_826_; 
v_a_boxed_823_ = lean_unbox_uint32(v_a_821_);
lean_dec(v_a_821_);
v_b_boxed_824_ = lean_unbox_uint32(v_b_822_);
lean_dec(v_b_822_);
v_res_825_ = lean_int32_sub(v_a_boxed_823_, v_b_boxed_824_);
v_r_826_ = lean_box_uint32(v_res_825_);
return v_r_826_;
}
}
LEAN_EXPORT lean_object* l_Int32_mul___boxed(lean_object* v_a_829_, lean_object* v_b_830_){
_start:
{
uint32_t v_a_boxed_831_; uint32_t v_b_boxed_832_; uint32_t v_res_833_; lean_object* v_r_834_; 
v_a_boxed_831_ = lean_unbox_uint32(v_a_829_);
lean_dec(v_a_829_);
v_b_boxed_832_ = lean_unbox_uint32(v_b_830_);
lean_dec(v_b_830_);
v_res_833_ = lean_int32_mul(v_a_boxed_831_, v_b_boxed_832_);
v_r_834_ = lean_box_uint32(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT lean_object* l_Int32_div___boxed(lean_object* v_a_837_, lean_object* v_b_838_){
_start:
{
uint32_t v_a_boxed_839_; uint32_t v_b_boxed_840_; uint32_t v_res_841_; lean_object* v_r_842_; 
v_a_boxed_839_ = lean_unbox_uint32(v_a_837_);
lean_dec(v_a_837_);
v_b_boxed_840_ = lean_unbox_uint32(v_b_838_);
lean_dec(v_b_838_);
v_res_841_ = lean_int32_div(v_a_boxed_839_, v_b_boxed_840_);
v_r_842_ = lean_box_uint32(v_res_841_);
return v_r_842_;
}
}
static uint32_t _init_l_Int32_pow___closed__0(void){
_start:
{
lean_object* v___x_843_; uint32_t v___x_844_; 
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = lean_int32_of_nat(v___x_843_);
return v___x_844_;
}
}
LEAN_EXPORT uint32_t l_Int32_pow(uint32_t v_x_845_, lean_object* v_n_846_){
_start:
{
lean_object* v_zero_847_; uint8_t v_isZero_848_; 
v_zero_847_ = lean_unsigned_to_nat(0u);
v_isZero_848_ = lean_nat_dec_eq(v_n_846_, v_zero_847_);
if (v_isZero_848_ == 1)
{
uint32_t v___x_849_; 
v___x_849_ = lean_uint32_once(&l_Int32_pow___closed__0, &l_Int32_pow___closed__0_once, _init_l_Int32_pow___closed__0);
return v___x_849_;
}
else
{
lean_object* v_one_850_; lean_object* v_n_851_; uint32_t v___x_852_; uint32_t v___x_853_; 
v_one_850_ = lean_unsigned_to_nat(1u);
v_n_851_ = lean_nat_sub(v_n_846_, v_one_850_);
v___x_852_ = l_Int32_pow(v_x_845_, v_n_851_);
lean_dec(v_n_851_);
v___x_853_ = lean_int32_mul(v___x_852_, v_x_845_);
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l_Int32_pow___boxed(lean_object* v_x_854_, lean_object* v_n_855_){
_start:
{
uint32_t v_x_boxed_856_; uint32_t v_res_857_; lean_object* v_r_858_; 
v_x_boxed_856_ = lean_unbox_uint32(v_x_854_);
lean_dec(v_x_854_);
v_res_857_ = l_Int32_pow(v_x_boxed_856_, v_n_855_);
lean_dec(v_n_855_);
v_r_858_ = lean_box_uint32(v_res_857_);
return v_r_858_;
}
}
LEAN_EXPORT lean_object* l_Int32_mod___boxed(lean_object* v_a_861_, lean_object* v_b_862_){
_start:
{
uint32_t v_a_boxed_863_; uint32_t v_b_boxed_864_; uint32_t v_res_865_; lean_object* v_r_866_; 
v_a_boxed_863_ = lean_unbox_uint32(v_a_861_);
lean_dec(v_a_861_);
v_b_boxed_864_ = lean_unbox_uint32(v_b_862_);
lean_dec(v_b_862_);
v_res_865_ = lean_int32_mod(v_a_boxed_863_, v_b_boxed_864_);
v_r_866_ = lean_box_uint32(v_res_865_);
return v_r_866_;
}
}
LEAN_EXPORT lean_object* l_Int32_land___boxed(lean_object* v_a_869_, lean_object* v_b_870_){
_start:
{
uint32_t v_a_boxed_871_; uint32_t v_b_boxed_872_; uint32_t v_res_873_; lean_object* v_r_874_; 
v_a_boxed_871_ = lean_unbox_uint32(v_a_869_);
lean_dec(v_a_869_);
v_b_boxed_872_ = lean_unbox_uint32(v_b_870_);
lean_dec(v_b_870_);
v_res_873_ = lean_int32_land(v_a_boxed_871_, v_b_boxed_872_);
v_r_874_ = lean_box_uint32(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT lean_object* l_Int32_lor___boxed(lean_object* v_a_877_, lean_object* v_b_878_){
_start:
{
uint32_t v_a_boxed_879_; uint32_t v_b_boxed_880_; uint32_t v_res_881_; lean_object* v_r_882_; 
v_a_boxed_879_ = lean_unbox_uint32(v_a_877_);
lean_dec(v_a_877_);
v_b_boxed_880_ = lean_unbox_uint32(v_b_878_);
lean_dec(v_b_878_);
v_res_881_ = lean_int32_lor(v_a_boxed_879_, v_b_boxed_880_);
v_r_882_ = lean_box_uint32(v_res_881_);
return v_r_882_;
}
}
LEAN_EXPORT lean_object* l_Int32_xor___boxed(lean_object* v_a_885_, lean_object* v_b_886_){
_start:
{
uint32_t v_a_boxed_887_; uint32_t v_b_boxed_888_; uint32_t v_res_889_; lean_object* v_r_890_; 
v_a_boxed_887_ = lean_unbox_uint32(v_a_885_);
lean_dec(v_a_885_);
v_b_boxed_888_ = lean_unbox_uint32(v_b_886_);
lean_dec(v_b_886_);
v_res_889_ = lean_int32_xor(v_a_boxed_887_, v_b_boxed_888_);
v_r_890_ = lean_box_uint32(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT lean_object* l_Int32_shiftLeft___boxed(lean_object* v_a_893_, lean_object* v_b_894_){
_start:
{
uint32_t v_a_boxed_895_; uint32_t v_b_boxed_896_; uint32_t v_res_897_; lean_object* v_r_898_; 
v_a_boxed_895_ = lean_unbox_uint32(v_a_893_);
lean_dec(v_a_893_);
v_b_boxed_896_ = lean_unbox_uint32(v_b_894_);
lean_dec(v_b_894_);
v_res_897_ = lean_int32_shift_left(v_a_boxed_895_, v_b_boxed_896_);
v_r_898_ = lean_box_uint32(v_res_897_);
return v_r_898_;
}
}
LEAN_EXPORT lean_object* l_Int32_shiftRight___boxed(lean_object* v_a_901_, lean_object* v_b_902_){
_start:
{
uint32_t v_a_boxed_903_; uint32_t v_b_boxed_904_; uint32_t v_res_905_; lean_object* v_r_906_; 
v_a_boxed_903_ = lean_unbox_uint32(v_a_901_);
lean_dec(v_a_901_);
v_b_boxed_904_ = lean_unbox_uint32(v_b_902_);
lean_dec(v_b_902_);
v_res_905_ = lean_int32_shift_right(v_a_boxed_903_, v_b_boxed_904_);
v_r_906_ = lean_box_uint32(v_res_905_);
return v_r_906_;
}
}
LEAN_EXPORT lean_object* l_Int32_complement___boxed(lean_object* v_a_908_){
_start:
{
uint32_t v_a_boxed_909_; uint32_t v_res_910_; lean_object* v_r_911_; 
v_a_boxed_909_ = lean_unbox_uint32(v_a_908_);
lean_dec(v_a_908_);
v_res_910_ = lean_int32_complement(v_a_boxed_909_);
v_r_911_ = lean_box_uint32(v_res_910_);
return v_r_911_;
}
}
LEAN_EXPORT lean_object* l_Int32_abs___boxed(lean_object* v_a_913_){
_start:
{
uint32_t v_a_boxed_914_; uint32_t v_res_915_; lean_object* v_r_916_; 
v_a_boxed_914_ = lean_unbox_uint32(v_a_913_);
lean_dec(v_a_913_);
v_res_915_ = lean_int32_abs(v_a_boxed_914_);
v_r_916_ = lean_box_uint32(v_res_915_);
return v_r_916_;
}
}
LEAN_EXPORT lean_object* l_Int32_decEq___boxed(lean_object* v_a_919_, lean_object* v_b_920_){
_start:
{
uint32_t v_a_boxed_921_; uint32_t v_b_boxed_922_; uint8_t v_res_923_; lean_object* v_r_924_; 
v_a_boxed_921_ = lean_unbox_uint32(v_a_919_);
lean_dec(v_a_919_);
v_b_boxed_922_ = lean_unbox_uint32(v_b_920_);
lean_dec(v_b_920_);
v_res_923_ = lean_int32_dec_eq(v_a_boxed_921_, v_b_boxed_922_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
static uint32_t _init_l_instInhabitedInt32___closed__0(void){
_start:
{
lean_object* v___x_925_; uint32_t v___x_926_; 
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = lean_int32_of_nat(v___x_925_);
return v___x_926_;
}
}
static uint32_t _init_l_instInhabitedInt32(void){
_start:
{
uint32_t v___x_927_; 
v___x_927_ = lean_uint32_once(&l_instInhabitedInt32___closed__0, &l_instInhabitedInt32___closed__0_once, _init_l_instInhabitedInt32___closed__0);
return v___x_927_;
}
}
static lean_object* _init_l_instLTInt32(void){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = lean_box(0);
return v___x_940_;
}
}
static lean_object* _init_l_instLEInt32(void){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = lean_box(0);
return v___x_941_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt32(uint32_t v_a_954_, uint32_t v_b_955_){
_start:
{
uint8_t v___x_956_; 
v___x_956_ = lean_int32_dec_eq(v_a_954_, v_b_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt32___boxed(lean_object* v_a_957_, lean_object* v_b_958_){
_start:
{
uint32_t v_a_boxed_959_; uint32_t v_b_boxed_960_; uint8_t v_res_961_; lean_object* v_r_962_; 
v_a_boxed_959_ = lean_unbox_uint32(v_a_957_);
lean_dec(v_a_957_);
v_b_boxed_960_ = lean_unbox_uint32(v_b_958_);
lean_dec(v_b_958_);
v_res_961_ = l_instDecidableEqInt32(v_a_boxed_959_, v_b_boxed_960_);
v_r_962_ = lean_box(v_res_961_);
return v_r_962_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt32___boxed(lean_object* v_b_964_){
_start:
{
uint8_t v_b_boxed_965_; uint32_t v_res_966_; lean_object* v_r_967_; 
v_b_boxed_965_ = lean_unbox(v_b_964_);
v_res_966_ = lean_bool_to_int32(v_b_boxed_965_);
v_r_967_ = lean_box_uint32(v_res_966_);
return v_r_967_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLt___boxed(lean_object* v_a_970_, lean_object* v_b_971_){
_start:
{
uint32_t v_a_boxed_972_; uint32_t v_b_boxed_973_; uint8_t v_res_974_; lean_object* v_r_975_; 
v_a_boxed_972_ = lean_unbox_uint32(v_a_970_);
lean_dec(v_a_970_);
v_b_boxed_973_ = lean_unbox_uint32(v_b_971_);
lean_dec(v_b_971_);
v_res_974_ = lean_int32_dec_lt(v_a_boxed_972_, v_b_boxed_973_);
v_r_975_ = lean_box(v_res_974_);
return v_r_975_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLe___boxed(lean_object* v_a_978_, lean_object* v_b_979_){
_start:
{
uint32_t v_a_boxed_980_; uint32_t v_b_boxed_981_; uint8_t v_res_982_; lean_object* v_r_983_; 
v_a_boxed_980_ = lean_unbox_uint32(v_a_978_);
lean_dec(v_a_978_);
v_b_boxed_981_ = lean_unbox_uint32(v_b_979_);
lean_dec(v_b_979_);
v_res_982_ = lean_int32_dec_le(v_a_boxed_980_, v_b_boxed_981_);
v_r_983_ = lean_box(v_res_982_);
return v_r_983_;
}
}
LEAN_EXPORT uint32_t l_instMaxInt32___lam__0(uint32_t v_x_984_, uint32_t v_y_985_){
_start:
{
uint8_t v___x_986_; 
v___x_986_ = lean_int32_dec_le(v_x_984_, v_y_985_);
if (v___x_986_ == 0)
{
return v_x_984_;
}
else
{
return v_y_985_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt32___lam__0___boxed(lean_object* v_x_987_, lean_object* v_y_988_){
_start:
{
uint32_t v_x_boxed_989_; uint32_t v_y_boxed_990_; uint32_t v_res_991_; lean_object* v_r_992_; 
v_x_boxed_989_ = lean_unbox_uint32(v_x_987_);
lean_dec(v_x_987_);
v_y_boxed_990_ = lean_unbox_uint32(v_y_988_);
lean_dec(v_y_988_);
v_res_991_ = l_instMaxInt32___lam__0(v_x_boxed_989_, v_y_boxed_990_);
v_r_992_ = lean_box_uint32(v_res_991_);
return v_r_992_;
}
}
LEAN_EXPORT uint32_t l_instMinInt32___lam__0(uint32_t v_x_995_, uint32_t v_y_996_){
_start:
{
uint8_t v___x_997_; 
v___x_997_ = lean_int32_dec_le(v_x_995_, v_y_996_);
if (v___x_997_ == 0)
{
return v_y_996_;
}
else
{
return v_x_995_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt32___lam__0___boxed(lean_object* v_x_998_, lean_object* v_y_999_){
_start:
{
uint32_t v_x_boxed_1000_; uint32_t v_y_boxed_1001_; uint32_t v_res_1002_; lean_object* v_r_1003_; 
v_x_boxed_1000_ = lean_unbox_uint32(v_x_998_);
lean_dec(v_x_998_);
v_y_boxed_1001_ = lean_unbox_uint32(v_y_999_);
lean_dec(v_y_999_);
v_res_1002_ = l_instMinInt32___lam__0(v_x_boxed_1000_, v_y_boxed_1001_);
v_r_1003_ = lean_box_uint32(v_res_1002_);
return v_r_1003_;
}
}
static lean_object* _init_l_Int64_size___closed__0(void){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_cstr_to_nat("18446744073709551616");
return v___x_1006_;
}
}
static lean_object* _init_l_Int64_size(void){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_obj_once(&l_Int64_size___closed__0, &l_Int64_size___closed__0_once, _init_l_Int64_size___closed__0);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Int64_toBitVec(uint64_t v_x_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_uint64_to_nat(v_x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Int64_toBitVec___boxed(lean_object* v_x_1010_){
_start:
{
uint64_t v_x_boxed_1011_; lean_object* v_res_1012_; 
v_x_boxed_1011_ = lean_unbox_uint64(v_x_1010_);
lean_dec_ref(v_x_1010_);
v_res_1012_ = l_Int64_toBitVec(v_x_boxed_1011_);
return v_res_1012_;
}
}
LEAN_EXPORT uint64_t l_UInt64_toInt64(uint64_t v_i_1013_){
_start:
{
return v_i_1013_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toInt64___boxed(lean_object* v_i_1014_){
_start:
{
uint64_t v_i_boxed_1015_; uint64_t v_res_1016_; lean_object* v_r_1017_; 
v_i_boxed_1015_ = lean_unbox_uint64(v_i_1014_);
lean_dec_ref(v_i_1014_);
v_res_1016_ = l_UInt64_toInt64(v_i_boxed_1015_);
v_r_1017_ = lean_box_uint64(v_res_1016_);
return v_r_1017_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofInt___boxed(lean_object* v_i_1019_){
_start:
{
uint64_t v_res_1020_; lean_object* v_r_1021_; 
v_res_1020_ = lean_int64_of_int(v_i_1019_);
lean_dec(v_i_1019_);
v_r_1021_ = lean_box_uint64(v_res_1020_);
return v_r_1021_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofNat___boxed(lean_object* v_n_1023_){
_start:
{
uint64_t v_res_1024_; lean_object* v_r_1025_; 
v_res_1024_ = lean_int64_of_nat(v_n_1023_);
lean_dec(v_n_1023_);
v_r_1025_ = lean_box_uint64(v_res_1024_);
return v_r_1025_;
}
}
LEAN_EXPORT uint64_t l_Int_toInt64(lean_object* v_i_1026_){
_start:
{
uint64_t v___x_1027_; 
v___x_1027_ = lean_int64_of_int(v_i_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt64___boxed(lean_object* v_i_1028_){
_start:
{
uint64_t v_res_1029_; lean_object* v_r_1030_; 
v_res_1029_ = l_Int_toInt64(v_i_1028_);
lean_dec(v_i_1028_);
v_r_1030_ = lean_box_uint64(v_res_1029_);
return v_r_1030_;
}
}
LEAN_EXPORT uint64_t l_Nat_toInt64(lean_object* v_n_1031_){
_start:
{
uint64_t v___x_1032_; 
v___x_1032_ = lean_int64_of_nat(v_n_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt64___boxed(lean_object* v_n_1033_){
_start:
{
uint64_t v_res_1034_; lean_object* v_r_1035_; 
v_res_1034_ = l_Nat_toInt64(v_n_1033_);
lean_dec(v_n_1033_);
v_r_1035_ = lean_box_uint64(v_res_1034_);
return v_r_1035_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt___boxed(lean_object* v_i_1037_){
_start:
{
uint64_t v_i_boxed_1038_; lean_object* v_res_1039_; 
v_i_boxed_1038_ = lean_unbox_uint64(v_i_1037_);
lean_dec_ref(v_i_1037_);
v_res_1039_ = lean_int64_to_int_sint(v_i_boxed_1038_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg(uint64_t v_i_1040_){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_int64_to_int_sint(v_i_1040_);
v___x_1042_ = l_Int_toNat(v___x_1041_);
lean_dec(v___x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg___boxed(lean_object* v_i_1043_){
_start:
{
uint64_t v_i_boxed_1044_; lean_object* v_res_1045_; 
v_i_boxed_1044_ = lean_unbox_uint64(v_i_1043_);
lean_dec_ref(v_i_1043_);
v_res_1045_ = l_Int64_toNatClampNeg(v_i_boxed_1044_);
return v_res_1045_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofBitVec(lean_object* v_b_1046_){
_start:
{
uint64_t v___x_1047_; 
v___x_1047_ = lean_uint64_of_nat_mk(v_b_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofBitVec___boxed(lean_object* v_b_1048_){
_start:
{
uint64_t v_res_1049_; lean_object* v_r_1050_; 
v_res_1049_ = l_Int64_ofBitVec(v_b_1048_);
v_r_1050_ = lean_box_uint64(v_res_1049_);
return v_r_1050_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt8___boxed(lean_object* v_a_1052_){
_start:
{
uint64_t v_a_boxed_1053_; uint8_t v_res_1054_; lean_object* v_r_1055_; 
v_a_boxed_1053_ = lean_unbox_uint64(v_a_1052_);
lean_dec_ref(v_a_1052_);
v_res_1054_ = lean_int64_to_int8(v_a_boxed_1053_);
v_r_1055_ = lean_box(v_res_1054_);
return v_r_1055_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt16___boxed(lean_object* v_a_1057_){
_start:
{
uint64_t v_a_boxed_1058_; uint16_t v_res_1059_; lean_object* v_r_1060_; 
v_a_boxed_1058_ = lean_unbox_uint64(v_a_1057_);
lean_dec_ref(v_a_1057_);
v_res_1059_ = lean_int64_to_int16(v_a_boxed_1058_);
v_r_1060_ = lean_box(v_res_1059_);
return v_r_1060_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt32___boxed(lean_object* v_a_1062_){
_start:
{
uint64_t v_a_boxed_1063_; uint32_t v_res_1064_; lean_object* v_r_1065_; 
v_a_boxed_1063_ = lean_unbox_uint64(v_a_1062_);
lean_dec_ref(v_a_1062_);
v_res_1064_ = lean_int64_to_int32(v_a_boxed_1063_);
v_r_1065_ = lean_box_uint32(v_res_1064_);
return v_r_1065_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt64___boxed(lean_object* v_a_1067_){
_start:
{
uint8_t v_a_boxed_1068_; uint64_t v_res_1069_; lean_object* v_r_1070_; 
v_a_boxed_1068_ = lean_unbox(v_a_1067_);
v_res_1069_ = lean_int8_to_int64(v_a_boxed_1068_);
v_r_1070_ = lean_box_uint64(v_res_1069_);
return v_r_1070_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt64___boxed(lean_object* v_a_1072_){
_start:
{
uint16_t v_a_boxed_1073_; uint64_t v_res_1074_; lean_object* v_r_1075_; 
v_a_boxed_1073_ = lean_unbox(v_a_1072_);
v_res_1074_ = lean_int16_to_int64(v_a_boxed_1073_);
v_r_1075_ = lean_box_uint64(v_res_1074_);
return v_r_1075_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt64___boxed(lean_object* v_a_1077_){
_start:
{
uint32_t v_a_boxed_1078_; uint64_t v_res_1079_; lean_object* v_r_1080_; 
v_a_boxed_1078_ = lean_unbox_uint32(v_a_1077_);
lean_dec(v_a_1077_);
v_res_1079_ = lean_int32_to_int64(v_a_boxed_1078_);
v_r_1080_ = lean_box_uint64(v_res_1079_);
return v_r_1080_;
}
}
LEAN_EXPORT lean_object* l_Int64_neg___boxed(lean_object* v_i_1082_){
_start:
{
uint64_t v_i_boxed_1083_; uint64_t v_res_1084_; lean_object* v_r_1085_; 
v_i_boxed_1083_ = lean_unbox_uint64(v_i_1082_);
lean_dec_ref(v_i_1082_);
v_res_1084_ = lean_int64_neg(v_i_boxed_1083_);
v_r_1085_ = lean_box_uint64(v_res_1084_);
return v_r_1085_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0(uint64_t v_i_1086_){
_start:
{
lean_object* v___x_1087_; lean_object* v_intZero_1088_; uint8_t v_isNeg_1089_; 
v___x_1087_ = lean_int64_to_int_sint(v_i_1086_);
v_intZero_1088_ = lean_obj_once(&l_instToStringInt8___lam__0___closed__0, &l_instToStringInt8___lam__0___closed__0_once, _init_l_instToStringInt8___lam__0___closed__0);
v_isNeg_1089_ = lean_int_dec_lt(v___x_1087_, v_intZero_1088_);
if (v_isNeg_1089_ == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1091_; 
v_a_1090_ = lean_nat_abs(v___x_1087_);
lean_dec(v___x_1087_);
v___x_1091_ = l_Nat_reprFast(v_a_1090_);
return v___x_1091_;
}
else
{
lean_object* v_abs_1092_; lean_object* v_one_1093_; lean_object* v_a_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_abs_1092_ = lean_nat_abs(v___x_1087_);
lean_dec(v___x_1087_);
v_one_1093_ = lean_unsigned_to_nat(1u);
v_a_1094_ = lean_nat_sub(v_abs_1092_, v_one_1093_);
lean_dec(v_abs_1092_);
v___x_1095_ = ((lean_object*)(l_instToStringInt8___lam__0___closed__1));
v___x_1096_ = lean_nat_add(v_a_1094_, v_one_1093_);
lean_dec(v_a_1094_);
v___x_1097_ = l_Nat_reprFast(v___x_1096_);
v___x_1098_ = lean_string_append(v___x_1095_, v___x_1097_);
lean_dec_ref(v___x_1097_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0___boxed(lean_object* v_i_1099_){
_start:
{
uint64_t v_i_boxed_1100_; lean_object* v_res_1101_; 
v_i_boxed_1100_ = lean_unbox_uint64(v_i_1099_);
lean_dec_ref(v_i_1099_);
v_res_1101_ = l_instToStringInt64___lam__0(v_i_boxed_1100_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_instReprInt64___lam__0(uint64_t v_i_1104_, lean_object* v_prec_1105_){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1106_ = lean_int64_to_int_sint(v_i_1104_);
v___x_1107_ = lean_obj_once(&l_instToStringInt8___lam__0___closed__0, &l_instToStringInt8___lam__0___closed__0_once, _init_l_instToStringInt8___lam__0___closed__0);
v___x_1108_ = lean_int_dec_lt(v___x_1106_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = l_Int_repr(v___x_1106_);
lean_dec(v___x_1106_);
v___x_1110_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = l_Int_repr(v___x_1106_);
lean_dec(v___x_1106_);
v___x_1112_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
v___x_1113_ = l_Repr_addAppParen(v___x_1112_, v_prec_1105_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt64___lam__0___boxed(lean_object* v_i_1114_, lean_object* v_prec_1115_){
_start:
{
uint64_t v_i_boxed_1116_; lean_object* v_res_1117_; 
v_i_boxed_1116_ = lean_unbox_uint64(v_i_1114_);
lean_dec_ref(v_i_1114_);
v_res_1117_ = l_instReprInt64___lam__0(v_i_boxed_1116_, v_prec_1115_);
lean_dec(v_prec_1115_);
return v_res_1117_;
}
}
static lean_object* _init_l_instReprAtomInt64(void){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_box(0);
return v___x_1120_;
}
}
LEAN_EXPORT uint64_t l_instHashableInt64___lam__0(uint64_t v_i_1121_){
_start:
{
return v_i_1121_;
}
}
LEAN_EXPORT lean_object* l_instHashableInt64___lam__0___boxed(lean_object* v_i_1122_){
_start:
{
uint64_t v_i_boxed_1123_; uint64_t v_res_1124_; lean_object* v_r_1125_; 
v_i_boxed_1123_ = lean_unbox_uint64(v_i_1122_);
lean_dec_ref(v_i_1122_);
v_res_1124_ = l_instHashableInt64___lam__0(v_i_boxed_1123_);
v_r_1125_ = lean_box_uint64(v_res_1124_);
return v_r_1125_;
}
}
LEAN_EXPORT uint64_t l_Int64_instOfNat(lean_object* v_n_1128_){
_start:
{
uint64_t v___x_1129_; 
v___x_1129_ = lean_int64_of_nat(v_n_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Int64_instOfNat___boxed(lean_object* v_n_1130_){
_start:
{
uint64_t v_res_1131_; lean_object* v_r_1132_; 
v_res_1131_ = l_Int64_instOfNat(v_n_1130_);
lean_dec(v_n_1130_);
v_r_1132_ = lean_box_uint64(v_res_1131_);
return v_r_1132_;
}
}
static uint64_t _init_l_Int64_maxValue___closed__0(void){
_start:
{
lean_object* v___x_1135_; uint64_t v___x_1136_; 
v___x_1135_ = lean_cstr_to_nat("9223372036854775807");
v___x_1136_ = lean_int64_of_nat(v___x_1135_);
return v___x_1136_;
}
}
static uint64_t _init_l_Int64_maxValue(void){
_start:
{
uint64_t v___x_1137_; 
v___x_1137_ = lean_uint64_once(&l_Int64_maxValue___closed__0, &l_Int64_maxValue___closed__0_once, _init_l_Int64_maxValue___closed__0);
return v___x_1137_;
}
}
static lean_object* _init_l_Int64_minValue___closed__0(void){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_cstr_to_nat("9223372036854775808");
return v___x_1138_;
}
}
static uint64_t _init_l_Int64_minValue___closed__1(void){
_start:
{
lean_object* v___x_1139_; uint64_t v___x_1140_; 
v___x_1139_ = lean_obj_once(&l_Int64_minValue___closed__0, &l_Int64_minValue___closed__0_once, _init_l_Int64_minValue___closed__0);
v___x_1140_ = lean_int64_of_nat(v___x_1139_);
return v___x_1140_;
}
}
static uint64_t _init_l_Int64_minValue___closed__2(void){
_start:
{
uint64_t v___x_1141_; uint64_t v___x_1142_; 
v___x_1141_ = lean_uint64_once(&l_Int64_minValue___closed__1, &l_Int64_minValue___closed__1_once, _init_l_Int64_minValue___closed__1);
v___x_1142_ = lean_int64_neg(v___x_1141_);
return v___x_1142_;
}
}
static uint64_t _init_l_Int64_minValue(void){
_start:
{
uint64_t v___x_1143_; 
v___x_1143_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
return v___x_1143_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntLE___redArg(lean_object* v_i_1144_){
_start:
{
uint64_t v___x_1145_; 
v___x_1145_ = lean_int64_of_int(v_i_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntLE___redArg___boxed(lean_object* v_i_1146_){
_start:
{
uint64_t v_res_1147_; lean_object* v_r_1148_; 
v_res_1147_ = l_Int64_ofIntLE___redArg(v_i_1146_);
lean_dec(v_i_1146_);
v_r_1148_ = lean_box_uint64(v_res_1147_);
return v_r_1148_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntLE(lean_object* v_i_1149_, lean_object* v___hl_1150_, lean_object* v___hr_1151_){
_start:
{
uint64_t v___x_1152_; 
v___x_1152_ = lean_int64_of_int(v_i_1149_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntLE___boxed(lean_object* v_i_1153_, lean_object* v___hl_1154_, lean_object* v___hr_1155_){
_start:
{
uint64_t v_res_1156_; lean_object* v_r_1157_; 
v_res_1156_ = l_Int64_ofIntLE(v_i_1153_, v___hl_1154_, v___hr_1155_);
lean_dec(v_i_1153_);
v_r_1157_ = lean_box_uint64(v_res_1156_);
return v_r_1157_;
}
}
static lean_object* _init_l_Int64_ofIntTruncate___closed__0(void){
_start:
{
uint64_t v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
v___x_1159_ = lean_int64_to_int_sint(v___x_1158_);
return v___x_1159_;
}
}
static lean_object* _init_l_Int64_ofIntTruncate___closed__1(void){
_start:
{
uint64_t v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_uint64_once(&l_Int64_maxValue___closed__0, &l_Int64_maxValue___closed__0_once, _init_l_Int64_maxValue___closed__0);
v___x_1161_ = lean_int64_to_int_sint(v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntTruncate(lean_object* v_i_1162_){
_start:
{
uint64_t v___x_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1163_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
v___x_1164_ = lean_obj_once(&l_Int64_ofIntTruncate___closed__0, &l_Int64_ofIntTruncate___closed__0_once, _init_l_Int64_ofIntTruncate___closed__0);
v___x_1165_ = lean_int_dec_le(v___x_1164_, v_i_1162_);
if (v___x_1165_ == 0)
{
return v___x_1163_;
}
else
{
lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = lean_obj_once(&l_Int64_ofIntTruncate___closed__1, &l_Int64_ofIntTruncate___closed__1_once, _init_l_Int64_ofIntTruncate___closed__1);
v___x_1167_ = lean_int_dec_le(v_i_1162_, v___x_1166_);
if (v___x_1167_ == 0)
{
return v___x_1163_;
}
else
{
uint64_t v___x_1168_; 
v___x_1168_ = lean_int64_of_int(v_i_1162_);
return v___x_1168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntTruncate___boxed(lean_object* v_i_1169_){
_start:
{
uint64_t v_res_1170_; lean_object* v_r_1171_; 
v_res_1170_ = l_Int64_ofIntTruncate(v_i_1169_);
lean_dec(v_i_1169_);
v_r_1171_ = lean_box_uint64(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT lean_object* l_Int64_add___boxed(lean_object* v_a_1174_, lean_object* v_b_1175_){
_start:
{
uint64_t v_a_boxed_1176_; uint64_t v_b_boxed_1177_; uint64_t v_res_1178_; lean_object* v_r_1179_; 
v_a_boxed_1176_ = lean_unbox_uint64(v_a_1174_);
lean_dec_ref(v_a_1174_);
v_b_boxed_1177_ = lean_unbox_uint64(v_b_1175_);
lean_dec_ref(v_b_1175_);
v_res_1178_ = lean_int64_add(v_a_boxed_1176_, v_b_boxed_1177_);
v_r_1179_ = lean_box_uint64(v_res_1178_);
return v_r_1179_;
}
}
LEAN_EXPORT lean_object* l_Int64_sub___boxed(lean_object* v_a_1182_, lean_object* v_b_1183_){
_start:
{
uint64_t v_a_boxed_1184_; uint64_t v_b_boxed_1185_; uint64_t v_res_1186_; lean_object* v_r_1187_; 
v_a_boxed_1184_ = lean_unbox_uint64(v_a_1182_);
lean_dec_ref(v_a_1182_);
v_b_boxed_1185_ = lean_unbox_uint64(v_b_1183_);
lean_dec_ref(v_b_1183_);
v_res_1186_ = lean_int64_sub(v_a_boxed_1184_, v_b_boxed_1185_);
v_r_1187_ = lean_box_uint64(v_res_1186_);
return v_r_1187_;
}
}
LEAN_EXPORT lean_object* l_Int64_mul___boxed(lean_object* v_a_1190_, lean_object* v_b_1191_){
_start:
{
uint64_t v_a_boxed_1192_; uint64_t v_b_boxed_1193_; uint64_t v_res_1194_; lean_object* v_r_1195_; 
v_a_boxed_1192_ = lean_unbox_uint64(v_a_1190_);
lean_dec_ref(v_a_1190_);
v_b_boxed_1193_ = lean_unbox_uint64(v_b_1191_);
lean_dec_ref(v_b_1191_);
v_res_1194_ = lean_int64_mul(v_a_boxed_1192_, v_b_boxed_1193_);
v_r_1195_ = lean_box_uint64(v_res_1194_);
return v_r_1195_;
}
}
LEAN_EXPORT lean_object* l_Int64_div___boxed(lean_object* v_a_1198_, lean_object* v_b_1199_){
_start:
{
uint64_t v_a_boxed_1200_; uint64_t v_b_boxed_1201_; uint64_t v_res_1202_; lean_object* v_r_1203_; 
v_a_boxed_1200_ = lean_unbox_uint64(v_a_1198_);
lean_dec_ref(v_a_1198_);
v_b_boxed_1201_ = lean_unbox_uint64(v_b_1199_);
lean_dec_ref(v_b_1199_);
v_res_1202_ = lean_int64_div(v_a_boxed_1200_, v_b_boxed_1201_);
v_r_1203_ = lean_box_uint64(v_res_1202_);
return v_r_1203_;
}
}
static uint64_t _init_l_Int64_pow___closed__0(void){
_start:
{
lean_object* v___x_1204_; uint64_t v___x_1205_; 
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = lean_int64_of_nat(v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT uint64_t l_Int64_pow(uint64_t v_x_1206_, lean_object* v_n_1207_){
_start:
{
lean_object* v_zero_1208_; uint8_t v_isZero_1209_; 
v_zero_1208_ = lean_unsigned_to_nat(0u);
v_isZero_1209_ = lean_nat_dec_eq(v_n_1207_, v_zero_1208_);
if (v_isZero_1209_ == 1)
{
uint64_t v___x_1210_; 
v___x_1210_ = lean_uint64_once(&l_Int64_pow___closed__0, &l_Int64_pow___closed__0_once, _init_l_Int64_pow___closed__0);
return v___x_1210_;
}
else
{
lean_object* v_one_1211_; lean_object* v_n_1212_; uint64_t v___x_1213_; uint64_t v___x_1214_; 
v_one_1211_ = lean_unsigned_to_nat(1u);
v_n_1212_ = lean_nat_sub(v_n_1207_, v_one_1211_);
v___x_1213_ = l_Int64_pow(v_x_1206_, v_n_1212_);
lean_dec(v_n_1212_);
v___x_1214_ = lean_int64_mul(v___x_1213_, v_x_1206_);
return v___x_1214_;
}
}
}
LEAN_EXPORT lean_object* l_Int64_pow___boxed(lean_object* v_x_1215_, lean_object* v_n_1216_){
_start:
{
uint64_t v_x_boxed_1217_; uint64_t v_res_1218_; lean_object* v_r_1219_; 
v_x_boxed_1217_ = lean_unbox_uint64(v_x_1215_);
lean_dec_ref(v_x_1215_);
v_res_1218_ = l_Int64_pow(v_x_boxed_1217_, v_n_1216_);
lean_dec(v_n_1216_);
v_r_1219_ = lean_box_uint64(v_res_1218_);
return v_r_1219_;
}
}
LEAN_EXPORT lean_object* l_Int64_mod___boxed(lean_object* v_a_1222_, lean_object* v_b_1223_){
_start:
{
uint64_t v_a_boxed_1224_; uint64_t v_b_boxed_1225_; uint64_t v_res_1226_; lean_object* v_r_1227_; 
v_a_boxed_1224_ = lean_unbox_uint64(v_a_1222_);
lean_dec_ref(v_a_1222_);
v_b_boxed_1225_ = lean_unbox_uint64(v_b_1223_);
lean_dec_ref(v_b_1223_);
v_res_1226_ = lean_int64_mod(v_a_boxed_1224_, v_b_boxed_1225_);
v_r_1227_ = lean_box_uint64(v_res_1226_);
return v_r_1227_;
}
}
LEAN_EXPORT lean_object* l_Int64_land___boxed(lean_object* v_a_1230_, lean_object* v_b_1231_){
_start:
{
uint64_t v_a_boxed_1232_; uint64_t v_b_boxed_1233_; uint64_t v_res_1234_; lean_object* v_r_1235_; 
v_a_boxed_1232_ = lean_unbox_uint64(v_a_1230_);
lean_dec_ref(v_a_1230_);
v_b_boxed_1233_ = lean_unbox_uint64(v_b_1231_);
lean_dec_ref(v_b_1231_);
v_res_1234_ = lean_int64_land(v_a_boxed_1232_, v_b_boxed_1233_);
v_r_1235_ = lean_box_uint64(v_res_1234_);
return v_r_1235_;
}
}
LEAN_EXPORT lean_object* l_Int64_lor___boxed(lean_object* v_a_1238_, lean_object* v_b_1239_){
_start:
{
uint64_t v_a_boxed_1240_; uint64_t v_b_boxed_1241_; uint64_t v_res_1242_; lean_object* v_r_1243_; 
v_a_boxed_1240_ = lean_unbox_uint64(v_a_1238_);
lean_dec_ref(v_a_1238_);
v_b_boxed_1241_ = lean_unbox_uint64(v_b_1239_);
lean_dec_ref(v_b_1239_);
v_res_1242_ = lean_int64_lor(v_a_boxed_1240_, v_b_boxed_1241_);
v_r_1243_ = lean_box_uint64(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT lean_object* l_Int64_xor___boxed(lean_object* v_a_1246_, lean_object* v_b_1247_){
_start:
{
uint64_t v_a_boxed_1248_; uint64_t v_b_boxed_1249_; uint64_t v_res_1250_; lean_object* v_r_1251_; 
v_a_boxed_1248_ = lean_unbox_uint64(v_a_1246_);
lean_dec_ref(v_a_1246_);
v_b_boxed_1249_ = lean_unbox_uint64(v_b_1247_);
lean_dec_ref(v_b_1247_);
v_res_1250_ = lean_int64_xor(v_a_boxed_1248_, v_b_boxed_1249_);
v_r_1251_ = lean_box_uint64(v_res_1250_);
return v_r_1251_;
}
}
LEAN_EXPORT lean_object* l_Int64_shiftLeft___boxed(lean_object* v_a_1254_, lean_object* v_b_1255_){
_start:
{
uint64_t v_a_boxed_1256_; uint64_t v_b_boxed_1257_; uint64_t v_res_1258_; lean_object* v_r_1259_; 
v_a_boxed_1256_ = lean_unbox_uint64(v_a_1254_);
lean_dec_ref(v_a_1254_);
v_b_boxed_1257_ = lean_unbox_uint64(v_b_1255_);
lean_dec_ref(v_b_1255_);
v_res_1258_ = lean_int64_shift_left(v_a_boxed_1256_, v_b_boxed_1257_);
v_r_1259_ = lean_box_uint64(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT lean_object* l_Int64_shiftRight___boxed(lean_object* v_a_1262_, lean_object* v_b_1263_){
_start:
{
uint64_t v_a_boxed_1264_; uint64_t v_b_boxed_1265_; uint64_t v_res_1266_; lean_object* v_r_1267_; 
v_a_boxed_1264_ = lean_unbox_uint64(v_a_1262_);
lean_dec_ref(v_a_1262_);
v_b_boxed_1265_ = lean_unbox_uint64(v_b_1263_);
lean_dec_ref(v_b_1263_);
v_res_1266_ = lean_int64_shift_right(v_a_boxed_1264_, v_b_boxed_1265_);
v_r_1267_ = lean_box_uint64(v_res_1266_);
return v_r_1267_;
}
}
LEAN_EXPORT lean_object* l_Int64_complement___boxed(lean_object* v_a_1269_){
_start:
{
uint64_t v_a_boxed_1270_; uint64_t v_res_1271_; lean_object* v_r_1272_; 
v_a_boxed_1270_ = lean_unbox_uint64(v_a_1269_);
lean_dec_ref(v_a_1269_);
v_res_1271_ = lean_int64_complement(v_a_boxed_1270_);
v_r_1272_ = lean_box_uint64(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT lean_object* l_Int64_abs___boxed(lean_object* v_a_1274_){
_start:
{
uint64_t v_a_boxed_1275_; uint64_t v_res_1276_; lean_object* v_r_1277_; 
v_a_boxed_1275_ = lean_unbox_uint64(v_a_1274_);
lean_dec_ref(v_a_1274_);
v_res_1276_ = lean_int64_abs(v_a_boxed_1275_);
v_r_1277_ = lean_box_uint64(v_res_1276_);
return v_r_1277_;
}
}
LEAN_EXPORT lean_object* l_Int64_decEq___boxed(lean_object* v_a_1280_, lean_object* v_b_1281_){
_start:
{
uint64_t v_a_boxed_1282_; uint64_t v_b_boxed_1283_; uint8_t v_res_1284_; lean_object* v_r_1285_; 
v_a_boxed_1282_ = lean_unbox_uint64(v_a_1280_);
lean_dec_ref(v_a_1280_);
v_b_boxed_1283_ = lean_unbox_uint64(v_b_1281_);
lean_dec_ref(v_b_1281_);
v_res_1284_ = lean_int64_dec_eq(v_a_boxed_1282_, v_b_boxed_1283_);
v_r_1285_ = lean_box(v_res_1284_);
return v_r_1285_;
}
}
static uint64_t _init_l_instInhabitedInt64___closed__0(void){
_start:
{
lean_object* v___x_1286_; uint64_t v___x_1287_; 
v___x_1286_ = lean_unsigned_to_nat(0u);
v___x_1287_ = lean_int64_of_nat(v___x_1286_);
return v___x_1287_;
}
}
static uint64_t _init_l_instInhabitedInt64(void){
_start:
{
uint64_t v___x_1288_; 
v___x_1288_ = lean_uint64_once(&l_instInhabitedInt64___closed__0, &l_instInhabitedInt64___closed__0_once, _init_l_instInhabitedInt64___closed__0);
return v___x_1288_;
}
}
static lean_object* _init_l_instLTInt64(void){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = lean_box(0);
return v___x_1301_;
}
}
static lean_object* _init_l_instLEInt64(void){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = lean_box(0);
return v___x_1302_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt64(uint64_t v_a_1315_, uint64_t v_b_1316_){
_start:
{
uint8_t v___x_1317_; 
v___x_1317_ = lean_int64_dec_eq(v_a_1315_, v_b_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt64___boxed(lean_object* v_a_1318_, lean_object* v_b_1319_){
_start:
{
uint64_t v_a_boxed_1320_; uint64_t v_b_boxed_1321_; uint8_t v_res_1322_; lean_object* v_r_1323_; 
v_a_boxed_1320_ = lean_unbox_uint64(v_a_1318_);
lean_dec_ref(v_a_1318_);
v_b_boxed_1321_ = lean_unbox_uint64(v_b_1319_);
lean_dec_ref(v_b_1319_);
v_res_1322_ = l_instDecidableEqInt64(v_a_boxed_1320_, v_b_boxed_1321_);
v_r_1323_ = lean_box(v_res_1322_);
return v_r_1323_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt64___boxed(lean_object* v_b_1325_){
_start:
{
uint8_t v_b_boxed_1326_; uint64_t v_res_1327_; lean_object* v_r_1328_; 
v_b_boxed_1326_ = lean_unbox(v_b_1325_);
v_res_1327_ = lean_bool_to_int64(v_b_boxed_1326_);
v_r_1328_ = lean_box_uint64(v_res_1327_);
return v_r_1328_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLt___boxed(lean_object* v_a_1331_, lean_object* v_b_1332_){
_start:
{
uint64_t v_a_boxed_1333_; uint64_t v_b_boxed_1334_; uint8_t v_res_1335_; lean_object* v_r_1336_; 
v_a_boxed_1333_ = lean_unbox_uint64(v_a_1331_);
lean_dec_ref(v_a_1331_);
v_b_boxed_1334_ = lean_unbox_uint64(v_b_1332_);
lean_dec_ref(v_b_1332_);
v_res_1335_ = lean_int64_dec_lt(v_a_boxed_1333_, v_b_boxed_1334_);
v_r_1336_ = lean_box(v_res_1335_);
return v_r_1336_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLe___boxed(lean_object* v_a_1339_, lean_object* v_b_1340_){
_start:
{
uint64_t v_a_boxed_1341_; uint64_t v_b_boxed_1342_; uint8_t v_res_1343_; lean_object* v_r_1344_; 
v_a_boxed_1341_ = lean_unbox_uint64(v_a_1339_);
lean_dec_ref(v_a_1339_);
v_b_boxed_1342_ = lean_unbox_uint64(v_b_1340_);
lean_dec_ref(v_b_1340_);
v_res_1343_ = lean_int64_dec_le(v_a_boxed_1341_, v_b_boxed_1342_);
v_r_1344_ = lean_box(v_res_1343_);
return v_r_1344_;
}
}
LEAN_EXPORT uint64_t l_instMaxInt64___lam__0(uint64_t v_x_1345_, uint64_t v_y_1346_){
_start:
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_int64_dec_le(v_x_1345_, v_y_1346_);
if (v___x_1347_ == 0)
{
return v_x_1345_;
}
else
{
return v_y_1346_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt64___lam__0___boxed(lean_object* v_x_1348_, lean_object* v_y_1349_){
_start:
{
uint64_t v_x_boxed_1350_; uint64_t v_y_boxed_1351_; uint64_t v_res_1352_; lean_object* v_r_1353_; 
v_x_boxed_1350_ = lean_unbox_uint64(v_x_1348_);
lean_dec_ref(v_x_1348_);
v_y_boxed_1351_ = lean_unbox_uint64(v_y_1349_);
lean_dec_ref(v_y_1349_);
v_res_1352_ = l_instMaxInt64___lam__0(v_x_boxed_1350_, v_y_boxed_1351_);
v_r_1353_ = lean_box_uint64(v_res_1352_);
return v_r_1353_;
}
}
LEAN_EXPORT uint64_t l_instMinInt64___lam__0(uint64_t v_x_1356_, uint64_t v_y_1357_){
_start:
{
uint8_t v___x_1358_; 
v___x_1358_ = lean_int64_dec_le(v_x_1356_, v_y_1357_);
if (v___x_1358_ == 0)
{
return v_y_1357_;
}
else
{
return v_x_1356_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt64___lam__0___boxed(lean_object* v_x_1359_, lean_object* v_y_1360_){
_start:
{
uint64_t v_x_boxed_1361_; uint64_t v_y_boxed_1362_; uint64_t v_res_1363_; lean_object* v_r_1364_; 
v_x_boxed_1361_ = lean_unbox_uint64(v_x_1359_);
lean_dec_ref(v_x_1359_);
v_y_boxed_1362_ = lean_unbox_uint64(v_y_1360_);
lean_dec_ref(v_y_1360_);
v_res_1363_ = l_instMinInt64___lam__0(v_x_boxed_1361_, v_y_boxed_1362_);
v_r_1364_ = lean_box_uint64(v_res_1363_);
return v_r_1364_;
}
}
static lean_object* _init_l_ISize_size___closed__0(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = l_System_Platform_numBits;
v___x_1368_ = lean_unsigned_to_nat(2u);
v___x_1369_ = lean_nat_pow(v___x_1368_, v___x_1367_);
return v___x_1369_;
}
}
static lean_object* _init_l_ISize_size(void){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_obj_once(&l_ISize_size___closed__0, &l_ISize_size___closed__0_once, _init_l_ISize_size___closed__0);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_ISize_toBitVec(size_t v_x_1371_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_usize_to_nat(v_x_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_ISize_toBitVec___boxed(lean_object* v_x_1373_){
_start:
{
size_t v_x_boxed_1374_; lean_object* v_res_1375_; 
v_x_boxed_1374_ = lean_unbox_usize(v_x_1373_);
lean_dec(v_x_1373_);
v_res_1375_ = l_ISize_toBitVec(v_x_boxed_1374_);
return v_res_1375_;
}
}
LEAN_EXPORT size_t l_USize_toISize(size_t v_i_1376_){
_start:
{
return v_i_1376_;
}
}
LEAN_EXPORT lean_object* l_USize_toISize___boxed(lean_object* v_i_1377_){
_start:
{
size_t v_i_boxed_1378_; size_t v_res_1379_; lean_object* v_r_1380_; 
v_i_boxed_1378_ = lean_unbox_usize(v_i_1377_);
lean_dec(v_i_1377_);
v_res_1379_ = l_USize_toISize(v_i_boxed_1378_);
v_r_1380_ = lean_box_usize(v_res_1379_);
return v_r_1380_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofInt___boxed(lean_object* v_i_1382_){
_start:
{
size_t v_res_1383_; lean_object* v_r_1384_; 
v_res_1383_ = lean_isize_of_int(v_i_1382_);
lean_dec(v_i_1382_);
v_r_1384_ = lean_box_usize(v_res_1383_);
return v_r_1384_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofNat___boxed(lean_object* v_n_1386_){
_start:
{
size_t v_res_1387_; lean_object* v_r_1388_; 
v_res_1387_ = lean_isize_of_nat(v_n_1386_);
lean_dec(v_n_1386_);
v_r_1388_ = lean_box_usize(v_res_1387_);
return v_r_1388_;
}
}
LEAN_EXPORT size_t l_Int_toISize(lean_object* v_i_1389_){
_start:
{
size_t v___x_1390_; 
v___x_1390_ = lean_isize_of_int(v_i_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Int_toISize___boxed(lean_object* v_i_1391_){
_start:
{
size_t v_res_1392_; lean_object* v_r_1393_; 
v_res_1392_ = l_Int_toISize(v_i_1391_);
lean_dec(v_i_1391_);
v_r_1393_ = lean_box_usize(v_res_1392_);
return v_r_1393_;
}
}
LEAN_EXPORT size_t l_Nat_toISize(lean_object* v_n_1394_){
_start:
{
size_t v___x_1395_; 
v___x_1395_ = lean_isize_of_nat(v_n_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Nat_toISize___boxed(lean_object* v_n_1396_){
_start:
{
size_t v_res_1397_; lean_object* v_r_1398_; 
v_res_1397_ = l_Nat_toISize(v_n_1396_);
lean_dec(v_n_1396_);
v_r_1398_ = lean_box_usize(v_res_1397_);
return v_r_1398_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt___boxed(lean_object* v_i_1400_){
_start:
{
size_t v_i_boxed_1401_; lean_object* v_res_1402_; 
v_i_boxed_1401_ = lean_unbox_usize(v_i_1400_);
lean_dec(v_i_1400_);
v_res_1402_ = lean_isize_to_int(v_i_boxed_1401_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg(size_t v_i_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_isize_to_int(v_i_1403_);
v___x_1405_ = l_Int_toNat(v___x_1404_);
lean_dec(v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg___boxed(lean_object* v_i_1406_){
_start:
{
size_t v_i_boxed_1407_; lean_object* v_res_1408_; 
v_i_boxed_1407_ = lean_unbox_usize(v_i_1406_);
lean_dec(v_i_1406_);
v_res_1408_ = l_ISize_toNatClampNeg(v_i_boxed_1407_);
return v_res_1408_;
}
}
LEAN_EXPORT size_t l_ISize_ofBitVec(lean_object* v_b_1409_){
_start:
{
size_t v___x_1410_; 
v___x_1410_ = lean_usize_of_nat_mk(v_b_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofBitVec___boxed(lean_object* v_b_1411_){
_start:
{
size_t v_res_1412_; lean_object* v_r_1413_; 
v_res_1412_ = l_ISize_ofBitVec(v_b_1411_);
v_r_1413_ = lean_box_usize(v_res_1412_);
return v_r_1413_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt8___boxed(lean_object* v_a_1415_){
_start:
{
size_t v_a_boxed_1416_; uint8_t v_res_1417_; lean_object* v_r_1418_; 
v_a_boxed_1416_ = lean_unbox_usize(v_a_1415_);
lean_dec(v_a_1415_);
v_res_1417_ = lean_isize_to_int8(v_a_boxed_1416_);
v_r_1418_ = lean_box(v_res_1417_);
return v_r_1418_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt16___boxed(lean_object* v_a_1420_){
_start:
{
size_t v_a_boxed_1421_; uint16_t v_res_1422_; lean_object* v_r_1423_; 
v_a_boxed_1421_ = lean_unbox_usize(v_a_1420_);
lean_dec(v_a_1420_);
v_res_1422_ = lean_isize_to_int16(v_a_boxed_1421_);
v_r_1423_ = lean_box(v_res_1422_);
return v_r_1423_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt32___boxed(lean_object* v_a_1425_){
_start:
{
size_t v_a_boxed_1426_; uint32_t v_res_1427_; lean_object* v_r_1428_; 
v_a_boxed_1426_ = lean_unbox_usize(v_a_1425_);
lean_dec(v_a_1425_);
v_res_1427_ = lean_isize_to_int32(v_a_boxed_1426_);
v_r_1428_ = lean_box_uint32(v_res_1427_);
return v_r_1428_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt64___boxed(lean_object* v_a_1430_){
_start:
{
size_t v_a_boxed_1431_; uint64_t v_res_1432_; lean_object* v_r_1433_; 
v_a_boxed_1431_ = lean_unbox_usize(v_a_1430_);
lean_dec(v_a_1430_);
v_res_1432_ = lean_isize_to_int64(v_a_boxed_1431_);
v_r_1433_ = lean_box_uint64(v_res_1432_);
return v_r_1433_;
}
}
LEAN_EXPORT lean_object* l_Int8_toISize___boxed(lean_object* v_a_1435_){
_start:
{
uint8_t v_a_boxed_1436_; size_t v_res_1437_; lean_object* v_r_1438_; 
v_a_boxed_1436_ = lean_unbox(v_a_1435_);
v_res_1437_ = lean_int8_to_isize(v_a_boxed_1436_);
v_r_1438_ = lean_box_usize(v_res_1437_);
return v_r_1438_;
}
}
LEAN_EXPORT lean_object* l_Int16_toISize___boxed(lean_object* v_a_1440_){
_start:
{
uint16_t v_a_boxed_1441_; size_t v_res_1442_; lean_object* v_r_1443_; 
v_a_boxed_1441_ = lean_unbox(v_a_1440_);
v_res_1442_ = lean_int16_to_isize(v_a_boxed_1441_);
v_r_1443_ = lean_box_usize(v_res_1442_);
return v_r_1443_;
}
}
LEAN_EXPORT lean_object* l_Int32_toISize___boxed(lean_object* v_a_1445_){
_start:
{
uint32_t v_a_boxed_1446_; size_t v_res_1447_; lean_object* v_r_1448_; 
v_a_boxed_1446_ = lean_unbox_uint32(v_a_1445_);
lean_dec(v_a_1445_);
v_res_1447_ = lean_int32_to_isize(v_a_boxed_1446_);
v_r_1448_ = lean_box_usize(v_res_1447_);
return v_r_1448_;
}
}
LEAN_EXPORT lean_object* l_Int64_toISize___boxed(lean_object* v_a_1450_){
_start:
{
uint64_t v_a_boxed_1451_; size_t v_res_1452_; lean_object* v_r_1453_; 
v_a_boxed_1451_ = lean_unbox_uint64(v_a_1450_);
lean_dec_ref(v_a_1450_);
v_res_1452_ = lean_int64_to_isize(v_a_boxed_1451_);
v_r_1453_ = lean_box_usize(v_res_1452_);
return v_r_1453_;
}
}
LEAN_EXPORT lean_object* l_ISize_neg___boxed(lean_object* v_i_1455_){
_start:
{
size_t v_i_boxed_1456_; size_t v_res_1457_; lean_object* v_r_1458_; 
v_i_boxed_1456_ = lean_unbox_usize(v_i_1455_);
lean_dec(v_i_1455_);
v_res_1457_ = lean_isize_neg(v_i_boxed_1456_);
v_r_1458_ = lean_box_usize(v_res_1457_);
return v_r_1458_;
}
}
LEAN_EXPORT lean_object* l_instToStringISize___lam__0(size_t v_i_1459_){
_start:
{
lean_object* v___x_1460_; lean_object* v_intZero_1461_; uint8_t v_isNeg_1462_; 
v___x_1460_ = lean_isize_to_int(v_i_1459_);
v_intZero_1461_ = lean_obj_once(&l_instToStringInt8___lam__0___closed__0, &l_instToStringInt8___lam__0___closed__0_once, _init_l_instToStringInt8___lam__0___closed__0);
v_isNeg_1462_ = lean_int_dec_lt(v___x_1460_, v_intZero_1461_);
if (v_isNeg_1462_ == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; 
v_a_1463_ = lean_nat_abs(v___x_1460_);
lean_dec(v___x_1460_);
v___x_1464_ = l_Nat_reprFast(v_a_1463_);
return v___x_1464_;
}
else
{
lean_object* v_abs_1465_; lean_object* v_one_1466_; lean_object* v_a_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_abs_1465_ = lean_nat_abs(v___x_1460_);
lean_dec(v___x_1460_);
v_one_1466_ = lean_unsigned_to_nat(1u);
v_a_1467_ = lean_nat_sub(v_abs_1465_, v_one_1466_);
lean_dec(v_abs_1465_);
v___x_1468_ = ((lean_object*)(l_instToStringInt8___lam__0___closed__1));
v___x_1469_ = lean_nat_add(v_a_1467_, v_one_1466_);
lean_dec(v_a_1467_);
v___x_1470_ = l_Nat_reprFast(v___x_1469_);
v___x_1471_ = lean_string_append(v___x_1468_, v___x_1470_);
lean_dec_ref(v___x_1470_);
return v___x_1471_;
}
}
}
LEAN_EXPORT lean_object* l_instToStringISize___lam__0___boxed(lean_object* v_i_1472_){
_start:
{
size_t v_i_boxed_1473_; lean_object* v_res_1474_; 
v_i_boxed_1473_ = lean_unbox_usize(v_i_1472_);
lean_dec(v_i_1472_);
v_res_1474_ = l_instToStringISize___lam__0(v_i_boxed_1473_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_instReprISize___lam__0(size_t v_i_1477_, lean_object* v_prec_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1479_ = lean_isize_to_int(v_i_1477_);
v___x_1480_ = lean_obj_once(&l_instToStringInt8___lam__0___closed__0, &l_instToStringInt8___lam__0___closed__0_once, _init_l_instToStringInt8___lam__0___closed__0);
v___x_1481_ = lean_int_dec_lt(v___x_1479_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = l_Int_repr(v___x_1479_);
lean_dec(v___x_1479_);
v___x_1483_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
else
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = l_Int_repr(v___x_1479_);
lean_dec(v___x_1479_);
v___x_1485_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
v___x_1486_ = l_Repr_addAppParen(v___x_1485_, v_prec_1478_);
return v___x_1486_;
}
}
}
LEAN_EXPORT lean_object* l_instReprISize___lam__0___boxed(lean_object* v_i_1487_, lean_object* v_prec_1488_){
_start:
{
size_t v_i_boxed_1489_; lean_object* v_res_1490_; 
v_i_boxed_1489_ = lean_unbox_usize(v_i_1487_);
lean_dec(v_i_1487_);
v_res_1490_ = l_instReprISize___lam__0(v_i_boxed_1489_, v_prec_1488_);
lean_dec(v_prec_1488_);
return v_res_1490_;
}
}
static lean_object* _init_l_instReprAtomISize(void){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_box(0);
return v___x_1493_;
}
}
LEAN_EXPORT size_t l_ISize_instOfNat(lean_object* v_n_1496_){
_start:
{
size_t v___x_1497_; 
v___x_1497_ = lean_isize_of_nat(v_n_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_ISize_instOfNat___boxed(lean_object* v_n_1498_){
_start:
{
size_t v_res_1499_; lean_object* v_r_1500_; 
v_res_1499_ = l_ISize_instOfNat(v_n_1498_);
lean_dec(v_n_1498_);
v_r_1500_ = lean_box_usize(v_res_1499_);
return v_r_1500_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__0(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_unsigned_to_nat(2u);
v___x_1504_ = lean_nat_to_int(v___x_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__1(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = lean_unsigned_to_nat(1u);
v___x_1506_ = l_System_Platform_numBits;
v___x_1507_ = lean_nat_sub(v___x_1506_, v___x_1505_);
return v___x_1507_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__2(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1508_ = lean_obj_once(&l_ISize_maxValue___closed__1, &l_ISize_maxValue___closed__1_once, _init_l_ISize_maxValue___closed__1);
v___x_1509_ = lean_obj_once(&l_ISize_maxValue___closed__0, &l_ISize_maxValue___closed__0_once, _init_l_ISize_maxValue___closed__0);
v___x_1510_ = l_Int_pow(v___x_1509_, v___x_1508_);
return v___x_1510_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__3(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = lean_unsigned_to_nat(1u);
v___x_1512_ = lean_nat_to_int(v___x_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__4(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_obj_once(&l_ISize_maxValue___closed__3, &l_ISize_maxValue___closed__3_once, _init_l_ISize_maxValue___closed__3);
v___x_1514_ = lean_obj_once(&l_ISize_maxValue___closed__2, &l_ISize_maxValue___closed__2_once, _init_l_ISize_maxValue___closed__2);
v___x_1515_ = lean_int_sub(v___x_1514_, v___x_1513_);
return v___x_1515_;
}
}
static size_t _init_l_ISize_maxValue___closed__5(void){
_start:
{
lean_object* v___x_1516_; size_t v___x_1517_; 
v___x_1516_ = lean_obj_once(&l_ISize_maxValue___closed__4, &l_ISize_maxValue___closed__4_once, _init_l_ISize_maxValue___closed__4);
v___x_1517_ = lean_isize_of_int(v___x_1516_);
return v___x_1517_;
}
}
static size_t _init_l_ISize_maxValue(void){
_start:
{
size_t v___x_1518_; 
v___x_1518_ = lean_usize_once(&l_ISize_maxValue___closed__5, &l_ISize_maxValue___closed__5_once, _init_l_ISize_maxValue___closed__5);
return v___x_1518_;
}
}
static lean_object* _init_l_ISize_minValue___closed__0(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_obj_once(&l_ISize_maxValue___closed__2, &l_ISize_maxValue___closed__2_once, _init_l_ISize_maxValue___closed__2);
v___x_1520_ = lean_int_neg(v___x_1519_);
return v___x_1520_;
}
}
static size_t _init_l_ISize_minValue___closed__1(void){
_start:
{
lean_object* v___x_1521_; size_t v___x_1522_; 
v___x_1521_ = lean_obj_once(&l_ISize_minValue___closed__0, &l_ISize_minValue___closed__0_once, _init_l_ISize_minValue___closed__0);
v___x_1522_ = lean_isize_of_int(v___x_1521_);
return v___x_1522_;
}
}
static size_t _init_l_ISize_minValue(void){
_start:
{
size_t v___x_1523_; 
v___x_1523_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
return v___x_1523_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntLE___redArg(lean_object* v_i_1524_){
_start:
{
size_t v___x_1525_; 
v___x_1525_ = lean_isize_of_int(v_i_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntLE___redArg___boxed(lean_object* v_i_1526_){
_start:
{
size_t v_res_1527_; lean_object* v_r_1528_; 
v_res_1527_ = l_ISize_ofIntLE___redArg(v_i_1526_);
lean_dec(v_i_1526_);
v_r_1528_ = lean_box_usize(v_res_1527_);
return v_r_1528_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntLE(lean_object* v_i_1529_, lean_object* v___hl_1530_, lean_object* v___hr_1531_){
_start:
{
size_t v___x_1532_; 
v___x_1532_ = lean_isize_of_int(v_i_1529_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntLE___boxed(lean_object* v_i_1533_, lean_object* v___hl_1534_, lean_object* v___hr_1535_){
_start:
{
size_t v_res_1536_; lean_object* v_r_1537_; 
v_res_1536_ = l_ISize_ofIntLE(v_i_1533_, v___hl_1534_, v___hr_1535_);
lean_dec(v_i_1533_);
v_r_1537_ = lean_box_usize(v_res_1536_);
return v_r_1537_;
}
}
static lean_object* _init_l_ISize_ofIntTruncate___closed__0(void){
_start:
{
size_t v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
v___x_1539_ = lean_isize_to_int(v___x_1538_);
return v___x_1539_;
}
}
static lean_object* _init_l_ISize_ofIntTruncate___closed__1(void){
_start:
{
size_t v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_usize_once(&l_ISize_maxValue___closed__5, &l_ISize_maxValue___closed__5_once, _init_l_ISize_maxValue___closed__5);
v___x_1541_ = lean_isize_to_int(v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntTruncate(lean_object* v_i_1542_){
_start:
{
size_t v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1543_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
v___x_1544_ = lean_obj_once(&l_ISize_ofIntTruncate___closed__0, &l_ISize_ofIntTruncate___closed__0_once, _init_l_ISize_ofIntTruncate___closed__0);
v___x_1545_ = lean_int_dec_le(v___x_1544_, v_i_1542_);
if (v___x_1545_ == 0)
{
return v___x_1543_;
}
else
{
lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1546_ = lean_obj_once(&l_ISize_ofIntTruncate___closed__1, &l_ISize_ofIntTruncate___closed__1_once, _init_l_ISize_ofIntTruncate___closed__1);
v___x_1547_ = lean_int_dec_le(v_i_1542_, v___x_1546_);
if (v___x_1547_ == 0)
{
return v___x_1543_;
}
else
{
size_t v___x_1548_; 
v___x_1548_ = lean_isize_of_int(v_i_1542_);
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntTruncate___boxed(lean_object* v_i_1549_){
_start:
{
size_t v_res_1550_; lean_object* v_r_1551_; 
v_res_1550_ = l_ISize_ofIntTruncate(v_i_1549_);
lean_dec(v_i_1549_);
v_r_1551_ = lean_box_usize(v_res_1550_);
return v_r_1551_;
}
}
LEAN_EXPORT lean_object* l_ISize_add___boxed(lean_object* v_a_1554_, lean_object* v_b_1555_){
_start:
{
size_t v_a_boxed_1556_; size_t v_b_boxed_1557_; size_t v_res_1558_; lean_object* v_r_1559_; 
v_a_boxed_1556_ = lean_unbox_usize(v_a_1554_);
lean_dec(v_a_1554_);
v_b_boxed_1557_ = lean_unbox_usize(v_b_1555_);
lean_dec(v_b_1555_);
v_res_1558_ = lean_isize_add(v_a_boxed_1556_, v_b_boxed_1557_);
v_r_1559_ = lean_box_usize(v_res_1558_);
return v_r_1559_;
}
}
LEAN_EXPORT lean_object* l_ISize_sub___boxed(lean_object* v_a_1562_, lean_object* v_b_1563_){
_start:
{
size_t v_a_boxed_1564_; size_t v_b_boxed_1565_; size_t v_res_1566_; lean_object* v_r_1567_; 
v_a_boxed_1564_ = lean_unbox_usize(v_a_1562_);
lean_dec(v_a_1562_);
v_b_boxed_1565_ = lean_unbox_usize(v_b_1563_);
lean_dec(v_b_1563_);
v_res_1566_ = lean_isize_sub(v_a_boxed_1564_, v_b_boxed_1565_);
v_r_1567_ = lean_box_usize(v_res_1566_);
return v_r_1567_;
}
}
LEAN_EXPORT lean_object* l_ISize_mul___boxed(lean_object* v_a_1570_, lean_object* v_b_1571_){
_start:
{
size_t v_a_boxed_1572_; size_t v_b_boxed_1573_; size_t v_res_1574_; lean_object* v_r_1575_; 
v_a_boxed_1572_ = lean_unbox_usize(v_a_1570_);
lean_dec(v_a_1570_);
v_b_boxed_1573_ = lean_unbox_usize(v_b_1571_);
lean_dec(v_b_1571_);
v_res_1574_ = lean_isize_mul(v_a_boxed_1572_, v_b_boxed_1573_);
v_r_1575_ = lean_box_usize(v_res_1574_);
return v_r_1575_;
}
}
LEAN_EXPORT lean_object* l_ISize_div___boxed(lean_object* v_a_1578_, lean_object* v_b_1579_){
_start:
{
size_t v_a_boxed_1580_; size_t v_b_boxed_1581_; size_t v_res_1582_; lean_object* v_r_1583_; 
v_a_boxed_1580_ = lean_unbox_usize(v_a_1578_);
lean_dec(v_a_1578_);
v_b_boxed_1581_ = lean_unbox_usize(v_b_1579_);
lean_dec(v_b_1579_);
v_res_1582_ = lean_isize_div(v_a_boxed_1580_, v_b_boxed_1581_);
v_r_1583_ = lean_box_usize(v_res_1582_);
return v_r_1583_;
}
}
static size_t _init_l_ISize_pow___closed__0(void){
_start:
{
lean_object* v___x_1584_; size_t v___x_1585_; 
v___x_1584_ = lean_unsigned_to_nat(1u);
v___x_1585_ = lean_isize_of_nat(v___x_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT size_t l_ISize_pow(size_t v_x_1586_, lean_object* v_n_1587_){
_start:
{
lean_object* v_zero_1588_; uint8_t v_isZero_1589_; 
v_zero_1588_ = lean_unsigned_to_nat(0u);
v_isZero_1589_ = lean_nat_dec_eq(v_n_1587_, v_zero_1588_);
if (v_isZero_1589_ == 1)
{
size_t v___x_1590_; 
v___x_1590_ = lean_usize_once(&l_ISize_pow___closed__0, &l_ISize_pow___closed__0_once, _init_l_ISize_pow___closed__0);
return v___x_1590_;
}
else
{
lean_object* v_one_1591_; lean_object* v_n_1592_; size_t v___x_1593_; size_t v___x_1594_; 
v_one_1591_ = lean_unsigned_to_nat(1u);
v_n_1592_ = lean_nat_sub(v_n_1587_, v_one_1591_);
v___x_1593_ = l_ISize_pow(v_x_1586_, v_n_1592_);
lean_dec(v_n_1592_);
v___x_1594_ = lean_isize_mul(v___x_1593_, v_x_1586_);
return v___x_1594_;
}
}
}
LEAN_EXPORT lean_object* l_ISize_pow___boxed(lean_object* v_x_1595_, lean_object* v_n_1596_){
_start:
{
size_t v_x_boxed_1597_; size_t v_res_1598_; lean_object* v_r_1599_; 
v_x_boxed_1597_ = lean_unbox_usize(v_x_1595_);
lean_dec(v_x_1595_);
v_res_1598_ = l_ISize_pow(v_x_boxed_1597_, v_n_1596_);
lean_dec(v_n_1596_);
v_r_1599_ = lean_box_usize(v_res_1598_);
return v_r_1599_;
}
}
LEAN_EXPORT lean_object* l_ISize_mod___boxed(lean_object* v_a_1602_, lean_object* v_b_1603_){
_start:
{
size_t v_a_boxed_1604_; size_t v_b_boxed_1605_; size_t v_res_1606_; lean_object* v_r_1607_; 
v_a_boxed_1604_ = lean_unbox_usize(v_a_1602_);
lean_dec(v_a_1602_);
v_b_boxed_1605_ = lean_unbox_usize(v_b_1603_);
lean_dec(v_b_1603_);
v_res_1606_ = lean_isize_mod(v_a_boxed_1604_, v_b_boxed_1605_);
v_r_1607_ = lean_box_usize(v_res_1606_);
return v_r_1607_;
}
}
LEAN_EXPORT lean_object* l_ISize_land___boxed(lean_object* v_a_1610_, lean_object* v_b_1611_){
_start:
{
size_t v_a_boxed_1612_; size_t v_b_boxed_1613_; size_t v_res_1614_; lean_object* v_r_1615_; 
v_a_boxed_1612_ = lean_unbox_usize(v_a_1610_);
lean_dec(v_a_1610_);
v_b_boxed_1613_ = lean_unbox_usize(v_b_1611_);
lean_dec(v_b_1611_);
v_res_1614_ = lean_isize_land(v_a_boxed_1612_, v_b_boxed_1613_);
v_r_1615_ = lean_box_usize(v_res_1614_);
return v_r_1615_;
}
}
LEAN_EXPORT lean_object* l_ISize_lor___boxed(lean_object* v_a_1618_, lean_object* v_b_1619_){
_start:
{
size_t v_a_boxed_1620_; size_t v_b_boxed_1621_; size_t v_res_1622_; lean_object* v_r_1623_; 
v_a_boxed_1620_ = lean_unbox_usize(v_a_1618_);
lean_dec(v_a_1618_);
v_b_boxed_1621_ = lean_unbox_usize(v_b_1619_);
lean_dec(v_b_1619_);
v_res_1622_ = lean_isize_lor(v_a_boxed_1620_, v_b_boxed_1621_);
v_r_1623_ = lean_box_usize(v_res_1622_);
return v_r_1623_;
}
}
LEAN_EXPORT lean_object* l_ISize_xor___boxed(lean_object* v_a_1626_, lean_object* v_b_1627_){
_start:
{
size_t v_a_boxed_1628_; size_t v_b_boxed_1629_; size_t v_res_1630_; lean_object* v_r_1631_; 
v_a_boxed_1628_ = lean_unbox_usize(v_a_1626_);
lean_dec(v_a_1626_);
v_b_boxed_1629_ = lean_unbox_usize(v_b_1627_);
lean_dec(v_b_1627_);
v_res_1630_ = lean_isize_xor(v_a_boxed_1628_, v_b_boxed_1629_);
v_r_1631_ = lean_box_usize(v_res_1630_);
return v_r_1631_;
}
}
LEAN_EXPORT lean_object* l_ISize_shiftLeft___boxed(lean_object* v_a_1634_, lean_object* v_b_1635_){
_start:
{
size_t v_a_boxed_1636_; size_t v_b_boxed_1637_; size_t v_res_1638_; lean_object* v_r_1639_; 
v_a_boxed_1636_ = lean_unbox_usize(v_a_1634_);
lean_dec(v_a_1634_);
v_b_boxed_1637_ = lean_unbox_usize(v_b_1635_);
lean_dec(v_b_1635_);
v_res_1638_ = lean_isize_shift_left(v_a_boxed_1636_, v_b_boxed_1637_);
v_r_1639_ = lean_box_usize(v_res_1638_);
return v_r_1639_;
}
}
LEAN_EXPORT lean_object* l_ISize_shiftRight___boxed(lean_object* v_a_1642_, lean_object* v_b_1643_){
_start:
{
size_t v_a_boxed_1644_; size_t v_b_boxed_1645_; size_t v_res_1646_; lean_object* v_r_1647_; 
v_a_boxed_1644_ = lean_unbox_usize(v_a_1642_);
lean_dec(v_a_1642_);
v_b_boxed_1645_ = lean_unbox_usize(v_b_1643_);
lean_dec(v_b_1643_);
v_res_1646_ = lean_isize_shift_right(v_a_boxed_1644_, v_b_boxed_1645_);
v_r_1647_ = lean_box_usize(v_res_1646_);
return v_r_1647_;
}
}
LEAN_EXPORT lean_object* l_ISize_complement___boxed(lean_object* v_a_1649_){
_start:
{
size_t v_a_boxed_1650_; size_t v_res_1651_; lean_object* v_r_1652_; 
v_a_boxed_1650_ = lean_unbox_usize(v_a_1649_);
lean_dec(v_a_1649_);
v_res_1651_ = lean_isize_complement(v_a_boxed_1650_);
v_r_1652_ = lean_box_usize(v_res_1651_);
return v_r_1652_;
}
}
LEAN_EXPORT lean_object* l_ISize_abs___boxed(lean_object* v_a_1654_){
_start:
{
size_t v_a_boxed_1655_; size_t v_res_1656_; lean_object* v_r_1657_; 
v_a_boxed_1655_ = lean_unbox_usize(v_a_1654_);
lean_dec(v_a_1654_);
v_res_1656_ = lean_isize_abs(v_a_boxed_1655_);
v_r_1657_ = lean_box_usize(v_res_1656_);
return v_r_1657_;
}
}
LEAN_EXPORT lean_object* l_ISize_decEq___boxed(lean_object* v_a_1660_, lean_object* v_b_1661_){
_start:
{
size_t v_a_boxed_1662_; size_t v_b_boxed_1663_; uint8_t v_res_1664_; lean_object* v_r_1665_; 
v_a_boxed_1662_ = lean_unbox_usize(v_a_1660_);
lean_dec(v_a_1660_);
v_b_boxed_1663_ = lean_unbox_usize(v_b_1661_);
lean_dec(v_b_1661_);
v_res_1664_ = lean_isize_dec_eq(v_a_boxed_1662_, v_b_boxed_1663_);
v_r_1665_ = lean_box(v_res_1664_);
return v_r_1665_;
}
}
static size_t _init_l_instInhabitedISize___closed__0(void){
_start:
{
lean_object* v___x_1666_; size_t v___x_1667_; 
v___x_1666_ = lean_unsigned_to_nat(0u);
v___x_1667_ = lean_isize_of_nat(v___x_1666_);
return v___x_1667_;
}
}
static size_t _init_l_instInhabitedISize(void){
_start:
{
size_t v___x_1668_; 
v___x_1668_ = lean_usize_once(&l_instInhabitedISize___closed__0, &l_instInhabitedISize___closed__0_once, _init_l_instInhabitedISize___closed__0);
return v___x_1668_;
}
}
static lean_object* _init_l_instLTISize(void){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_box(0);
return v___x_1681_;
}
}
static lean_object* _init_l_instLEISize(void){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_box(0);
return v___x_1682_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqISize(size_t v_a_1695_, size_t v_b_1696_){
_start:
{
uint8_t v___x_1697_; 
v___x_1697_ = lean_isize_dec_eq(v_a_1695_, v_b_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqISize___boxed(lean_object* v_a_1698_, lean_object* v_b_1699_){
_start:
{
size_t v_a_boxed_1700_; size_t v_b_boxed_1701_; uint8_t v_res_1702_; lean_object* v_r_1703_; 
v_a_boxed_1700_ = lean_unbox_usize(v_a_1698_);
lean_dec(v_a_1698_);
v_b_boxed_1701_ = lean_unbox_usize(v_b_1699_);
lean_dec(v_b_1699_);
v_res_1702_ = l_instDecidableEqISize(v_a_boxed_1700_, v_b_boxed_1701_);
v_r_1703_ = lean_box(v_res_1702_);
return v_r_1703_;
}
}
LEAN_EXPORT lean_object* l_Bool_toISize___boxed(lean_object* v_b_1705_){
_start:
{
uint8_t v_b_boxed_1706_; size_t v_res_1707_; lean_object* v_r_1708_; 
v_b_boxed_1706_ = lean_unbox(v_b_1705_);
v_res_1707_ = lean_bool_to_isize(v_b_boxed_1706_);
v_r_1708_ = lean_box_usize(v_res_1707_);
return v_r_1708_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLt___boxed(lean_object* v_a_1711_, lean_object* v_b_1712_){
_start:
{
size_t v_a_boxed_1713_; size_t v_b_boxed_1714_; uint8_t v_res_1715_; lean_object* v_r_1716_; 
v_a_boxed_1713_ = lean_unbox_usize(v_a_1711_);
lean_dec(v_a_1711_);
v_b_boxed_1714_ = lean_unbox_usize(v_b_1712_);
lean_dec(v_b_1712_);
v_res_1715_ = lean_isize_dec_lt(v_a_boxed_1713_, v_b_boxed_1714_);
v_r_1716_ = lean_box(v_res_1715_);
return v_r_1716_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLe___boxed(lean_object* v_a_1719_, lean_object* v_b_1720_){
_start:
{
size_t v_a_boxed_1721_; size_t v_b_boxed_1722_; uint8_t v_res_1723_; lean_object* v_r_1724_; 
v_a_boxed_1721_ = lean_unbox_usize(v_a_1719_);
lean_dec(v_a_1719_);
v_b_boxed_1722_ = lean_unbox_usize(v_b_1720_);
lean_dec(v_b_1720_);
v_res_1723_ = lean_isize_dec_le(v_a_boxed_1721_, v_b_boxed_1722_);
v_r_1724_ = lean_box(v_res_1723_);
return v_r_1724_;
}
}
LEAN_EXPORT size_t l_instMaxISize___lam__0(size_t v_x_1725_, size_t v_y_1726_){
_start:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_isize_dec_le(v_x_1725_, v_y_1726_);
if (v___x_1727_ == 0)
{
return v_x_1725_;
}
else
{
return v_y_1726_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxISize___lam__0___boxed(lean_object* v_x_1728_, lean_object* v_y_1729_){
_start:
{
size_t v_x_boxed_1730_; size_t v_y_boxed_1731_; size_t v_res_1732_; lean_object* v_r_1733_; 
v_x_boxed_1730_ = lean_unbox_usize(v_x_1728_);
lean_dec(v_x_1728_);
v_y_boxed_1731_ = lean_unbox_usize(v_y_1729_);
lean_dec(v_y_1729_);
v_res_1732_ = l_instMaxISize___lam__0(v_x_boxed_1730_, v_y_boxed_1731_);
v_r_1733_ = lean_box_usize(v_res_1732_);
return v_r_1733_;
}
}
LEAN_EXPORT size_t l_instMinISize___lam__0(size_t v_x_1736_, size_t v_y_1737_){
_start:
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_isize_dec_le(v_x_1736_, v_y_1737_);
if (v___x_1738_ == 0)
{
return v_y_1737_;
}
else
{
return v_x_1736_;
}
}
}
LEAN_EXPORT lean_object* l_instMinISize___lam__0___boxed(lean_object* v_x_1739_, lean_object* v_y_1740_){
_start:
{
size_t v_x_boxed_1741_; size_t v_y_boxed_1742_; size_t v_res_1743_; lean_object* v_r_1744_; 
v_x_boxed_1741_ = lean_unbox_usize(v_x_1739_);
lean_dec(v_x_1739_);
v_y_boxed_1742_ = lean_unbox_usize(v_y_1740_);
lean_dec(v_y_1740_);
v_res_1743_ = l_instMinISize___lam__0(v_x_boxed_1741_, v_y_boxed_1742_);
v_r_1744_ = lean_box_usize(v_res_1743_);
return v_r_1744_;
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
