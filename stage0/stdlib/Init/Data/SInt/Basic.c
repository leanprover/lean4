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
lean_object* lean_uint16_to_nat(uint16_t);
uint8_t l_BitVec_slt(lean_object*, lean_object*, lean_object*);
lean_object* l_UInt32_toUInt64___boxed(lean_object*);
size_t lean_usize_of_nat_mk(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint32_t lean_uint32_of_nat_mk(lean_object*);
uint8_t l_BitVec_sle(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_USize_toUInt64___boxed(lean_object*);
lean_object* l_UInt16_toUInt64___boxed(lean_object*);
uint8_t lean_uint8_of_nat_mk(lean_object*);
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
LEAN_EXPORT uint8_t l_Int8_decLt___aux__1(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_decLt___aux__1___boxed(lean_object*, lean_object*);
uint8_t lean_int8_dec_lt(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int8_decLe___aux__1(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Int8_decLe___aux__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Int16_decLt___aux__1(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_decLt___aux__1___boxed(lean_object*, lean_object*);
uint8_t lean_int16_dec_lt(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int16_decLe___aux__1(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Int16_decLe___aux__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Int32_decLt___aux__1(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_decLt___aux__1___boxed(lean_object*, lean_object*);
uint8_t lean_int32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int32_decLe___aux__1(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Int32_decLe___aux__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Int64_decLt___aux__1(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_decLt___aux__1___boxed(lean_object*, lean_object*);
uint8_t lean_int64_dec_lt(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int64_decLe___aux__1(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Int64_decLe___aux__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_ISize_decLt___aux__1(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_decLt___aux__1___boxed(lean_object*, lean_object*);
uint8_t lean_isize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ISize_decLe___aux__1(size_t, size_t);
LEAN_EXPORT lean_object* l_ISize_decLe___aux__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Int8_decLt___aux__1(uint8_t v_a_279_, uint8_t v_b_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_281_ = lean_unsigned_to_nat(8u);
v___x_282_ = lean_uint8_to_nat(v_a_279_);
v___x_283_ = lean_uint8_to_nat(v_b_280_);
v___x_284_ = l_BitVec_slt(v___x_281_, v___x_282_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLt___aux__1___boxed(lean_object* v_a_285_, lean_object* v_b_286_){
_start:
{
uint8_t v_a_boxed_287_; uint8_t v_b_boxed_288_; uint8_t v_res_289_; lean_object* v_r_290_; 
v_a_boxed_287_ = lean_unbox(v_a_285_);
v_b_boxed_288_ = lean_unbox(v_b_286_);
v_res_289_ = l_Int8_decLt___aux__1(v_a_boxed_287_, v_b_boxed_288_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLt___boxed(lean_object* v_a_293_, lean_object* v_b_294_){
_start:
{
uint8_t v_a_boxed_295_; uint8_t v_b_boxed_296_; uint8_t v_res_297_; lean_object* v_r_298_; 
v_a_boxed_295_ = lean_unbox(v_a_293_);
v_b_boxed_296_ = lean_unbox(v_b_294_);
v_res_297_ = lean_int8_dec_lt(v_a_boxed_295_, v_b_boxed_296_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT uint8_t l_Int8_decLe___aux__1(uint8_t v_a_299_, uint8_t v_b_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_301_ = lean_unsigned_to_nat(8u);
v___x_302_ = lean_uint8_to_nat(v_a_299_);
v___x_303_ = lean_uint8_to_nat(v_b_300_);
v___x_304_ = l_BitVec_sle(v___x_301_, v___x_302_, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLe___aux__1___boxed(lean_object* v_a_305_, lean_object* v_b_306_){
_start:
{
uint8_t v_a_boxed_307_; uint8_t v_b_boxed_308_; uint8_t v_res_309_; lean_object* v_r_310_; 
v_a_boxed_307_ = lean_unbox(v_a_305_);
v_b_boxed_308_ = lean_unbox(v_b_306_);
v_res_309_ = l_Int8_decLe___aux__1(v_a_boxed_307_, v_b_boxed_308_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLe___boxed(lean_object* v_a_313_, lean_object* v_b_314_){
_start:
{
uint8_t v_a_boxed_315_; uint8_t v_b_boxed_316_; uint8_t v_res_317_; lean_object* v_r_318_; 
v_a_boxed_315_ = lean_unbox(v_a_313_);
v_b_boxed_316_ = lean_unbox(v_b_314_);
v_res_317_ = lean_int8_dec_le(v_a_boxed_315_, v_b_boxed_316_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT uint8_t l_instMaxInt8___lam__0(uint8_t v_x_319_, uint8_t v_y_320_){
_start:
{
uint8_t v___x_321_; 
v___x_321_ = lean_int8_dec_le(v_x_319_, v_y_320_);
if (v___x_321_ == 0)
{
return v_x_319_;
}
else
{
return v_y_320_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt8___lam__0___boxed(lean_object* v_x_322_, lean_object* v_y_323_){
_start:
{
uint8_t v_x_boxed_324_; uint8_t v_y_boxed_325_; uint8_t v_res_326_; lean_object* v_r_327_; 
v_x_boxed_324_ = lean_unbox(v_x_322_);
v_y_boxed_325_ = lean_unbox(v_y_323_);
v_res_326_ = l_instMaxInt8___lam__0(v_x_boxed_324_, v_y_boxed_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT uint8_t l_instMinInt8___lam__0(uint8_t v_x_330_, uint8_t v_y_331_){
_start:
{
uint8_t v___x_332_; 
v___x_332_ = lean_int8_dec_le(v_x_330_, v_y_331_);
if (v___x_332_ == 0)
{
return v_y_331_;
}
else
{
return v_x_330_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt8___lam__0___boxed(lean_object* v_x_333_, lean_object* v_y_334_){
_start:
{
uint8_t v_x_boxed_335_; uint8_t v_y_boxed_336_; uint8_t v_res_337_; lean_object* v_r_338_; 
v_x_boxed_335_ = lean_unbox(v_x_333_);
v_y_boxed_336_ = lean_unbox(v_y_334_);
v_res_337_ = l_instMinInt8___lam__0(v_x_boxed_335_, v_y_boxed_336_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
static lean_object* _init_l_Int16_size(void){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lean_unsigned_to_nat(65536u);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Int16_toBitVec(uint16_t v_x_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = lean_uint16_to_nat(v_x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Int16_toBitVec___boxed(lean_object* v_x_344_){
_start:
{
uint16_t v_x_boxed_345_; lean_object* v_res_346_; 
v_x_boxed_345_ = lean_unbox(v_x_344_);
v_res_346_ = l_Int16_toBitVec(v_x_boxed_345_);
return v_res_346_;
}
}
LEAN_EXPORT uint16_t l_UInt16_toInt16(uint16_t v_i_347_){
_start:
{
return v_i_347_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toInt16___boxed(lean_object* v_i_348_){
_start:
{
uint16_t v_i_boxed_349_; uint16_t v_res_350_; lean_object* v_r_351_; 
v_i_boxed_349_ = lean_unbox(v_i_348_);
v_res_350_ = l_UInt16_toInt16(v_i_boxed_349_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofInt___boxed(lean_object* v_i_353_){
_start:
{
uint16_t v_res_354_; lean_object* v_r_355_; 
v_res_354_ = lean_int16_of_int(v_i_353_);
lean_dec(v_i_353_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofNat___boxed(lean_object* v_n_357_){
_start:
{
uint16_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = lean_int16_of_nat(v_n_357_);
lean_dec(v_n_357_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT uint16_t l_Int_toInt16(lean_object* v_i_360_){
_start:
{
uint16_t v___x_361_; 
v___x_361_ = lean_int16_of_int(v_i_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt16___boxed(lean_object* v_i_362_){
_start:
{
uint16_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_Int_toInt16(v_i_362_);
lean_dec(v_i_362_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT uint16_t l_Nat_toInt16(lean_object* v_n_365_){
_start:
{
uint16_t v___x_366_; 
v___x_366_ = lean_int16_of_nat(v_n_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt16___boxed(lean_object* v_n_367_){
_start:
{
uint16_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Nat_toInt16(v_n_367_);
lean_dec(v_n_367_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt___boxed(lean_object* v_i_371_){
_start:
{
uint16_t v_i_boxed_372_; lean_object* v_res_373_; 
v_i_boxed_372_ = lean_unbox(v_i_371_);
v_res_373_ = lean_int16_to_int(v_i_boxed_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg(uint16_t v_i_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_int16_to_int(v_i_374_);
v___x_376_ = l_Int_toNat(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg___boxed(lean_object* v_i_377_){
_start:
{
uint16_t v_i_boxed_378_; lean_object* v_res_379_; 
v_i_boxed_378_ = lean_unbox(v_i_377_);
v_res_379_ = l_Int16_toNatClampNeg(v_i_boxed_378_);
return v_res_379_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofBitVec(lean_object* v_b_380_){
_start:
{
uint16_t v___x_381_; 
v___x_381_ = lean_uint16_of_nat_mk(v_b_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofBitVec___boxed(lean_object* v_b_382_){
_start:
{
uint16_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l_Int16_ofBitVec(v_b_382_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt8___boxed(lean_object* v_a_386_){
_start:
{
uint16_t v_a_boxed_387_; uint8_t v_res_388_; lean_object* v_r_389_; 
v_a_boxed_387_ = lean_unbox(v_a_386_);
v_res_388_ = lean_int16_to_int8(v_a_boxed_387_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt16___boxed(lean_object* v_a_391_){
_start:
{
uint8_t v_a_boxed_392_; uint16_t v_res_393_; lean_object* v_r_394_; 
v_a_boxed_392_ = lean_unbox(v_a_391_);
v_res_393_ = lean_int8_to_int16(v_a_boxed_392_);
v_r_394_ = lean_box(v_res_393_);
return v_r_394_;
}
}
LEAN_EXPORT lean_object* l_Int16_neg___boxed(lean_object* v_i_396_){
_start:
{
uint16_t v_i_boxed_397_; uint16_t v_res_398_; lean_object* v_r_399_; 
v_i_boxed_397_ = lean_unbox(v_i_396_);
v_res_398_ = lean_int16_neg(v_i_boxed_397_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0(uint16_t v_i_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_int16_to_int(v_i_400_);
v___x_402_ = l_Int_repr(v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0___boxed(lean_object* v_i_403_){
_start:
{
uint16_t v_i_boxed_404_; lean_object* v_res_405_; 
v_i_boxed_404_ = lean_unbox(v_i_403_);
v_res_405_ = l_instToStringInt16___lam__0(v_i_boxed_404_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_instReprInt16___lam__0(uint16_t v_i_408_, lean_object* v_prec_409_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_410_ = lean_int16_to_int(v_i_408_);
v___x_411_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_412_ = lean_int_dec_lt(v___x_410_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = l_Int_repr(v___x_410_);
v___x_414_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = l_Int_repr(v___x_410_);
v___x_416_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
v___x_417_ = l_Repr_addAppParen(v___x_416_, v_prec_409_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt16___lam__0___boxed(lean_object* v_i_418_, lean_object* v_prec_419_){
_start:
{
uint16_t v_i_boxed_420_; lean_object* v_res_421_; 
v_i_boxed_420_ = lean_unbox(v_i_418_);
v_res_421_ = l_instReprInt16___lam__0(v_i_boxed_420_, v_prec_419_);
lean_dec(v_prec_419_);
return v_res_421_;
}
}
static lean_object* _init_l_instReprAtomInt16(void){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = lean_box(0);
return v___x_424_;
}
}
LEAN_EXPORT uint16_t l_Int16_instOfNat(lean_object* v_n_427_){
_start:
{
uint16_t v___x_428_; 
v___x_428_ = lean_int16_of_nat(v_n_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Int16_instOfNat___boxed(lean_object* v_n_429_){
_start:
{
uint16_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l_Int16_instOfNat(v_n_429_);
lean_dec(v_n_429_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
static uint16_t _init_l_Int16_maxValue___closed__0(void){
_start:
{
lean_object* v___x_434_; uint16_t v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(32767u);
v___x_435_ = lean_int16_of_nat(v___x_434_);
return v___x_435_;
}
}
static uint16_t _init_l_Int16_maxValue(void){
_start:
{
uint16_t v___x_436_; 
v___x_436_ = lean_uint16_once(&l_Int16_maxValue___closed__0, &l_Int16_maxValue___closed__0_once, _init_l_Int16_maxValue___closed__0);
return v___x_436_;
}
}
static uint16_t _init_l_Int16_minValue___closed__0(void){
_start:
{
lean_object* v___x_437_; uint16_t v___x_438_; 
v___x_437_ = lean_unsigned_to_nat(32768u);
v___x_438_ = lean_int16_of_nat(v___x_437_);
return v___x_438_;
}
}
static uint16_t _init_l_Int16_minValue___closed__1(void){
_start:
{
uint16_t v___x_439_; uint16_t v___x_440_; 
v___x_439_ = lean_uint16_once(&l_Int16_minValue___closed__0, &l_Int16_minValue___closed__0_once, _init_l_Int16_minValue___closed__0);
v___x_440_ = lean_int16_neg(v___x_439_);
return v___x_440_;
}
}
static uint16_t _init_l_Int16_minValue(void){
_start:
{
uint16_t v___x_441_; 
v___x_441_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
return v___x_441_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntLE___redArg(lean_object* v_i_442_){
_start:
{
uint16_t v___x_443_; 
v___x_443_ = lean_int16_of_int(v_i_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntLE___redArg___boxed(lean_object* v_i_444_){
_start:
{
uint16_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l_Int16_ofIntLE___redArg(v_i_444_);
lean_dec(v_i_444_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntLE(lean_object* v_i_447_, lean_object* v___hl_448_, lean_object* v___hr_449_){
_start:
{
uint16_t v___x_450_; 
v___x_450_ = lean_int16_of_int(v_i_447_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntLE___boxed(lean_object* v_i_451_, lean_object* v___hl_452_, lean_object* v___hr_453_){
_start:
{
uint16_t v_res_454_; lean_object* v_r_455_; 
v_res_454_ = l_Int16_ofIntLE(v_i_451_, v___hl_452_, v___hr_453_);
lean_dec(v_i_451_);
v_r_455_ = lean_box(v_res_454_);
return v_r_455_;
}
}
static lean_object* _init_l_Int16_ofIntTruncate___closed__0(void){
_start:
{
uint16_t v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
v___x_457_ = lean_int16_to_int(v___x_456_);
return v___x_457_;
}
}
static lean_object* _init_l_Int16_ofIntTruncate___closed__1(void){
_start:
{
uint16_t v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_uint16_once(&l_Int16_maxValue___closed__0, &l_Int16_maxValue___closed__0_once, _init_l_Int16_maxValue___closed__0);
v___x_459_ = lean_int16_to_int(v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntTruncate(lean_object* v_i_460_){
_start:
{
uint16_t v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_461_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
v___x_462_ = lean_obj_once(&l_Int16_ofIntTruncate___closed__0, &l_Int16_ofIntTruncate___closed__0_once, _init_l_Int16_ofIntTruncate___closed__0);
v___x_463_ = lean_int_dec_le(v___x_462_, v_i_460_);
if (v___x_463_ == 0)
{
return v___x_461_;
}
else
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = lean_obj_once(&l_Int16_ofIntTruncate___closed__1, &l_Int16_ofIntTruncate___closed__1_once, _init_l_Int16_ofIntTruncate___closed__1);
v___x_465_ = lean_int_dec_le(v_i_460_, v___x_464_);
if (v___x_465_ == 0)
{
return v___x_461_;
}
else
{
uint16_t v___x_466_; 
v___x_466_ = lean_int16_of_int(v_i_460_);
return v___x_466_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntTruncate___boxed(lean_object* v_i_467_){
_start:
{
uint16_t v_res_468_; lean_object* v_r_469_; 
v_res_468_ = l_Int16_ofIntTruncate(v_i_467_);
lean_dec(v_i_467_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT lean_object* l_Int16_add___boxed(lean_object* v_a_472_, lean_object* v_b_473_){
_start:
{
uint16_t v_a_boxed_474_; uint16_t v_b_boxed_475_; uint16_t v_res_476_; lean_object* v_r_477_; 
v_a_boxed_474_ = lean_unbox(v_a_472_);
v_b_boxed_475_ = lean_unbox(v_b_473_);
v_res_476_ = lean_int16_add(v_a_boxed_474_, v_b_boxed_475_);
v_r_477_ = lean_box(v_res_476_);
return v_r_477_;
}
}
LEAN_EXPORT lean_object* l_Int16_sub___boxed(lean_object* v_a_480_, lean_object* v_b_481_){
_start:
{
uint16_t v_a_boxed_482_; uint16_t v_b_boxed_483_; uint16_t v_res_484_; lean_object* v_r_485_; 
v_a_boxed_482_ = lean_unbox(v_a_480_);
v_b_boxed_483_ = lean_unbox(v_b_481_);
v_res_484_ = lean_int16_sub(v_a_boxed_482_, v_b_boxed_483_);
v_r_485_ = lean_box(v_res_484_);
return v_r_485_;
}
}
LEAN_EXPORT lean_object* l_Int16_mul___boxed(lean_object* v_a_488_, lean_object* v_b_489_){
_start:
{
uint16_t v_a_boxed_490_; uint16_t v_b_boxed_491_; uint16_t v_res_492_; lean_object* v_r_493_; 
v_a_boxed_490_ = lean_unbox(v_a_488_);
v_b_boxed_491_ = lean_unbox(v_b_489_);
v_res_492_ = lean_int16_mul(v_a_boxed_490_, v_b_boxed_491_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l_Int16_div___boxed(lean_object* v_a_496_, lean_object* v_b_497_){
_start:
{
uint16_t v_a_boxed_498_; uint16_t v_b_boxed_499_; uint16_t v_res_500_; lean_object* v_r_501_; 
v_a_boxed_498_ = lean_unbox(v_a_496_);
v_b_boxed_499_ = lean_unbox(v_b_497_);
v_res_500_ = lean_int16_div(v_a_boxed_498_, v_b_boxed_499_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
static uint16_t _init_l_Int16_pow___closed__0(void){
_start:
{
lean_object* v___x_502_; uint16_t v___x_503_; 
v___x_502_ = lean_unsigned_to_nat(1u);
v___x_503_ = lean_int16_of_nat(v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT uint16_t l_Int16_pow(uint16_t v_x_504_, lean_object* v_n_505_){
_start:
{
lean_object* v_zero_506_; uint8_t v_isZero_507_; 
v_zero_506_ = lean_unsigned_to_nat(0u);
v_isZero_507_ = lean_nat_dec_eq(v_n_505_, v_zero_506_);
if (v_isZero_507_ == 1)
{
uint16_t v___x_508_; 
v___x_508_ = lean_uint16_once(&l_Int16_pow___closed__0, &l_Int16_pow___closed__0_once, _init_l_Int16_pow___closed__0);
return v___x_508_;
}
else
{
lean_object* v_one_509_; lean_object* v_n_510_; uint16_t v___x_511_; uint16_t v___x_512_; 
v_one_509_ = lean_unsigned_to_nat(1u);
v_n_510_ = lean_nat_sub(v_n_505_, v_one_509_);
v___x_511_ = l_Int16_pow(v_x_504_, v_n_510_);
lean_dec(v_n_510_);
v___x_512_ = lean_int16_mul(v___x_511_, v_x_504_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_Int16_pow___boxed(lean_object* v_x_513_, lean_object* v_n_514_){
_start:
{
uint16_t v_x_boxed_515_; uint16_t v_res_516_; lean_object* v_r_517_; 
v_x_boxed_515_ = lean_unbox(v_x_513_);
v_res_516_ = l_Int16_pow(v_x_boxed_515_, v_n_514_);
lean_dec(v_n_514_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT lean_object* l_Int16_mod___boxed(lean_object* v_a_520_, lean_object* v_b_521_){
_start:
{
uint16_t v_a_boxed_522_; uint16_t v_b_boxed_523_; uint16_t v_res_524_; lean_object* v_r_525_; 
v_a_boxed_522_ = lean_unbox(v_a_520_);
v_b_boxed_523_ = lean_unbox(v_b_521_);
v_res_524_ = lean_int16_mod(v_a_boxed_522_, v_b_boxed_523_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT lean_object* l_Int16_land___boxed(lean_object* v_a_528_, lean_object* v_b_529_){
_start:
{
uint16_t v_a_boxed_530_; uint16_t v_b_boxed_531_; uint16_t v_res_532_; lean_object* v_r_533_; 
v_a_boxed_530_ = lean_unbox(v_a_528_);
v_b_boxed_531_ = lean_unbox(v_b_529_);
v_res_532_ = lean_int16_land(v_a_boxed_530_, v_b_boxed_531_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT lean_object* l_Int16_lor___boxed(lean_object* v_a_536_, lean_object* v_b_537_){
_start:
{
uint16_t v_a_boxed_538_; uint16_t v_b_boxed_539_; uint16_t v_res_540_; lean_object* v_r_541_; 
v_a_boxed_538_ = lean_unbox(v_a_536_);
v_b_boxed_539_ = lean_unbox(v_b_537_);
v_res_540_ = lean_int16_lor(v_a_boxed_538_, v_b_boxed_539_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT lean_object* l_Int16_xor___boxed(lean_object* v_a_544_, lean_object* v_b_545_){
_start:
{
uint16_t v_a_boxed_546_; uint16_t v_b_boxed_547_; uint16_t v_res_548_; lean_object* v_r_549_; 
v_a_boxed_546_ = lean_unbox(v_a_544_);
v_b_boxed_547_ = lean_unbox(v_b_545_);
v_res_548_ = lean_int16_xor(v_a_boxed_546_, v_b_boxed_547_);
v_r_549_ = lean_box(v_res_548_);
return v_r_549_;
}
}
LEAN_EXPORT lean_object* l_Int16_shiftLeft___boxed(lean_object* v_a_552_, lean_object* v_b_553_){
_start:
{
uint16_t v_a_boxed_554_; uint16_t v_b_boxed_555_; uint16_t v_res_556_; lean_object* v_r_557_; 
v_a_boxed_554_ = lean_unbox(v_a_552_);
v_b_boxed_555_ = lean_unbox(v_b_553_);
v_res_556_ = lean_int16_shift_left(v_a_boxed_554_, v_b_boxed_555_);
v_r_557_ = lean_box(v_res_556_);
return v_r_557_;
}
}
LEAN_EXPORT lean_object* l_Int16_shiftRight___boxed(lean_object* v_a_560_, lean_object* v_b_561_){
_start:
{
uint16_t v_a_boxed_562_; uint16_t v_b_boxed_563_; uint16_t v_res_564_; lean_object* v_r_565_; 
v_a_boxed_562_ = lean_unbox(v_a_560_);
v_b_boxed_563_ = lean_unbox(v_b_561_);
v_res_564_ = lean_int16_shift_right(v_a_boxed_562_, v_b_boxed_563_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT lean_object* l_Int16_complement___boxed(lean_object* v_a_567_){
_start:
{
uint16_t v_a_boxed_568_; uint16_t v_res_569_; lean_object* v_r_570_; 
v_a_boxed_568_ = lean_unbox(v_a_567_);
v_res_569_ = lean_int16_complement(v_a_boxed_568_);
v_r_570_ = lean_box(v_res_569_);
return v_r_570_;
}
}
LEAN_EXPORT lean_object* l_Int16_abs___boxed(lean_object* v_a_572_){
_start:
{
uint16_t v_a_boxed_573_; uint16_t v_res_574_; lean_object* v_r_575_; 
v_a_boxed_573_ = lean_unbox(v_a_572_);
v_res_574_ = lean_int16_abs(v_a_boxed_573_);
v_r_575_ = lean_box(v_res_574_);
return v_r_575_;
}
}
LEAN_EXPORT lean_object* l_Int16_decEq___boxed(lean_object* v_a_578_, lean_object* v_b_579_){
_start:
{
uint16_t v_a_boxed_580_; uint16_t v_b_boxed_581_; uint8_t v_res_582_; lean_object* v_r_583_; 
v_a_boxed_580_ = lean_unbox(v_a_578_);
v_b_boxed_581_ = lean_unbox(v_b_579_);
v_res_582_ = lean_int16_dec_eq(v_a_boxed_580_, v_b_boxed_581_);
v_r_583_ = lean_box(v_res_582_);
return v_r_583_;
}
}
static uint16_t _init_l_instInhabitedInt16___closed__0(void){
_start:
{
lean_object* v___x_584_; uint16_t v___x_585_; 
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_int16_of_nat(v___x_584_);
return v___x_585_;
}
}
static uint16_t _init_l_instInhabitedInt16(void){
_start:
{
uint16_t v___x_586_; 
v___x_586_ = lean_uint16_once(&l_instInhabitedInt16___closed__0, &l_instInhabitedInt16___closed__0_once, _init_l_instInhabitedInt16___closed__0);
return v___x_586_;
}
}
static lean_object* _init_l_instLTInt16(void){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = lean_box(0);
return v___x_599_;
}
}
static lean_object* _init_l_instLEInt16(void){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = lean_box(0);
return v___x_600_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt16(uint16_t v_a_613_, uint16_t v_b_614_){
_start:
{
uint8_t v___x_615_; 
v___x_615_ = lean_int16_dec_eq(v_a_613_, v_b_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt16___boxed(lean_object* v_a_616_, lean_object* v_b_617_){
_start:
{
uint16_t v_a_boxed_618_; uint16_t v_b_boxed_619_; uint8_t v_res_620_; lean_object* v_r_621_; 
v_a_boxed_618_ = lean_unbox(v_a_616_);
v_b_boxed_619_ = lean_unbox(v_b_617_);
v_res_620_ = l_instDecidableEqInt16(v_a_boxed_618_, v_b_boxed_619_);
v_r_621_ = lean_box(v_res_620_);
return v_r_621_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt16___boxed(lean_object* v_b_623_){
_start:
{
uint8_t v_b_boxed_624_; uint16_t v_res_625_; lean_object* v_r_626_; 
v_b_boxed_624_ = lean_unbox(v_b_623_);
v_res_625_ = lean_bool_to_int16(v_b_boxed_624_);
v_r_626_ = lean_box(v_res_625_);
return v_r_626_;
}
}
LEAN_EXPORT uint8_t l_Int16_decLt___aux__1(uint16_t v_a_627_, uint16_t v_b_628_){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_629_ = lean_unsigned_to_nat(16u);
v___x_630_ = lean_uint16_to_nat(v_a_627_);
v___x_631_ = lean_uint16_to_nat(v_b_628_);
v___x_632_ = l_BitVec_slt(v___x_629_, v___x_630_, v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLt___aux__1___boxed(lean_object* v_a_633_, lean_object* v_b_634_){
_start:
{
uint16_t v_a_boxed_635_; uint16_t v_b_boxed_636_; uint8_t v_res_637_; lean_object* v_r_638_; 
v_a_boxed_635_ = lean_unbox(v_a_633_);
v_b_boxed_636_ = lean_unbox(v_b_634_);
v_res_637_ = l_Int16_decLt___aux__1(v_a_boxed_635_, v_b_boxed_636_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLt___boxed(lean_object* v_a_641_, lean_object* v_b_642_){
_start:
{
uint16_t v_a_boxed_643_; uint16_t v_b_boxed_644_; uint8_t v_res_645_; lean_object* v_r_646_; 
v_a_boxed_643_ = lean_unbox(v_a_641_);
v_b_boxed_644_ = lean_unbox(v_b_642_);
v_res_645_ = lean_int16_dec_lt(v_a_boxed_643_, v_b_boxed_644_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT uint8_t l_Int16_decLe___aux__1(uint16_t v_a_647_, uint16_t v_b_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_649_ = lean_unsigned_to_nat(16u);
v___x_650_ = lean_uint16_to_nat(v_a_647_);
v___x_651_ = lean_uint16_to_nat(v_b_648_);
v___x_652_ = l_BitVec_sle(v___x_649_, v___x_650_, v___x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLe___aux__1___boxed(lean_object* v_a_653_, lean_object* v_b_654_){
_start:
{
uint16_t v_a_boxed_655_; uint16_t v_b_boxed_656_; uint8_t v_res_657_; lean_object* v_r_658_; 
v_a_boxed_655_ = lean_unbox(v_a_653_);
v_b_boxed_656_ = lean_unbox(v_b_654_);
v_res_657_ = l_Int16_decLe___aux__1(v_a_boxed_655_, v_b_boxed_656_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLe___boxed(lean_object* v_a_661_, lean_object* v_b_662_){
_start:
{
uint16_t v_a_boxed_663_; uint16_t v_b_boxed_664_; uint8_t v_res_665_; lean_object* v_r_666_; 
v_a_boxed_663_ = lean_unbox(v_a_661_);
v_b_boxed_664_ = lean_unbox(v_b_662_);
v_res_665_ = lean_int16_dec_le(v_a_boxed_663_, v_b_boxed_664_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT uint16_t l_instMaxInt16___lam__0(uint16_t v_x_667_, uint16_t v_y_668_){
_start:
{
uint8_t v___x_669_; 
v___x_669_ = lean_int16_dec_le(v_x_667_, v_y_668_);
if (v___x_669_ == 0)
{
return v_x_667_;
}
else
{
return v_y_668_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt16___lam__0___boxed(lean_object* v_x_670_, lean_object* v_y_671_){
_start:
{
uint16_t v_x_boxed_672_; uint16_t v_y_boxed_673_; uint16_t v_res_674_; lean_object* v_r_675_; 
v_x_boxed_672_ = lean_unbox(v_x_670_);
v_y_boxed_673_ = lean_unbox(v_y_671_);
v_res_674_ = l_instMaxInt16___lam__0(v_x_boxed_672_, v_y_boxed_673_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
LEAN_EXPORT uint16_t l_instMinInt16___lam__0(uint16_t v_x_678_, uint16_t v_y_679_){
_start:
{
uint8_t v___x_680_; 
v___x_680_ = lean_int16_dec_le(v_x_678_, v_y_679_);
if (v___x_680_ == 0)
{
return v_y_679_;
}
else
{
return v_x_678_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt16___lam__0___boxed(lean_object* v_x_681_, lean_object* v_y_682_){
_start:
{
uint16_t v_x_boxed_683_; uint16_t v_y_boxed_684_; uint16_t v_res_685_; lean_object* v_r_686_; 
v_x_boxed_683_ = lean_unbox(v_x_681_);
v_y_boxed_684_ = lean_unbox(v_y_682_);
v_res_685_ = l_instMinInt16___lam__0(v_x_boxed_683_, v_y_boxed_684_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
static lean_object* _init_l_Int32_size(void){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = lean_cstr_to_nat("4294967296");
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Int32_toBitVec(uint32_t v_x_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = lean_uint32_to_nat(v_x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Int32_toBitVec___boxed(lean_object* v_x_692_){
_start:
{
uint32_t v_x_boxed_693_; lean_object* v_res_694_; 
v_x_boxed_693_ = lean_unbox_uint32(v_x_692_);
lean_dec(v_x_692_);
v_res_694_ = l_Int32_toBitVec(v_x_boxed_693_);
return v_res_694_;
}
}
LEAN_EXPORT uint32_t l_UInt32_toInt32(uint32_t v_i_695_){
_start:
{
return v_i_695_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toInt32___boxed(lean_object* v_i_696_){
_start:
{
uint32_t v_i_boxed_697_; uint32_t v_res_698_; lean_object* v_r_699_; 
v_i_boxed_697_ = lean_unbox_uint32(v_i_696_);
lean_dec(v_i_696_);
v_res_698_ = l_UInt32_toInt32(v_i_boxed_697_);
v_r_699_ = lean_box_uint32(v_res_698_);
return v_r_699_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofInt___boxed(lean_object* v_i_701_){
_start:
{
uint32_t v_res_702_; lean_object* v_r_703_; 
v_res_702_ = lean_int32_of_int(v_i_701_);
lean_dec(v_i_701_);
v_r_703_ = lean_box_uint32(v_res_702_);
return v_r_703_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofNat___boxed(lean_object* v_n_705_){
_start:
{
uint32_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = lean_int32_of_nat(v_n_705_);
lean_dec(v_n_705_);
v_r_707_ = lean_box_uint32(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT uint32_t l_Int_toInt32(lean_object* v_i_708_){
_start:
{
uint32_t v___x_709_; 
v___x_709_ = lean_int32_of_int(v_i_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt32___boxed(lean_object* v_i_710_){
_start:
{
uint32_t v_res_711_; lean_object* v_r_712_; 
v_res_711_ = l_Int_toInt32(v_i_710_);
lean_dec(v_i_710_);
v_r_712_ = lean_box_uint32(v_res_711_);
return v_r_712_;
}
}
LEAN_EXPORT uint32_t l_Nat_toInt32(lean_object* v_n_713_){
_start:
{
uint32_t v___x_714_; 
v___x_714_ = lean_int32_of_nat(v_n_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt32___boxed(lean_object* v_n_715_){
_start:
{
uint32_t v_res_716_; lean_object* v_r_717_; 
v_res_716_ = l_Nat_toInt32(v_n_715_);
lean_dec(v_n_715_);
v_r_717_ = lean_box_uint32(v_res_716_);
return v_r_717_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt___boxed(lean_object* v_i_719_){
_start:
{
uint32_t v_i_boxed_720_; lean_object* v_res_721_; 
v_i_boxed_720_ = lean_unbox_uint32(v_i_719_);
lean_dec(v_i_719_);
v_res_721_ = lean_int32_to_int(v_i_boxed_720_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg(uint32_t v_i_722_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_int32_to_int(v_i_722_);
v___x_724_ = l_Int_toNat(v___x_723_);
lean_dec(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg___boxed(lean_object* v_i_725_){
_start:
{
uint32_t v_i_boxed_726_; lean_object* v_res_727_; 
v_i_boxed_726_ = lean_unbox_uint32(v_i_725_);
lean_dec(v_i_725_);
v_res_727_ = l_Int32_toNatClampNeg(v_i_boxed_726_);
return v_res_727_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofBitVec(lean_object* v_b_728_){
_start:
{
uint32_t v___x_729_; 
v___x_729_ = lean_uint32_of_nat_mk(v_b_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofBitVec___boxed(lean_object* v_b_730_){
_start:
{
uint32_t v_res_731_; lean_object* v_r_732_; 
v_res_731_ = l_Int32_ofBitVec(v_b_730_);
v_r_732_ = lean_box_uint32(v_res_731_);
return v_r_732_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt8___boxed(lean_object* v_a_734_){
_start:
{
uint32_t v_a_boxed_735_; uint8_t v_res_736_; lean_object* v_r_737_; 
v_a_boxed_735_ = lean_unbox_uint32(v_a_734_);
lean_dec(v_a_734_);
v_res_736_ = lean_int32_to_int8(v_a_boxed_735_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt16___boxed(lean_object* v_a_739_){
_start:
{
uint32_t v_a_boxed_740_; uint16_t v_res_741_; lean_object* v_r_742_; 
v_a_boxed_740_ = lean_unbox_uint32(v_a_739_);
lean_dec(v_a_739_);
v_res_741_ = lean_int32_to_int16(v_a_boxed_740_);
v_r_742_ = lean_box(v_res_741_);
return v_r_742_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt32___boxed(lean_object* v_a_744_){
_start:
{
uint8_t v_a_boxed_745_; uint32_t v_res_746_; lean_object* v_r_747_; 
v_a_boxed_745_ = lean_unbox(v_a_744_);
v_res_746_ = lean_int8_to_int32(v_a_boxed_745_);
v_r_747_ = lean_box_uint32(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt32___boxed(lean_object* v_a_749_){
_start:
{
uint16_t v_a_boxed_750_; uint32_t v_res_751_; lean_object* v_r_752_; 
v_a_boxed_750_ = lean_unbox(v_a_749_);
v_res_751_ = lean_int16_to_int32(v_a_boxed_750_);
v_r_752_ = lean_box_uint32(v_res_751_);
return v_r_752_;
}
}
LEAN_EXPORT lean_object* l_Int32_neg___boxed(lean_object* v_i_754_){
_start:
{
uint32_t v_i_boxed_755_; uint32_t v_res_756_; lean_object* v_r_757_; 
v_i_boxed_755_ = lean_unbox_uint32(v_i_754_);
lean_dec(v_i_754_);
v_res_756_ = lean_int32_neg(v_i_boxed_755_);
v_r_757_ = lean_box_uint32(v_res_756_);
return v_r_757_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0(uint32_t v_i_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_int32_to_int(v_i_758_);
v___x_760_ = l_Int_repr(v___x_759_);
lean_dec(v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0___boxed(lean_object* v_i_761_){
_start:
{
uint32_t v_i_boxed_762_; lean_object* v_res_763_; 
v_i_boxed_762_ = lean_unbox_uint32(v_i_761_);
lean_dec(v_i_761_);
v_res_763_ = l_instToStringInt32___lam__0(v_i_boxed_762_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_instReprInt32___lam__0(uint32_t v_i_766_, lean_object* v_prec_767_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_768_ = lean_int32_to_int(v_i_766_);
v___x_769_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_770_ = lean_int_dec_lt(v___x_768_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = l_Int_repr(v___x_768_);
lean_dec(v___x_768_);
v___x_772_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
return v___x_772_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = l_Int_repr(v___x_768_);
lean_dec(v___x_768_);
v___x_774_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
v___x_775_ = l_Repr_addAppParen(v___x_774_, v_prec_767_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt32___lam__0___boxed(lean_object* v_i_776_, lean_object* v_prec_777_){
_start:
{
uint32_t v_i_boxed_778_; lean_object* v_res_779_; 
v_i_boxed_778_ = lean_unbox_uint32(v_i_776_);
lean_dec(v_i_776_);
v_res_779_ = l_instReprInt32___lam__0(v_i_boxed_778_, v_prec_777_);
lean_dec(v_prec_777_);
return v_res_779_;
}
}
static lean_object* _init_l_instReprAtomInt32(void){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = lean_box(0);
return v___x_782_;
}
}
LEAN_EXPORT uint32_t l_Int32_instOfNat(lean_object* v_n_785_){
_start:
{
uint32_t v___x_786_; 
v___x_786_ = lean_int32_of_nat(v_n_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Int32_instOfNat___boxed(lean_object* v_n_787_){
_start:
{
uint32_t v_res_788_; lean_object* v_r_789_; 
v_res_788_ = l_Int32_instOfNat(v_n_787_);
lean_dec(v_n_787_);
v_r_789_ = lean_box_uint32(v_res_788_);
return v_r_789_;
}
}
static uint32_t _init_l_Int32_maxValue___closed__0(void){
_start:
{
lean_object* v___x_792_; uint32_t v___x_793_; 
v___x_792_ = lean_unsigned_to_nat(2147483647u);
v___x_793_ = lean_int32_of_nat(v___x_792_);
return v___x_793_;
}
}
static uint32_t _init_l_Int32_maxValue(void){
_start:
{
uint32_t v___x_794_; 
v___x_794_ = lean_uint32_once(&l_Int32_maxValue___closed__0, &l_Int32_maxValue___closed__0_once, _init_l_Int32_maxValue___closed__0);
return v___x_794_;
}
}
static uint32_t _init_l_Int32_minValue___closed__0(void){
_start:
{
lean_object* v___x_795_; uint32_t v___x_796_; 
v___x_795_ = lean_unsigned_to_nat(2147483648u);
v___x_796_ = lean_int32_of_nat(v___x_795_);
return v___x_796_;
}
}
static uint32_t _init_l_Int32_minValue___closed__1(void){
_start:
{
uint32_t v___x_797_; uint32_t v___x_798_; 
v___x_797_ = lean_uint32_once(&l_Int32_minValue___closed__0, &l_Int32_minValue___closed__0_once, _init_l_Int32_minValue___closed__0);
v___x_798_ = lean_int32_neg(v___x_797_);
return v___x_798_;
}
}
static uint32_t _init_l_Int32_minValue(void){
_start:
{
uint32_t v___x_799_; 
v___x_799_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
return v___x_799_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntLE___redArg(lean_object* v_i_800_){
_start:
{
uint32_t v___x_801_; 
v___x_801_ = lean_int32_of_int(v_i_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntLE___redArg___boxed(lean_object* v_i_802_){
_start:
{
uint32_t v_res_803_; lean_object* v_r_804_; 
v_res_803_ = l_Int32_ofIntLE___redArg(v_i_802_);
lean_dec(v_i_802_);
v_r_804_ = lean_box_uint32(v_res_803_);
return v_r_804_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntLE(lean_object* v_i_805_, lean_object* v___hl_806_, lean_object* v___hr_807_){
_start:
{
uint32_t v___x_808_; 
v___x_808_ = lean_int32_of_int(v_i_805_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntLE___boxed(lean_object* v_i_809_, lean_object* v___hl_810_, lean_object* v___hr_811_){
_start:
{
uint32_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_Int32_ofIntLE(v_i_809_, v___hl_810_, v___hr_811_);
lean_dec(v_i_809_);
v_r_813_ = lean_box_uint32(v_res_812_);
return v_r_813_;
}
}
static lean_object* _init_l_Int32_ofIntTruncate___closed__0(void){
_start:
{
uint32_t v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
v___x_815_ = lean_int32_to_int(v___x_814_);
return v___x_815_;
}
}
static lean_object* _init_l_Int32_ofIntTruncate___closed__1(void){
_start:
{
uint32_t v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_uint32_once(&l_Int32_maxValue___closed__0, &l_Int32_maxValue___closed__0_once, _init_l_Int32_maxValue___closed__0);
v___x_817_ = lean_int32_to_int(v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntTruncate(lean_object* v_i_818_){
_start:
{
uint32_t v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_819_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
v___x_820_ = lean_obj_once(&l_Int32_ofIntTruncate___closed__0, &l_Int32_ofIntTruncate___closed__0_once, _init_l_Int32_ofIntTruncate___closed__0);
v___x_821_ = lean_int_dec_le(v___x_820_, v_i_818_);
if (v___x_821_ == 0)
{
return v___x_819_;
}
else
{
lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_822_ = lean_obj_once(&l_Int32_ofIntTruncate___closed__1, &l_Int32_ofIntTruncate___closed__1_once, _init_l_Int32_ofIntTruncate___closed__1);
v___x_823_ = lean_int_dec_le(v_i_818_, v___x_822_);
if (v___x_823_ == 0)
{
return v___x_819_;
}
else
{
uint32_t v___x_824_; 
v___x_824_ = lean_int32_of_int(v_i_818_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntTruncate___boxed(lean_object* v_i_825_){
_start:
{
uint32_t v_res_826_; lean_object* v_r_827_; 
v_res_826_ = l_Int32_ofIntTruncate(v_i_825_);
lean_dec(v_i_825_);
v_r_827_ = lean_box_uint32(v_res_826_);
return v_r_827_;
}
}
LEAN_EXPORT lean_object* l_Int32_add___boxed(lean_object* v_a_830_, lean_object* v_b_831_){
_start:
{
uint32_t v_a_boxed_832_; uint32_t v_b_boxed_833_; uint32_t v_res_834_; lean_object* v_r_835_; 
v_a_boxed_832_ = lean_unbox_uint32(v_a_830_);
lean_dec(v_a_830_);
v_b_boxed_833_ = lean_unbox_uint32(v_b_831_);
lean_dec(v_b_831_);
v_res_834_ = lean_int32_add(v_a_boxed_832_, v_b_boxed_833_);
v_r_835_ = lean_box_uint32(v_res_834_);
return v_r_835_;
}
}
LEAN_EXPORT lean_object* l_Int32_sub___boxed(lean_object* v_a_838_, lean_object* v_b_839_){
_start:
{
uint32_t v_a_boxed_840_; uint32_t v_b_boxed_841_; uint32_t v_res_842_; lean_object* v_r_843_; 
v_a_boxed_840_ = lean_unbox_uint32(v_a_838_);
lean_dec(v_a_838_);
v_b_boxed_841_ = lean_unbox_uint32(v_b_839_);
lean_dec(v_b_839_);
v_res_842_ = lean_int32_sub(v_a_boxed_840_, v_b_boxed_841_);
v_r_843_ = lean_box_uint32(v_res_842_);
return v_r_843_;
}
}
LEAN_EXPORT lean_object* l_Int32_mul___boxed(lean_object* v_a_846_, lean_object* v_b_847_){
_start:
{
uint32_t v_a_boxed_848_; uint32_t v_b_boxed_849_; uint32_t v_res_850_; lean_object* v_r_851_; 
v_a_boxed_848_ = lean_unbox_uint32(v_a_846_);
lean_dec(v_a_846_);
v_b_boxed_849_ = lean_unbox_uint32(v_b_847_);
lean_dec(v_b_847_);
v_res_850_ = lean_int32_mul(v_a_boxed_848_, v_b_boxed_849_);
v_r_851_ = lean_box_uint32(v_res_850_);
return v_r_851_;
}
}
LEAN_EXPORT lean_object* l_Int32_div___boxed(lean_object* v_a_854_, lean_object* v_b_855_){
_start:
{
uint32_t v_a_boxed_856_; uint32_t v_b_boxed_857_; uint32_t v_res_858_; lean_object* v_r_859_; 
v_a_boxed_856_ = lean_unbox_uint32(v_a_854_);
lean_dec(v_a_854_);
v_b_boxed_857_ = lean_unbox_uint32(v_b_855_);
lean_dec(v_b_855_);
v_res_858_ = lean_int32_div(v_a_boxed_856_, v_b_boxed_857_);
v_r_859_ = lean_box_uint32(v_res_858_);
return v_r_859_;
}
}
static uint32_t _init_l_Int32_pow___closed__0(void){
_start:
{
lean_object* v___x_860_; uint32_t v___x_861_; 
v___x_860_ = lean_unsigned_to_nat(1u);
v___x_861_ = lean_int32_of_nat(v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT uint32_t l_Int32_pow(uint32_t v_x_862_, lean_object* v_n_863_){
_start:
{
lean_object* v_zero_864_; uint8_t v_isZero_865_; 
v_zero_864_ = lean_unsigned_to_nat(0u);
v_isZero_865_ = lean_nat_dec_eq(v_n_863_, v_zero_864_);
if (v_isZero_865_ == 1)
{
uint32_t v___x_866_; 
v___x_866_ = lean_uint32_once(&l_Int32_pow___closed__0, &l_Int32_pow___closed__0_once, _init_l_Int32_pow___closed__0);
return v___x_866_;
}
else
{
lean_object* v_one_867_; lean_object* v_n_868_; uint32_t v___x_869_; uint32_t v___x_870_; 
v_one_867_ = lean_unsigned_to_nat(1u);
v_n_868_ = lean_nat_sub(v_n_863_, v_one_867_);
v___x_869_ = l_Int32_pow(v_x_862_, v_n_868_);
lean_dec(v_n_868_);
v___x_870_ = lean_int32_mul(v___x_869_, v_x_862_);
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l_Int32_pow___boxed(lean_object* v_x_871_, lean_object* v_n_872_){
_start:
{
uint32_t v_x_boxed_873_; uint32_t v_res_874_; lean_object* v_r_875_; 
v_x_boxed_873_ = lean_unbox_uint32(v_x_871_);
lean_dec(v_x_871_);
v_res_874_ = l_Int32_pow(v_x_boxed_873_, v_n_872_);
lean_dec(v_n_872_);
v_r_875_ = lean_box_uint32(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l_Int32_mod___boxed(lean_object* v_a_878_, lean_object* v_b_879_){
_start:
{
uint32_t v_a_boxed_880_; uint32_t v_b_boxed_881_; uint32_t v_res_882_; lean_object* v_r_883_; 
v_a_boxed_880_ = lean_unbox_uint32(v_a_878_);
lean_dec(v_a_878_);
v_b_boxed_881_ = lean_unbox_uint32(v_b_879_);
lean_dec(v_b_879_);
v_res_882_ = lean_int32_mod(v_a_boxed_880_, v_b_boxed_881_);
v_r_883_ = lean_box_uint32(v_res_882_);
return v_r_883_;
}
}
LEAN_EXPORT lean_object* l_Int32_land___boxed(lean_object* v_a_886_, lean_object* v_b_887_){
_start:
{
uint32_t v_a_boxed_888_; uint32_t v_b_boxed_889_; uint32_t v_res_890_; lean_object* v_r_891_; 
v_a_boxed_888_ = lean_unbox_uint32(v_a_886_);
lean_dec(v_a_886_);
v_b_boxed_889_ = lean_unbox_uint32(v_b_887_);
lean_dec(v_b_887_);
v_res_890_ = lean_int32_land(v_a_boxed_888_, v_b_boxed_889_);
v_r_891_ = lean_box_uint32(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT lean_object* l_Int32_lor___boxed(lean_object* v_a_894_, lean_object* v_b_895_){
_start:
{
uint32_t v_a_boxed_896_; uint32_t v_b_boxed_897_; uint32_t v_res_898_; lean_object* v_r_899_; 
v_a_boxed_896_ = lean_unbox_uint32(v_a_894_);
lean_dec(v_a_894_);
v_b_boxed_897_ = lean_unbox_uint32(v_b_895_);
lean_dec(v_b_895_);
v_res_898_ = lean_int32_lor(v_a_boxed_896_, v_b_boxed_897_);
v_r_899_ = lean_box_uint32(v_res_898_);
return v_r_899_;
}
}
LEAN_EXPORT lean_object* l_Int32_xor___boxed(lean_object* v_a_902_, lean_object* v_b_903_){
_start:
{
uint32_t v_a_boxed_904_; uint32_t v_b_boxed_905_; uint32_t v_res_906_; lean_object* v_r_907_; 
v_a_boxed_904_ = lean_unbox_uint32(v_a_902_);
lean_dec(v_a_902_);
v_b_boxed_905_ = lean_unbox_uint32(v_b_903_);
lean_dec(v_b_903_);
v_res_906_ = lean_int32_xor(v_a_boxed_904_, v_b_boxed_905_);
v_r_907_ = lean_box_uint32(v_res_906_);
return v_r_907_;
}
}
LEAN_EXPORT lean_object* l_Int32_shiftLeft___boxed(lean_object* v_a_910_, lean_object* v_b_911_){
_start:
{
uint32_t v_a_boxed_912_; uint32_t v_b_boxed_913_; uint32_t v_res_914_; lean_object* v_r_915_; 
v_a_boxed_912_ = lean_unbox_uint32(v_a_910_);
lean_dec(v_a_910_);
v_b_boxed_913_ = lean_unbox_uint32(v_b_911_);
lean_dec(v_b_911_);
v_res_914_ = lean_int32_shift_left(v_a_boxed_912_, v_b_boxed_913_);
v_r_915_ = lean_box_uint32(v_res_914_);
return v_r_915_;
}
}
LEAN_EXPORT lean_object* l_Int32_shiftRight___boxed(lean_object* v_a_918_, lean_object* v_b_919_){
_start:
{
uint32_t v_a_boxed_920_; uint32_t v_b_boxed_921_; uint32_t v_res_922_; lean_object* v_r_923_; 
v_a_boxed_920_ = lean_unbox_uint32(v_a_918_);
lean_dec(v_a_918_);
v_b_boxed_921_ = lean_unbox_uint32(v_b_919_);
lean_dec(v_b_919_);
v_res_922_ = lean_int32_shift_right(v_a_boxed_920_, v_b_boxed_921_);
v_r_923_ = lean_box_uint32(v_res_922_);
return v_r_923_;
}
}
LEAN_EXPORT lean_object* l_Int32_complement___boxed(lean_object* v_a_925_){
_start:
{
uint32_t v_a_boxed_926_; uint32_t v_res_927_; lean_object* v_r_928_; 
v_a_boxed_926_ = lean_unbox_uint32(v_a_925_);
lean_dec(v_a_925_);
v_res_927_ = lean_int32_complement(v_a_boxed_926_);
v_r_928_ = lean_box_uint32(v_res_927_);
return v_r_928_;
}
}
LEAN_EXPORT lean_object* l_Int32_abs___boxed(lean_object* v_a_930_){
_start:
{
uint32_t v_a_boxed_931_; uint32_t v_res_932_; lean_object* v_r_933_; 
v_a_boxed_931_ = lean_unbox_uint32(v_a_930_);
lean_dec(v_a_930_);
v_res_932_ = lean_int32_abs(v_a_boxed_931_);
v_r_933_ = lean_box_uint32(v_res_932_);
return v_r_933_;
}
}
LEAN_EXPORT lean_object* l_Int32_decEq___boxed(lean_object* v_a_936_, lean_object* v_b_937_){
_start:
{
uint32_t v_a_boxed_938_; uint32_t v_b_boxed_939_; uint8_t v_res_940_; lean_object* v_r_941_; 
v_a_boxed_938_ = lean_unbox_uint32(v_a_936_);
lean_dec(v_a_936_);
v_b_boxed_939_ = lean_unbox_uint32(v_b_937_);
lean_dec(v_b_937_);
v_res_940_ = lean_int32_dec_eq(v_a_boxed_938_, v_b_boxed_939_);
v_r_941_ = lean_box(v_res_940_);
return v_r_941_;
}
}
static uint32_t _init_l_instInhabitedInt32___closed__0(void){
_start:
{
lean_object* v___x_942_; uint32_t v___x_943_; 
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_int32_of_nat(v___x_942_);
return v___x_943_;
}
}
static uint32_t _init_l_instInhabitedInt32(void){
_start:
{
uint32_t v___x_944_; 
v___x_944_ = lean_uint32_once(&l_instInhabitedInt32___closed__0, &l_instInhabitedInt32___closed__0_once, _init_l_instInhabitedInt32___closed__0);
return v___x_944_;
}
}
static lean_object* _init_l_instLTInt32(void){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = lean_box(0);
return v___x_957_;
}
}
static lean_object* _init_l_instLEInt32(void){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = lean_box(0);
return v___x_958_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt32(uint32_t v_a_971_, uint32_t v_b_972_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = lean_int32_dec_eq(v_a_971_, v_b_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt32___boxed(lean_object* v_a_974_, lean_object* v_b_975_){
_start:
{
uint32_t v_a_boxed_976_; uint32_t v_b_boxed_977_; uint8_t v_res_978_; lean_object* v_r_979_; 
v_a_boxed_976_ = lean_unbox_uint32(v_a_974_);
lean_dec(v_a_974_);
v_b_boxed_977_ = lean_unbox_uint32(v_b_975_);
lean_dec(v_b_975_);
v_res_978_ = l_instDecidableEqInt32(v_a_boxed_976_, v_b_boxed_977_);
v_r_979_ = lean_box(v_res_978_);
return v_r_979_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt32___boxed(lean_object* v_b_981_){
_start:
{
uint8_t v_b_boxed_982_; uint32_t v_res_983_; lean_object* v_r_984_; 
v_b_boxed_982_ = lean_unbox(v_b_981_);
v_res_983_ = lean_bool_to_int32(v_b_boxed_982_);
v_r_984_ = lean_box_uint32(v_res_983_);
return v_r_984_;
}
}
LEAN_EXPORT uint8_t l_Int32_decLt___aux__1(uint32_t v_a_985_, uint32_t v_b_986_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_987_ = lean_unsigned_to_nat(32u);
v___x_988_ = lean_uint32_to_nat(v_a_985_);
v___x_989_ = lean_uint32_to_nat(v_b_986_);
v___x_990_ = l_BitVec_slt(v___x_987_, v___x_988_, v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLt___aux__1___boxed(lean_object* v_a_991_, lean_object* v_b_992_){
_start:
{
uint32_t v_a_boxed_993_; uint32_t v_b_boxed_994_; uint8_t v_res_995_; lean_object* v_r_996_; 
v_a_boxed_993_ = lean_unbox_uint32(v_a_991_);
lean_dec(v_a_991_);
v_b_boxed_994_ = lean_unbox_uint32(v_b_992_);
lean_dec(v_b_992_);
v_res_995_ = l_Int32_decLt___aux__1(v_a_boxed_993_, v_b_boxed_994_);
v_r_996_ = lean_box(v_res_995_);
return v_r_996_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLt___boxed(lean_object* v_a_999_, lean_object* v_b_1000_){
_start:
{
uint32_t v_a_boxed_1001_; uint32_t v_b_boxed_1002_; uint8_t v_res_1003_; lean_object* v_r_1004_; 
v_a_boxed_1001_ = lean_unbox_uint32(v_a_999_);
lean_dec(v_a_999_);
v_b_boxed_1002_ = lean_unbox_uint32(v_b_1000_);
lean_dec(v_b_1000_);
v_res_1003_ = lean_int32_dec_lt(v_a_boxed_1001_, v_b_boxed_1002_);
v_r_1004_ = lean_box(v_res_1003_);
return v_r_1004_;
}
}
LEAN_EXPORT uint8_t l_Int32_decLe___aux__1(uint32_t v_a_1005_, uint32_t v_b_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1007_ = lean_unsigned_to_nat(32u);
v___x_1008_ = lean_uint32_to_nat(v_a_1005_);
v___x_1009_ = lean_uint32_to_nat(v_b_1006_);
v___x_1010_ = l_BitVec_sle(v___x_1007_, v___x_1008_, v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLe___aux__1___boxed(lean_object* v_a_1011_, lean_object* v_b_1012_){
_start:
{
uint32_t v_a_boxed_1013_; uint32_t v_b_boxed_1014_; uint8_t v_res_1015_; lean_object* v_r_1016_; 
v_a_boxed_1013_ = lean_unbox_uint32(v_a_1011_);
lean_dec(v_a_1011_);
v_b_boxed_1014_ = lean_unbox_uint32(v_b_1012_);
lean_dec(v_b_1012_);
v_res_1015_ = l_Int32_decLe___aux__1(v_a_boxed_1013_, v_b_boxed_1014_);
v_r_1016_ = lean_box(v_res_1015_);
return v_r_1016_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLe___boxed(lean_object* v_a_1019_, lean_object* v_b_1020_){
_start:
{
uint32_t v_a_boxed_1021_; uint32_t v_b_boxed_1022_; uint8_t v_res_1023_; lean_object* v_r_1024_; 
v_a_boxed_1021_ = lean_unbox_uint32(v_a_1019_);
lean_dec(v_a_1019_);
v_b_boxed_1022_ = lean_unbox_uint32(v_b_1020_);
lean_dec(v_b_1020_);
v_res_1023_ = lean_int32_dec_le(v_a_boxed_1021_, v_b_boxed_1022_);
v_r_1024_ = lean_box(v_res_1023_);
return v_r_1024_;
}
}
LEAN_EXPORT uint32_t l_instMaxInt32___lam__0(uint32_t v_x_1025_, uint32_t v_y_1026_){
_start:
{
uint8_t v___x_1027_; 
v___x_1027_ = lean_int32_dec_le(v_x_1025_, v_y_1026_);
if (v___x_1027_ == 0)
{
return v_x_1025_;
}
else
{
return v_y_1026_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt32___lam__0___boxed(lean_object* v_x_1028_, lean_object* v_y_1029_){
_start:
{
uint32_t v_x_boxed_1030_; uint32_t v_y_boxed_1031_; uint32_t v_res_1032_; lean_object* v_r_1033_; 
v_x_boxed_1030_ = lean_unbox_uint32(v_x_1028_);
lean_dec(v_x_1028_);
v_y_boxed_1031_ = lean_unbox_uint32(v_y_1029_);
lean_dec(v_y_1029_);
v_res_1032_ = l_instMaxInt32___lam__0(v_x_boxed_1030_, v_y_boxed_1031_);
v_r_1033_ = lean_box_uint32(v_res_1032_);
return v_r_1033_;
}
}
LEAN_EXPORT uint32_t l_instMinInt32___lam__0(uint32_t v_x_1036_, uint32_t v_y_1037_){
_start:
{
uint8_t v___x_1038_; 
v___x_1038_ = lean_int32_dec_le(v_x_1036_, v_y_1037_);
if (v___x_1038_ == 0)
{
return v_y_1037_;
}
else
{
return v_x_1036_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt32___lam__0___boxed(lean_object* v_x_1039_, lean_object* v_y_1040_){
_start:
{
uint32_t v_x_boxed_1041_; uint32_t v_y_boxed_1042_; uint32_t v_res_1043_; lean_object* v_r_1044_; 
v_x_boxed_1041_ = lean_unbox_uint32(v_x_1039_);
lean_dec(v_x_1039_);
v_y_boxed_1042_ = lean_unbox_uint32(v_y_1040_);
lean_dec(v_y_1040_);
v_res_1043_ = l_instMinInt32___lam__0(v_x_boxed_1041_, v_y_boxed_1042_);
v_r_1044_ = lean_box_uint32(v_res_1043_);
return v_r_1044_;
}
}
static lean_object* _init_l_Int64_size___closed__0(void){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_cstr_to_nat("18446744073709551616");
return v___x_1047_;
}
}
static lean_object* _init_l_Int64_size(void){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_obj_once(&l_Int64_size___closed__0, &l_Int64_size___closed__0_once, _init_l_Int64_size___closed__0);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Int64_toBitVec(uint64_t v_x_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_uint64_to_nat(v_x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Int64_toBitVec___boxed(lean_object* v_x_1051_){
_start:
{
uint64_t v_x_boxed_1052_; lean_object* v_res_1053_; 
v_x_boxed_1052_ = lean_unbox_uint64(v_x_1051_);
lean_dec_ref(v_x_1051_);
v_res_1053_ = l_Int64_toBitVec(v_x_boxed_1052_);
return v_res_1053_;
}
}
LEAN_EXPORT uint64_t l_UInt64_toInt64(uint64_t v_i_1054_){
_start:
{
return v_i_1054_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toInt64___boxed(lean_object* v_i_1055_){
_start:
{
uint64_t v_i_boxed_1056_; uint64_t v_res_1057_; lean_object* v_r_1058_; 
v_i_boxed_1056_ = lean_unbox_uint64(v_i_1055_);
lean_dec_ref(v_i_1055_);
v_res_1057_ = l_UInt64_toInt64(v_i_boxed_1056_);
v_r_1058_ = lean_box_uint64(v_res_1057_);
return v_r_1058_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofInt___boxed(lean_object* v_i_1060_){
_start:
{
uint64_t v_res_1061_; lean_object* v_r_1062_; 
v_res_1061_ = lean_int64_of_int(v_i_1060_);
lean_dec(v_i_1060_);
v_r_1062_ = lean_box_uint64(v_res_1061_);
return v_r_1062_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofNat___boxed(lean_object* v_n_1064_){
_start:
{
uint64_t v_res_1065_; lean_object* v_r_1066_; 
v_res_1065_ = lean_int64_of_nat(v_n_1064_);
lean_dec(v_n_1064_);
v_r_1066_ = lean_box_uint64(v_res_1065_);
return v_r_1066_;
}
}
LEAN_EXPORT uint64_t l_Int_toInt64(lean_object* v_i_1067_){
_start:
{
uint64_t v___x_1068_; 
v___x_1068_ = lean_int64_of_int(v_i_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt64___boxed(lean_object* v_i_1069_){
_start:
{
uint64_t v_res_1070_; lean_object* v_r_1071_; 
v_res_1070_ = l_Int_toInt64(v_i_1069_);
lean_dec(v_i_1069_);
v_r_1071_ = lean_box_uint64(v_res_1070_);
return v_r_1071_;
}
}
LEAN_EXPORT uint64_t l_Nat_toInt64(lean_object* v_n_1072_){
_start:
{
uint64_t v___x_1073_; 
v___x_1073_ = lean_int64_of_nat(v_n_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt64___boxed(lean_object* v_n_1074_){
_start:
{
uint64_t v_res_1075_; lean_object* v_r_1076_; 
v_res_1075_ = l_Nat_toInt64(v_n_1074_);
lean_dec(v_n_1074_);
v_r_1076_ = lean_box_uint64(v_res_1075_);
return v_r_1076_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt___boxed(lean_object* v_i_1078_){
_start:
{
uint64_t v_i_boxed_1079_; lean_object* v_res_1080_; 
v_i_boxed_1079_ = lean_unbox_uint64(v_i_1078_);
lean_dec_ref(v_i_1078_);
v_res_1080_ = lean_int64_to_int_sint(v_i_boxed_1079_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg(uint64_t v_i_1081_){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_int64_to_int_sint(v_i_1081_);
v___x_1083_ = l_Int_toNat(v___x_1082_);
lean_dec(v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg___boxed(lean_object* v_i_1084_){
_start:
{
uint64_t v_i_boxed_1085_; lean_object* v_res_1086_; 
v_i_boxed_1085_ = lean_unbox_uint64(v_i_1084_);
lean_dec_ref(v_i_1084_);
v_res_1086_ = l_Int64_toNatClampNeg(v_i_boxed_1085_);
return v_res_1086_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofBitVec(lean_object* v_b_1087_){
_start:
{
uint64_t v___x_1088_; 
v___x_1088_ = lean_uint64_of_nat_mk(v_b_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofBitVec___boxed(lean_object* v_b_1089_){
_start:
{
uint64_t v_res_1090_; lean_object* v_r_1091_; 
v_res_1090_ = l_Int64_ofBitVec(v_b_1089_);
v_r_1091_ = lean_box_uint64(v_res_1090_);
return v_r_1091_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt8___boxed(lean_object* v_a_1093_){
_start:
{
uint64_t v_a_boxed_1094_; uint8_t v_res_1095_; lean_object* v_r_1096_; 
v_a_boxed_1094_ = lean_unbox_uint64(v_a_1093_);
lean_dec_ref(v_a_1093_);
v_res_1095_ = lean_int64_to_int8(v_a_boxed_1094_);
v_r_1096_ = lean_box(v_res_1095_);
return v_r_1096_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt16___boxed(lean_object* v_a_1098_){
_start:
{
uint64_t v_a_boxed_1099_; uint16_t v_res_1100_; lean_object* v_r_1101_; 
v_a_boxed_1099_ = lean_unbox_uint64(v_a_1098_);
lean_dec_ref(v_a_1098_);
v_res_1100_ = lean_int64_to_int16(v_a_boxed_1099_);
v_r_1101_ = lean_box(v_res_1100_);
return v_r_1101_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt32___boxed(lean_object* v_a_1103_){
_start:
{
uint64_t v_a_boxed_1104_; uint32_t v_res_1105_; lean_object* v_r_1106_; 
v_a_boxed_1104_ = lean_unbox_uint64(v_a_1103_);
lean_dec_ref(v_a_1103_);
v_res_1105_ = lean_int64_to_int32(v_a_boxed_1104_);
v_r_1106_ = lean_box_uint32(v_res_1105_);
return v_r_1106_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt64___boxed(lean_object* v_a_1108_){
_start:
{
uint8_t v_a_boxed_1109_; uint64_t v_res_1110_; lean_object* v_r_1111_; 
v_a_boxed_1109_ = lean_unbox(v_a_1108_);
v_res_1110_ = lean_int8_to_int64(v_a_boxed_1109_);
v_r_1111_ = lean_box_uint64(v_res_1110_);
return v_r_1111_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt64___boxed(lean_object* v_a_1113_){
_start:
{
uint16_t v_a_boxed_1114_; uint64_t v_res_1115_; lean_object* v_r_1116_; 
v_a_boxed_1114_ = lean_unbox(v_a_1113_);
v_res_1115_ = lean_int16_to_int64(v_a_boxed_1114_);
v_r_1116_ = lean_box_uint64(v_res_1115_);
return v_r_1116_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt64___boxed(lean_object* v_a_1118_){
_start:
{
uint32_t v_a_boxed_1119_; uint64_t v_res_1120_; lean_object* v_r_1121_; 
v_a_boxed_1119_ = lean_unbox_uint32(v_a_1118_);
lean_dec(v_a_1118_);
v_res_1120_ = lean_int32_to_int64(v_a_boxed_1119_);
v_r_1121_ = lean_box_uint64(v_res_1120_);
return v_r_1121_;
}
}
LEAN_EXPORT lean_object* l_Int64_neg___boxed(lean_object* v_i_1123_){
_start:
{
uint64_t v_i_boxed_1124_; uint64_t v_res_1125_; lean_object* v_r_1126_; 
v_i_boxed_1124_ = lean_unbox_uint64(v_i_1123_);
lean_dec_ref(v_i_1123_);
v_res_1125_ = lean_int64_neg(v_i_boxed_1124_);
v_r_1126_ = lean_box_uint64(v_res_1125_);
return v_r_1126_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0(uint64_t v_i_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_int64_to_int_sint(v_i_1127_);
v___x_1129_ = l_Int_repr(v___x_1128_);
lean_dec(v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0___boxed(lean_object* v_i_1130_){
_start:
{
uint64_t v_i_boxed_1131_; lean_object* v_res_1132_; 
v_i_boxed_1131_ = lean_unbox_uint64(v_i_1130_);
lean_dec_ref(v_i_1130_);
v_res_1132_ = l_instToStringInt64___lam__0(v_i_boxed_1131_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_instReprInt64___lam__0(uint64_t v_i_1135_, lean_object* v_prec_1136_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1137_ = lean_int64_to_int_sint(v_i_1135_);
v___x_1138_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_1139_ = lean_int_dec_lt(v___x_1137_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = l_Int_repr(v___x_1137_);
lean_dec(v___x_1137_);
v___x_1141_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = l_Int_repr(v___x_1137_);
lean_dec(v___x_1137_);
v___x_1143_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
v___x_1144_ = l_Repr_addAppParen(v___x_1143_, v_prec_1136_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt64___lam__0___boxed(lean_object* v_i_1145_, lean_object* v_prec_1146_){
_start:
{
uint64_t v_i_boxed_1147_; lean_object* v_res_1148_; 
v_i_boxed_1147_ = lean_unbox_uint64(v_i_1145_);
lean_dec_ref(v_i_1145_);
v_res_1148_ = l_instReprInt64___lam__0(v_i_boxed_1147_, v_prec_1146_);
lean_dec(v_prec_1146_);
return v_res_1148_;
}
}
static lean_object* _init_l_instReprAtomInt64(void){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_box(0);
return v___x_1151_;
}
}
LEAN_EXPORT uint64_t l_instHashableInt64___lam__0(uint64_t v_i_1152_){
_start:
{
return v_i_1152_;
}
}
LEAN_EXPORT lean_object* l_instHashableInt64___lam__0___boxed(lean_object* v_i_1153_){
_start:
{
uint64_t v_i_boxed_1154_; uint64_t v_res_1155_; lean_object* v_r_1156_; 
v_i_boxed_1154_ = lean_unbox_uint64(v_i_1153_);
lean_dec_ref(v_i_1153_);
v_res_1155_ = l_instHashableInt64___lam__0(v_i_boxed_1154_);
v_r_1156_ = lean_box_uint64(v_res_1155_);
return v_r_1156_;
}
}
LEAN_EXPORT uint64_t l_Int64_instOfNat(lean_object* v_n_1159_){
_start:
{
uint64_t v___x_1160_; 
v___x_1160_ = lean_int64_of_nat(v_n_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Int64_instOfNat___boxed(lean_object* v_n_1161_){
_start:
{
uint64_t v_res_1162_; lean_object* v_r_1163_; 
v_res_1162_ = l_Int64_instOfNat(v_n_1161_);
lean_dec(v_n_1161_);
v_r_1163_ = lean_box_uint64(v_res_1162_);
return v_r_1163_;
}
}
static uint64_t _init_l_Int64_maxValue___closed__0(void){
_start:
{
lean_object* v___x_1166_; uint64_t v___x_1167_; 
v___x_1166_ = lean_cstr_to_nat("9223372036854775807");
v___x_1167_ = lean_int64_of_nat(v___x_1166_);
return v___x_1167_;
}
}
static uint64_t _init_l_Int64_maxValue(void){
_start:
{
uint64_t v___x_1168_; 
v___x_1168_ = lean_uint64_once(&l_Int64_maxValue___closed__0, &l_Int64_maxValue___closed__0_once, _init_l_Int64_maxValue___closed__0);
return v___x_1168_;
}
}
static lean_object* _init_l_Int64_minValue___closed__0(void){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_cstr_to_nat("9223372036854775808");
return v___x_1169_;
}
}
static uint64_t _init_l_Int64_minValue___closed__1(void){
_start:
{
lean_object* v___x_1170_; uint64_t v___x_1171_; 
v___x_1170_ = lean_obj_once(&l_Int64_minValue___closed__0, &l_Int64_minValue___closed__0_once, _init_l_Int64_minValue___closed__0);
v___x_1171_ = lean_int64_of_nat(v___x_1170_);
return v___x_1171_;
}
}
static uint64_t _init_l_Int64_minValue___closed__2(void){
_start:
{
uint64_t v___x_1172_; uint64_t v___x_1173_; 
v___x_1172_ = lean_uint64_once(&l_Int64_minValue___closed__1, &l_Int64_minValue___closed__1_once, _init_l_Int64_minValue___closed__1);
v___x_1173_ = lean_int64_neg(v___x_1172_);
return v___x_1173_;
}
}
static uint64_t _init_l_Int64_minValue(void){
_start:
{
uint64_t v___x_1174_; 
v___x_1174_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
return v___x_1174_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntLE___redArg(lean_object* v_i_1175_){
_start:
{
uint64_t v___x_1176_; 
v___x_1176_ = lean_int64_of_int(v_i_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntLE___redArg___boxed(lean_object* v_i_1177_){
_start:
{
uint64_t v_res_1178_; lean_object* v_r_1179_; 
v_res_1178_ = l_Int64_ofIntLE___redArg(v_i_1177_);
lean_dec(v_i_1177_);
v_r_1179_ = lean_box_uint64(v_res_1178_);
return v_r_1179_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntLE(lean_object* v_i_1180_, lean_object* v___hl_1181_, lean_object* v___hr_1182_){
_start:
{
uint64_t v___x_1183_; 
v___x_1183_ = lean_int64_of_int(v_i_1180_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntLE___boxed(lean_object* v_i_1184_, lean_object* v___hl_1185_, lean_object* v___hr_1186_){
_start:
{
uint64_t v_res_1187_; lean_object* v_r_1188_; 
v_res_1187_ = l_Int64_ofIntLE(v_i_1184_, v___hl_1185_, v___hr_1186_);
lean_dec(v_i_1184_);
v_r_1188_ = lean_box_uint64(v_res_1187_);
return v_r_1188_;
}
}
static lean_object* _init_l_Int64_ofIntTruncate___closed__0(void){
_start:
{
uint64_t v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
v___x_1190_ = lean_int64_to_int_sint(v___x_1189_);
return v___x_1190_;
}
}
static lean_object* _init_l_Int64_ofIntTruncate___closed__1(void){
_start:
{
uint64_t v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_uint64_once(&l_Int64_maxValue___closed__0, &l_Int64_maxValue___closed__0_once, _init_l_Int64_maxValue___closed__0);
v___x_1192_ = lean_int64_to_int_sint(v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntTruncate(lean_object* v_i_1193_){
_start:
{
uint64_t v___x_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1194_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
v___x_1195_ = lean_obj_once(&l_Int64_ofIntTruncate___closed__0, &l_Int64_ofIntTruncate___closed__0_once, _init_l_Int64_ofIntTruncate___closed__0);
v___x_1196_ = lean_int_dec_le(v___x_1195_, v_i_1193_);
if (v___x_1196_ == 0)
{
return v___x_1194_;
}
else
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = lean_obj_once(&l_Int64_ofIntTruncate___closed__1, &l_Int64_ofIntTruncate___closed__1_once, _init_l_Int64_ofIntTruncate___closed__1);
v___x_1198_ = lean_int_dec_le(v_i_1193_, v___x_1197_);
if (v___x_1198_ == 0)
{
return v___x_1194_;
}
else
{
uint64_t v___x_1199_; 
v___x_1199_ = lean_int64_of_int(v_i_1193_);
return v___x_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntTruncate___boxed(lean_object* v_i_1200_){
_start:
{
uint64_t v_res_1201_; lean_object* v_r_1202_; 
v_res_1201_ = l_Int64_ofIntTruncate(v_i_1200_);
lean_dec(v_i_1200_);
v_r_1202_ = lean_box_uint64(v_res_1201_);
return v_r_1202_;
}
}
LEAN_EXPORT lean_object* l_Int64_add___boxed(lean_object* v_a_1205_, lean_object* v_b_1206_){
_start:
{
uint64_t v_a_boxed_1207_; uint64_t v_b_boxed_1208_; uint64_t v_res_1209_; lean_object* v_r_1210_; 
v_a_boxed_1207_ = lean_unbox_uint64(v_a_1205_);
lean_dec_ref(v_a_1205_);
v_b_boxed_1208_ = lean_unbox_uint64(v_b_1206_);
lean_dec_ref(v_b_1206_);
v_res_1209_ = lean_int64_add(v_a_boxed_1207_, v_b_boxed_1208_);
v_r_1210_ = lean_box_uint64(v_res_1209_);
return v_r_1210_;
}
}
LEAN_EXPORT lean_object* l_Int64_sub___boxed(lean_object* v_a_1213_, lean_object* v_b_1214_){
_start:
{
uint64_t v_a_boxed_1215_; uint64_t v_b_boxed_1216_; uint64_t v_res_1217_; lean_object* v_r_1218_; 
v_a_boxed_1215_ = lean_unbox_uint64(v_a_1213_);
lean_dec_ref(v_a_1213_);
v_b_boxed_1216_ = lean_unbox_uint64(v_b_1214_);
lean_dec_ref(v_b_1214_);
v_res_1217_ = lean_int64_sub(v_a_boxed_1215_, v_b_boxed_1216_);
v_r_1218_ = lean_box_uint64(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT lean_object* l_Int64_mul___boxed(lean_object* v_a_1221_, lean_object* v_b_1222_){
_start:
{
uint64_t v_a_boxed_1223_; uint64_t v_b_boxed_1224_; uint64_t v_res_1225_; lean_object* v_r_1226_; 
v_a_boxed_1223_ = lean_unbox_uint64(v_a_1221_);
lean_dec_ref(v_a_1221_);
v_b_boxed_1224_ = lean_unbox_uint64(v_b_1222_);
lean_dec_ref(v_b_1222_);
v_res_1225_ = lean_int64_mul(v_a_boxed_1223_, v_b_boxed_1224_);
v_r_1226_ = lean_box_uint64(v_res_1225_);
return v_r_1226_;
}
}
LEAN_EXPORT lean_object* l_Int64_div___boxed(lean_object* v_a_1229_, lean_object* v_b_1230_){
_start:
{
uint64_t v_a_boxed_1231_; uint64_t v_b_boxed_1232_; uint64_t v_res_1233_; lean_object* v_r_1234_; 
v_a_boxed_1231_ = lean_unbox_uint64(v_a_1229_);
lean_dec_ref(v_a_1229_);
v_b_boxed_1232_ = lean_unbox_uint64(v_b_1230_);
lean_dec_ref(v_b_1230_);
v_res_1233_ = lean_int64_div(v_a_boxed_1231_, v_b_boxed_1232_);
v_r_1234_ = lean_box_uint64(v_res_1233_);
return v_r_1234_;
}
}
static uint64_t _init_l_Int64_pow___closed__0(void){
_start:
{
lean_object* v___x_1235_; uint64_t v___x_1236_; 
v___x_1235_ = lean_unsigned_to_nat(1u);
v___x_1236_ = lean_int64_of_nat(v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT uint64_t l_Int64_pow(uint64_t v_x_1237_, lean_object* v_n_1238_){
_start:
{
lean_object* v_zero_1239_; uint8_t v_isZero_1240_; 
v_zero_1239_ = lean_unsigned_to_nat(0u);
v_isZero_1240_ = lean_nat_dec_eq(v_n_1238_, v_zero_1239_);
if (v_isZero_1240_ == 1)
{
uint64_t v___x_1241_; 
v___x_1241_ = lean_uint64_once(&l_Int64_pow___closed__0, &l_Int64_pow___closed__0_once, _init_l_Int64_pow___closed__0);
return v___x_1241_;
}
else
{
lean_object* v_one_1242_; lean_object* v_n_1243_; uint64_t v___x_1244_; uint64_t v___x_1245_; 
v_one_1242_ = lean_unsigned_to_nat(1u);
v_n_1243_ = lean_nat_sub(v_n_1238_, v_one_1242_);
v___x_1244_ = l_Int64_pow(v_x_1237_, v_n_1243_);
lean_dec(v_n_1243_);
v___x_1245_ = lean_int64_mul(v___x_1244_, v_x_1237_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Int64_pow___boxed(lean_object* v_x_1246_, lean_object* v_n_1247_){
_start:
{
uint64_t v_x_boxed_1248_; uint64_t v_res_1249_; lean_object* v_r_1250_; 
v_x_boxed_1248_ = lean_unbox_uint64(v_x_1246_);
lean_dec_ref(v_x_1246_);
v_res_1249_ = l_Int64_pow(v_x_boxed_1248_, v_n_1247_);
lean_dec(v_n_1247_);
v_r_1250_ = lean_box_uint64(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT lean_object* l_Int64_mod___boxed(lean_object* v_a_1253_, lean_object* v_b_1254_){
_start:
{
uint64_t v_a_boxed_1255_; uint64_t v_b_boxed_1256_; uint64_t v_res_1257_; lean_object* v_r_1258_; 
v_a_boxed_1255_ = lean_unbox_uint64(v_a_1253_);
lean_dec_ref(v_a_1253_);
v_b_boxed_1256_ = lean_unbox_uint64(v_b_1254_);
lean_dec_ref(v_b_1254_);
v_res_1257_ = lean_int64_mod(v_a_boxed_1255_, v_b_boxed_1256_);
v_r_1258_ = lean_box_uint64(v_res_1257_);
return v_r_1258_;
}
}
LEAN_EXPORT lean_object* l_Int64_land___boxed(lean_object* v_a_1261_, lean_object* v_b_1262_){
_start:
{
uint64_t v_a_boxed_1263_; uint64_t v_b_boxed_1264_; uint64_t v_res_1265_; lean_object* v_r_1266_; 
v_a_boxed_1263_ = lean_unbox_uint64(v_a_1261_);
lean_dec_ref(v_a_1261_);
v_b_boxed_1264_ = lean_unbox_uint64(v_b_1262_);
lean_dec_ref(v_b_1262_);
v_res_1265_ = lean_int64_land(v_a_boxed_1263_, v_b_boxed_1264_);
v_r_1266_ = lean_box_uint64(v_res_1265_);
return v_r_1266_;
}
}
LEAN_EXPORT lean_object* l_Int64_lor___boxed(lean_object* v_a_1269_, lean_object* v_b_1270_){
_start:
{
uint64_t v_a_boxed_1271_; uint64_t v_b_boxed_1272_; uint64_t v_res_1273_; lean_object* v_r_1274_; 
v_a_boxed_1271_ = lean_unbox_uint64(v_a_1269_);
lean_dec_ref(v_a_1269_);
v_b_boxed_1272_ = lean_unbox_uint64(v_b_1270_);
lean_dec_ref(v_b_1270_);
v_res_1273_ = lean_int64_lor(v_a_boxed_1271_, v_b_boxed_1272_);
v_r_1274_ = lean_box_uint64(v_res_1273_);
return v_r_1274_;
}
}
LEAN_EXPORT lean_object* l_Int64_xor___boxed(lean_object* v_a_1277_, lean_object* v_b_1278_){
_start:
{
uint64_t v_a_boxed_1279_; uint64_t v_b_boxed_1280_; uint64_t v_res_1281_; lean_object* v_r_1282_; 
v_a_boxed_1279_ = lean_unbox_uint64(v_a_1277_);
lean_dec_ref(v_a_1277_);
v_b_boxed_1280_ = lean_unbox_uint64(v_b_1278_);
lean_dec_ref(v_b_1278_);
v_res_1281_ = lean_int64_xor(v_a_boxed_1279_, v_b_boxed_1280_);
v_r_1282_ = lean_box_uint64(v_res_1281_);
return v_r_1282_;
}
}
LEAN_EXPORT lean_object* l_Int64_shiftLeft___boxed(lean_object* v_a_1285_, lean_object* v_b_1286_){
_start:
{
uint64_t v_a_boxed_1287_; uint64_t v_b_boxed_1288_; uint64_t v_res_1289_; lean_object* v_r_1290_; 
v_a_boxed_1287_ = lean_unbox_uint64(v_a_1285_);
lean_dec_ref(v_a_1285_);
v_b_boxed_1288_ = lean_unbox_uint64(v_b_1286_);
lean_dec_ref(v_b_1286_);
v_res_1289_ = lean_int64_shift_left(v_a_boxed_1287_, v_b_boxed_1288_);
v_r_1290_ = lean_box_uint64(v_res_1289_);
return v_r_1290_;
}
}
LEAN_EXPORT lean_object* l_Int64_shiftRight___boxed(lean_object* v_a_1293_, lean_object* v_b_1294_){
_start:
{
uint64_t v_a_boxed_1295_; uint64_t v_b_boxed_1296_; uint64_t v_res_1297_; lean_object* v_r_1298_; 
v_a_boxed_1295_ = lean_unbox_uint64(v_a_1293_);
lean_dec_ref(v_a_1293_);
v_b_boxed_1296_ = lean_unbox_uint64(v_b_1294_);
lean_dec_ref(v_b_1294_);
v_res_1297_ = lean_int64_shift_right(v_a_boxed_1295_, v_b_boxed_1296_);
v_r_1298_ = lean_box_uint64(v_res_1297_);
return v_r_1298_;
}
}
LEAN_EXPORT lean_object* l_Int64_complement___boxed(lean_object* v_a_1300_){
_start:
{
uint64_t v_a_boxed_1301_; uint64_t v_res_1302_; lean_object* v_r_1303_; 
v_a_boxed_1301_ = lean_unbox_uint64(v_a_1300_);
lean_dec_ref(v_a_1300_);
v_res_1302_ = lean_int64_complement(v_a_boxed_1301_);
v_r_1303_ = lean_box_uint64(v_res_1302_);
return v_r_1303_;
}
}
LEAN_EXPORT lean_object* l_Int64_abs___boxed(lean_object* v_a_1305_){
_start:
{
uint64_t v_a_boxed_1306_; uint64_t v_res_1307_; lean_object* v_r_1308_; 
v_a_boxed_1306_ = lean_unbox_uint64(v_a_1305_);
lean_dec_ref(v_a_1305_);
v_res_1307_ = lean_int64_abs(v_a_boxed_1306_);
v_r_1308_ = lean_box_uint64(v_res_1307_);
return v_r_1308_;
}
}
LEAN_EXPORT lean_object* l_Int64_decEq___boxed(lean_object* v_a_1311_, lean_object* v_b_1312_){
_start:
{
uint64_t v_a_boxed_1313_; uint64_t v_b_boxed_1314_; uint8_t v_res_1315_; lean_object* v_r_1316_; 
v_a_boxed_1313_ = lean_unbox_uint64(v_a_1311_);
lean_dec_ref(v_a_1311_);
v_b_boxed_1314_ = lean_unbox_uint64(v_b_1312_);
lean_dec_ref(v_b_1312_);
v_res_1315_ = lean_int64_dec_eq(v_a_boxed_1313_, v_b_boxed_1314_);
v_r_1316_ = lean_box(v_res_1315_);
return v_r_1316_;
}
}
static uint64_t _init_l_instInhabitedInt64___closed__0(void){
_start:
{
lean_object* v___x_1317_; uint64_t v___x_1318_; 
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_int64_of_nat(v___x_1317_);
return v___x_1318_;
}
}
static uint64_t _init_l_instInhabitedInt64(void){
_start:
{
uint64_t v___x_1319_; 
v___x_1319_ = lean_uint64_once(&l_instInhabitedInt64___closed__0, &l_instInhabitedInt64___closed__0_once, _init_l_instInhabitedInt64___closed__0);
return v___x_1319_;
}
}
static lean_object* _init_l_instLTInt64(void){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_box(0);
return v___x_1332_;
}
}
static lean_object* _init_l_instLEInt64(void){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_box(0);
return v___x_1333_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt64(uint64_t v_a_1346_, uint64_t v_b_1347_){
_start:
{
uint8_t v___x_1348_; 
v___x_1348_ = lean_int64_dec_eq(v_a_1346_, v_b_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt64___boxed(lean_object* v_a_1349_, lean_object* v_b_1350_){
_start:
{
uint64_t v_a_boxed_1351_; uint64_t v_b_boxed_1352_; uint8_t v_res_1353_; lean_object* v_r_1354_; 
v_a_boxed_1351_ = lean_unbox_uint64(v_a_1349_);
lean_dec_ref(v_a_1349_);
v_b_boxed_1352_ = lean_unbox_uint64(v_b_1350_);
lean_dec_ref(v_b_1350_);
v_res_1353_ = l_instDecidableEqInt64(v_a_boxed_1351_, v_b_boxed_1352_);
v_r_1354_ = lean_box(v_res_1353_);
return v_r_1354_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt64___boxed(lean_object* v_b_1356_){
_start:
{
uint8_t v_b_boxed_1357_; uint64_t v_res_1358_; lean_object* v_r_1359_; 
v_b_boxed_1357_ = lean_unbox(v_b_1356_);
v_res_1358_ = lean_bool_to_int64(v_b_boxed_1357_);
v_r_1359_ = lean_box_uint64(v_res_1358_);
return v_r_1359_;
}
}
LEAN_EXPORT uint8_t l_Int64_decLt___aux__1(uint64_t v_a_1360_, uint64_t v_b_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1362_ = lean_unsigned_to_nat(64u);
v___x_1363_ = lean_uint64_to_nat(v_a_1360_);
v___x_1364_ = lean_uint64_to_nat(v_b_1361_);
v___x_1365_ = l_BitVec_slt(v___x_1362_, v___x_1363_, v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLt___aux__1___boxed(lean_object* v_a_1366_, lean_object* v_b_1367_){
_start:
{
uint64_t v_a_boxed_1368_; uint64_t v_b_boxed_1369_; uint8_t v_res_1370_; lean_object* v_r_1371_; 
v_a_boxed_1368_ = lean_unbox_uint64(v_a_1366_);
lean_dec_ref(v_a_1366_);
v_b_boxed_1369_ = lean_unbox_uint64(v_b_1367_);
lean_dec_ref(v_b_1367_);
v_res_1370_ = l_Int64_decLt___aux__1(v_a_boxed_1368_, v_b_boxed_1369_);
v_r_1371_ = lean_box(v_res_1370_);
return v_r_1371_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLt___boxed(lean_object* v_a_1374_, lean_object* v_b_1375_){
_start:
{
uint64_t v_a_boxed_1376_; uint64_t v_b_boxed_1377_; uint8_t v_res_1378_; lean_object* v_r_1379_; 
v_a_boxed_1376_ = lean_unbox_uint64(v_a_1374_);
lean_dec_ref(v_a_1374_);
v_b_boxed_1377_ = lean_unbox_uint64(v_b_1375_);
lean_dec_ref(v_b_1375_);
v_res_1378_ = lean_int64_dec_lt(v_a_boxed_1376_, v_b_boxed_1377_);
v_r_1379_ = lean_box(v_res_1378_);
return v_r_1379_;
}
}
LEAN_EXPORT uint8_t l_Int64_decLe___aux__1(uint64_t v_a_1380_, uint64_t v_b_1381_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1382_ = lean_unsigned_to_nat(64u);
v___x_1383_ = lean_uint64_to_nat(v_a_1380_);
v___x_1384_ = lean_uint64_to_nat(v_b_1381_);
v___x_1385_ = l_BitVec_sle(v___x_1382_, v___x_1383_, v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLe___aux__1___boxed(lean_object* v_a_1386_, lean_object* v_b_1387_){
_start:
{
uint64_t v_a_boxed_1388_; uint64_t v_b_boxed_1389_; uint8_t v_res_1390_; lean_object* v_r_1391_; 
v_a_boxed_1388_ = lean_unbox_uint64(v_a_1386_);
lean_dec_ref(v_a_1386_);
v_b_boxed_1389_ = lean_unbox_uint64(v_b_1387_);
lean_dec_ref(v_b_1387_);
v_res_1390_ = l_Int64_decLe___aux__1(v_a_boxed_1388_, v_b_boxed_1389_);
v_r_1391_ = lean_box(v_res_1390_);
return v_r_1391_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLe___boxed(lean_object* v_a_1394_, lean_object* v_b_1395_){
_start:
{
uint64_t v_a_boxed_1396_; uint64_t v_b_boxed_1397_; uint8_t v_res_1398_; lean_object* v_r_1399_; 
v_a_boxed_1396_ = lean_unbox_uint64(v_a_1394_);
lean_dec_ref(v_a_1394_);
v_b_boxed_1397_ = lean_unbox_uint64(v_b_1395_);
lean_dec_ref(v_b_1395_);
v_res_1398_ = lean_int64_dec_le(v_a_boxed_1396_, v_b_boxed_1397_);
v_r_1399_ = lean_box(v_res_1398_);
return v_r_1399_;
}
}
LEAN_EXPORT uint64_t l_instMaxInt64___lam__0(uint64_t v_x_1400_, uint64_t v_y_1401_){
_start:
{
uint8_t v___x_1402_; 
v___x_1402_ = lean_int64_dec_le(v_x_1400_, v_y_1401_);
if (v___x_1402_ == 0)
{
return v_x_1400_;
}
else
{
return v_y_1401_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt64___lam__0___boxed(lean_object* v_x_1403_, lean_object* v_y_1404_){
_start:
{
uint64_t v_x_boxed_1405_; uint64_t v_y_boxed_1406_; uint64_t v_res_1407_; lean_object* v_r_1408_; 
v_x_boxed_1405_ = lean_unbox_uint64(v_x_1403_);
lean_dec_ref(v_x_1403_);
v_y_boxed_1406_ = lean_unbox_uint64(v_y_1404_);
lean_dec_ref(v_y_1404_);
v_res_1407_ = l_instMaxInt64___lam__0(v_x_boxed_1405_, v_y_boxed_1406_);
v_r_1408_ = lean_box_uint64(v_res_1407_);
return v_r_1408_;
}
}
LEAN_EXPORT uint64_t l_instMinInt64___lam__0(uint64_t v_x_1411_, uint64_t v_y_1412_){
_start:
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_int64_dec_le(v_x_1411_, v_y_1412_);
if (v___x_1413_ == 0)
{
return v_y_1412_;
}
else
{
return v_x_1411_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt64___lam__0___boxed(lean_object* v_x_1414_, lean_object* v_y_1415_){
_start:
{
uint64_t v_x_boxed_1416_; uint64_t v_y_boxed_1417_; uint64_t v_res_1418_; lean_object* v_r_1419_; 
v_x_boxed_1416_ = lean_unbox_uint64(v_x_1414_);
lean_dec_ref(v_x_1414_);
v_y_boxed_1417_ = lean_unbox_uint64(v_y_1415_);
lean_dec_ref(v_y_1415_);
v_res_1418_ = l_instMinInt64___lam__0(v_x_boxed_1416_, v_y_boxed_1417_);
v_r_1419_ = lean_box_uint64(v_res_1418_);
return v_r_1419_;
}
}
static lean_object* _init_l_ISize_size___closed__0(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = l_System_Platform_numBits;
v___x_1423_ = lean_unsigned_to_nat(2u);
v___x_1424_ = lean_nat_pow(v___x_1423_, v___x_1422_);
return v___x_1424_;
}
}
static lean_object* _init_l_ISize_size(void){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_obj_once(&l_ISize_size___closed__0, &l_ISize_size___closed__0_once, _init_l_ISize_size___closed__0);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_ISize_toBitVec(size_t v_x_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_usize_to_nat(v_x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_ISize_toBitVec___boxed(lean_object* v_x_1428_){
_start:
{
size_t v_x_boxed_1429_; lean_object* v_res_1430_; 
v_x_boxed_1429_ = lean_unbox_usize(v_x_1428_);
lean_dec(v_x_1428_);
v_res_1430_ = l_ISize_toBitVec(v_x_boxed_1429_);
return v_res_1430_;
}
}
LEAN_EXPORT size_t l_USize_toISize(size_t v_i_1431_){
_start:
{
return v_i_1431_;
}
}
LEAN_EXPORT lean_object* l_USize_toISize___boxed(lean_object* v_i_1432_){
_start:
{
size_t v_i_boxed_1433_; size_t v_res_1434_; lean_object* v_r_1435_; 
v_i_boxed_1433_ = lean_unbox_usize(v_i_1432_);
lean_dec(v_i_1432_);
v_res_1434_ = l_USize_toISize(v_i_boxed_1433_);
v_r_1435_ = lean_box_usize(v_res_1434_);
return v_r_1435_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofInt___boxed(lean_object* v_i_1437_){
_start:
{
size_t v_res_1438_; lean_object* v_r_1439_; 
v_res_1438_ = lean_isize_of_int(v_i_1437_);
lean_dec(v_i_1437_);
v_r_1439_ = lean_box_usize(v_res_1438_);
return v_r_1439_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofNat___boxed(lean_object* v_n_1441_){
_start:
{
size_t v_res_1442_; lean_object* v_r_1443_; 
v_res_1442_ = lean_isize_of_nat(v_n_1441_);
lean_dec(v_n_1441_);
v_r_1443_ = lean_box_usize(v_res_1442_);
return v_r_1443_;
}
}
LEAN_EXPORT size_t l_Int_toISize(lean_object* v_i_1444_){
_start:
{
size_t v___x_1445_; 
v___x_1445_ = lean_isize_of_int(v_i_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Int_toISize___boxed(lean_object* v_i_1446_){
_start:
{
size_t v_res_1447_; lean_object* v_r_1448_; 
v_res_1447_ = l_Int_toISize(v_i_1446_);
lean_dec(v_i_1446_);
v_r_1448_ = lean_box_usize(v_res_1447_);
return v_r_1448_;
}
}
LEAN_EXPORT size_t l_Nat_toISize(lean_object* v_n_1449_){
_start:
{
size_t v___x_1450_; 
v___x_1450_ = lean_isize_of_nat(v_n_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Nat_toISize___boxed(lean_object* v_n_1451_){
_start:
{
size_t v_res_1452_; lean_object* v_r_1453_; 
v_res_1452_ = l_Nat_toISize(v_n_1451_);
lean_dec(v_n_1451_);
v_r_1453_ = lean_box_usize(v_res_1452_);
return v_r_1453_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt___boxed(lean_object* v_i_1455_){
_start:
{
size_t v_i_boxed_1456_; lean_object* v_res_1457_; 
v_i_boxed_1456_ = lean_unbox_usize(v_i_1455_);
lean_dec(v_i_1455_);
v_res_1457_ = lean_isize_to_int(v_i_boxed_1456_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg(size_t v_i_1458_){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_isize_to_int(v_i_1458_);
v___x_1460_ = l_Int_toNat(v___x_1459_);
lean_dec(v___x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg___boxed(lean_object* v_i_1461_){
_start:
{
size_t v_i_boxed_1462_; lean_object* v_res_1463_; 
v_i_boxed_1462_ = lean_unbox_usize(v_i_1461_);
lean_dec(v_i_1461_);
v_res_1463_ = l_ISize_toNatClampNeg(v_i_boxed_1462_);
return v_res_1463_;
}
}
LEAN_EXPORT size_t l_ISize_ofBitVec(lean_object* v_b_1464_){
_start:
{
size_t v___x_1465_; 
v___x_1465_ = lean_usize_of_nat_mk(v_b_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofBitVec___boxed(lean_object* v_b_1466_){
_start:
{
size_t v_res_1467_; lean_object* v_r_1468_; 
v_res_1467_ = l_ISize_ofBitVec(v_b_1466_);
v_r_1468_ = lean_box_usize(v_res_1467_);
return v_r_1468_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt8___boxed(lean_object* v_a_1470_){
_start:
{
size_t v_a_boxed_1471_; uint8_t v_res_1472_; lean_object* v_r_1473_; 
v_a_boxed_1471_ = lean_unbox_usize(v_a_1470_);
lean_dec(v_a_1470_);
v_res_1472_ = lean_isize_to_int8(v_a_boxed_1471_);
v_r_1473_ = lean_box(v_res_1472_);
return v_r_1473_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt16___boxed(lean_object* v_a_1475_){
_start:
{
size_t v_a_boxed_1476_; uint16_t v_res_1477_; lean_object* v_r_1478_; 
v_a_boxed_1476_ = lean_unbox_usize(v_a_1475_);
lean_dec(v_a_1475_);
v_res_1477_ = lean_isize_to_int16(v_a_boxed_1476_);
v_r_1478_ = lean_box(v_res_1477_);
return v_r_1478_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt32___boxed(lean_object* v_a_1480_){
_start:
{
size_t v_a_boxed_1481_; uint32_t v_res_1482_; lean_object* v_r_1483_; 
v_a_boxed_1481_ = lean_unbox_usize(v_a_1480_);
lean_dec(v_a_1480_);
v_res_1482_ = lean_isize_to_int32(v_a_boxed_1481_);
v_r_1483_ = lean_box_uint32(v_res_1482_);
return v_r_1483_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt64___boxed(lean_object* v_a_1485_){
_start:
{
size_t v_a_boxed_1486_; uint64_t v_res_1487_; lean_object* v_r_1488_; 
v_a_boxed_1486_ = lean_unbox_usize(v_a_1485_);
lean_dec(v_a_1485_);
v_res_1487_ = lean_isize_to_int64(v_a_boxed_1486_);
v_r_1488_ = lean_box_uint64(v_res_1487_);
return v_r_1488_;
}
}
LEAN_EXPORT lean_object* l_Int8_toISize___boxed(lean_object* v_a_1490_){
_start:
{
uint8_t v_a_boxed_1491_; size_t v_res_1492_; lean_object* v_r_1493_; 
v_a_boxed_1491_ = lean_unbox(v_a_1490_);
v_res_1492_ = lean_int8_to_isize(v_a_boxed_1491_);
v_r_1493_ = lean_box_usize(v_res_1492_);
return v_r_1493_;
}
}
LEAN_EXPORT lean_object* l_Int16_toISize___boxed(lean_object* v_a_1495_){
_start:
{
uint16_t v_a_boxed_1496_; size_t v_res_1497_; lean_object* v_r_1498_; 
v_a_boxed_1496_ = lean_unbox(v_a_1495_);
v_res_1497_ = lean_int16_to_isize(v_a_boxed_1496_);
v_r_1498_ = lean_box_usize(v_res_1497_);
return v_r_1498_;
}
}
LEAN_EXPORT lean_object* l_Int32_toISize___boxed(lean_object* v_a_1500_){
_start:
{
uint32_t v_a_boxed_1501_; size_t v_res_1502_; lean_object* v_r_1503_; 
v_a_boxed_1501_ = lean_unbox_uint32(v_a_1500_);
lean_dec(v_a_1500_);
v_res_1502_ = lean_int32_to_isize(v_a_boxed_1501_);
v_r_1503_ = lean_box_usize(v_res_1502_);
return v_r_1503_;
}
}
LEAN_EXPORT lean_object* l_Int64_toISize___boxed(lean_object* v_a_1505_){
_start:
{
uint64_t v_a_boxed_1506_; size_t v_res_1507_; lean_object* v_r_1508_; 
v_a_boxed_1506_ = lean_unbox_uint64(v_a_1505_);
lean_dec_ref(v_a_1505_);
v_res_1507_ = lean_int64_to_isize(v_a_boxed_1506_);
v_r_1508_ = lean_box_usize(v_res_1507_);
return v_r_1508_;
}
}
LEAN_EXPORT lean_object* l_ISize_neg___boxed(lean_object* v_i_1510_){
_start:
{
size_t v_i_boxed_1511_; size_t v_res_1512_; lean_object* v_r_1513_; 
v_i_boxed_1511_ = lean_unbox_usize(v_i_1510_);
lean_dec(v_i_1510_);
v_res_1512_ = lean_isize_neg(v_i_boxed_1511_);
v_r_1513_ = lean_box_usize(v_res_1512_);
return v_r_1513_;
}
}
LEAN_EXPORT lean_object* l_instToStringISize___lam__0(size_t v_i_1514_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_isize_to_int(v_i_1514_);
v___x_1516_ = l_Int_repr(v___x_1515_);
lean_dec(v___x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_instToStringISize___lam__0___boxed(lean_object* v_i_1517_){
_start:
{
size_t v_i_boxed_1518_; lean_object* v_res_1519_; 
v_i_boxed_1518_ = lean_unbox_usize(v_i_1517_);
lean_dec(v_i_1517_);
v_res_1519_ = l_instToStringISize___lam__0(v_i_boxed_1518_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_instReprISize___lam__0(size_t v_i_1522_, lean_object* v_prec_1523_){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1524_ = lean_isize_to_int(v_i_1522_);
v___x_1525_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_1526_ = lean_int_dec_lt(v___x_1524_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = l_Int_repr(v___x_1524_);
lean_dec(v___x_1524_);
v___x_1528_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
return v___x_1528_;
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1529_ = l_Int_repr(v___x_1524_);
lean_dec(v___x_1524_);
v___x_1530_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
v___x_1531_ = l_Repr_addAppParen(v___x_1530_, v_prec_1523_);
return v___x_1531_;
}
}
}
LEAN_EXPORT lean_object* l_instReprISize___lam__0___boxed(lean_object* v_i_1532_, lean_object* v_prec_1533_){
_start:
{
size_t v_i_boxed_1534_; lean_object* v_res_1535_; 
v_i_boxed_1534_ = lean_unbox_usize(v_i_1532_);
lean_dec(v_i_1532_);
v_res_1535_ = l_instReprISize___lam__0(v_i_boxed_1534_, v_prec_1533_);
lean_dec(v_prec_1533_);
return v_res_1535_;
}
}
static lean_object* _init_l_instReprAtomISize(void){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = lean_box(0);
return v___x_1538_;
}
}
LEAN_EXPORT size_t l_ISize_instOfNat(lean_object* v_n_1541_){
_start:
{
size_t v___x_1542_; 
v___x_1542_ = lean_isize_of_nat(v_n_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_ISize_instOfNat___boxed(lean_object* v_n_1543_){
_start:
{
size_t v_res_1544_; lean_object* v_r_1545_; 
v_res_1544_ = l_ISize_instOfNat(v_n_1543_);
lean_dec(v_n_1543_);
v_r_1545_ = lean_box_usize(v_res_1544_);
return v_r_1545_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__0(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_unsigned_to_nat(2u);
v___x_1549_ = lean_nat_to_int(v___x_1548_);
return v___x_1549_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__1(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = lean_unsigned_to_nat(1u);
v___x_1551_ = l_System_Platform_numBits;
v___x_1552_ = lean_nat_sub(v___x_1551_, v___x_1550_);
return v___x_1552_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__2(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = lean_obj_once(&l_ISize_maxValue___closed__1, &l_ISize_maxValue___closed__1_once, _init_l_ISize_maxValue___closed__1);
v___x_1554_ = lean_obj_once(&l_ISize_maxValue___closed__0, &l_ISize_maxValue___closed__0_once, _init_l_ISize_maxValue___closed__0);
v___x_1555_ = l_Int_pow(v___x_1554_, v___x_1553_);
return v___x_1555_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__3(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_nat_to_int(v___x_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__4(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = lean_obj_once(&l_ISize_maxValue___closed__3, &l_ISize_maxValue___closed__3_once, _init_l_ISize_maxValue___closed__3);
v___x_1559_ = lean_obj_once(&l_ISize_maxValue___closed__2, &l_ISize_maxValue___closed__2_once, _init_l_ISize_maxValue___closed__2);
v___x_1560_ = lean_int_sub(v___x_1559_, v___x_1558_);
return v___x_1560_;
}
}
static size_t _init_l_ISize_maxValue___closed__5(void){
_start:
{
lean_object* v___x_1561_; size_t v___x_1562_; 
v___x_1561_ = lean_obj_once(&l_ISize_maxValue___closed__4, &l_ISize_maxValue___closed__4_once, _init_l_ISize_maxValue___closed__4);
v___x_1562_ = lean_isize_of_int(v___x_1561_);
return v___x_1562_;
}
}
static size_t _init_l_ISize_maxValue(void){
_start:
{
size_t v___x_1563_; 
v___x_1563_ = lean_usize_once(&l_ISize_maxValue___closed__5, &l_ISize_maxValue___closed__5_once, _init_l_ISize_maxValue___closed__5);
return v___x_1563_;
}
}
static lean_object* _init_l_ISize_minValue___closed__0(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_obj_once(&l_ISize_maxValue___closed__2, &l_ISize_maxValue___closed__2_once, _init_l_ISize_maxValue___closed__2);
v___x_1565_ = lean_int_neg(v___x_1564_);
return v___x_1565_;
}
}
static size_t _init_l_ISize_minValue___closed__1(void){
_start:
{
lean_object* v___x_1566_; size_t v___x_1567_; 
v___x_1566_ = lean_obj_once(&l_ISize_minValue___closed__0, &l_ISize_minValue___closed__0_once, _init_l_ISize_minValue___closed__0);
v___x_1567_ = lean_isize_of_int(v___x_1566_);
return v___x_1567_;
}
}
static size_t _init_l_ISize_minValue(void){
_start:
{
size_t v___x_1568_; 
v___x_1568_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
return v___x_1568_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntLE___redArg(lean_object* v_i_1569_){
_start:
{
size_t v___x_1570_; 
v___x_1570_ = lean_isize_of_int(v_i_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntLE___redArg___boxed(lean_object* v_i_1571_){
_start:
{
size_t v_res_1572_; lean_object* v_r_1573_; 
v_res_1572_ = l_ISize_ofIntLE___redArg(v_i_1571_);
lean_dec(v_i_1571_);
v_r_1573_ = lean_box_usize(v_res_1572_);
return v_r_1573_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntLE(lean_object* v_i_1574_, lean_object* v___hl_1575_, lean_object* v___hr_1576_){
_start:
{
size_t v___x_1577_; 
v___x_1577_ = lean_isize_of_int(v_i_1574_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntLE___boxed(lean_object* v_i_1578_, lean_object* v___hl_1579_, lean_object* v___hr_1580_){
_start:
{
size_t v_res_1581_; lean_object* v_r_1582_; 
v_res_1581_ = l_ISize_ofIntLE(v_i_1578_, v___hl_1579_, v___hr_1580_);
lean_dec(v_i_1578_);
v_r_1582_ = lean_box_usize(v_res_1581_);
return v_r_1582_;
}
}
static lean_object* _init_l_ISize_ofIntTruncate___closed__0(void){
_start:
{
size_t v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
v___x_1584_ = lean_isize_to_int(v___x_1583_);
return v___x_1584_;
}
}
static lean_object* _init_l_ISize_ofIntTruncate___closed__1(void){
_start:
{
size_t v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_usize_once(&l_ISize_maxValue___closed__5, &l_ISize_maxValue___closed__5_once, _init_l_ISize_maxValue___closed__5);
v___x_1586_ = lean_isize_to_int(v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntTruncate(lean_object* v_i_1587_){
_start:
{
size_t v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1588_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
v___x_1589_ = lean_obj_once(&l_ISize_ofIntTruncate___closed__0, &l_ISize_ofIntTruncate___closed__0_once, _init_l_ISize_ofIntTruncate___closed__0);
v___x_1590_ = lean_int_dec_le(v___x_1589_, v_i_1587_);
if (v___x_1590_ == 0)
{
return v___x_1588_;
}
else
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = lean_obj_once(&l_ISize_ofIntTruncate___closed__1, &l_ISize_ofIntTruncate___closed__1_once, _init_l_ISize_ofIntTruncate___closed__1);
v___x_1592_ = lean_int_dec_le(v_i_1587_, v___x_1591_);
if (v___x_1592_ == 0)
{
return v___x_1588_;
}
else
{
size_t v___x_1593_; 
v___x_1593_ = lean_isize_of_int(v_i_1587_);
return v___x_1593_;
}
}
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntTruncate___boxed(lean_object* v_i_1594_){
_start:
{
size_t v_res_1595_; lean_object* v_r_1596_; 
v_res_1595_ = l_ISize_ofIntTruncate(v_i_1594_);
lean_dec(v_i_1594_);
v_r_1596_ = lean_box_usize(v_res_1595_);
return v_r_1596_;
}
}
LEAN_EXPORT lean_object* l_ISize_add___boxed(lean_object* v_a_1599_, lean_object* v_b_1600_){
_start:
{
size_t v_a_boxed_1601_; size_t v_b_boxed_1602_; size_t v_res_1603_; lean_object* v_r_1604_; 
v_a_boxed_1601_ = lean_unbox_usize(v_a_1599_);
lean_dec(v_a_1599_);
v_b_boxed_1602_ = lean_unbox_usize(v_b_1600_);
lean_dec(v_b_1600_);
v_res_1603_ = lean_isize_add(v_a_boxed_1601_, v_b_boxed_1602_);
v_r_1604_ = lean_box_usize(v_res_1603_);
return v_r_1604_;
}
}
LEAN_EXPORT lean_object* l_ISize_sub___boxed(lean_object* v_a_1607_, lean_object* v_b_1608_){
_start:
{
size_t v_a_boxed_1609_; size_t v_b_boxed_1610_; size_t v_res_1611_; lean_object* v_r_1612_; 
v_a_boxed_1609_ = lean_unbox_usize(v_a_1607_);
lean_dec(v_a_1607_);
v_b_boxed_1610_ = lean_unbox_usize(v_b_1608_);
lean_dec(v_b_1608_);
v_res_1611_ = lean_isize_sub(v_a_boxed_1609_, v_b_boxed_1610_);
v_r_1612_ = lean_box_usize(v_res_1611_);
return v_r_1612_;
}
}
LEAN_EXPORT lean_object* l_ISize_mul___boxed(lean_object* v_a_1615_, lean_object* v_b_1616_){
_start:
{
size_t v_a_boxed_1617_; size_t v_b_boxed_1618_; size_t v_res_1619_; lean_object* v_r_1620_; 
v_a_boxed_1617_ = lean_unbox_usize(v_a_1615_);
lean_dec(v_a_1615_);
v_b_boxed_1618_ = lean_unbox_usize(v_b_1616_);
lean_dec(v_b_1616_);
v_res_1619_ = lean_isize_mul(v_a_boxed_1617_, v_b_boxed_1618_);
v_r_1620_ = lean_box_usize(v_res_1619_);
return v_r_1620_;
}
}
LEAN_EXPORT lean_object* l_ISize_div___boxed(lean_object* v_a_1623_, lean_object* v_b_1624_){
_start:
{
size_t v_a_boxed_1625_; size_t v_b_boxed_1626_; size_t v_res_1627_; lean_object* v_r_1628_; 
v_a_boxed_1625_ = lean_unbox_usize(v_a_1623_);
lean_dec(v_a_1623_);
v_b_boxed_1626_ = lean_unbox_usize(v_b_1624_);
lean_dec(v_b_1624_);
v_res_1627_ = lean_isize_div(v_a_boxed_1625_, v_b_boxed_1626_);
v_r_1628_ = lean_box_usize(v_res_1627_);
return v_r_1628_;
}
}
static size_t _init_l_ISize_pow___closed__0(void){
_start:
{
lean_object* v___x_1629_; size_t v___x_1630_; 
v___x_1629_ = lean_unsigned_to_nat(1u);
v___x_1630_ = lean_isize_of_nat(v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT size_t l_ISize_pow(size_t v_x_1631_, lean_object* v_n_1632_){
_start:
{
lean_object* v_zero_1633_; uint8_t v_isZero_1634_; 
v_zero_1633_ = lean_unsigned_to_nat(0u);
v_isZero_1634_ = lean_nat_dec_eq(v_n_1632_, v_zero_1633_);
if (v_isZero_1634_ == 1)
{
size_t v___x_1635_; 
v___x_1635_ = lean_usize_once(&l_ISize_pow___closed__0, &l_ISize_pow___closed__0_once, _init_l_ISize_pow___closed__0);
return v___x_1635_;
}
else
{
lean_object* v_one_1636_; lean_object* v_n_1637_; size_t v___x_1638_; size_t v___x_1639_; 
v_one_1636_ = lean_unsigned_to_nat(1u);
v_n_1637_ = lean_nat_sub(v_n_1632_, v_one_1636_);
v___x_1638_ = l_ISize_pow(v_x_1631_, v_n_1637_);
lean_dec(v_n_1637_);
v___x_1639_ = lean_isize_mul(v___x_1638_, v_x_1631_);
return v___x_1639_;
}
}
}
LEAN_EXPORT lean_object* l_ISize_pow___boxed(lean_object* v_x_1640_, lean_object* v_n_1641_){
_start:
{
size_t v_x_boxed_1642_; size_t v_res_1643_; lean_object* v_r_1644_; 
v_x_boxed_1642_ = lean_unbox_usize(v_x_1640_);
lean_dec(v_x_1640_);
v_res_1643_ = l_ISize_pow(v_x_boxed_1642_, v_n_1641_);
lean_dec(v_n_1641_);
v_r_1644_ = lean_box_usize(v_res_1643_);
return v_r_1644_;
}
}
LEAN_EXPORT lean_object* l_ISize_mod___boxed(lean_object* v_a_1647_, lean_object* v_b_1648_){
_start:
{
size_t v_a_boxed_1649_; size_t v_b_boxed_1650_; size_t v_res_1651_; lean_object* v_r_1652_; 
v_a_boxed_1649_ = lean_unbox_usize(v_a_1647_);
lean_dec(v_a_1647_);
v_b_boxed_1650_ = lean_unbox_usize(v_b_1648_);
lean_dec(v_b_1648_);
v_res_1651_ = lean_isize_mod(v_a_boxed_1649_, v_b_boxed_1650_);
v_r_1652_ = lean_box_usize(v_res_1651_);
return v_r_1652_;
}
}
LEAN_EXPORT lean_object* l_ISize_land___boxed(lean_object* v_a_1655_, lean_object* v_b_1656_){
_start:
{
size_t v_a_boxed_1657_; size_t v_b_boxed_1658_; size_t v_res_1659_; lean_object* v_r_1660_; 
v_a_boxed_1657_ = lean_unbox_usize(v_a_1655_);
lean_dec(v_a_1655_);
v_b_boxed_1658_ = lean_unbox_usize(v_b_1656_);
lean_dec(v_b_1656_);
v_res_1659_ = lean_isize_land(v_a_boxed_1657_, v_b_boxed_1658_);
v_r_1660_ = lean_box_usize(v_res_1659_);
return v_r_1660_;
}
}
LEAN_EXPORT lean_object* l_ISize_lor___boxed(lean_object* v_a_1663_, lean_object* v_b_1664_){
_start:
{
size_t v_a_boxed_1665_; size_t v_b_boxed_1666_; size_t v_res_1667_; lean_object* v_r_1668_; 
v_a_boxed_1665_ = lean_unbox_usize(v_a_1663_);
lean_dec(v_a_1663_);
v_b_boxed_1666_ = lean_unbox_usize(v_b_1664_);
lean_dec(v_b_1664_);
v_res_1667_ = lean_isize_lor(v_a_boxed_1665_, v_b_boxed_1666_);
v_r_1668_ = lean_box_usize(v_res_1667_);
return v_r_1668_;
}
}
LEAN_EXPORT lean_object* l_ISize_xor___boxed(lean_object* v_a_1671_, lean_object* v_b_1672_){
_start:
{
size_t v_a_boxed_1673_; size_t v_b_boxed_1674_; size_t v_res_1675_; lean_object* v_r_1676_; 
v_a_boxed_1673_ = lean_unbox_usize(v_a_1671_);
lean_dec(v_a_1671_);
v_b_boxed_1674_ = lean_unbox_usize(v_b_1672_);
lean_dec(v_b_1672_);
v_res_1675_ = lean_isize_xor(v_a_boxed_1673_, v_b_boxed_1674_);
v_r_1676_ = lean_box_usize(v_res_1675_);
return v_r_1676_;
}
}
LEAN_EXPORT lean_object* l_ISize_shiftLeft___boxed(lean_object* v_a_1679_, lean_object* v_b_1680_){
_start:
{
size_t v_a_boxed_1681_; size_t v_b_boxed_1682_; size_t v_res_1683_; lean_object* v_r_1684_; 
v_a_boxed_1681_ = lean_unbox_usize(v_a_1679_);
lean_dec(v_a_1679_);
v_b_boxed_1682_ = lean_unbox_usize(v_b_1680_);
lean_dec(v_b_1680_);
v_res_1683_ = lean_isize_shift_left(v_a_boxed_1681_, v_b_boxed_1682_);
v_r_1684_ = lean_box_usize(v_res_1683_);
return v_r_1684_;
}
}
LEAN_EXPORT lean_object* l_ISize_shiftRight___boxed(lean_object* v_a_1687_, lean_object* v_b_1688_){
_start:
{
size_t v_a_boxed_1689_; size_t v_b_boxed_1690_; size_t v_res_1691_; lean_object* v_r_1692_; 
v_a_boxed_1689_ = lean_unbox_usize(v_a_1687_);
lean_dec(v_a_1687_);
v_b_boxed_1690_ = lean_unbox_usize(v_b_1688_);
lean_dec(v_b_1688_);
v_res_1691_ = lean_isize_shift_right(v_a_boxed_1689_, v_b_boxed_1690_);
v_r_1692_ = lean_box_usize(v_res_1691_);
return v_r_1692_;
}
}
LEAN_EXPORT lean_object* l_ISize_complement___boxed(lean_object* v_a_1694_){
_start:
{
size_t v_a_boxed_1695_; size_t v_res_1696_; lean_object* v_r_1697_; 
v_a_boxed_1695_ = lean_unbox_usize(v_a_1694_);
lean_dec(v_a_1694_);
v_res_1696_ = lean_isize_complement(v_a_boxed_1695_);
v_r_1697_ = lean_box_usize(v_res_1696_);
return v_r_1697_;
}
}
LEAN_EXPORT lean_object* l_ISize_abs___boxed(lean_object* v_a_1699_){
_start:
{
size_t v_a_boxed_1700_; size_t v_res_1701_; lean_object* v_r_1702_; 
v_a_boxed_1700_ = lean_unbox_usize(v_a_1699_);
lean_dec(v_a_1699_);
v_res_1701_ = lean_isize_abs(v_a_boxed_1700_);
v_r_1702_ = lean_box_usize(v_res_1701_);
return v_r_1702_;
}
}
LEAN_EXPORT lean_object* l_ISize_decEq___boxed(lean_object* v_a_1705_, lean_object* v_b_1706_){
_start:
{
size_t v_a_boxed_1707_; size_t v_b_boxed_1708_; uint8_t v_res_1709_; lean_object* v_r_1710_; 
v_a_boxed_1707_ = lean_unbox_usize(v_a_1705_);
lean_dec(v_a_1705_);
v_b_boxed_1708_ = lean_unbox_usize(v_b_1706_);
lean_dec(v_b_1706_);
v_res_1709_ = lean_isize_dec_eq(v_a_boxed_1707_, v_b_boxed_1708_);
v_r_1710_ = lean_box(v_res_1709_);
return v_r_1710_;
}
}
static size_t _init_l_instInhabitedISize___closed__0(void){
_start:
{
lean_object* v___x_1711_; size_t v___x_1712_; 
v___x_1711_ = lean_unsigned_to_nat(0u);
v___x_1712_ = lean_isize_of_nat(v___x_1711_);
return v___x_1712_;
}
}
static size_t _init_l_instInhabitedISize(void){
_start:
{
size_t v___x_1713_; 
v___x_1713_ = lean_usize_once(&l_instInhabitedISize___closed__0, &l_instInhabitedISize___closed__0_once, _init_l_instInhabitedISize___closed__0);
return v___x_1713_;
}
}
static lean_object* _init_l_instLTISize(void){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = lean_box(0);
return v___x_1726_;
}
}
static lean_object* _init_l_instLEISize(void){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_box(0);
return v___x_1727_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqISize(size_t v_a_1740_, size_t v_b_1741_){
_start:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_isize_dec_eq(v_a_1740_, v_b_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqISize___boxed(lean_object* v_a_1743_, lean_object* v_b_1744_){
_start:
{
size_t v_a_boxed_1745_; size_t v_b_boxed_1746_; uint8_t v_res_1747_; lean_object* v_r_1748_; 
v_a_boxed_1745_ = lean_unbox_usize(v_a_1743_);
lean_dec(v_a_1743_);
v_b_boxed_1746_ = lean_unbox_usize(v_b_1744_);
lean_dec(v_b_1744_);
v_res_1747_ = l_instDecidableEqISize(v_a_boxed_1745_, v_b_boxed_1746_);
v_r_1748_ = lean_box(v_res_1747_);
return v_r_1748_;
}
}
LEAN_EXPORT lean_object* l_Bool_toISize___boxed(lean_object* v_b_1750_){
_start:
{
uint8_t v_b_boxed_1751_; size_t v_res_1752_; lean_object* v_r_1753_; 
v_b_boxed_1751_ = lean_unbox(v_b_1750_);
v_res_1752_ = lean_bool_to_isize(v_b_boxed_1751_);
v_r_1753_ = lean_box_usize(v_res_1752_);
return v_r_1753_;
}
}
LEAN_EXPORT uint8_t l_ISize_decLt___aux__1(size_t v_a_1754_, size_t v_b_1755_){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1756_ = l_System_Platform_numBits;
v___x_1757_ = lean_usize_to_nat(v_a_1754_);
v___x_1758_ = lean_usize_to_nat(v_b_1755_);
v___x_1759_ = l_BitVec_slt(v___x_1756_, v___x_1757_, v___x_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLt___aux__1___boxed(lean_object* v_a_1760_, lean_object* v_b_1761_){
_start:
{
size_t v_a_boxed_1762_; size_t v_b_boxed_1763_; uint8_t v_res_1764_; lean_object* v_r_1765_; 
v_a_boxed_1762_ = lean_unbox_usize(v_a_1760_);
lean_dec(v_a_1760_);
v_b_boxed_1763_ = lean_unbox_usize(v_b_1761_);
lean_dec(v_b_1761_);
v_res_1764_ = l_ISize_decLt___aux__1(v_a_boxed_1762_, v_b_boxed_1763_);
v_r_1765_ = lean_box(v_res_1764_);
return v_r_1765_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLt___boxed(lean_object* v_a_1768_, lean_object* v_b_1769_){
_start:
{
size_t v_a_boxed_1770_; size_t v_b_boxed_1771_; uint8_t v_res_1772_; lean_object* v_r_1773_; 
v_a_boxed_1770_ = lean_unbox_usize(v_a_1768_);
lean_dec(v_a_1768_);
v_b_boxed_1771_ = lean_unbox_usize(v_b_1769_);
lean_dec(v_b_1769_);
v_res_1772_ = lean_isize_dec_lt(v_a_boxed_1770_, v_b_boxed_1771_);
v_r_1773_ = lean_box(v_res_1772_);
return v_r_1773_;
}
}
LEAN_EXPORT uint8_t l_ISize_decLe___aux__1(size_t v_a_1774_, size_t v_b_1775_){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1776_ = l_System_Platform_numBits;
v___x_1777_ = lean_usize_to_nat(v_a_1774_);
v___x_1778_ = lean_usize_to_nat(v_b_1775_);
v___x_1779_ = l_BitVec_sle(v___x_1776_, v___x_1777_, v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLe___aux__1___boxed(lean_object* v_a_1780_, lean_object* v_b_1781_){
_start:
{
size_t v_a_boxed_1782_; size_t v_b_boxed_1783_; uint8_t v_res_1784_; lean_object* v_r_1785_; 
v_a_boxed_1782_ = lean_unbox_usize(v_a_1780_);
lean_dec(v_a_1780_);
v_b_boxed_1783_ = lean_unbox_usize(v_b_1781_);
lean_dec(v_b_1781_);
v_res_1784_ = l_ISize_decLe___aux__1(v_a_boxed_1782_, v_b_boxed_1783_);
v_r_1785_ = lean_box(v_res_1784_);
return v_r_1785_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLe___boxed(lean_object* v_a_1788_, lean_object* v_b_1789_){
_start:
{
size_t v_a_boxed_1790_; size_t v_b_boxed_1791_; uint8_t v_res_1792_; lean_object* v_r_1793_; 
v_a_boxed_1790_ = lean_unbox_usize(v_a_1788_);
lean_dec(v_a_1788_);
v_b_boxed_1791_ = lean_unbox_usize(v_b_1789_);
lean_dec(v_b_1789_);
v_res_1792_ = lean_isize_dec_le(v_a_boxed_1790_, v_b_boxed_1791_);
v_r_1793_ = lean_box(v_res_1792_);
return v_r_1793_;
}
}
LEAN_EXPORT size_t l_instMaxISize___lam__0(size_t v_x_1794_, size_t v_y_1795_){
_start:
{
uint8_t v___x_1796_; 
v___x_1796_ = lean_isize_dec_le(v_x_1794_, v_y_1795_);
if (v___x_1796_ == 0)
{
return v_x_1794_;
}
else
{
return v_y_1795_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxISize___lam__0___boxed(lean_object* v_x_1797_, lean_object* v_y_1798_){
_start:
{
size_t v_x_boxed_1799_; size_t v_y_boxed_1800_; size_t v_res_1801_; lean_object* v_r_1802_; 
v_x_boxed_1799_ = lean_unbox_usize(v_x_1797_);
lean_dec(v_x_1797_);
v_y_boxed_1800_ = lean_unbox_usize(v_y_1798_);
lean_dec(v_y_1798_);
v_res_1801_ = l_instMaxISize___lam__0(v_x_boxed_1799_, v_y_boxed_1800_);
v_r_1802_ = lean_box_usize(v_res_1801_);
return v_r_1802_;
}
}
LEAN_EXPORT size_t l_instMinISize___lam__0(size_t v_x_1805_, size_t v_y_1806_){
_start:
{
uint8_t v___x_1807_; 
v___x_1807_ = lean_isize_dec_le(v_x_1805_, v_y_1806_);
if (v___x_1807_ == 0)
{
return v_y_1806_;
}
else
{
return v_x_1805_;
}
}
}
LEAN_EXPORT lean_object* l_instMinISize___lam__0___boxed(lean_object* v_x_1808_, lean_object* v_y_1809_){
_start:
{
size_t v_x_boxed_1810_; size_t v_y_boxed_1811_; size_t v_res_1812_; lean_object* v_r_1813_; 
v_x_boxed_1810_ = lean_unbox_usize(v_x_1808_);
lean_dec(v_x_1808_);
v_y_boxed_1811_ = lean_unbox_usize(v_y_1809_);
lean_dec(v_y_1809_);
v_res_1812_ = l_instMinISize___lam__0(v_x_boxed_1810_, v_y_boxed_1811_);
v_r_1813_ = lean_box_usize(v_res_1812_);
return v_r_1813_;
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
