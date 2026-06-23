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
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
uint8_t l_BitVec_slt(lean_object*, lean_object*, lean_object*);
lean_object* l_UInt32_toUInt64___boxed(lean_object*);
size_t lean_usize_of_nat_mk(lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_int_neg(lean_object*);
uint32_t lean_uint32_of_nat_mk(lean_object*);
uint8_t l_BitVec_sle(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Int8_ofIntClamp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int8_ofIntClamp___closed__0;
static lean_once_cell_t l_Int8_ofIntClamp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int8_ofIntClamp___closed__1;
LEAN_EXPORT uint8_t l_Int8_ofIntClamp(lean_object*);
LEAN_EXPORT lean_object* l_Int8_ofIntClamp___boxed(lean_object*);
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
static lean_once_cell_t l_Int16_ofIntClamp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int16_ofIntClamp___closed__0;
static lean_once_cell_t l_Int16_ofIntClamp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int16_ofIntClamp___closed__1;
LEAN_EXPORT uint16_t l_Int16_ofIntClamp(lean_object*);
LEAN_EXPORT lean_object* l_Int16_ofIntClamp___boxed(lean_object*);
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
static lean_once_cell_t l_Int32_ofIntClamp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int32_ofIntClamp___closed__0;
static lean_once_cell_t l_Int32_ofIntClamp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int32_ofIntClamp___closed__1;
LEAN_EXPORT uint32_t l_Int32_ofIntClamp(lean_object*);
LEAN_EXPORT lean_object* l_Int32_ofIntClamp___boxed(lean_object*);
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
static lean_once_cell_t l_Int64_ofIntClamp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int64_ofIntClamp___closed__0;
static lean_once_cell_t l_Int64_ofIntClamp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int64_ofIntClamp___closed__1;
LEAN_EXPORT uint64_t l_Int64_ofIntClamp(lean_object*);
LEAN_EXPORT lean_object* l_Int64_ofIntClamp___boxed(lean_object*);
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
static lean_once_cell_t l_ISize_ofIntClamp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ISize_ofIntClamp___closed__0;
static lean_once_cell_t l_ISize_ofIntClamp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_ISize_ofIntClamp___closed__1;
LEAN_EXPORT size_t l_ISize_ofIntClamp(lean_object*);
LEAN_EXPORT lean_object* l_ISize_ofIntClamp___boxed(lean_object*);
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
static lean_object* _init_l_Int8_ofIntClamp___closed__0(void){
_start:
{
uint8_t v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_uint8_once(&l_Int8_minValue___closed__1, &l_Int8_minValue___closed__1_once, _init_l_Int8_minValue___closed__1);
v___x_109_ = lean_int8_to_int(v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l_Int8_ofIntClamp___closed__1(void){
_start:
{
uint8_t v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_uint8_once(&l_Int8_maxValue___closed__0, &l_Int8_maxValue___closed__0_once, _init_l_Int8_maxValue___closed__0);
v___x_111_ = lean_int8_to_int(v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT uint8_t l_Int8_ofIntClamp(lean_object* v_i_112_){
_start:
{
uint8_t v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_113_ = lean_uint8_once(&l_Int8_minValue___closed__1, &l_Int8_minValue___closed__1_once, _init_l_Int8_minValue___closed__1);
v___x_114_ = lean_obj_once(&l_Int8_ofIntClamp___closed__0, &l_Int8_ofIntClamp___closed__0_once, _init_l_Int8_ofIntClamp___closed__0);
v___x_115_ = lean_int_dec_le(v___x_114_, v_i_112_);
if (v___x_115_ == 0)
{
return v___x_113_;
}
else
{
uint8_t v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_116_ = lean_uint8_once(&l_Int8_maxValue___closed__0, &l_Int8_maxValue___closed__0_once, _init_l_Int8_maxValue___closed__0);
v___x_117_ = lean_obj_once(&l_Int8_ofIntClamp___closed__1, &l_Int8_ofIntClamp___closed__1_once, _init_l_Int8_ofIntClamp___closed__1);
v___x_118_ = lean_int_dec_le(v_i_112_, v___x_117_);
if (v___x_118_ == 0)
{
return v___x_116_;
}
else
{
uint8_t v___x_119_; 
v___x_119_ = lean_int8_of_int(v_i_112_);
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int8_ofIntClamp___boxed(lean_object* v_i_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Int8_ofIntClamp(v_i_120_);
lean_dec(v_i_120_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT uint8_t l_Int8_ofIntTruncate(lean_object* v_i_123_){
_start:
{
uint8_t v___x_124_; 
v___x_124_ = l_Int8_ofIntClamp(v_i_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Int8_ofIntTruncate___boxed(lean_object* v_i_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = l_Int8_ofIntTruncate(v_i_125_);
lean_dec(v_i_125_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
LEAN_EXPORT lean_object* l_Int8_add___boxed(lean_object* v_a_130_, lean_object* v_b_131_){
_start:
{
uint8_t v_a_boxed_132_; uint8_t v_b_boxed_133_; uint8_t v_res_134_; lean_object* v_r_135_; 
v_a_boxed_132_ = lean_unbox(v_a_130_);
v_b_boxed_133_ = lean_unbox(v_b_131_);
v_res_134_ = lean_int8_add(v_a_boxed_132_, v_b_boxed_133_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT lean_object* l_Int8_sub___boxed(lean_object* v_a_138_, lean_object* v_b_139_){
_start:
{
uint8_t v_a_boxed_140_; uint8_t v_b_boxed_141_; uint8_t v_res_142_; lean_object* v_r_143_; 
v_a_boxed_140_ = lean_unbox(v_a_138_);
v_b_boxed_141_ = lean_unbox(v_b_139_);
v_res_142_ = lean_int8_sub(v_a_boxed_140_, v_b_boxed_141_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
LEAN_EXPORT lean_object* l_Int8_mul___boxed(lean_object* v_a_146_, lean_object* v_b_147_){
_start:
{
uint8_t v_a_boxed_148_; uint8_t v_b_boxed_149_; uint8_t v_res_150_; lean_object* v_r_151_; 
v_a_boxed_148_ = lean_unbox(v_a_146_);
v_b_boxed_149_ = lean_unbox(v_b_147_);
v_res_150_ = lean_int8_mul(v_a_boxed_148_, v_b_boxed_149_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT lean_object* l_Int8_div___boxed(lean_object* v_a_154_, lean_object* v_b_155_){
_start:
{
uint8_t v_a_boxed_156_; uint8_t v_b_boxed_157_; uint8_t v_res_158_; lean_object* v_r_159_; 
v_a_boxed_156_ = lean_unbox(v_a_154_);
v_b_boxed_157_ = lean_unbox(v_b_155_);
v_res_158_ = lean_int8_div(v_a_boxed_156_, v_b_boxed_157_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
static uint8_t _init_l_Int8_pow___closed__0(void){
_start:
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = lean_int8_of_nat(v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT uint8_t l_Int8_pow(uint8_t v_x_162_, lean_object* v_n_163_){
_start:
{
lean_object* v_zero_164_; uint8_t v_isZero_165_; 
v_zero_164_ = lean_unsigned_to_nat(0u);
v_isZero_165_ = lean_nat_dec_eq(v_n_163_, v_zero_164_);
if (v_isZero_165_ == 1)
{
uint8_t v___x_166_; 
v___x_166_ = lean_uint8_once(&l_Int8_pow___closed__0, &l_Int8_pow___closed__0_once, _init_l_Int8_pow___closed__0);
return v___x_166_;
}
else
{
lean_object* v_one_167_; lean_object* v_n_168_; uint8_t v___x_169_; uint8_t v___x_170_; 
v_one_167_ = lean_unsigned_to_nat(1u);
v_n_168_ = lean_nat_sub(v_n_163_, v_one_167_);
v___x_169_ = l_Int8_pow(v_x_162_, v_n_168_);
lean_dec(v_n_168_);
v___x_170_ = lean_int8_mul(v___x_169_, v_x_162_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Int8_pow___boxed(lean_object* v_x_171_, lean_object* v_n_172_){
_start:
{
uint8_t v_x_boxed_173_; uint8_t v_res_174_; lean_object* v_r_175_; 
v_x_boxed_173_ = lean_unbox(v_x_171_);
v_res_174_ = l_Int8_pow(v_x_boxed_173_, v_n_172_);
lean_dec(v_n_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l_Int8_mod___boxed(lean_object* v_a_178_, lean_object* v_b_179_){
_start:
{
uint8_t v_a_boxed_180_; uint8_t v_b_boxed_181_; uint8_t v_res_182_; lean_object* v_r_183_; 
v_a_boxed_180_ = lean_unbox(v_a_178_);
v_b_boxed_181_ = lean_unbox(v_b_179_);
v_res_182_ = lean_int8_mod(v_a_boxed_180_, v_b_boxed_181_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l_Int8_land___boxed(lean_object* v_a_186_, lean_object* v_b_187_){
_start:
{
uint8_t v_a_boxed_188_; uint8_t v_b_boxed_189_; uint8_t v_res_190_; lean_object* v_r_191_; 
v_a_boxed_188_ = lean_unbox(v_a_186_);
v_b_boxed_189_ = lean_unbox(v_b_187_);
v_res_190_ = lean_int8_land(v_a_boxed_188_, v_b_boxed_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* l_Int8_lor___boxed(lean_object* v_a_194_, lean_object* v_b_195_){
_start:
{
uint8_t v_a_boxed_196_; uint8_t v_b_boxed_197_; uint8_t v_res_198_; lean_object* v_r_199_; 
v_a_boxed_196_ = lean_unbox(v_a_194_);
v_b_boxed_197_ = lean_unbox(v_b_195_);
v_res_198_ = lean_int8_lor(v_a_boxed_196_, v_b_boxed_197_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT lean_object* l_Int8_xor___boxed(lean_object* v_a_202_, lean_object* v_b_203_){
_start:
{
uint8_t v_a_boxed_204_; uint8_t v_b_boxed_205_; uint8_t v_res_206_; lean_object* v_r_207_; 
v_a_boxed_204_ = lean_unbox(v_a_202_);
v_b_boxed_205_ = lean_unbox(v_b_203_);
v_res_206_ = lean_int8_xor(v_a_boxed_204_, v_b_boxed_205_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT lean_object* l_Int8_shiftLeft___boxed(lean_object* v_a_210_, lean_object* v_b_211_){
_start:
{
uint8_t v_a_boxed_212_; uint8_t v_b_boxed_213_; uint8_t v_res_214_; lean_object* v_r_215_; 
v_a_boxed_212_ = lean_unbox(v_a_210_);
v_b_boxed_213_ = lean_unbox(v_b_211_);
v_res_214_ = lean_int8_shift_left(v_a_boxed_212_, v_b_boxed_213_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT lean_object* l_Int8_shiftRight___boxed(lean_object* v_a_218_, lean_object* v_b_219_){
_start:
{
uint8_t v_a_boxed_220_; uint8_t v_b_boxed_221_; uint8_t v_res_222_; lean_object* v_r_223_; 
v_a_boxed_220_ = lean_unbox(v_a_218_);
v_b_boxed_221_ = lean_unbox(v_b_219_);
v_res_222_ = lean_int8_shift_right(v_a_boxed_220_, v_b_boxed_221_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT lean_object* l_Int8_complement___boxed(lean_object* v_a_225_){
_start:
{
uint8_t v_a_boxed_226_; uint8_t v_res_227_; lean_object* v_r_228_; 
v_a_boxed_226_ = lean_unbox(v_a_225_);
v_res_227_ = lean_int8_complement(v_a_boxed_226_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT lean_object* l_Int8_abs___boxed(lean_object* v_a_230_){
_start:
{
uint8_t v_a_boxed_231_; uint8_t v_res_232_; lean_object* v_r_233_; 
v_a_boxed_231_ = lean_unbox(v_a_230_);
v_res_232_ = lean_int8_abs(v_a_boxed_231_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT lean_object* l_Int8_decEq___boxed(lean_object* v_a_236_, lean_object* v_b_237_){
_start:
{
uint8_t v_a_boxed_238_; uint8_t v_b_boxed_239_; uint8_t v_res_240_; lean_object* v_r_241_; 
v_a_boxed_238_ = lean_unbox(v_a_236_);
v_b_boxed_239_ = lean_unbox(v_b_237_);
v_res_240_ = lean_int8_dec_eq(v_a_boxed_238_, v_b_boxed_239_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
static uint8_t _init_l_instInhabitedInt8___closed__0(void){
_start:
{
lean_object* v___x_242_; uint8_t v___x_243_; 
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_int8_of_nat(v___x_242_);
return v___x_243_;
}
}
static uint8_t _init_l_instInhabitedInt8(void){
_start:
{
uint8_t v___x_244_; 
v___x_244_ = lean_uint8_once(&l_instInhabitedInt8___closed__0, &l_instInhabitedInt8___closed__0_once, _init_l_instInhabitedInt8___closed__0);
return v___x_244_;
}
}
static lean_object* _init_l_instLTInt8(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_box(0);
return v___x_257_;
}
}
static lean_object* _init_l_instLEInt8(void){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = lean_box(0);
return v___x_258_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt8(uint8_t v_a_271_, uint8_t v_b_272_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = lean_int8_dec_eq(v_a_271_, v_b_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt8___boxed(lean_object* v_a_274_, lean_object* v_b_275_){
_start:
{
uint8_t v_a_boxed_276_; uint8_t v_b_boxed_277_; uint8_t v_res_278_; lean_object* v_r_279_; 
v_a_boxed_276_ = lean_unbox(v_a_274_);
v_b_boxed_277_ = lean_unbox(v_b_275_);
v_res_278_ = l_instDecidableEqInt8(v_a_boxed_276_, v_b_boxed_277_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt8___boxed(lean_object* v_b_281_){
_start:
{
uint8_t v_b_boxed_282_; uint8_t v_res_283_; lean_object* v_r_284_; 
v_b_boxed_282_ = lean_unbox(v_b_281_);
v_res_283_ = lean_bool_to_int8(v_b_boxed_282_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT uint8_t l_Int8_decLt___aux__1(uint8_t v_a_285_, uint8_t v_b_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_287_ = lean_unsigned_to_nat(8u);
v___x_288_ = lean_uint8_to_nat(v_a_285_);
v___x_289_ = lean_uint8_to_nat(v_b_286_);
v___x_290_ = l_BitVec_slt(v___x_287_, v___x_288_, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLt___aux__1___boxed(lean_object* v_a_291_, lean_object* v_b_292_){
_start:
{
uint8_t v_a_boxed_293_; uint8_t v_b_boxed_294_; uint8_t v_res_295_; lean_object* v_r_296_; 
v_a_boxed_293_ = lean_unbox(v_a_291_);
v_b_boxed_294_ = lean_unbox(v_b_292_);
v_res_295_ = l_Int8_decLt___aux__1(v_a_boxed_293_, v_b_boxed_294_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLt___boxed(lean_object* v_a_299_, lean_object* v_b_300_){
_start:
{
uint8_t v_a_boxed_301_; uint8_t v_b_boxed_302_; uint8_t v_res_303_; lean_object* v_r_304_; 
v_a_boxed_301_ = lean_unbox(v_a_299_);
v_b_boxed_302_ = lean_unbox(v_b_300_);
v_res_303_ = lean_int8_dec_lt(v_a_boxed_301_, v_b_boxed_302_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
LEAN_EXPORT uint8_t l_Int8_decLe___aux__1(uint8_t v_a_305_, uint8_t v_b_306_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_307_ = lean_unsigned_to_nat(8u);
v___x_308_ = lean_uint8_to_nat(v_a_305_);
v___x_309_ = lean_uint8_to_nat(v_b_306_);
v___x_310_ = l_BitVec_sle(v___x_307_, v___x_308_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLe___aux__1___boxed(lean_object* v_a_311_, lean_object* v_b_312_){
_start:
{
uint8_t v_a_boxed_313_; uint8_t v_b_boxed_314_; uint8_t v_res_315_; lean_object* v_r_316_; 
v_a_boxed_313_ = lean_unbox(v_a_311_);
v_b_boxed_314_ = lean_unbox(v_b_312_);
v_res_315_ = l_Int8_decLe___aux__1(v_a_boxed_313_, v_b_boxed_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLe___boxed(lean_object* v_a_319_, lean_object* v_b_320_){
_start:
{
uint8_t v_a_boxed_321_; uint8_t v_b_boxed_322_; uint8_t v_res_323_; lean_object* v_r_324_; 
v_a_boxed_321_ = lean_unbox(v_a_319_);
v_b_boxed_322_ = lean_unbox(v_b_320_);
v_res_323_ = lean_int8_dec_le(v_a_boxed_321_, v_b_boxed_322_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT uint8_t l_instMaxInt8___lam__0(uint8_t v_x_325_, uint8_t v_y_326_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = lean_int8_dec_le(v_x_325_, v_y_326_);
if (v___x_327_ == 0)
{
return v_x_325_;
}
else
{
return v_y_326_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt8___lam__0___boxed(lean_object* v_x_328_, lean_object* v_y_329_){
_start:
{
uint8_t v_x_boxed_330_; uint8_t v_y_boxed_331_; uint8_t v_res_332_; lean_object* v_r_333_; 
v_x_boxed_330_ = lean_unbox(v_x_328_);
v_y_boxed_331_ = lean_unbox(v_y_329_);
v_res_332_ = l_instMaxInt8___lam__0(v_x_boxed_330_, v_y_boxed_331_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT uint8_t l_instMinInt8___lam__0(uint8_t v_x_336_, uint8_t v_y_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_int8_dec_le(v_x_336_, v_y_337_);
if (v___x_338_ == 0)
{
return v_y_337_;
}
else
{
return v_x_336_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt8___lam__0___boxed(lean_object* v_x_339_, lean_object* v_y_340_){
_start:
{
uint8_t v_x_boxed_341_; uint8_t v_y_boxed_342_; uint8_t v_res_343_; lean_object* v_r_344_; 
v_x_boxed_341_ = lean_unbox(v_x_339_);
v_y_boxed_342_ = lean_unbox(v_y_340_);
v_res_343_ = l_instMinInt8___lam__0(v_x_boxed_341_, v_y_boxed_342_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
static lean_object* _init_l_Int16_size(void){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = lean_unsigned_to_nat(65536u);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Int16_toBitVec(uint16_t v_x_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_uint16_to_nat(v_x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Int16_toBitVec___boxed(lean_object* v_x_350_){
_start:
{
uint16_t v_x_boxed_351_; lean_object* v_res_352_; 
v_x_boxed_351_ = lean_unbox(v_x_350_);
v_res_352_ = l_Int16_toBitVec(v_x_boxed_351_);
return v_res_352_;
}
}
LEAN_EXPORT uint16_t l_UInt16_toInt16(uint16_t v_i_353_){
_start:
{
return v_i_353_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toInt16___boxed(lean_object* v_i_354_){
_start:
{
uint16_t v_i_boxed_355_; uint16_t v_res_356_; lean_object* v_r_357_; 
v_i_boxed_355_ = lean_unbox(v_i_354_);
v_res_356_ = l_UInt16_toInt16(v_i_boxed_355_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofInt___boxed(lean_object* v_i_359_){
_start:
{
uint16_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = lean_int16_of_int(v_i_359_);
lean_dec(v_i_359_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofNat___boxed(lean_object* v_n_363_){
_start:
{
uint16_t v_res_364_; lean_object* v_r_365_; 
v_res_364_ = lean_int16_of_nat(v_n_363_);
lean_dec(v_n_363_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT uint16_t l_Int_toInt16(lean_object* v_i_366_){
_start:
{
uint16_t v___x_367_; 
v___x_367_ = lean_int16_of_int(v_i_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt16___boxed(lean_object* v_i_368_){
_start:
{
uint16_t v_res_369_; lean_object* v_r_370_; 
v_res_369_ = l_Int_toInt16(v_i_368_);
lean_dec(v_i_368_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT uint16_t l_Nat_toInt16(lean_object* v_n_371_){
_start:
{
uint16_t v___x_372_; 
v___x_372_ = lean_int16_of_nat(v_n_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt16___boxed(lean_object* v_n_373_){
_start:
{
uint16_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l_Nat_toInt16(v_n_373_);
lean_dec(v_n_373_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt___boxed(lean_object* v_i_377_){
_start:
{
uint16_t v_i_boxed_378_; lean_object* v_res_379_; 
v_i_boxed_378_ = lean_unbox(v_i_377_);
v_res_379_ = lean_int16_to_int(v_i_boxed_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg(uint16_t v_i_380_){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_int16_to_int(v_i_380_);
v___x_382_ = l_Int_toNat(v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg___boxed(lean_object* v_i_383_){
_start:
{
uint16_t v_i_boxed_384_; lean_object* v_res_385_; 
v_i_boxed_384_ = lean_unbox(v_i_383_);
v_res_385_ = l_Int16_toNatClampNeg(v_i_boxed_384_);
return v_res_385_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofBitVec(lean_object* v_b_386_){
_start:
{
uint16_t v___x_387_; 
v___x_387_ = lean_uint16_of_nat_mk(v_b_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofBitVec___boxed(lean_object* v_b_388_){
_start:
{
uint16_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Int16_ofBitVec(v_b_388_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt8___boxed(lean_object* v_a_392_){
_start:
{
uint16_t v_a_boxed_393_; uint8_t v_res_394_; lean_object* v_r_395_; 
v_a_boxed_393_ = lean_unbox(v_a_392_);
v_res_394_ = lean_int16_to_int8(v_a_boxed_393_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt16___boxed(lean_object* v_a_397_){
_start:
{
uint8_t v_a_boxed_398_; uint16_t v_res_399_; lean_object* v_r_400_; 
v_a_boxed_398_ = lean_unbox(v_a_397_);
v_res_399_ = lean_int8_to_int16(v_a_boxed_398_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT lean_object* l_Int16_neg___boxed(lean_object* v_i_402_){
_start:
{
uint16_t v_i_boxed_403_; uint16_t v_res_404_; lean_object* v_r_405_; 
v_i_boxed_403_ = lean_unbox(v_i_402_);
v_res_404_ = lean_int16_neg(v_i_boxed_403_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0(uint16_t v_i_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_int16_to_int(v_i_406_);
v___x_408_ = l_Int_repr(v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0___boxed(lean_object* v_i_409_){
_start:
{
uint16_t v_i_boxed_410_; lean_object* v_res_411_; 
v_i_boxed_410_ = lean_unbox(v_i_409_);
v_res_411_ = l_instToStringInt16___lam__0(v_i_boxed_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_instReprInt16___lam__0(uint16_t v_i_414_, lean_object* v_prec_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_416_ = lean_int16_to_int(v_i_414_);
v___x_417_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_418_ = lean_int_dec_lt(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = l_Int_repr(v___x_416_);
v___x_420_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = l_Int_repr(v___x_416_);
v___x_422_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
v___x_423_ = l_Repr_addAppParen(v___x_422_, v_prec_415_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt16___lam__0___boxed(lean_object* v_i_424_, lean_object* v_prec_425_){
_start:
{
uint16_t v_i_boxed_426_; lean_object* v_res_427_; 
v_i_boxed_426_ = lean_unbox(v_i_424_);
v_res_427_ = l_instReprInt16___lam__0(v_i_boxed_426_, v_prec_425_);
lean_dec(v_prec_425_);
return v_res_427_;
}
}
static lean_object* _init_l_instReprAtomInt16(void){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_box(0);
return v___x_430_;
}
}
LEAN_EXPORT uint16_t l_Int16_instOfNat(lean_object* v_n_433_){
_start:
{
uint16_t v___x_434_; 
v___x_434_ = lean_int16_of_nat(v_n_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Int16_instOfNat___boxed(lean_object* v_n_435_){
_start:
{
uint16_t v_res_436_; lean_object* v_r_437_; 
v_res_436_ = l_Int16_instOfNat(v_n_435_);
lean_dec(v_n_435_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
static uint16_t _init_l_Int16_maxValue___closed__0(void){
_start:
{
lean_object* v___x_440_; uint16_t v___x_441_; 
v___x_440_ = lean_unsigned_to_nat(32767u);
v___x_441_ = lean_int16_of_nat(v___x_440_);
return v___x_441_;
}
}
static uint16_t _init_l_Int16_maxValue(void){
_start:
{
uint16_t v___x_442_; 
v___x_442_ = lean_uint16_once(&l_Int16_maxValue___closed__0, &l_Int16_maxValue___closed__0_once, _init_l_Int16_maxValue___closed__0);
return v___x_442_;
}
}
static uint16_t _init_l_Int16_minValue___closed__0(void){
_start:
{
lean_object* v___x_443_; uint16_t v___x_444_; 
v___x_443_ = lean_unsigned_to_nat(32768u);
v___x_444_ = lean_int16_of_nat(v___x_443_);
return v___x_444_;
}
}
static uint16_t _init_l_Int16_minValue___closed__1(void){
_start:
{
uint16_t v___x_445_; uint16_t v___x_446_; 
v___x_445_ = lean_uint16_once(&l_Int16_minValue___closed__0, &l_Int16_minValue___closed__0_once, _init_l_Int16_minValue___closed__0);
v___x_446_ = lean_int16_neg(v___x_445_);
return v___x_446_;
}
}
static uint16_t _init_l_Int16_minValue(void){
_start:
{
uint16_t v___x_447_; 
v___x_447_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
return v___x_447_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntLE___redArg(lean_object* v_i_448_){
_start:
{
uint16_t v___x_449_; 
v___x_449_ = lean_int16_of_int(v_i_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntLE___redArg___boxed(lean_object* v_i_450_){
_start:
{
uint16_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l_Int16_ofIntLE___redArg(v_i_450_);
lean_dec(v_i_450_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntLE(lean_object* v_i_453_, lean_object* v___hl_454_, lean_object* v___hr_455_){
_start:
{
uint16_t v___x_456_; 
v___x_456_ = lean_int16_of_int(v_i_453_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntLE___boxed(lean_object* v_i_457_, lean_object* v___hl_458_, lean_object* v___hr_459_){
_start:
{
uint16_t v_res_460_; lean_object* v_r_461_; 
v_res_460_ = l_Int16_ofIntLE(v_i_457_, v___hl_458_, v___hr_459_);
lean_dec(v_i_457_);
v_r_461_ = lean_box(v_res_460_);
return v_r_461_;
}
}
static lean_object* _init_l_Int16_ofIntClamp___closed__0(void){
_start:
{
uint16_t v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
v___x_463_ = lean_int16_to_int(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l_Int16_ofIntClamp___closed__1(void){
_start:
{
uint16_t v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_uint16_once(&l_Int16_maxValue___closed__0, &l_Int16_maxValue___closed__0_once, _init_l_Int16_maxValue___closed__0);
v___x_465_ = lean_int16_to_int(v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntClamp(lean_object* v_i_466_){
_start:
{
uint16_t v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_467_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
v___x_468_ = lean_obj_once(&l_Int16_ofIntClamp___closed__0, &l_Int16_ofIntClamp___closed__0_once, _init_l_Int16_ofIntClamp___closed__0);
v___x_469_ = lean_int_dec_le(v___x_468_, v_i_466_);
if (v___x_469_ == 0)
{
return v___x_467_;
}
else
{
uint16_t v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_470_ = lean_uint16_once(&l_Int16_maxValue___closed__0, &l_Int16_maxValue___closed__0_once, _init_l_Int16_maxValue___closed__0);
v___x_471_ = lean_obj_once(&l_Int16_ofIntClamp___closed__1, &l_Int16_ofIntClamp___closed__1_once, _init_l_Int16_ofIntClamp___closed__1);
v___x_472_ = lean_int_dec_le(v_i_466_, v___x_471_);
if (v___x_472_ == 0)
{
return v___x_470_;
}
else
{
uint16_t v___x_473_; 
v___x_473_ = lean_int16_of_int(v_i_466_);
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntClamp___boxed(lean_object* v_i_474_){
_start:
{
uint16_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_Int16_ofIntClamp(v_i_474_);
lean_dec(v_i_474_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntTruncate(lean_object* v_i_477_){
_start:
{
uint16_t v___x_478_; 
v___x_478_ = l_Int16_ofIntClamp(v_i_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntTruncate___boxed(lean_object* v_i_479_){
_start:
{
uint16_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_Int16_ofIntTruncate(v_i_479_);
lean_dec(v_i_479_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT lean_object* l_Int16_add___boxed(lean_object* v_a_484_, lean_object* v_b_485_){
_start:
{
uint16_t v_a_boxed_486_; uint16_t v_b_boxed_487_; uint16_t v_res_488_; lean_object* v_r_489_; 
v_a_boxed_486_ = lean_unbox(v_a_484_);
v_b_boxed_487_ = lean_unbox(v_b_485_);
v_res_488_ = lean_int16_add(v_a_boxed_486_, v_b_boxed_487_);
v_r_489_ = lean_box(v_res_488_);
return v_r_489_;
}
}
LEAN_EXPORT lean_object* l_Int16_sub___boxed(lean_object* v_a_492_, lean_object* v_b_493_){
_start:
{
uint16_t v_a_boxed_494_; uint16_t v_b_boxed_495_; uint16_t v_res_496_; lean_object* v_r_497_; 
v_a_boxed_494_ = lean_unbox(v_a_492_);
v_b_boxed_495_ = lean_unbox(v_b_493_);
v_res_496_ = lean_int16_sub(v_a_boxed_494_, v_b_boxed_495_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT lean_object* l_Int16_mul___boxed(lean_object* v_a_500_, lean_object* v_b_501_){
_start:
{
uint16_t v_a_boxed_502_; uint16_t v_b_boxed_503_; uint16_t v_res_504_; lean_object* v_r_505_; 
v_a_boxed_502_ = lean_unbox(v_a_500_);
v_b_boxed_503_ = lean_unbox(v_b_501_);
v_res_504_ = lean_int16_mul(v_a_boxed_502_, v_b_boxed_503_);
v_r_505_ = lean_box(v_res_504_);
return v_r_505_;
}
}
LEAN_EXPORT lean_object* l_Int16_div___boxed(lean_object* v_a_508_, lean_object* v_b_509_){
_start:
{
uint16_t v_a_boxed_510_; uint16_t v_b_boxed_511_; uint16_t v_res_512_; lean_object* v_r_513_; 
v_a_boxed_510_ = lean_unbox(v_a_508_);
v_b_boxed_511_ = lean_unbox(v_b_509_);
v_res_512_ = lean_int16_div(v_a_boxed_510_, v_b_boxed_511_);
v_r_513_ = lean_box(v_res_512_);
return v_r_513_;
}
}
static uint16_t _init_l_Int16_pow___closed__0(void){
_start:
{
lean_object* v___x_514_; uint16_t v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_int16_of_nat(v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT uint16_t l_Int16_pow(uint16_t v_x_516_, lean_object* v_n_517_){
_start:
{
lean_object* v_zero_518_; uint8_t v_isZero_519_; 
v_zero_518_ = lean_unsigned_to_nat(0u);
v_isZero_519_ = lean_nat_dec_eq(v_n_517_, v_zero_518_);
if (v_isZero_519_ == 1)
{
uint16_t v___x_520_; 
v___x_520_ = lean_uint16_once(&l_Int16_pow___closed__0, &l_Int16_pow___closed__0_once, _init_l_Int16_pow___closed__0);
return v___x_520_;
}
else
{
lean_object* v_one_521_; lean_object* v_n_522_; uint16_t v___x_523_; uint16_t v___x_524_; 
v_one_521_ = lean_unsigned_to_nat(1u);
v_n_522_ = lean_nat_sub(v_n_517_, v_one_521_);
v___x_523_ = l_Int16_pow(v_x_516_, v_n_522_);
lean_dec(v_n_522_);
v___x_524_ = lean_int16_mul(v___x_523_, v_x_516_);
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l_Int16_pow___boxed(lean_object* v_x_525_, lean_object* v_n_526_){
_start:
{
uint16_t v_x_boxed_527_; uint16_t v_res_528_; lean_object* v_r_529_; 
v_x_boxed_527_ = lean_unbox(v_x_525_);
v_res_528_ = l_Int16_pow(v_x_boxed_527_, v_n_526_);
lean_dec(v_n_526_);
v_r_529_ = lean_box(v_res_528_);
return v_r_529_;
}
}
LEAN_EXPORT lean_object* l_Int16_mod___boxed(lean_object* v_a_532_, lean_object* v_b_533_){
_start:
{
uint16_t v_a_boxed_534_; uint16_t v_b_boxed_535_; uint16_t v_res_536_; lean_object* v_r_537_; 
v_a_boxed_534_ = lean_unbox(v_a_532_);
v_b_boxed_535_ = lean_unbox(v_b_533_);
v_res_536_ = lean_int16_mod(v_a_boxed_534_, v_b_boxed_535_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT lean_object* l_Int16_land___boxed(lean_object* v_a_540_, lean_object* v_b_541_){
_start:
{
uint16_t v_a_boxed_542_; uint16_t v_b_boxed_543_; uint16_t v_res_544_; lean_object* v_r_545_; 
v_a_boxed_542_ = lean_unbox(v_a_540_);
v_b_boxed_543_ = lean_unbox(v_b_541_);
v_res_544_ = lean_int16_land(v_a_boxed_542_, v_b_boxed_543_);
v_r_545_ = lean_box(v_res_544_);
return v_r_545_;
}
}
LEAN_EXPORT lean_object* l_Int16_lor___boxed(lean_object* v_a_548_, lean_object* v_b_549_){
_start:
{
uint16_t v_a_boxed_550_; uint16_t v_b_boxed_551_; uint16_t v_res_552_; lean_object* v_r_553_; 
v_a_boxed_550_ = lean_unbox(v_a_548_);
v_b_boxed_551_ = lean_unbox(v_b_549_);
v_res_552_ = lean_int16_lor(v_a_boxed_550_, v_b_boxed_551_);
v_r_553_ = lean_box(v_res_552_);
return v_r_553_;
}
}
LEAN_EXPORT lean_object* l_Int16_xor___boxed(lean_object* v_a_556_, lean_object* v_b_557_){
_start:
{
uint16_t v_a_boxed_558_; uint16_t v_b_boxed_559_; uint16_t v_res_560_; lean_object* v_r_561_; 
v_a_boxed_558_ = lean_unbox(v_a_556_);
v_b_boxed_559_ = lean_unbox(v_b_557_);
v_res_560_ = lean_int16_xor(v_a_boxed_558_, v_b_boxed_559_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT lean_object* l_Int16_shiftLeft___boxed(lean_object* v_a_564_, lean_object* v_b_565_){
_start:
{
uint16_t v_a_boxed_566_; uint16_t v_b_boxed_567_; uint16_t v_res_568_; lean_object* v_r_569_; 
v_a_boxed_566_ = lean_unbox(v_a_564_);
v_b_boxed_567_ = lean_unbox(v_b_565_);
v_res_568_ = lean_int16_shift_left(v_a_boxed_566_, v_b_boxed_567_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l_Int16_shiftRight___boxed(lean_object* v_a_572_, lean_object* v_b_573_){
_start:
{
uint16_t v_a_boxed_574_; uint16_t v_b_boxed_575_; uint16_t v_res_576_; lean_object* v_r_577_; 
v_a_boxed_574_ = lean_unbox(v_a_572_);
v_b_boxed_575_ = lean_unbox(v_b_573_);
v_res_576_ = lean_int16_shift_right(v_a_boxed_574_, v_b_boxed_575_);
v_r_577_ = lean_box(v_res_576_);
return v_r_577_;
}
}
LEAN_EXPORT lean_object* l_Int16_complement___boxed(lean_object* v_a_579_){
_start:
{
uint16_t v_a_boxed_580_; uint16_t v_res_581_; lean_object* v_r_582_; 
v_a_boxed_580_ = lean_unbox(v_a_579_);
v_res_581_ = lean_int16_complement(v_a_boxed_580_);
v_r_582_ = lean_box(v_res_581_);
return v_r_582_;
}
}
LEAN_EXPORT lean_object* l_Int16_abs___boxed(lean_object* v_a_584_){
_start:
{
uint16_t v_a_boxed_585_; uint16_t v_res_586_; lean_object* v_r_587_; 
v_a_boxed_585_ = lean_unbox(v_a_584_);
v_res_586_ = lean_int16_abs(v_a_boxed_585_);
v_r_587_ = lean_box(v_res_586_);
return v_r_587_;
}
}
LEAN_EXPORT lean_object* l_Int16_decEq___boxed(lean_object* v_a_590_, lean_object* v_b_591_){
_start:
{
uint16_t v_a_boxed_592_; uint16_t v_b_boxed_593_; uint8_t v_res_594_; lean_object* v_r_595_; 
v_a_boxed_592_ = lean_unbox(v_a_590_);
v_b_boxed_593_ = lean_unbox(v_b_591_);
v_res_594_ = lean_int16_dec_eq(v_a_boxed_592_, v_b_boxed_593_);
v_r_595_ = lean_box(v_res_594_);
return v_r_595_;
}
}
static uint16_t _init_l_instInhabitedInt16___closed__0(void){
_start:
{
lean_object* v___x_596_; uint16_t v___x_597_; 
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_int16_of_nat(v___x_596_);
return v___x_597_;
}
}
static uint16_t _init_l_instInhabitedInt16(void){
_start:
{
uint16_t v___x_598_; 
v___x_598_ = lean_uint16_once(&l_instInhabitedInt16___closed__0, &l_instInhabitedInt16___closed__0_once, _init_l_instInhabitedInt16___closed__0);
return v___x_598_;
}
}
static lean_object* _init_l_instLTInt16(void){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = lean_box(0);
return v___x_611_;
}
}
static lean_object* _init_l_instLEInt16(void){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = lean_box(0);
return v___x_612_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt16(uint16_t v_a_625_, uint16_t v_b_626_){
_start:
{
uint8_t v___x_627_; 
v___x_627_ = lean_int16_dec_eq(v_a_625_, v_b_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt16___boxed(lean_object* v_a_628_, lean_object* v_b_629_){
_start:
{
uint16_t v_a_boxed_630_; uint16_t v_b_boxed_631_; uint8_t v_res_632_; lean_object* v_r_633_; 
v_a_boxed_630_ = lean_unbox(v_a_628_);
v_b_boxed_631_ = lean_unbox(v_b_629_);
v_res_632_ = l_instDecidableEqInt16(v_a_boxed_630_, v_b_boxed_631_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt16___boxed(lean_object* v_b_635_){
_start:
{
uint8_t v_b_boxed_636_; uint16_t v_res_637_; lean_object* v_r_638_; 
v_b_boxed_636_ = lean_unbox(v_b_635_);
v_res_637_ = lean_bool_to_int16(v_b_boxed_636_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT uint8_t l_Int16_decLt___aux__1(uint16_t v_a_639_, uint16_t v_b_640_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_641_ = lean_unsigned_to_nat(16u);
v___x_642_ = lean_uint16_to_nat(v_a_639_);
v___x_643_ = lean_uint16_to_nat(v_b_640_);
v___x_644_ = l_BitVec_slt(v___x_641_, v___x_642_, v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLt___aux__1___boxed(lean_object* v_a_645_, lean_object* v_b_646_){
_start:
{
uint16_t v_a_boxed_647_; uint16_t v_b_boxed_648_; uint8_t v_res_649_; lean_object* v_r_650_; 
v_a_boxed_647_ = lean_unbox(v_a_645_);
v_b_boxed_648_ = lean_unbox(v_b_646_);
v_res_649_ = l_Int16_decLt___aux__1(v_a_boxed_647_, v_b_boxed_648_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLt___boxed(lean_object* v_a_653_, lean_object* v_b_654_){
_start:
{
uint16_t v_a_boxed_655_; uint16_t v_b_boxed_656_; uint8_t v_res_657_; lean_object* v_r_658_; 
v_a_boxed_655_ = lean_unbox(v_a_653_);
v_b_boxed_656_ = lean_unbox(v_b_654_);
v_res_657_ = lean_int16_dec_lt(v_a_boxed_655_, v_b_boxed_656_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT uint8_t l_Int16_decLe___aux__1(uint16_t v_a_659_, uint16_t v_b_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_661_ = lean_unsigned_to_nat(16u);
v___x_662_ = lean_uint16_to_nat(v_a_659_);
v___x_663_ = lean_uint16_to_nat(v_b_660_);
v___x_664_ = l_BitVec_sle(v___x_661_, v___x_662_, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLe___aux__1___boxed(lean_object* v_a_665_, lean_object* v_b_666_){
_start:
{
uint16_t v_a_boxed_667_; uint16_t v_b_boxed_668_; uint8_t v_res_669_; lean_object* v_r_670_; 
v_a_boxed_667_ = lean_unbox(v_a_665_);
v_b_boxed_668_ = lean_unbox(v_b_666_);
v_res_669_ = l_Int16_decLe___aux__1(v_a_boxed_667_, v_b_boxed_668_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLe___boxed(lean_object* v_a_673_, lean_object* v_b_674_){
_start:
{
uint16_t v_a_boxed_675_; uint16_t v_b_boxed_676_; uint8_t v_res_677_; lean_object* v_r_678_; 
v_a_boxed_675_ = lean_unbox(v_a_673_);
v_b_boxed_676_ = lean_unbox(v_b_674_);
v_res_677_ = lean_int16_dec_le(v_a_boxed_675_, v_b_boxed_676_);
v_r_678_ = lean_box(v_res_677_);
return v_r_678_;
}
}
LEAN_EXPORT uint16_t l_instMaxInt16___lam__0(uint16_t v_x_679_, uint16_t v_y_680_){
_start:
{
uint8_t v___x_681_; 
v___x_681_ = lean_int16_dec_le(v_x_679_, v_y_680_);
if (v___x_681_ == 0)
{
return v_x_679_;
}
else
{
return v_y_680_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt16___lam__0___boxed(lean_object* v_x_682_, lean_object* v_y_683_){
_start:
{
uint16_t v_x_boxed_684_; uint16_t v_y_boxed_685_; uint16_t v_res_686_; lean_object* v_r_687_; 
v_x_boxed_684_ = lean_unbox(v_x_682_);
v_y_boxed_685_ = lean_unbox(v_y_683_);
v_res_686_ = l_instMaxInt16___lam__0(v_x_boxed_684_, v_y_boxed_685_);
v_r_687_ = lean_box(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT uint16_t l_instMinInt16___lam__0(uint16_t v_x_690_, uint16_t v_y_691_){
_start:
{
uint8_t v___x_692_; 
v___x_692_ = lean_int16_dec_le(v_x_690_, v_y_691_);
if (v___x_692_ == 0)
{
return v_y_691_;
}
else
{
return v_x_690_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt16___lam__0___boxed(lean_object* v_x_693_, lean_object* v_y_694_){
_start:
{
uint16_t v_x_boxed_695_; uint16_t v_y_boxed_696_; uint16_t v_res_697_; lean_object* v_r_698_; 
v_x_boxed_695_ = lean_unbox(v_x_693_);
v_y_boxed_696_ = lean_unbox(v_y_694_);
v_res_697_ = l_instMinInt16___lam__0(v_x_boxed_695_, v_y_boxed_696_);
v_r_698_ = lean_box(v_res_697_);
return v_r_698_;
}
}
static lean_object* _init_l_Int32_size(void){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = lean_cstr_to_nat("4294967296");
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Int32_toBitVec(uint32_t v_x_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = lean_uint32_to_nat(v_x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Int32_toBitVec___boxed(lean_object* v_x_704_){
_start:
{
uint32_t v_x_boxed_705_; lean_object* v_res_706_; 
v_x_boxed_705_ = lean_unbox_uint32(v_x_704_);
lean_dec(v_x_704_);
v_res_706_ = l_Int32_toBitVec(v_x_boxed_705_);
return v_res_706_;
}
}
LEAN_EXPORT uint32_t l_UInt32_toInt32(uint32_t v_i_707_){
_start:
{
return v_i_707_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toInt32___boxed(lean_object* v_i_708_){
_start:
{
uint32_t v_i_boxed_709_; uint32_t v_res_710_; lean_object* v_r_711_; 
v_i_boxed_709_ = lean_unbox_uint32(v_i_708_);
lean_dec(v_i_708_);
v_res_710_ = l_UInt32_toInt32(v_i_boxed_709_);
v_r_711_ = lean_box_uint32(v_res_710_);
return v_r_711_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofInt___boxed(lean_object* v_i_713_){
_start:
{
uint32_t v_res_714_; lean_object* v_r_715_; 
v_res_714_ = lean_int32_of_int(v_i_713_);
lean_dec(v_i_713_);
v_r_715_ = lean_box_uint32(v_res_714_);
return v_r_715_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofNat___boxed(lean_object* v_n_717_){
_start:
{
uint32_t v_res_718_; lean_object* v_r_719_; 
v_res_718_ = lean_int32_of_nat(v_n_717_);
lean_dec(v_n_717_);
v_r_719_ = lean_box_uint32(v_res_718_);
return v_r_719_;
}
}
LEAN_EXPORT uint32_t l_Int_toInt32(lean_object* v_i_720_){
_start:
{
uint32_t v___x_721_; 
v___x_721_ = lean_int32_of_int(v_i_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt32___boxed(lean_object* v_i_722_){
_start:
{
uint32_t v_res_723_; lean_object* v_r_724_; 
v_res_723_ = l_Int_toInt32(v_i_722_);
lean_dec(v_i_722_);
v_r_724_ = lean_box_uint32(v_res_723_);
return v_r_724_;
}
}
LEAN_EXPORT uint32_t l_Nat_toInt32(lean_object* v_n_725_){
_start:
{
uint32_t v___x_726_; 
v___x_726_ = lean_int32_of_nat(v_n_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt32___boxed(lean_object* v_n_727_){
_start:
{
uint32_t v_res_728_; lean_object* v_r_729_; 
v_res_728_ = l_Nat_toInt32(v_n_727_);
lean_dec(v_n_727_);
v_r_729_ = lean_box_uint32(v_res_728_);
return v_r_729_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt___boxed(lean_object* v_i_731_){
_start:
{
uint32_t v_i_boxed_732_; lean_object* v_res_733_; 
v_i_boxed_732_ = lean_unbox_uint32(v_i_731_);
lean_dec(v_i_731_);
v_res_733_ = lean_int32_to_int(v_i_boxed_732_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg(uint32_t v_i_734_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_int32_to_int(v_i_734_);
v___x_736_ = l_Int_toNat(v___x_735_);
lean_dec(v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg___boxed(lean_object* v_i_737_){
_start:
{
uint32_t v_i_boxed_738_; lean_object* v_res_739_; 
v_i_boxed_738_ = lean_unbox_uint32(v_i_737_);
lean_dec(v_i_737_);
v_res_739_ = l_Int32_toNatClampNeg(v_i_boxed_738_);
return v_res_739_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofBitVec(lean_object* v_b_740_){
_start:
{
uint32_t v___x_741_; 
v___x_741_ = lean_uint32_of_nat_mk(v_b_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofBitVec___boxed(lean_object* v_b_742_){
_start:
{
uint32_t v_res_743_; lean_object* v_r_744_; 
v_res_743_ = l_Int32_ofBitVec(v_b_742_);
v_r_744_ = lean_box_uint32(v_res_743_);
return v_r_744_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt8___boxed(lean_object* v_a_746_){
_start:
{
uint32_t v_a_boxed_747_; uint8_t v_res_748_; lean_object* v_r_749_; 
v_a_boxed_747_ = lean_unbox_uint32(v_a_746_);
lean_dec(v_a_746_);
v_res_748_ = lean_int32_to_int8(v_a_boxed_747_);
v_r_749_ = lean_box(v_res_748_);
return v_r_749_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt16___boxed(lean_object* v_a_751_){
_start:
{
uint32_t v_a_boxed_752_; uint16_t v_res_753_; lean_object* v_r_754_; 
v_a_boxed_752_ = lean_unbox_uint32(v_a_751_);
lean_dec(v_a_751_);
v_res_753_ = lean_int32_to_int16(v_a_boxed_752_);
v_r_754_ = lean_box(v_res_753_);
return v_r_754_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt32___boxed(lean_object* v_a_756_){
_start:
{
uint8_t v_a_boxed_757_; uint32_t v_res_758_; lean_object* v_r_759_; 
v_a_boxed_757_ = lean_unbox(v_a_756_);
v_res_758_ = lean_int8_to_int32(v_a_boxed_757_);
v_r_759_ = lean_box_uint32(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt32___boxed(lean_object* v_a_761_){
_start:
{
uint16_t v_a_boxed_762_; uint32_t v_res_763_; lean_object* v_r_764_; 
v_a_boxed_762_ = lean_unbox(v_a_761_);
v_res_763_ = lean_int16_to_int32(v_a_boxed_762_);
v_r_764_ = lean_box_uint32(v_res_763_);
return v_r_764_;
}
}
LEAN_EXPORT lean_object* l_Int32_neg___boxed(lean_object* v_i_766_){
_start:
{
uint32_t v_i_boxed_767_; uint32_t v_res_768_; lean_object* v_r_769_; 
v_i_boxed_767_ = lean_unbox_uint32(v_i_766_);
lean_dec(v_i_766_);
v_res_768_ = lean_int32_neg(v_i_boxed_767_);
v_r_769_ = lean_box_uint32(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0(uint32_t v_i_770_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_int32_to_int(v_i_770_);
v___x_772_ = l_Int_repr(v___x_771_);
lean_dec(v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0___boxed(lean_object* v_i_773_){
_start:
{
uint32_t v_i_boxed_774_; lean_object* v_res_775_; 
v_i_boxed_774_ = lean_unbox_uint32(v_i_773_);
lean_dec(v_i_773_);
v_res_775_ = l_instToStringInt32___lam__0(v_i_boxed_774_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_instReprInt32___lam__0(uint32_t v_i_778_, lean_object* v_prec_779_){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_780_ = lean_int32_to_int(v_i_778_);
v___x_781_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_782_ = lean_int_dec_lt(v___x_780_, v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = l_Int_repr(v___x_780_);
lean_dec(v___x_780_);
v___x_784_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = l_Int_repr(v___x_780_);
lean_dec(v___x_780_);
v___x_786_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
v___x_787_ = l_Repr_addAppParen(v___x_786_, v_prec_779_);
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt32___lam__0___boxed(lean_object* v_i_788_, lean_object* v_prec_789_){
_start:
{
uint32_t v_i_boxed_790_; lean_object* v_res_791_; 
v_i_boxed_790_ = lean_unbox_uint32(v_i_788_);
lean_dec(v_i_788_);
v_res_791_ = l_instReprInt32___lam__0(v_i_boxed_790_, v_prec_789_);
lean_dec(v_prec_789_);
return v_res_791_;
}
}
static lean_object* _init_l_instReprAtomInt32(void){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = lean_box(0);
return v___x_794_;
}
}
LEAN_EXPORT uint32_t l_Int32_instOfNat(lean_object* v_n_797_){
_start:
{
uint32_t v___x_798_; 
v___x_798_ = lean_int32_of_nat(v_n_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Int32_instOfNat___boxed(lean_object* v_n_799_){
_start:
{
uint32_t v_res_800_; lean_object* v_r_801_; 
v_res_800_ = l_Int32_instOfNat(v_n_799_);
lean_dec(v_n_799_);
v_r_801_ = lean_box_uint32(v_res_800_);
return v_r_801_;
}
}
static uint32_t _init_l_Int32_maxValue___closed__0(void){
_start:
{
lean_object* v___x_804_; uint32_t v___x_805_; 
v___x_804_ = lean_unsigned_to_nat(2147483647u);
v___x_805_ = lean_int32_of_nat(v___x_804_);
return v___x_805_;
}
}
static uint32_t _init_l_Int32_maxValue(void){
_start:
{
uint32_t v___x_806_; 
v___x_806_ = lean_uint32_once(&l_Int32_maxValue___closed__0, &l_Int32_maxValue___closed__0_once, _init_l_Int32_maxValue___closed__0);
return v___x_806_;
}
}
static uint32_t _init_l_Int32_minValue___closed__0(void){
_start:
{
lean_object* v___x_807_; uint32_t v___x_808_; 
v___x_807_ = lean_unsigned_to_nat(2147483648u);
v___x_808_ = lean_int32_of_nat(v___x_807_);
return v___x_808_;
}
}
static uint32_t _init_l_Int32_minValue___closed__1(void){
_start:
{
uint32_t v___x_809_; uint32_t v___x_810_; 
v___x_809_ = lean_uint32_once(&l_Int32_minValue___closed__0, &l_Int32_minValue___closed__0_once, _init_l_Int32_minValue___closed__0);
v___x_810_ = lean_int32_neg(v___x_809_);
return v___x_810_;
}
}
static uint32_t _init_l_Int32_minValue(void){
_start:
{
uint32_t v___x_811_; 
v___x_811_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
return v___x_811_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntLE___redArg(lean_object* v_i_812_){
_start:
{
uint32_t v___x_813_; 
v___x_813_ = lean_int32_of_int(v_i_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntLE___redArg___boxed(lean_object* v_i_814_){
_start:
{
uint32_t v_res_815_; lean_object* v_r_816_; 
v_res_815_ = l_Int32_ofIntLE___redArg(v_i_814_);
lean_dec(v_i_814_);
v_r_816_ = lean_box_uint32(v_res_815_);
return v_r_816_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntLE(lean_object* v_i_817_, lean_object* v___hl_818_, lean_object* v___hr_819_){
_start:
{
uint32_t v___x_820_; 
v___x_820_ = lean_int32_of_int(v_i_817_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntLE___boxed(lean_object* v_i_821_, lean_object* v___hl_822_, lean_object* v___hr_823_){
_start:
{
uint32_t v_res_824_; lean_object* v_r_825_; 
v_res_824_ = l_Int32_ofIntLE(v_i_821_, v___hl_822_, v___hr_823_);
lean_dec(v_i_821_);
v_r_825_ = lean_box_uint32(v_res_824_);
return v_r_825_;
}
}
static lean_object* _init_l_Int32_ofIntClamp___closed__0(void){
_start:
{
uint32_t v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
v___x_827_ = lean_int32_to_int(v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l_Int32_ofIntClamp___closed__1(void){
_start:
{
uint32_t v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_uint32_once(&l_Int32_maxValue___closed__0, &l_Int32_maxValue___closed__0_once, _init_l_Int32_maxValue___closed__0);
v___x_829_ = lean_int32_to_int(v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntClamp(lean_object* v_i_830_){
_start:
{
uint32_t v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_831_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
v___x_832_ = lean_obj_once(&l_Int32_ofIntClamp___closed__0, &l_Int32_ofIntClamp___closed__0_once, _init_l_Int32_ofIntClamp___closed__0);
v___x_833_ = lean_int_dec_le(v___x_832_, v_i_830_);
if (v___x_833_ == 0)
{
return v___x_831_;
}
else
{
uint32_t v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_834_ = lean_uint32_once(&l_Int32_maxValue___closed__0, &l_Int32_maxValue___closed__0_once, _init_l_Int32_maxValue___closed__0);
v___x_835_ = lean_obj_once(&l_Int32_ofIntClamp___closed__1, &l_Int32_ofIntClamp___closed__1_once, _init_l_Int32_ofIntClamp___closed__1);
v___x_836_ = lean_int_dec_le(v_i_830_, v___x_835_);
if (v___x_836_ == 0)
{
return v___x_834_;
}
else
{
uint32_t v___x_837_; 
v___x_837_ = lean_int32_of_int(v_i_830_);
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntClamp___boxed(lean_object* v_i_838_){
_start:
{
uint32_t v_res_839_; lean_object* v_r_840_; 
v_res_839_ = l_Int32_ofIntClamp(v_i_838_);
lean_dec(v_i_838_);
v_r_840_ = lean_box_uint32(v_res_839_);
return v_r_840_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntTruncate(lean_object* v_i_841_){
_start:
{
uint32_t v___x_842_; 
v___x_842_ = l_Int32_ofIntClamp(v_i_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntTruncate___boxed(lean_object* v_i_843_){
_start:
{
uint32_t v_res_844_; lean_object* v_r_845_; 
v_res_844_ = l_Int32_ofIntTruncate(v_i_843_);
lean_dec(v_i_843_);
v_r_845_ = lean_box_uint32(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT lean_object* l_Int32_add___boxed(lean_object* v_a_848_, lean_object* v_b_849_){
_start:
{
uint32_t v_a_boxed_850_; uint32_t v_b_boxed_851_; uint32_t v_res_852_; lean_object* v_r_853_; 
v_a_boxed_850_ = lean_unbox_uint32(v_a_848_);
lean_dec(v_a_848_);
v_b_boxed_851_ = lean_unbox_uint32(v_b_849_);
lean_dec(v_b_849_);
v_res_852_ = lean_int32_add(v_a_boxed_850_, v_b_boxed_851_);
v_r_853_ = lean_box_uint32(v_res_852_);
return v_r_853_;
}
}
LEAN_EXPORT lean_object* l_Int32_sub___boxed(lean_object* v_a_856_, lean_object* v_b_857_){
_start:
{
uint32_t v_a_boxed_858_; uint32_t v_b_boxed_859_; uint32_t v_res_860_; lean_object* v_r_861_; 
v_a_boxed_858_ = lean_unbox_uint32(v_a_856_);
lean_dec(v_a_856_);
v_b_boxed_859_ = lean_unbox_uint32(v_b_857_);
lean_dec(v_b_857_);
v_res_860_ = lean_int32_sub(v_a_boxed_858_, v_b_boxed_859_);
v_r_861_ = lean_box_uint32(v_res_860_);
return v_r_861_;
}
}
LEAN_EXPORT lean_object* l_Int32_mul___boxed(lean_object* v_a_864_, lean_object* v_b_865_){
_start:
{
uint32_t v_a_boxed_866_; uint32_t v_b_boxed_867_; uint32_t v_res_868_; lean_object* v_r_869_; 
v_a_boxed_866_ = lean_unbox_uint32(v_a_864_);
lean_dec(v_a_864_);
v_b_boxed_867_ = lean_unbox_uint32(v_b_865_);
lean_dec(v_b_865_);
v_res_868_ = lean_int32_mul(v_a_boxed_866_, v_b_boxed_867_);
v_r_869_ = lean_box_uint32(v_res_868_);
return v_r_869_;
}
}
LEAN_EXPORT lean_object* l_Int32_div___boxed(lean_object* v_a_872_, lean_object* v_b_873_){
_start:
{
uint32_t v_a_boxed_874_; uint32_t v_b_boxed_875_; uint32_t v_res_876_; lean_object* v_r_877_; 
v_a_boxed_874_ = lean_unbox_uint32(v_a_872_);
lean_dec(v_a_872_);
v_b_boxed_875_ = lean_unbox_uint32(v_b_873_);
lean_dec(v_b_873_);
v_res_876_ = lean_int32_div(v_a_boxed_874_, v_b_boxed_875_);
v_r_877_ = lean_box_uint32(v_res_876_);
return v_r_877_;
}
}
static uint32_t _init_l_Int32_pow___closed__0(void){
_start:
{
lean_object* v___x_878_; uint32_t v___x_879_; 
v___x_878_ = lean_unsigned_to_nat(1u);
v___x_879_ = lean_int32_of_nat(v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT uint32_t l_Int32_pow(uint32_t v_x_880_, lean_object* v_n_881_){
_start:
{
lean_object* v_zero_882_; uint8_t v_isZero_883_; 
v_zero_882_ = lean_unsigned_to_nat(0u);
v_isZero_883_ = lean_nat_dec_eq(v_n_881_, v_zero_882_);
if (v_isZero_883_ == 1)
{
uint32_t v___x_884_; 
v___x_884_ = lean_uint32_once(&l_Int32_pow___closed__0, &l_Int32_pow___closed__0_once, _init_l_Int32_pow___closed__0);
return v___x_884_;
}
else
{
lean_object* v_one_885_; lean_object* v_n_886_; uint32_t v___x_887_; uint32_t v___x_888_; 
v_one_885_ = lean_unsigned_to_nat(1u);
v_n_886_ = lean_nat_sub(v_n_881_, v_one_885_);
v___x_887_ = l_Int32_pow(v_x_880_, v_n_886_);
lean_dec(v_n_886_);
v___x_888_ = lean_int32_mul(v___x_887_, v_x_880_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Int32_pow___boxed(lean_object* v_x_889_, lean_object* v_n_890_){
_start:
{
uint32_t v_x_boxed_891_; uint32_t v_res_892_; lean_object* v_r_893_; 
v_x_boxed_891_ = lean_unbox_uint32(v_x_889_);
lean_dec(v_x_889_);
v_res_892_ = l_Int32_pow(v_x_boxed_891_, v_n_890_);
lean_dec(v_n_890_);
v_r_893_ = lean_box_uint32(v_res_892_);
return v_r_893_;
}
}
LEAN_EXPORT lean_object* l_Int32_mod___boxed(lean_object* v_a_896_, lean_object* v_b_897_){
_start:
{
uint32_t v_a_boxed_898_; uint32_t v_b_boxed_899_; uint32_t v_res_900_; lean_object* v_r_901_; 
v_a_boxed_898_ = lean_unbox_uint32(v_a_896_);
lean_dec(v_a_896_);
v_b_boxed_899_ = lean_unbox_uint32(v_b_897_);
lean_dec(v_b_897_);
v_res_900_ = lean_int32_mod(v_a_boxed_898_, v_b_boxed_899_);
v_r_901_ = lean_box_uint32(v_res_900_);
return v_r_901_;
}
}
LEAN_EXPORT lean_object* l_Int32_land___boxed(lean_object* v_a_904_, lean_object* v_b_905_){
_start:
{
uint32_t v_a_boxed_906_; uint32_t v_b_boxed_907_; uint32_t v_res_908_; lean_object* v_r_909_; 
v_a_boxed_906_ = lean_unbox_uint32(v_a_904_);
lean_dec(v_a_904_);
v_b_boxed_907_ = lean_unbox_uint32(v_b_905_);
lean_dec(v_b_905_);
v_res_908_ = lean_int32_land(v_a_boxed_906_, v_b_boxed_907_);
v_r_909_ = lean_box_uint32(v_res_908_);
return v_r_909_;
}
}
LEAN_EXPORT lean_object* l_Int32_lor___boxed(lean_object* v_a_912_, lean_object* v_b_913_){
_start:
{
uint32_t v_a_boxed_914_; uint32_t v_b_boxed_915_; uint32_t v_res_916_; lean_object* v_r_917_; 
v_a_boxed_914_ = lean_unbox_uint32(v_a_912_);
lean_dec(v_a_912_);
v_b_boxed_915_ = lean_unbox_uint32(v_b_913_);
lean_dec(v_b_913_);
v_res_916_ = lean_int32_lor(v_a_boxed_914_, v_b_boxed_915_);
v_r_917_ = lean_box_uint32(v_res_916_);
return v_r_917_;
}
}
LEAN_EXPORT lean_object* l_Int32_xor___boxed(lean_object* v_a_920_, lean_object* v_b_921_){
_start:
{
uint32_t v_a_boxed_922_; uint32_t v_b_boxed_923_; uint32_t v_res_924_; lean_object* v_r_925_; 
v_a_boxed_922_ = lean_unbox_uint32(v_a_920_);
lean_dec(v_a_920_);
v_b_boxed_923_ = lean_unbox_uint32(v_b_921_);
lean_dec(v_b_921_);
v_res_924_ = lean_int32_xor(v_a_boxed_922_, v_b_boxed_923_);
v_r_925_ = lean_box_uint32(v_res_924_);
return v_r_925_;
}
}
LEAN_EXPORT lean_object* l_Int32_shiftLeft___boxed(lean_object* v_a_928_, lean_object* v_b_929_){
_start:
{
uint32_t v_a_boxed_930_; uint32_t v_b_boxed_931_; uint32_t v_res_932_; lean_object* v_r_933_; 
v_a_boxed_930_ = lean_unbox_uint32(v_a_928_);
lean_dec(v_a_928_);
v_b_boxed_931_ = lean_unbox_uint32(v_b_929_);
lean_dec(v_b_929_);
v_res_932_ = lean_int32_shift_left(v_a_boxed_930_, v_b_boxed_931_);
v_r_933_ = lean_box_uint32(v_res_932_);
return v_r_933_;
}
}
LEAN_EXPORT lean_object* l_Int32_shiftRight___boxed(lean_object* v_a_936_, lean_object* v_b_937_){
_start:
{
uint32_t v_a_boxed_938_; uint32_t v_b_boxed_939_; uint32_t v_res_940_; lean_object* v_r_941_; 
v_a_boxed_938_ = lean_unbox_uint32(v_a_936_);
lean_dec(v_a_936_);
v_b_boxed_939_ = lean_unbox_uint32(v_b_937_);
lean_dec(v_b_937_);
v_res_940_ = lean_int32_shift_right(v_a_boxed_938_, v_b_boxed_939_);
v_r_941_ = lean_box_uint32(v_res_940_);
return v_r_941_;
}
}
LEAN_EXPORT lean_object* l_Int32_complement___boxed(lean_object* v_a_943_){
_start:
{
uint32_t v_a_boxed_944_; uint32_t v_res_945_; lean_object* v_r_946_; 
v_a_boxed_944_ = lean_unbox_uint32(v_a_943_);
lean_dec(v_a_943_);
v_res_945_ = lean_int32_complement(v_a_boxed_944_);
v_r_946_ = lean_box_uint32(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT lean_object* l_Int32_abs___boxed(lean_object* v_a_948_){
_start:
{
uint32_t v_a_boxed_949_; uint32_t v_res_950_; lean_object* v_r_951_; 
v_a_boxed_949_ = lean_unbox_uint32(v_a_948_);
lean_dec(v_a_948_);
v_res_950_ = lean_int32_abs(v_a_boxed_949_);
v_r_951_ = lean_box_uint32(v_res_950_);
return v_r_951_;
}
}
LEAN_EXPORT lean_object* l_Int32_decEq___boxed(lean_object* v_a_954_, lean_object* v_b_955_){
_start:
{
uint32_t v_a_boxed_956_; uint32_t v_b_boxed_957_; uint8_t v_res_958_; lean_object* v_r_959_; 
v_a_boxed_956_ = lean_unbox_uint32(v_a_954_);
lean_dec(v_a_954_);
v_b_boxed_957_ = lean_unbox_uint32(v_b_955_);
lean_dec(v_b_955_);
v_res_958_ = lean_int32_dec_eq(v_a_boxed_956_, v_b_boxed_957_);
v_r_959_ = lean_box(v_res_958_);
return v_r_959_;
}
}
static uint32_t _init_l_instInhabitedInt32___closed__0(void){
_start:
{
lean_object* v___x_960_; uint32_t v___x_961_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = lean_int32_of_nat(v___x_960_);
return v___x_961_;
}
}
static uint32_t _init_l_instInhabitedInt32(void){
_start:
{
uint32_t v___x_962_; 
v___x_962_ = lean_uint32_once(&l_instInhabitedInt32___closed__0, &l_instInhabitedInt32___closed__0_once, _init_l_instInhabitedInt32___closed__0);
return v___x_962_;
}
}
static lean_object* _init_l_instLTInt32(void){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = lean_box(0);
return v___x_975_;
}
}
static lean_object* _init_l_instLEInt32(void){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = lean_box(0);
return v___x_976_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt32(uint32_t v_a_989_, uint32_t v_b_990_){
_start:
{
uint8_t v___x_991_; 
v___x_991_ = lean_int32_dec_eq(v_a_989_, v_b_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt32___boxed(lean_object* v_a_992_, lean_object* v_b_993_){
_start:
{
uint32_t v_a_boxed_994_; uint32_t v_b_boxed_995_; uint8_t v_res_996_; lean_object* v_r_997_; 
v_a_boxed_994_ = lean_unbox_uint32(v_a_992_);
lean_dec(v_a_992_);
v_b_boxed_995_ = lean_unbox_uint32(v_b_993_);
lean_dec(v_b_993_);
v_res_996_ = l_instDecidableEqInt32(v_a_boxed_994_, v_b_boxed_995_);
v_r_997_ = lean_box(v_res_996_);
return v_r_997_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt32___boxed(lean_object* v_b_999_){
_start:
{
uint8_t v_b_boxed_1000_; uint32_t v_res_1001_; lean_object* v_r_1002_; 
v_b_boxed_1000_ = lean_unbox(v_b_999_);
v_res_1001_ = lean_bool_to_int32(v_b_boxed_1000_);
v_r_1002_ = lean_box_uint32(v_res_1001_);
return v_r_1002_;
}
}
LEAN_EXPORT uint8_t l_Int32_decLt___aux__1(uint32_t v_a_1003_, uint32_t v_b_1004_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1005_ = lean_unsigned_to_nat(32u);
v___x_1006_ = lean_uint32_to_nat(v_a_1003_);
v___x_1007_ = lean_uint32_to_nat(v_b_1004_);
v___x_1008_ = l_BitVec_slt(v___x_1005_, v___x_1006_, v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLt___aux__1___boxed(lean_object* v_a_1009_, lean_object* v_b_1010_){
_start:
{
uint32_t v_a_boxed_1011_; uint32_t v_b_boxed_1012_; uint8_t v_res_1013_; lean_object* v_r_1014_; 
v_a_boxed_1011_ = lean_unbox_uint32(v_a_1009_);
lean_dec(v_a_1009_);
v_b_boxed_1012_ = lean_unbox_uint32(v_b_1010_);
lean_dec(v_b_1010_);
v_res_1013_ = l_Int32_decLt___aux__1(v_a_boxed_1011_, v_b_boxed_1012_);
v_r_1014_ = lean_box(v_res_1013_);
return v_r_1014_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLt___boxed(lean_object* v_a_1017_, lean_object* v_b_1018_){
_start:
{
uint32_t v_a_boxed_1019_; uint32_t v_b_boxed_1020_; uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_a_boxed_1019_ = lean_unbox_uint32(v_a_1017_);
lean_dec(v_a_1017_);
v_b_boxed_1020_ = lean_unbox_uint32(v_b_1018_);
lean_dec(v_b_1018_);
v_res_1021_ = lean_int32_dec_lt(v_a_boxed_1019_, v_b_boxed_1020_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
LEAN_EXPORT uint8_t l_Int32_decLe___aux__1(uint32_t v_a_1023_, uint32_t v_b_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1025_ = lean_unsigned_to_nat(32u);
v___x_1026_ = lean_uint32_to_nat(v_a_1023_);
v___x_1027_ = lean_uint32_to_nat(v_b_1024_);
v___x_1028_ = l_BitVec_sle(v___x_1025_, v___x_1026_, v___x_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLe___aux__1___boxed(lean_object* v_a_1029_, lean_object* v_b_1030_){
_start:
{
uint32_t v_a_boxed_1031_; uint32_t v_b_boxed_1032_; uint8_t v_res_1033_; lean_object* v_r_1034_; 
v_a_boxed_1031_ = lean_unbox_uint32(v_a_1029_);
lean_dec(v_a_1029_);
v_b_boxed_1032_ = lean_unbox_uint32(v_b_1030_);
lean_dec(v_b_1030_);
v_res_1033_ = l_Int32_decLe___aux__1(v_a_boxed_1031_, v_b_boxed_1032_);
v_r_1034_ = lean_box(v_res_1033_);
return v_r_1034_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLe___boxed(lean_object* v_a_1037_, lean_object* v_b_1038_){
_start:
{
uint32_t v_a_boxed_1039_; uint32_t v_b_boxed_1040_; uint8_t v_res_1041_; lean_object* v_r_1042_; 
v_a_boxed_1039_ = lean_unbox_uint32(v_a_1037_);
lean_dec(v_a_1037_);
v_b_boxed_1040_ = lean_unbox_uint32(v_b_1038_);
lean_dec(v_b_1038_);
v_res_1041_ = lean_int32_dec_le(v_a_boxed_1039_, v_b_boxed_1040_);
v_r_1042_ = lean_box(v_res_1041_);
return v_r_1042_;
}
}
LEAN_EXPORT uint32_t l_instMaxInt32___lam__0(uint32_t v_x_1043_, uint32_t v_y_1044_){
_start:
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_int32_dec_le(v_x_1043_, v_y_1044_);
if (v___x_1045_ == 0)
{
return v_x_1043_;
}
else
{
return v_y_1044_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt32___lam__0___boxed(lean_object* v_x_1046_, lean_object* v_y_1047_){
_start:
{
uint32_t v_x_boxed_1048_; uint32_t v_y_boxed_1049_; uint32_t v_res_1050_; lean_object* v_r_1051_; 
v_x_boxed_1048_ = lean_unbox_uint32(v_x_1046_);
lean_dec(v_x_1046_);
v_y_boxed_1049_ = lean_unbox_uint32(v_y_1047_);
lean_dec(v_y_1047_);
v_res_1050_ = l_instMaxInt32___lam__0(v_x_boxed_1048_, v_y_boxed_1049_);
v_r_1051_ = lean_box_uint32(v_res_1050_);
return v_r_1051_;
}
}
LEAN_EXPORT uint32_t l_instMinInt32___lam__0(uint32_t v_x_1054_, uint32_t v_y_1055_){
_start:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_int32_dec_le(v_x_1054_, v_y_1055_);
if (v___x_1056_ == 0)
{
return v_y_1055_;
}
else
{
return v_x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt32___lam__0___boxed(lean_object* v_x_1057_, lean_object* v_y_1058_){
_start:
{
uint32_t v_x_boxed_1059_; uint32_t v_y_boxed_1060_; uint32_t v_res_1061_; lean_object* v_r_1062_; 
v_x_boxed_1059_ = lean_unbox_uint32(v_x_1057_);
lean_dec(v_x_1057_);
v_y_boxed_1060_ = lean_unbox_uint32(v_y_1058_);
lean_dec(v_y_1058_);
v_res_1061_ = l_instMinInt32___lam__0(v_x_boxed_1059_, v_y_boxed_1060_);
v_r_1062_ = lean_box_uint32(v_res_1061_);
return v_r_1062_;
}
}
static lean_object* _init_l_Int64_size___closed__0(void){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_cstr_to_nat("18446744073709551616");
return v___x_1065_;
}
}
static lean_object* _init_l_Int64_size(void){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_obj_once(&l_Int64_size___closed__0, &l_Int64_size___closed__0_once, _init_l_Int64_size___closed__0);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Int64_toBitVec(uint64_t v_x_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_uint64_to_nat(v_x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Int64_toBitVec___boxed(lean_object* v_x_1069_){
_start:
{
uint64_t v_x_boxed_1070_; lean_object* v_res_1071_; 
v_x_boxed_1070_ = lean_unbox_uint64(v_x_1069_);
lean_dec_ref(v_x_1069_);
v_res_1071_ = l_Int64_toBitVec(v_x_boxed_1070_);
return v_res_1071_;
}
}
LEAN_EXPORT uint64_t l_UInt64_toInt64(uint64_t v_i_1072_){
_start:
{
return v_i_1072_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toInt64___boxed(lean_object* v_i_1073_){
_start:
{
uint64_t v_i_boxed_1074_; uint64_t v_res_1075_; lean_object* v_r_1076_; 
v_i_boxed_1074_ = lean_unbox_uint64(v_i_1073_);
lean_dec_ref(v_i_1073_);
v_res_1075_ = l_UInt64_toInt64(v_i_boxed_1074_);
v_r_1076_ = lean_box_uint64(v_res_1075_);
return v_r_1076_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofInt___boxed(lean_object* v_i_1078_){
_start:
{
uint64_t v_res_1079_; lean_object* v_r_1080_; 
v_res_1079_ = lean_int64_of_int(v_i_1078_);
lean_dec(v_i_1078_);
v_r_1080_ = lean_box_uint64(v_res_1079_);
return v_r_1080_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofNat___boxed(lean_object* v_n_1082_){
_start:
{
uint64_t v_res_1083_; lean_object* v_r_1084_; 
v_res_1083_ = lean_int64_of_nat(v_n_1082_);
lean_dec(v_n_1082_);
v_r_1084_ = lean_box_uint64(v_res_1083_);
return v_r_1084_;
}
}
LEAN_EXPORT uint64_t l_Int_toInt64(lean_object* v_i_1085_){
_start:
{
uint64_t v___x_1086_; 
v___x_1086_ = lean_int64_of_int(v_i_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt64___boxed(lean_object* v_i_1087_){
_start:
{
uint64_t v_res_1088_; lean_object* v_r_1089_; 
v_res_1088_ = l_Int_toInt64(v_i_1087_);
lean_dec(v_i_1087_);
v_r_1089_ = lean_box_uint64(v_res_1088_);
return v_r_1089_;
}
}
LEAN_EXPORT uint64_t l_Nat_toInt64(lean_object* v_n_1090_){
_start:
{
uint64_t v___x_1091_; 
v___x_1091_ = lean_int64_of_nat(v_n_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt64___boxed(lean_object* v_n_1092_){
_start:
{
uint64_t v_res_1093_; lean_object* v_r_1094_; 
v_res_1093_ = l_Nat_toInt64(v_n_1092_);
lean_dec(v_n_1092_);
v_r_1094_ = lean_box_uint64(v_res_1093_);
return v_r_1094_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt___boxed(lean_object* v_i_1096_){
_start:
{
uint64_t v_i_boxed_1097_; lean_object* v_res_1098_; 
v_i_boxed_1097_ = lean_unbox_uint64(v_i_1096_);
lean_dec_ref(v_i_1096_);
v_res_1098_ = lean_int64_to_int_sint(v_i_boxed_1097_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg(uint64_t v_i_1099_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_int64_to_int_sint(v_i_1099_);
v___x_1101_ = l_Int_toNat(v___x_1100_);
lean_dec(v___x_1100_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg___boxed(lean_object* v_i_1102_){
_start:
{
uint64_t v_i_boxed_1103_; lean_object* v_res_1104_; 
v_i_boxed_1103_ = lean_unbox_uint64(v_i_1102_);
lean_dec_ref(v_i_1102_);
v_res_1104_ = l_Int64_toNatClampNeg(v_i_boxed_1103_);
return v_res_1104_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofBitVec(lean_object* v_b_1105_){
_start:
{
uint64_t v___x_1106_; 
v___x_1106_ = lean_uint64_of_nat_mk(v_b_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofBitVec___boxed(lean_object* v_b_1107_){
_start:
{
uint64_t v_res_1108_; lean_object* v_r_1109_; 
v_res_1108_ = l_Int64_ofBitVec(v_b_1107_);
v_r_1109_ = lean_box_uint64(v_res_1108_);
return v_r_1109_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt8___boxed(lean_object* v_a_1111_){
_start:
{
uint64_t v_a_boxed_1112_; uint8_t v_res_1113_; lean_object* v_r_1114_; 
v_a_boxed_1112_ = lean_unbox_uint64(v_a_1111_);
lean_dec_ref(v_a_1111_);
v_res_1113_ = lean_int64_to_int8(v_a_boxed_1112_);
v_r_1114_ = lean_box(v_res_1113_);
return v_r_1114_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt16___boxed(lean_object* v_a_1116_){
_start:
{
uint64_t v_a_boxed_1117_; uint16_t v_res_1118_; lean_object* v_r_1119_; 
v_a_boxed_1117_ = lean_unbox_uint64(v_a_1116_);
lean_dec_ref(v_a_1116_);
v_res_1118_ = lean_int64_to_int16(v_a_boxed_1117_);
v_r_1119_ = lean_box(v_res_1118_);
return v_r_1119_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt32___boxed(lean_object* v_a_1121_){
_start:
{
uint64_t v_a_boxed_1122_; uint32_t v_res_1123_; lean_object* v_r_1124_; 
v_a_boxed_1122_ = lean_unbox_uint64(v_a_1121_);
lean_dec_ref(v_a_1121_);
v_res_1123_ = lean_int64_to_int32(v_a_boxed_1122_);
v_r_1124_ = lean_box_uint32(v_res_1123_);
return v_r_1124_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt64___boxed(lean_object* v_a_1126_){
_start:
{
uint8_t v_a_boxed_1127_; uint64_t v_res_1128_; lean_object* v_r_1129_; 
v_a_boxed_1127_ = lean_unbox(v_a_1126_);
v_res_1128_ = lean_int8_to_int64(v_a_boxed_1127_);
v_r_1129_ = lean_box_uint64(v_res_1128_);
return v_r_1129_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt64___boxed(lean_object* v_a_1131_){
_start:
{
uint16_t v_a_boxed_1132_; uint64_t v_res_1133_; lean_object* v_r_1134_; 
v_a_boxed_1132_ = lean_unbox(v_a_1131_);
v_res_1133_ = lean_int16_to_int64(v_a_boxed_1132_);
v_r_1134_ = lean_box_uint64(v_res_1133_);
return v_r_1134_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt64___boxed(lean_object* v_a_1136_){
_start:
{
uint32_t v_a_boxed_1137_; uint64_t v_res_1138_; lean_object* v_r_1139_; 
v_a_boxed_1137_ = lean_unbox_uint32(v_a_1136_);
lean_dec(v_a_1136_);
v_res_1138_ = lean_int32_to_int64(v_a_boxed_1137_);
v_r_1139_ = lean_box_uint64(v_res_1138_);
return v_r_1139_;
}
}
LEAN_EXPORT lean_object* l_Int64_neg___boxed(lean_object* v_i_1141_){
_start:
{
uint64_t v_i_boxed_1142_; uint64_t v_res_1143_; lean_object* v_r_1144_; 
v_i_boxed_1142_ = lean_unbox_uint64(v_i_1141_);
lean_dec_ref(v_i_1141_);
v_res_1143_ = lean_int64_neg(v_i_boxed_1142_);
v_r_1144_ = lean_box_uint64(v_res_1143_);
return v_r_1144_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0(uint64_t v_i_1145_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_int64_to_int_sint(v_i_1145_);
v___x_1147_ = l_Int_repr(v___x_1146_);
lean_dec(v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0___boxed(lean_object* v_i_1148_){
_start:
{
uint64_t v_i_boxed_1149_; lean_object* v_res_1150_; 
v_i_boxed_1149_ = lean_unbox_uint64(v_i_1148_);
lean_dec_ref(v_i_1148_);
v_res_1150_ = l_instToStringInt64___lam__0(v_i_boxed_1149_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_instReprInt64___lam__0(uint64_t v_i_1153_, lean_object* v_prec_1154_){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v___x_1155_ = lean_int64_to_int_sint(v_i_1153_);
v___x_1156_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_1157_ = lean_int_dec_lt(v___x_1155_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = l_Int_repr(v___x_1155_);
lean_dec(v___x_1155_);
v___x_1159_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
return v___x_1159_;
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = l_Int_repr(v___x_1155_);
lean_dec(v___x_1155_);
v___x_1161_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1160_);
v___x_1162_ = l_Repr_addAppParen(v___x_1161_, v_prec_1154_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt64___lam__0___boxed(lean_object* v_i_1163_, lean_object* v_prec_1164_){
_start:
{
uint64_t v_i_boxed_1165_; lean_object* v_res_1166_; 
v_i_boxed_1165_ = lean_unbox_uint64(v_i_1163_);
lean_dec_ref(v_i_1163_);
v_res_1166_ = l_instReprInt64___lam__0(v_i_boxed_1165_, v_prec_1164_);
lean_dec(v_prec_1164_);
return v_res_1166_;
}
}
static lean_object* _init_l_instReprAtomInt64(void){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_box(0);
return v___x_1169_;
}
}
LEAN_EXPORT uint64_t l_instHashableInt64___lam__0(uint64_t v_i_1170_){
_start:
{
return v_i_1170_;
}
}
LEAN_EXPORT lean_object* l_instHashableInt64___lam__0___boxed(lean_object* v_i_1171_){
_start:
{
uint64_t v_i_boxed_1172_; uint64_t v_res_1173_; lean_object* v_r_1174_; 
v_i_boxed_1172_ = lean_unbox_uint64(v_i_1171_);
lean_dec_ref(v_i_1171_);
v_res_1173_ = l_instHashableInt64___lam__0(v_i_boxed_1172_);
v_r_1174_ = lean_box_uint64(v_res_1173_);
return v_r_1174_;
}
}
LEAN_EXPORT uint64_t l_Int64_instOfNat(lean_object* v_n_1177_){
_start:
{
uint64_t v___x_1178_; 
v___x_1178_ = lean_int64_of_nat(v_n_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Int64_instOfNat___boxed(lean_object* v_n_1179_){
_start:
{
uint64_t v_res_1180_; lean_object* v_r_1181_; 
v_res_1180_ = l_Int64_instOfNat(v_n_1179_);
lean_dec(v_n_1179_);
v_r_1181_ = lean_box_uint64(v_res_1180_);
return v_r_1181_;
}
}
static uint64_t _init_l_Int64_maxValue___closed__0(void){
_start:
{
lean_object* v___x_1184_; uint64_t v___x_1185_; 
v___x_1184_ = lean_cstr_to_nat("9223372036854775807");
v___x_1185_ = lean_int64_of_nat(v___x_1184_);
return v___x_1185_;
}
}
static uint64_t _init_l_Int64_maxValue(void){
_start:
{
uint64_t v___x_1186_; 
v___x_1186_ = lean_uint64_once(&l_Int64_maxValue___closed__0, &l_Int64_maxValue___closed__0_once, _init_l_Int64_maxValue___closed__0);
return v___x_1186_;
}
}
static lean_object* _init_l_Int64_minValue___closed__0(void){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_cstr_to_nat("9223372036854775808");
return v___x_1187_;
}
}
static uint64_t _init_l_Int64_minValue___closed__1(void){
_start:
{
lean_object* v___x_1188_; uint64_t v___x_1189_; 
v___x_1188_ = lean_obj_once(&l_Int64_minValue___closed__0, &l_Int64_minValue___closed__0_once, _init_l_Int64_minValue___closed__0);
v___x_1189_ = lean_int64_of_nat(v___x_1188_);
return v___x_1189_;
}
}
static uint64_t _init_l_Int64_minValue___closed__2(void){
_start:
{
uint64_t v___x_1190_; uint64_t v___x_1191_; 
v___x_1190_ = lean_uint64_once(&l_Int64_minValue___closed__1, &l_Int64_minValue___closed__1_once, _init_l_Int64_minValue___closed__1);
v___x_1191_ = lean_int64_neg(v___x_1190_);
return v___x_1191_;
}
}
static uint64_t _init_l_Int64_minValue(void){
_start:
{
uint64_t v___x_1192_; 
v___x_1192_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
return v___x_1192_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntLE___redArg(lean_object* v_i_1193_){
_start:
{
uint64_t v___x_1194_; 
v___x_1194_ = lean_int64_of_int(v_i_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntLE___redArg___boxed(lean_object* v_i_1195_){
_start:
{
uint64_t v_res_1196_; lean_object* v_r_1197_; 
v_res_1196_ = l_Int64_ofIntLE___redArg(v_i_1195_);
lean_dec(v_i_1195_);
v_r_1197_ = lean_box_uint64(v_res_1196_);
return v_r_1197_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntLE(lean_object* v_i_1198_, lean_object* v___hl_1199_, lean_object* v___hr_1200_){
_start:
{
uint64_t v___x_1201_; 
v___x_1201_ = lean_int64_of_int(v_i_1198_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntLE___boxed(lean_object* v_i_1202_, lean_object* v___hl_1203_, lean_object* v___hr_1204_){
_start:
{
uint64_t v_res_1205_; lean_object* v_r_1206_; 
v_res_1205_ = l_Int64_ofIntLE(v_i_1202_, v___hl_1203_, v___hr_1204_);
lean_dec(v_i_1202_);
v_r_1206_ = lean_box_uint64(v_res_1205_);
return v_r_1206_;
}
}
static lean_object* _init_l_Int64_ofIntClamp___closed__0(void){
_start:
{
uint64_t v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
v___x_1208_ = lean_int64_to_int_sint(v___x_1207_);
return v___x_1208_;
}
}
static lean_object* _init_l_Int64_ofIntClamp___closed__1(void){
_start:
{
uint64_t v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_uint64_once(&l_Int64_maxValue___closed__0, &l_Int64_maxValue___closed__0_once, _init_l_Int64_maxValue___closed__0);
v___x_1210_ = lean_int64_to_int_sint(v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntClamp(lean_object* v_i_1211_){
_start:
{
uint64_t v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1212_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
v___x_1213_ = lean_obj_once(&l_Int64_ofIntClamp___closed__0, &l_Int64_ofIntClamp___closed__0_once, _init_l_Int64_ofIntClamp___closed__0);
v___x_1214_ = lean_int_dec_le(v___x_1213_, v_i_1211_);
if (v___x_1214_ == 0)
{
return v___x_1212_;
}
else
{
uint64_t v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1215_ = lean_uint64_once(&l_Int64_maxValue___closed__0, &l_Int64_maxValue___closed__0_once, _init_l_Int64_maxValue___closed__0);
v___x_1216_ = lean_obj_once(&l_Int64_ofIntClamp___closed__1, &l_Int64_ofIntClamp___closed__1_once, _init_l_Int64_ofIntClamp___closed__1);
v___x_1217_ = lean_int_dec_le(v_i_1211_, v___x_1216_);
if (v___x_1217_ == 0)
{
return v___x_1215_;
}
else
{
uint64_t v___x_1218_; 
v___x_1218_ = lean_int64_of_int(v_i_1211_);
return v___x_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntClamp___boxed(lean_object* v_i_1219_){
_start:
{
uint64_t v_res_1220_; lean_object* v_r_1221_; 
v_res_1220_ = l_Int64_ofIntClamp(v_i_1219_);
lean_dec(v_i_1219_);
v_r_1221_ = lean_box_uint64(v_res_1220_);
return v_r_1221_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntTruncate(lean_object* v_i_1222_){
_start:
{
uint64_t v___x_1223_; 
v___x_1223_ = l_Int64_ofIntClamp(v_i_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntTruncate___boxed(lean_object* v_i_1224_){
_start:
{
uint64_t v_res_1225_; lean_object* v_r_1226_; 
v_res_1225_ = l_Int64_ofIntTruncate(v_i_1224_);
lean_dec(v_i_1224_);
v_r_1226_ = lean_box_uint64(v_res_1225_);
return v_r_1226_;
}
}
LEAN_EXPORT lean_object* l_Int64_add___boxed(lean_object* v_a_1229_, lean_object* v_b_1230_){
_start:
{
uint64_t v_a_boxed_1231_; uint64_t v_b_boxed_1232_; uint64_t v_res_1233_; lean_object* v_r_1234_; 
v_a_boxed_1231_ = lean_unbox_uint64(v_a_1229_);
lean_dec_ref(v_a_1229_);
v_b_boxed_1232_ = lean_unbox_uint64(v_b_1230_);
lean_dec_ref(v_b_1230_);
v_res_1233_ = lean_int64_add(v_a_boxed_1231_, v_b_boxed_1232_);
v_r_1234_ = lean_box_uint64(v_res_1233_);
return v_r_1234_;
}
}
LEAN_EXPORT lean_object* l_Int64_sub___boxed(lean_object* v_a_1237_, lean_object* v_b_1238_){
_start:
{
uint64_t v_a_boxed_1239_; uint64_t v_b_boxed_1240_; uint64_t v_res_1241_; lean_object* v_r_1242_; 
v_a_boxed_1239_ = lean_unbox_uint64(v_a_1237_);
lean_dec_ref(v_a_1237_);
v_b_boxed_1240_ = lean_unbox_uint64(v_b_1238_);
lean_dec_ref(v_b_1238_);
v_res_1241_ = lean_int64_sub(v_a_boxed_1239_, v_b_boxed_1240_);
v_r_1242_ = lean_box_uint64(v_res_1241_);
return v_r_1242_;
}
}
LEAN_EXPORT lean_object* l_Int64_mul___boxed(lean_object* v_a_1245_, lean_object* v_b_1246_){
_start:
{
uint64_t v_a_boxed_1247_; uint64_t v_b_boxed_1248_; uint64_t v_res_1249_; lean_object* v_r_1250_; 
v_a_boxed_1247_ = lean_unbox_uint64(v_a_1245_);
lean_dec_ref(v_a_1245_);
v_b_boxed_1248_ = lean_unbox_uint64(v_b_1246_);
lean_dec_ref(v_b_1246_);
v_res_1249_ = lean_int64_mul(v_a_boxed_1247_, v_b_boxed_1248_);
v_r_1250_ = lean_box_uint64(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT lean_object* l_Int64_div___boxed(lean_object* v_a_1253_, lean_object* v_b_1254_){
_start:
{
uint64_t v_a_boxed_1255_; uint64_t v_b_boxed_1256_; uint64_t v_res_1257_; lean_object* v_r_1258_; 
v_a_boxed_1255_ = lean_unbox_uint64(v_a_1253_);
lean_dec_ref(v_a_1253_);
v_b_boxed_1256_ = lean_unbox_uint64(v_b_1254_);
lean_dec_ref(v_b_1254_);
v_res_1257_ = lean_int64_div(v_a_boxed_1255_, v_b_boxed_1256_);
v_r_1258_ = lean_box_uint64(v_res_1257_);
return v_r_1258_;
}
}
static uint64_t _init_l_Int64_pow___closed__0(void){
_start:
{
lean_object* v___x_1259_; uint64_t v___x_1260_; 
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_int64_of_nat(v___x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT uint64_t l_Int64_pow(uint64_t v_x_1261_, lean_object* v_n_1262_){
_start:
{
lean_object* v_zero_1263_; uint8_t v_isZero_1264_; 
v_zero_1263_ = lean_unsigned_to_nat(0u);
v_isZero_1264_ = lean_nat_dec_eq(v_n_1262_, v_zero_1263_);
if (v_isZero_1264_ == 1)
{
uint64_t v___x_1265_; 
v___x_1265_ = lean_uint64_once(&l_Int64_pow___closed__0, &l_Int64_pow___closed__0_once, _init_l_Int64_pow___closed__0);
return v___x_1265_;
}
else
{
lean_object* v_one_1266_; lean_object* v_n_1267_; uint64_t v___x_1268_; uint64_t v___x_1269_; 
v_one_1266_ = lean_unsigned_to_nat(1u);
v_n_1267_ = lean_nat_sub(v_n_1262_, v_one_1266_);
v___x_1268_ = l_Int64_pow(v_x_1261_, v_n_1267_);
lean_dec(v_n_1267_);
v___x_1269_ = lean_int64_mul(v___x_1268_, v_x_1261_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l_Int64_pow___boxed(lean_object* v_x_1270_, lean_object* v_n_1271_){
_start:
{
uint64_t v_x_boxed_1272_; uint64_t v_res_1273_; lean_object* v_r_1274_; 
v_x_boxed_1272_ = lean_unbox_uint64(v_x_1270_);
lean_dec_ref(v_x_1270_);
v_res_1273_ = l_Int64_pow(v_x_boxed_1272_, v_n_1271_);
lean_dec(v_n_1271_);
v_r_1274_ = lean_box_uint64(v_res_1273_);
return v_r_1274_;
}
}
LEAN_EXPORT lean_object* l_Int64_mod___boxed(lean_object* v_a_1277_, lean_object* v_b_1278_){
_start:
{
uint64_t v_a_boxed_1279_; uint64_t v_b_boxed_1280_; uint64_t v_res_1281_; lean_object* v_r_1282_; 
v_a_boxed_1279_ = lean_unbox_uint64(v_a_1277_);
lean_dec_ref(v_a_1277_);
v_b_boxed_1280_ = lean_unbox_uint64(v_b_1278_);
lean_dec_ref(v_b_1278_);
v_res_1281_ = lean_int64_mod(v_a_boxed_1279_, v_b_boxed_1280_);
v_r_1282_ = lean_box_uint64(v_res_1281_);
return v_r_1282_;
}
}
LEAN_EXPORT lean_object* l_Int64_land___boxed(lean_object* v_a_1285_, lean_object* v_b_1286_){
_start:
{
uint64_t v_a_boxed_1287_; uint64_t v_b_boxed_1288_; uint64_t v_res_1289_; lean_object* v_r_1290_; 
v_a_boxed_1287_ = lean_unbox_uint64(v_a_1285_);
lean_dec_ref(v_a_1285_);
v_b_boxed_1288_ = lean_unbox_uint64(v_b_1286_);
lean_dec_ref(v_b_1286_);
v_res_1289_ = lean_int64_land(v_a_boxed_1287_, v_b_boxed_1288_);
v_r_1290_ = lean_box_uint64(v_res_1289_);
return v_r_1290_;
}
}
LEAN_EXPORT lean_object* l_Int64_lor___boxed(lean_object* v_a_1293_, lean_object* v_b_1294_){
_start:
{
uint64_t v_a_boxed_1295_; uint64_t v_b_boxed_1296_; uint64_t v_res_1297_; lean_object* v_r_1298_; 
v_a_boxed_1295_ = lean_unbox_uint64(v_a_1293_);
lean_dec_ref(v_a_1293_);
v_b_boxed_1296_ = lean_unbox_uint64(v_b_1294_);
lean_dec_ref(v_b_1294_);
v_res_1297_ = lean_int64_lor(v_a_boxed_1295_, v_b_boxed_1296_);
v_r_1298_ = lean_box_uint64(v_res_1297_);
return v_r_1298_;
}
}
LEAN_EXPORT lean_object* l_Int64_xor___boxed(lean_object* v_a_1301_, lean_object* v_b_1302_){
_start:
{
uint64_t v_a_boxed_1303_; uint64_t v_b_boxed_1304_; uint64_t v_res_1305_; lean_object* v_r_1306_; 
v_a_boxed_1303_ = lean_unbox_uint64(v_a_1301_);
lean_dec_ref(v_a_1301_);
v_b_boxed_1304_ = lean_unbox_uint64(v_b_1302_);
lean_dec_ref(v_b_1302_);
v_res_1305_ = lean_int64_xor(v_a_boxed_1303_, v_b_boxed_1304_);
v_r_1306_ = lean_box_uint64(v_res_1305_);
return v_r_1306_;
}
}
LEAN_EXPORT lean_object* l_Int64_shiftLeft___boxed(lean_object* v_a_1309_, lean_object* v_b_1310_){
_start:
{
uint64_t v_a_boxed_1311_; uint64_t v_b_boxed_1312_; uint64_t v_res_1313_; lean_object* v_r_1314_; 
v_a_boxed_1311_ = lean_unbox_uint64(v_a_1309_);
lean_dec_ref(v_a_1309_);
v_b_boxed_1312_ = lean_unbox_uint64(v_b_1310_);
lean_dec_ref(v_b_1310_);
v_res_1313_ = lean_int64_shift_left(v_a_boxed_1311_, v_b_boxed_1312_);
v_r_1314_ = lean_box_uint64(v_res_1313_);
return v_r_1314_;
}
}
LEAN_EXPORT lean_object* l_Int64_shiftRight___boxed(lean_object* v_a_1317_, lean_object* v_b_1318_){
_start:
{
uint64_t v_a_boxed_1319_; uint64_t v_b_boxed_1320_; uint64_t v_res_1321_; lean_object* v_r_1322_; 
v_a_boxed_1319_ = lean_unbox_uint64(v_a_1317_);
lean_dec_ref(v_a_1317_);
v_b_boxed_1320_ = lean_unbox_uint64(v_b_1318_);
lean_dec_ref(v_b_1318_);
v_res_1321_ = lean_int64_shift_right(v_a_boxed_1319_, v_b_boxed_1320_);
v_r_1322_ = lean_box_uint64(v_res_1321_);
return v_r_1322_;
}
}
LEAN_EXPORT lean_object* l_Int64_complement___boxed(lean_object* v_a_1324_){
_start:
{
uint64_t v_a_boxed_1325_; uint64_t v_res_1326_; lean_object* v_r_1327_; 
v_a_boxed_1325_ = lean_unbox_uint64(v_a_1324_);
lean_dec_ref(v_a_1324_);
v_res_1326_ = lean_int64_complement(v_a_boxed_1325_);
v_r_1327_ = lean_box_uint64(v_res_1326_);
return v_r_1327_;
}
}
LEAN_EXPORT lean_object* l_Int64_abs___boxed(lean_object* v_a_1329_){
_start:
{
uint64_t v_a_boxed_1330_; uint64_t v_res_1331_; lean_object* v_r_1332_; 
v_a_boxed_1330_ = lean_unbox_uint64(v_a_1329_);
lean_dec_ref(v_a_1329_);
v_res_1331_ = lean_int64_abs(v_a_boxed_1330_);
v_r_1332_ = lean_box_uint64(v_res_1331_);
return v_r_1332_;
}
}
LEAN_EXPORT lean_object* l_Int64_decEq___boxed(lean_object* v_a_1335_, lean_object* v_b_1336_){
_start:
{
uint64_t v_a_boxed_1337_; uint64_t v_b_boxed_1338_; uint8_t v_res_1339_; lean_object* v_r_1340_; 
v_a_boxed_1337_ = lean_unbox_uint64(v_a_1335_);
lean_dec_ref(v_a_1335_);
v_b_boxed_1338_ = lean_unbox_uint64(v_b_1336_);
lean_dec_ref(v_b_1336_);
v_res_1339_ = lean_int64_dec_eq(v_a_boxed_1337_, v_b_boxed_1338_);
v_r_1340_ = lean_box(v_res_1339_);
return v_r_1340_;
}
}
static uint64_t _init_l_instInhabitedInt64___closed__0(void){
_start:
{
lean_object* v___x_1341_; uint64_t v___x_1342_; 
v___x_1341_ = lean_unsigned_to_nat(0u);
v___x_1342_ = lean_int64_of_nat(v___x_1341_);
return v___x_1342_;
}
}
static uint64_t _init_l_instInhabitedInt64(void){
_start:
{
uint64_t v___x_1343_; 
v___x_1343_ = lean_uint64_once(&l_instInhabitedInt64___closed__0, &l_instInhabitedInt64___closed__0_once, _init_l_instInhabitedInt64___closed__0);
return v___x_1343_;
}
}
static lean_object* _init_l_instLTInt64(void){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = lean_box(0);
return v___x_1356_;
}
}
static lean_object* _init_l_instLEInt64(void){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_box(0);
return v___x_1357_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt64(uint64_t v_a_1370_, uint64_t v_b_1371_){
_start:
{
uint8_t v___x_1372_; 
v___x_1372_ = lean_int64_dec_eq(v_a_1370_, v_b_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt64___boxed(lean_object* v_a_1373_, lean_object* v_b_1374_){
_start:
{
uint64_t v_a_boxed_1375_; uint64_t v_b_boxed_1376_; uint8_t v_res_1377_; lean_object* v_r_1378_; 
v_a_boxed_1375_ = lean_unbox_uint64(v_a_1373_);
lean_dec_ref(v_a_1373_);
v_b_boxed_1376_ = lean_unbox_uint64(v_b_1374_);
lean_dec_ref(v_b_1374_);
v_res_1377_ = l_instDecidableEqInt64(v_a_boxed_1375_, v_b_boxed_1376_);
v_r_1378_ = lean_box(v_res_1377_);
return v_r_1378_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt64___boxed(lean_object* v_b_1380_){
_start:
{
uint8_t v_b_boxed_1381_; uint64_t v_res_1382_; lean_object* v_r_1383_; 
v_b_boxed_1381_ = lean_unbox(v_b_1380_);
v_res_1382_ = lean_bool_to_int64(v_b_boxed_1381_);
v_r_1383_ = lean_box_uint64(v_res_1382_);
return v_r_1383_;
}
}
LEAN_EXPORT uint8_t l_Int64_decLt___aux__1(uint64_t v_a_1384_, uint64_t v_b_1385_){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1386_ = lean_unsigned_to_nat(64u);
v___x_1387_ = lean_uint64_to_nat(v_a_1384_);
v___x_1388_ = lean_uint64_to_nat(v_b_1385_);
v___x_1389_ = l_BitVec_slt(v___x_1386_, v___x_1387_, v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLt___aux__1___boxed(lean_object* v_a_1390_, lean_object* v_b_1391_){
_start:
{
uint64_t v_a_boxed_1392_; uint64_t v_b_boxed_1393_; uint8_t v_res_1394_; lean_object* v_r_1395_; 
v_a_boxed_1392_ = lean_unbox_uint64(v_a_1390_);
lean_dec_ref(v_a_1390_);
v_b_boxed_1393_ = lean_unbox_uint64(v_b_1391_);
lean_dec_ref(v_b_1391_);
v_res_1394_ = l_Int64_decLt___aux__1(v_a_boxed_1392_, v_b_boxed_1393_);
v_r_1395_ = lean_box(v_res_1394_);
return v_r_1395_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLt___boxed(lean_object* v_a_1398_, lean_object* v_b_1399_){
_start:
{
uint64_t v_a_boxed_1400_; uint64_t v_b_boxed_1401_; uint8_t v_res_1402_; lean_object* v_r_1403_; 
v_a_boxed_1400_ = lean_unbox_uint64(v_a_1398_);
lean_dec_ref(v_a_1398_);
v_b_boxed_1401_ = lean_unbox_uint64(v_b_1399_);
lean_dec_ref(v_b_1399_);
v_res_1402_ = lean_int64_dec_lt(v_a_boxed_1400_, v_b_boxed_1401_);
v_r_1403_ = lean_box(v_res_1402_);
return v_r_1403_;
}
}
LEAN_EXPORT uint8_t l_Int64_decLe___aux__1(uint64_t v_a_1404_, uint64_t v_b_1405_){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1406_ = lean_unsigned_to_nat(64u);
v___x_1407_ = lean_uint64_to_nat(v_a_1404_);
v___x_1408_ = lean_uint64_to_nat(v_b_1405_);
v___x_1409_ = l_BitVec_sle(v___x_1406_, v___x_1407_, v___x_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLe___aux__1___boxed(lean_object* v_a_1410_, lean_object* v_b_1411_){
_start:
{
uint64_t v_a_boxed_1412_; uint64_t v_b_boxed_1413_; uint8_t v_res_1414_; lean_object* v_r_1415_; 
v_a_boxed_1412_ = lean_unbox_uint64(v_a_1410_);
lean_dec_ref(v_a_1410_);
v_b_boxed_1413_ = lean_unbox_uint64(v_b_1411_);
lean_dec_ref(v_b_1411_);
v_res_1414_ = l_Int64_decLe___aux__1(v_a_boxed_1412_, v_b_boxed_1413_);
v_r_1415_ = lean_box(v_res_1414_);
return v_r_1415_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLe___boxed(lean_object* v_a_1418_, lean_object* v_b_1419_){
_start:
{
uint64_t v_a_boxed_1420_; uint64_t v_b_boxed_1421_; uint8_t v_res_1422_; lean_object* v_r_1423_; 
v_a_boxed_1420_ = lean_unbox_uint64(v_a_1418_);
lean_dec_ref(v_a_1418_);
v_b_boxed_1421_ = lean_unbox_uint64(v_b_1419_);
lean_dec_ref(v_b_1419_);
v_res_1422_ = lean_int64_dec_le(v_a_boxed_1420_, v_b_boxed_1421_);
v_r_1423_ = lean_box(v_res_1422_);
return v_r_1423_;
}
}
LEAN_EXPORT uint64_t l_instMaxInt64___lam__0(uint64_t v_x_1424_, uint64_t v_y_1425_){
_start:
{
uint8_t v___x_1426_; 
v___x_1426_ = lean_int64_dec_le(v_x_1424_, v_y_1425_);
if (v___x_1426_ == 0)
{
return v_x_1424_;
}
else
{
return v_y_1425_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt64___lam__0___boxed(lean_object* v_x_1427_, lean_object* v_y_1428_){
_start:
{
uint64_t v_x_boxed_1429_; uint64_t v_y_boxed_1430_; uint64_t v_res_1431_; lean_object* v_r_1432_; 
v_x_boxed_1429_ = lean_unbox_uint64(v_x_1427_);
lean_dec_ref(v_x_1427_);
v_y_boxed_1430_ = lean_unbox_uint64(v_y_1428_);
lean_dec_ref(v_y_1428_);
v_res_1431_ = l_instMaxInt64___lam__0(v_x_boxed_1429_, v_y_boxed_1430_);
v_r_1432_ = lean_box_uint64(v_res_1431_);
return v_r_1432_;
}
}
LEAN_EXPORT uint64_t l_instMinInt64___lam__0(uint64_t v_x_1435_, uint64_t v_y_1436_){
_start:
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_int64_dec_le(v_x_1435_, v_y_1436_);
if (v___x_1437_ == 0)
{
return v_y_1436_;
}
else
{
return v_x_1435_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt64___lam__0___boxed(lean_object* v_x_1438_, lean_object* v_y_1439_){
_start:
{
uint64_t v_x_boxed_1440_; uint64_t v_y_boxed_1441_; uint64_t v_res_1442_; lean_object* v_r_1443_; 
v_x_boxed_1440_ = lean_unbox_uint64(v_x_1438_);
lean_dec_ref(v_x_1438_);
v_y_boxed_1441_ = lean_unbox_uint64(v_y_1439_);
lean_dec_ref(v_y_1439_);
v_res_1442_ = l_instMinInt64___lam__0(v_x_boxed_1440_, v_y_boxed_1441_);
v_r_1443_ = lean_box_uint64(v_res_1442_);
return v_r_1443_;
}
}
static lean_object* _init_l_ISize_size___closed__0(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = l_System_Platform_numBits;
v___x_1447_ = lean_unsigned_to_nat(2u);
v___x_1448_ = lean_nat_pow(v___x_1447_, v___x_1446_);
return v___x_1448_;
}
}
static lean_object* _init_l_ISize_size(void){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_obj_once(&l_ISize_size___closed__0, &l_ISize_size___closed__0_once, _init_l_ISize_size___closed__0);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_ISize_toBitVec(size_t v_x_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_usize_to_nat(v_x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_ISize_toBitVec___boxed(lean_object* v_x_1452_){
_start:
{
size_t v_x_boxed_1453_; lean_object* v_res_1454_; 
v_x_boxed_1453_ = lean_unbox_usize(v_x_1452_);
lean_dec(v_x_1452_);
v_res_1454_ = l_ISize_toBitVec(v_x_boxed_1453_);
return v_res_1454_;
}
}
LEAN_EXPORT size_t l_USize_toISize(size_t v_i_1455_){
_start:
{
return v_i_1455_;
}
}
LEAN_EXPORT lean_object* l_USize_toISize___boxed(lean_object* v_i_1456_){
_start:
{
size_t v_i_boxed_1457_; size_t v_res_1458_; lean_object* v_r_1459_; 
v_i_boxed_1457_ = lean_unbox_usize(v_i_1456_);
lean_dec(v_i_1456_);
v_res_1458_ = l_USize_toISize(v_i_boxed_1457_);
v_r_1459_ = lean_box_usize(v_res_1458_);
return v_r_1459_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofInt___boxed(lean_object* v_i_1461_){
_start:
{
size_t v_res_1462_; lean_object* v_r_1463_; 
v_res_1462_ = lean_isize_of_int(v_i_1461_);
lean_dec(v_i_1461_);
v_r_1463_ = lean_box_usize(v_res_1462_);
return v_r_1463_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofNat___boxed(lean_object* v_n_1465_){
_start:
{
size_t v_res_1466_; lean_object* v_r_1467_; 
v_res_1466_ = lean_isize_of_nat(v_n_1465_);
lean_dec(v_n_1465_);
v_r_1467_ = lean_box_usize(v_res_1466_);
return v_r_1467_;
}
}
LEAN_EXPORT size_t l_Int_toISize(lean_object* v_i_1468_){
_start:
{
size_t v___x_1469_; 
v___x_1469_ = lean_isize_of_int(v_i_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Int_toISize___boxed(lean_object* v_i_1470_){
_start:
{
size_t v_res_1471_; lean_object* v_r_1472_; 
v_res_1471_ = l_Int_toISize(v_i_1470_);
lean_dec(v_i_1470_);
v_r_1472_ = lean_box_usize(v_res_1471_);
return v_r_1472_;
}
}
LEAN_EXPORT size_t l_Nat_toISize(lean_object* v_n_1473_){
_start:
{
size_t v___x_1474_; 
v___x_1474_ = lean_isize_of_nat(v_n_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Nat_toISize___boxed(lean_object* v_n_1475_){
_start:
{
size_t v_res_1476_; lean_object* v_r_1477_; 
v_res_1476_ = l_Nat_toISize(v_n_1475_);
lean_dec(v_n_1475_);
v_r_1477_ = lean_box_usize(v_res_1476_);
return v_r_1477_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt___boxed(lean_object* v_i_1479_){
_start:
{
size_t v_i_boxed_1480_; lean_object* v_res_1481_; 
v_i_boxed_1480_ = lean_unbox_usize(v_i_1479_);
lean_dec(v_i_1479_);
v_res_1481_ = lean_isize_to_int(v_i_boxed_1480_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg(size_t v_i_1482_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = lean_isize_to_int(v_i_1482_);
v___x_1484_ = l_Int_toNat(v___x_1483_);
lean_dec(v___x_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg___boxed(lean_object* v_i_1485_){
_start:
{
size_t v_i_boxed_1486_; lean_object* v_res_1487_; 
v_i_boxed_1486_ = lean_unbox_usize(v_i_1485_);
lean_dec(v_i_1485_);
v_res_1487_ = l_ISize_toNatClampNeg(v_i_boxed_1486_);
return v_res_1487_;
}
}
LEAN_EXPORT size_t l_ISize_ofBitVec(lean_object* v_b_1488_){
_start:
{
size_t v___x_1489_; 
v___x_1489_ = lean_usize_of_nat_mk(v_b_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofBitVec___boxed(lean_object* v_b_1490_){
_start:
{
size_t v_res_1491_; lean_object* v_r_1492_; 
v_res_1491_ = l_ISize_ofBitVec(v_b_1490_);
v_r_1492_ = lean_box_usize(v_res_1491_);
return v_r_1492_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt8___boxed(lean_object* v_a_1494_){
_start:
{
size_t v_a_boxed_1495_; uint8_t v_res_1496_; lean_object* v_r_1497_; 
v_a_boxed_1495_ = lean_unbox_usize(v_a_1494_);
lean_dec(v_a_1494_);
v_res_1496_ = lean_isize_to_int8(v_a_boxed_1495_);
v_r_1497_ = lean_box(v_res_1496_);
return v_r_1497_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt16___boxed(lean_object* v_a_1499_){
_start:
{
size_t v_a_boxed_1500_; uint16_t v_res_1501_; lean_object* v_r_1502_; 
v_a_boxed_1500_ = lean_unbox_usize(v_a_1499_);
lean_dec(v_a_1499_);
v_res_1501_ = lean_isize_to_int16(v_a_boxed_1500_);
v_r_1502_ = lean_box(v_res_1501_);
return v_r_1502_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt32___boxed(lean_object* v_a_1504_){
_start:
{
size_t v_a_boxed_1505_; uint32_t v_res_1506_; lean_object* v_r_1507_; 
v_a_boxed_1505_ = lean_unbox_usize(v_a_1504_);
lean_dec(v_a_1504_);
v_res_1506_ = lean_isize_to_int32(v_a_boxed_1505_);
v_r_1507_ = lean_box_uint32(v_res_1506_);
return v_r_1507_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt64___boxed(lean_object* v_a_1509_){
_start:
{
size_t v_a_boxed_1510_; uint64_t v_res_1511_; lean_object* v_r_1512_; 
v_a_boxed_1510_ = lean_unbox_usize(v_a_1509_);
lean_dec(v_a_1509_);
v_res_1511_ = lean_isize_to_int64(v_a_boxed_1510_);
v_r_1512_ = lean_box_uint64(v_res_1511_);
return v_r_1512_;
}
}
LEAN_EXPORT lean_object* l_Int8_toISize___boxed(lean_object* v_a_1514_){
_start:
{
uint8_t v_a_boxed_1515_; size_t v_res_1516_; lean_object* v_r_1517_; 
v_a_boxed_1515_ = lean_unbox(v_a_1514_);
v_res_1516_ = lean_int8_to_isize(v_a_boxed_1515_);
v_r_1517_ = lean_box_usize(v_res_1516_);
return v_r_1517_;
}
}
LEAN_EXPORT lean_object* l_Int16_toISize___boxed(lean_object* v_a_1519_){
_start:
{
uint16_t v_a_boxed_1520_; size_t v_res_1521_; lean_object* v_r_1522_; 
v_a_boxed_1520_ = lean_unbox(v_a_1519_);
v_res_1521_ = lean_int16_to_isize(v_a_boxed_1520_);
v_r_1522_ = lean_box_usize(v_res_1521_);
return v_r_1522_;
}
}
LEAN_EXPORT lean_object* l_Int32_toISize___boxed(lean_object* v_a_1524_){
_start:
{
uint32_t v_a_boxed_1525_; size_t v_res_1526_; lean_object* v_r_1527_; 
v_a_boxed_1525_ = lean_unbox_uint32(v_a_1524_);
lean_dec(v_a_1524_);
v_res_1526_ = lean_int32_to_isize(v_a_boxed_1525_);
v_r_1527_ = lean_box_usize(v_res_1526_);
return v_r_1527_;
}
}
LEAN_EXPORT lean_object* l_Int64_toISize___boxed(lean_object* v_a_1529_){
_start:
{
uint64_t v_a_boxed_1530_; size_t v_res_1531_; lean_object* v_r_1532_; 
v_a_boxed_1530_ = lean_unbox_uint64(v_a_1529_);
lean_dec_ref(v_a_1529_);
v_res_1531_ = lean_int64_to_isize(v_a_boxed_1530_);
v_r_1532_ = lean_box_usize(v_res_1531_);
return v_r_1532_;
}
}
LEAN_EXPORT lean_object* l_ISize_neg___boxed(lean_object* v_i_1534_){
_start:
{
size_t v_i_boxed_1535_; size_t v_res_1536_; lean_object* v_r_1537_; 
v_i_boxed_1535_ = lean_unbox_usize(v_i_1534_);
lean_dec(v_i_1534_);
v_res_1536_ = lean_isize_neg(v_i_boxed_1535_);
v_r_1537_ = lean_box_usize(v_res_1536_);
return v_r_1537_;
}
}
LEAN_EXPORT lean_object* l_instToStringISize___lam__0(size_t v_i_1538_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_isize_to_int(v_i_1538_);
v___x_1540_ = l_Int_repr(v___x_1539_);
lean_dec(v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_instToStringISize___lam__0___boxed(lean_object* v_i_1541_){
_start:
{
size_t v_i_boxed_1542_; lean_object* v_res_1543_; 
v_i_boxed_1542_ = lean_unbox_usize(v_i_1541_);
lean_dec(v_i_1541_);
v_res_1543_ = l_instToStringISize___lam__0(v_i_boxed_1542_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_instReprISize___lam__0(size_t v_i_1546_, lean_object* v_prec_1547_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1548_ = lean_isize_to_int(v_i_1546_);
v___x_1549_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_1550_ = lean_int_dec_lt(v___x_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = l_Int_repr(v___x_1548_);
lean_dec(v___x_1548_);
v___x_1552_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = l_Int_repr(v___x_1548_);
lean_dec(v___x_1548_);
v___x_1554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
v___x_1555_ = l_Repr_addAppParen(v___x_1554_, v_prec_1547_);
return v___x_1555_;
}
}
}
LEAN_EXPORT lean_object* l_instReprISize___lam__0___boxed(lean_object* v_i_1556_, lean_object* v_prec_1557_){
_start:
{
size_t v_i_boxed_1558_; lean_object* v_res_1559_; 
v_i_boxed_1558_ = lean_unbox_usize(v_i_1556_);
lean_dec(v_i_1556_);
v_res_1559_ = l_instReprISize___lam__0(v_i_boxed_1558_, v_prec_1557_);
lean_dec(v_prec_1557_);
return v_res_1559_;
}
}
static lean_object* _init_l_instReprAtomISize(void){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_box(0);
return v___x_1562_;
}
}
LEAN_EXPORT size_t l_ISize_instOfNat(lean_object* v_n_1565_){
_start:
{
size_t v___x_1566_; 
v___x_1566_ = lean_isize_of_nat(v_n_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_ISize_instOfNat___boxed(lean_object* v_n_1567_){
_start:
{
size_t v_res_1568_; lean_object* v_r_1569_; 
v_res_1568_ = l_ISize_instOfNat(v_n_1567_);
lean_dec(v_n_1567_);
v_r_1569_ = lean_box_usize(v_res_1568_);
return v_r_1569_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__0(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_unsigned_to_nat(2u);
v___x_1573_ = lean_nat_to_int(v___x_1572_);
return v___x_1573_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__1(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_unsigned_to_nat(1u);
v___x_1575_ = l_System_Platform_numBits;
v___x_1576_ = lean_nat_sub(v___x_1575_, v___x_1574_);
return v___x_1576_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__2(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = lean_obj_once(&l_ISize_maxValue___closed__1, &l_ISize_maxValue___closed__1_once, _init_l_ISize_maxValue___closed__1);
v___x_1578_ = lean_obj_once(&l_ISize_maxValue___closed__0, &l_ISize_maxValue___closed__0_once, _init_l_ISize_maxValue___closed__0);
v___x_1579_ = l_Int_pow(v___x_1578_, v___x_1577_);
return v___x_1579_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__3(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_unsigned_to_nat(1u);
v___x_1581_ = lean_nat_to_int(v___x_1580_);
return v___x_1581_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__4(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = lean_obj_once(&l_ISize_maxValue___closed__3, &l_ISize_maxValue___closed__3_once, _init_l_ISize_maxValue___closed__3);
v___x_1583_ = lean_obj_once(&l_ISize_maxValue___closed__2, &l_ISize_maxValue___closed__2_once, _init_l_ISize_maxValue___closed__2);
v___x_1584_ = lean_int_sub(v___x_1583_, v___x_1582_);
return v___x_1584_;
}
}
static size_t _init_l_ISize_maxValue___closed__5(void){
_start:
{
lean_object* v___x_1585_; size_t v___x_1586_; 
v___x_1585_ = lean_obj_once(&l_ISize_maxValue___closed__4, &l_ISize_maxValue___closed__4_once, _init_l_ISize_maxValue___closed__4);
v___x_1586_ = lean_isize_of_int(v___x_1585_);
return v___x_1586_;
}
}
static size_t _init_l_ISize_maxValue(void){
_start:
{
size_t v___x_1587_; 
v___x_1587_ = lean_usize_once(&l_ISize_maxValue___closed__5, &l_ISize_maxValue___closed__5_once, _init_l_ISize_maxValue___closed__5);
return v___x_1587_;
}
}
static lean_object* _init_l_ISize_minValue___closed__0(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = lean_obj_once(&l_ISize_maxValue___closed__2, &l_ISize_maxValue___closed__2_once, _init_l_ISize_maxValue___closed__2);
v___x_1589_ = lean_int_neg(v___x_1588_);
return v___x_1589_;
}
}
static size_t _init_l_ISize_minValue___closed__1(void){
_start:
{
lean_object* v___x_1590_; size_t v___x_1591_; 
v___x_1590_ = lean_obj_once(&l_ISize_minValue___closed__0, &l_ISize_minValue___closed__0_once, _init_l_ISize_minValue___closed__0);
v___x_1591_ = lean_isize_of_int(v___x_1590_);
return v___x_1591_;
}
}
static size_t _init_l_ISize_minValue(void){
_start:
{
size_t v___x_1592_; 
v___x_1592_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
return v___x_1592_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntLE___redArg(lean_object* v_i_1593_){
_start:
{
size_t v___x_1594_; 
v___x_1594_ = lean_isize_of_int(v_i_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntLE___redArg___boxed(lean_object* v_i_1595_){
_start:
{
size_t v_res_1596_; lean_object* v_r_1597_; 
v_res_1596_ = l_ISize_ofIntLE___redArg(v_i_1595_);
lean_dec(v_i_1595_);
v_r_1597_ = lean_box_usize(v_res_1596_);
return v_r_1597_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntLE(lean_object* v_i_1598_, lean_object* v___hl_1599_, lean_object* v___hr_1600_){
_start:
{
size_t v___x_1601_; 
v___x_1601_ = lean_isize_of_int(v_i_1598_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntLE___boxed(lean_object* v_i_1602_, lean_object* v___hl_1603_, lean_object* v___hr_1604_){
_start:
{
size_t v_res_1605_; lean_object* v_r_1606_; 
v_res_1605_ = l_ISize_ofIntLE(v_i_1602_, v___hl_1603_, v___hr_1604_);
lean_dec(v_i_1602_);
v_r_1606_ = lean_box_usize(v_res_1605_);
return v_r_1606_;
}
}
static lean_object* _init_l_ISize_ofIntClamp___closed__0(void){
_start:
{
size_t v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
v___x_1608_ = lean_isize_to_int(v___x_1607_);
return v___x_1608_;
}
}
static lean_object* _init_l_ISize_ofIntClamp___closed__1(void){
_start:
{
size_t v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_usize_once(&l_ISize_maxValue___closed__5, &l_ISize_maxValue___closed__5_once, _init_l_ISize_maxValue___closed__5);
v___x_1610_ = lean_isize_to_int(v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntClamp(lean_object* v_i_1611_){
_start:
{
size_t v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1612_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
v___x_1613_ = lean_obj_once(&l_ISize_ofIntClamp___closed__0, &l_ISize_ofIntClamp___closed__0_once, _init_l_ISize_ofIntClamp___closed__0);
v___x_1614_ = lean_int_dec_le(v___x_1613_, v_i_1611_);
if (v___x_1614_ == 0)
{
return v___x_1612_;
}
else
{
size_t v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1615_ = lean_usize_once(&l_ISize_maxValue___closed__5, &l_ISize_maxValue___closed__5_once, _init_l_ISize_maxValue___closed__5);
v___x_1616_ = lean_obj_once(&l_ISize_ofIntClamp___closed__1, &l_ISize_ofIntClamp___closed__1_once, _init_l_ISize_ofIntClamp___closed__1);
v___x_1617_ = lean_int_dec_le(v_i_1611_, v___x_1616_);
if (v___x_1617_ == 0)
{
return v___x_1615_;
}
else
{
size_t v___x_1618_; 
v___x_1618_ = lean_isize_of_int(v_i_1611_);
return v___x_1618_;
}
}
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntClamp___boxed(lean_object* v_i_1619_){
_start:
{
size_t v_res_1620_; lean_object* v_r_1621_; 
v_res_1620_ = l_ISize_ofIntClamp(v_i_1619_);
lean_dec(v_i_1619_);
v_r_1621_ = lean_box_usize(v_res_1620_);
return v_r_1621_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntTruncate(lean_object* v_i_1622_){
_start:
{
size_t v___x_1623_; 
v___x_1623_ = l_ISize_ofIntClamp(v_i_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntTruncate___boxed(lean_object* v_i_1624_){
_start:
{
size_t v_res_1625_; lean_object* v_r_1626_; 
v_res_1625_ = l_ISize_ofIntTruncate(v_i_1624_);
lean_dec(v_i_1624_);
v_r_1626_ = lean_box_usize(v_res_1625_);
return v_r_1626_;
}
}
LEAN_EXPORT lean_object* l_ISize_add___boxed(lean_object* v_a_1629_, lean_object* v_b_1630_){
_start:
{
size_t v_a_boxed_1631_; size_t v_b_boxed_1632_; size_t v_res_1633_; lean_object* v_r_1634_; 
v_a_boxed_1631_ = lean_unbox_usize(v_a_1629_);
lean_dec(v_a_1629_);
v_b_boxed_1632_ = lean_unbox_usize(v_b_1630_);
lean_dec(v_b_1630_);
v_res_1633_ = lean_isize_add(v_a_boxed_1631_, v_b_boxed_1632_);
v_r_1634_ = lean_box_usize(v_res_1633_);
return v_r_1634_;
}
}
LEAN_EXPORT lean_object* l_ISize_sub___boxed(lean_object* v_a_1637_, lean_object* v_b_1638_){
_start:
{
size_t v_a_boxed_1639_; size_t v_b_boxed_1640_; size_t v_res_1641_; lean_object* v_r_1642_; 
v_a_boxed_1639_ = lean_unbox_usize(v_a_1637_);
lean_dec(v_a_1637_);
v_b_boxed_1640_ = lean_unbox_usize(v_b_1638_);
lean_dec(v_b_1638_);
v_res_1641_ = lean_isize_sub(v_a_boxed_1639_, v_b_boxed_1640_);
v_r_1642_ = lean_box_usize(v_res_1641_);
return v_r_1642_;
}
}
LEAN_EXPORT lean_object* l_ISize_mul___boxed(lean_object* v_a_1645_, lean_object* v_b_1646_){
_start:
{
size_t v_a_boxed_1647_; size_t v_b_boxed_1648_; size_t v_res_1649_; lean_object* v_r_1650_; 
v_a_boxed_1647_ = lean_unbox_usize(v_a_1645_);
lean_dec(v_a_1645_);
v_b_boxed_1648_ = lean_unbox_usize(v_b_1646_);
lean_dec(v_b_1646_);
v_res_1649_ = lean_isize_mul(v_a_boxed_1647_, v_b_boxed_1648_);
v_r_1650_ = lean_box_usize(v_res_1649_);
return v_r_1650_;
}
}
LEAN_EXPORT lean_object* l_ISize_div___boxed(lean_object* v_a_1653_, lean_object* v_b_1654_){
_start:
{
size_t v_a_boxed_1655_; size_t v_b_boxed_1656_; size_t v_res_1657_; lean_object* v_r_1658_; 
v_a_boxed_1655_ = lean_unbox_usize(v_a_1653_);
lean_dec(v_a_1653_);
v_b_boxed_1656_ = lean_unbox_usize(v_b_1654_);
lean_dec(v_b_1654_);
v_res_1657_ = lean_isize_div(v_a_boxed_1655_, v_b_boxed_1656_);
v_r_1658_ = lean_box_usize(v_res_1657_);
return v_r_1658_;
}
}
static size_t _init_l_ISize_pow___closed__0(void){
_start:
{
lean_object* v___x_1659_; size_t v___x_1660_; 
v___x_1659_ = lean_unsigned_to_nat(1u);
v___x_1660_ = lean_isize_of_nat(v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT size_t l_ISize_pow(size_t v_x_1661_, lean_object* v_n_1662_){
_start:
{
lean_object* v_zero_1663_; uint8_t v_isZero_1664_; 
v_zero_1663_ = lean_unsigned_to_nat(0u);
v_isZero_1664_ = lean_nat_dec_eq(v_n_1662_, v_zero_1663_);
if (v_isZero_1664_ == 1)
{
size_t v___x_1665_; 
v___x_1665_ = lean_usize_once(&l_ISize_pow___closed__0, &l_ISize_pow___closed__0_once, _init_l_ISize_pow___closed__0);
return v___x_1665_;
}
else
{
lean_object* v_one_1666_; lean_object* v_n_1667_; size_t v___x_1668_; size_t v___x_1669_; 
v_one_1666_ = lean_unsigned_to_nat(1u);
v_n_1667_ = lean_nat_sub(v_n_1662_, v_one_1666_);
v___x_1668_ = l_ISize_pow(v_x_1661_, v_n_1667_);
lean_dec(v_n_1667_);
v___x_1669_ = lean_isize_mul(v___x_1668_, v_x_1661_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l_ISize_pow___boxed(lean_object* v_x_1670_, lean_object* v_n_1671_){
_start:
{
size_t v_x_boxed_1672_; size_t v_res_1673_; lean_object* v_r_1674_; 
v_x_boxed_1672_ = lean_unbox_usize(v_x_1670_);
lean_dec(v_x_1670_);
v_res_1673_ = l_ISize_pow(v_x_boxed_1672_, v_n_1671_);
lean_dec(v_n_1671_);
v_r_1674_ = lean_box_usize(v_res_1673_);
return v_r_1674_;
}
}
LEAN_EXPORT lean_object* l_ISize_mod___boxed(lean_object* v_a_1677_, lean_object* v_b_1678_){
_start:
{
size_t v_a_boxed_1679_; size_t v_b_boxed_1680_; size_t v_res_1681_; lean_object* v_r_1682_; 
v_a_boxed_1679_ = lean_unbox_usize(v_a_1677_);
lean_dec(v_a_1677_);
v_b_boxed_1680_ = lean_unbox_usize(v_b_1678_);
lean_dec(v_b_1678_);
v_res_1681_ = lean_isize_mod(v_a_boxed_1679_, v_b_boxed_1680_);
v_r_1682_ = lean_box_usize(v_res_1681_);
return v_r_1682_;
}
}
LEAN_EXPORT lean_object* l_ISize_land___boxed(lean_object* v_a_1685_, lean_object* v_b_1686_){
_start:
{
size_t v_a_boxed_1687_; size_t v_b_boxed_1688_; size_t v_res_1689_; lean_object* v_r_1690_; 
v_a_boxed_1687_ = lean_unbox_usize(v_a_1685_);
lean_dec(v_a_1685_);
v_b_boxed_1688_ = lean_unbox_usize(v_b_1686_);
lean_dec(v_b_1686_);
v_res_1689_ = lean_isize_land(v_a_boxed_1687_, v_b_boxed_1688_);
v_r_1690_ = lean_box_usize(v_res_1689_);
return v_r_1690_;
}
}
LEAN_EXPORT lean_object* l_ISize_lor___boxed(lean_object* v_a_1693_, lean_object* v_b_1694_){
_start:
{
size_t v_a_boxed_1695_; size_t v_b_boxed_1696_; size_t v_res_1697_; lean_object* v_r_1698_; 
v_a_boxed_1695_ = lean_unbox_usize(v_a_1693_);
lean_dec(v_a_1693_);
v_b_boxed_1696_ = lean_unbox_usize(v_b_1694_);
lean_dec(v_b_1694_);
v_res_1697_ = lean_isize_lor(v_a_boxed_1695_, v_b_boxed_1696_);
v_r_1698_ = lean_box_usize(v_res_1697_);
return v_r_1698_;
}
}
LEAN_EXPORT lean_object* l_ISize_xor___boxed(lean_object* v_a_1701_, lean_object* v_b_1702_){
_start:
{
size_t v_a_boxed_1703_; size_t v_b_boxed_1704_; size_t v_res_1705_; lean_object* v_r_1706_; 
v_a_boxed_1703_ = lean_unbox_usize(v_a_1701_);
lean_dec(v_a_1701_);
v_b_boxed_1704_ = lean_unbox_usize(v_b_1702_);
lean_dec(v_b_1702_);
v_res_1705_ = lean_isize_xor(v_a_boxed_1703_, v_b_boxed_1704_);
v_r_1706_ = lean_box_usize(v_res_1705_);
return v_r_1706_;
}
}
LEAN_EXPORT lean_object* l_ISize_shiftLeft___boxed(lean_object* v_a_1709_, lean_object* v_b_1710_){
_start:
{
size_t v_a_boxed_1711_; size_t v_b_boxed_1712_; size_t v_res_1713_; lean_object* v_r_1714_; 
v_a_boxed_1711_ = lean_unbox_usize(v_a_1709_);
lean_dec(v_a_1709_);
v_b_boxed_1712_ = lean_unbox_usize(v_b_1710_);
lean_dec(v_b_1710_);
v_res_1713_ = lean_isize_shift_left(v_a_boxed_1711_, v_b_boxed_1712_);
v_r_1714_ = lean_box_usize(v_res_1713_);
return v_r_1714_;
}
}
LEAN_EXPORT lean_object* l_ISize_shiftRight___boxed(lean_object* v_a_1717_, lean_object* v_b_1718_){
_start:
{
size_t v_a_boxed_1719_; size_t v_b_boxed_1720_; size_t v_res_1721_; lean_object* v_r_1722_; 
v_a_boxed_1719_ = lean_unbox_usize(v_a_1717_);
lean_dec(v_a_1717_);
v_b_boxed_1720_ = lean_unbox_usize(v_b_1718_);
lean_dec(v_b_1718_);
v_res_1721_ = lean_isize_shift_right(v_a_boxed_1719_, v_b_boxed_1720_);
v_r_1722_ = lean_box_usize(v_res_1721_);
return v_r_1722_;
}
}
LEAN_EXPORT lean_object* l_ISize_complement___boxed(lean_object* v_a_1724_){
_start:
{
size_t v_a_boxed_1725_; size_t v_res_1726_; lean_object* v_r_1727_; 
v_a_boxed_1725_ = lean_unbox_usize(v_a_1724_);
lean_dec(v_a_1724_);
v_res_1726_ = lean_isize_complement(v_a_boxed_1725_);
v_r_1727_ = lean_box_usize(v_res_1726_);
return v_r_1727_;
}
}
LEAN_EXPORT lean_object* l_ISize_abs___boxed(lean_object* v_a_1729_){
_start:
{
size_t v_a_boxed_1730_; size_t v_res_1731_; lean_object* v_r_1732_; 
v_a_boxed_1730_ = lean_unbox_usize(v_a_1729_);
lean_dec(v_a_1729_);
v_res_1731_ = lean_isize_abs(v_a_boxed_1730_);
v_r_1732_ = lean_box_usize(v_res_1731_);
return v_r_1732_;
}
}
LEAN_EXPORT lean_object* l_ISize_decEq___boxed(lean_object* v_a_1735_, lean_object* v_b_1736_){
_start:
{
size_t v_a_boxed_1737_; size_t v_b_boxed_1738_; uint8_t v_res_1739_; lean_object* v_r_1740_; 
v_a_boxed_1737_ = lean_unbox_usize(v_a_1735_);
lean_dec(v_a_1735_);
v_b_boxed_1738_ = lean_unbox_usize(v_b_1736_);
lean_dec(v_b_1736_);
v_res_1739_ = lean_isize_dec_eq(v_a_boxed_1737_, v_b_boxed_1738_);
v_r_1740_ = lean_box(v_res_1739_);
return v_r_1740_;
}
}
static size_t _init_l_instInhabitedISize___closed__0(void){
_start:
{
lean_object* v___x_1741_; size_t v___x_1742_; 
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = lean_isize_of_nat(v___x_1741_);
return v___x_1742_;
}
}
static size_t _init_l_instInhabitedISize(void){
_start:
{
size_t v___x_1743_; 
v___x_1743_ = lean_usize_once(&l_instInhabitedISize___closed__0, &l_instInhabitedISize___closed__0_once, _init_l_instInhabitedISize___closed__0);
return v___x_1743_;
}
}
static lean_object* _init_l_instLTISize(void){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_box(0);
return v___x_1756_;
}
}
static lean_object* _init_l_instLEISize(void){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_box(0);
return v___x_1757_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqISize(size_t v_a_1770_, size_t v_b_1771_){
_start:
{
uint8_t v___x_1772_; 
v___x_1772_ = lean_isize_dec_eq(v_a_1770_, v_b_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqISize___boxed(lean_object* v_a_1773_, lean_object* v_b_1774_){
_start:
{
size_t v_a_boxed_1775_; size_t v_b_boxed_1776_; uint8_t v_res_1777_; lean_object* v_r_1778_; 
v_a_boxed_1775_ = lean_unbox_usize(v_a_1773_);
lean_dec(v_a_1773_);
v_b_boxed_1776_ = lean_unbox_usize(v_b_1774_);
lean_dec(v_b_1774_);
v_res_1777_ = l_instDecidableEqISize(v_a_boxed_1775_, v_b_boxed_1776_);
v_r_1778_ = lean_box(v_res_1777_);
return v_r_1778_;
}
}
LEAN_EXPORT lean_object* l_Bool_toISize___boxed(lean_object* v_b_1780_){
_start:
{
uint8_t v_b_boxed_1781_; size_t v_res_1782_; lean_object* v_r_1783_; 
v_b_boxed_1781_ = lean_unbox(v_b_1780_);
v_res_1782_ = lean_bool_to_isize(v_b_boxed_1781_);
v_r_1783_ = lean_box_usize(v_res_1782_);
return v_r_1783_;
}
}
LEAN_EXPORT uint8_t l_ISize_decLt___aux__1(size_t v_a_1784_, size_t v_b_1785_){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1786_ = l_System_Platform_numBits;
v___x_1787_ = lean_usize_to_nat(v_a_1784_);
v___x_1788_ = lean_usize_to_nat(v_b_1785_);
v___x_1789_ = l_BitVec_slt(v___x_1786_, v___x_1787_, v___x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLt___aux__1___boxed(lean_object* v_a_1790_, lean_object* v_b_1791_){
_start:
{
size_t v_a_boxed_1792_; size_t v_b_boxed_1793_; uint8_t v_res_1794_; lean_object* v_r_1795_; 
v_a_boxed_1792_ = lean_unbox_usize(v_a_1790_);
lean_dec(v_a_1790_);
v_b_boxed_1793_ = lean_unbox_usize(v_b_1791_);
lean_dec(v_b_1791_);
v_res_1794_ = l_ISize_decLt___aux__1(v_a_boxed_1792_, v_b_boxed_1793_);
v_r_1795_ = lean_box(v_res_1794_);
return v_r_1795_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLt___boxed(lean_object* v_a_1798_, lean_object* v_b_1799_){
_start:
{
size_t v_a_boxed_1800_; size_t v_b_boxed_1801_; uint8_t v_res_1802_; lean_object* v_r_1803_; 
v_a_boxed_1800_ = lean_unbox_usize(v_a_1798_);
lean_dec(v_a_1798_);
v_b_boxed_1801_ = lean_unbox_usize(v_b_1799_);
lean_dec(v_b_1799_);
v_res_1802_ = lean_isize_dec_lt(v_a_boxed_1800_, v_b_boxed_1801_);
v_r_1803_ = lean_box(v_res_1802_);
return v_r_1803_;
}
}
LEAN_EXPORT uint8_t l_ISize_decLe___aux__1(size_t v_a_1804_, size_t v_b_1805_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1806_ = l_System_Platform_numBits;
v___x_1807_ = lean_usize_to_nat(v_a_1804_);
v___x_1808_ = lean_usize_to_nat(v_b_1805_);
v___x_1809_ = l_BitVec_sle(v___x_1806_, v___x_1807_, v___x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLe___aux__1___boxed(lean_object* v_a_1810_, lean_object* v_b_1811_){
_start:
{
size_t v_a_boxed_1812_; size_t v_b_boxed_1813_; uint8_t v_res_1814_; lean_object* v_r_1815_; 
v_a_boxed_1812_ = lean_unbox_usize(v_a_1810_);
lean_dec(v_a_1810_);
v_b_boxed_1813_ = lean_unbox_usize(v_b_1811_);
lean_dec(v_b_1811_);
v_res_1814_ = l_ISize_decLe___aux__1(v_a_boxed_1812_, v_b_boxed_1813_);
v_r_1815_ = lean_box(v_res_1814_);
return v_r_1815_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLe___boxed(lean_object* v_a_1818_, lean_object* v_b_1819_){
_start:
{
size_t v_a_boxed_1820_; size_t v_b_boxed_1821_; uint8_t v_res_1822_; lean_object* v_r_1823_; 
v_a_boxed_1820_ = lean_unbox_usize(v_a_1818_);
lean_dec(v_a_1818_);
v_b_boxed_1821_ = lean_unbox_usize(v_b_1819_);
lean_dec(v_b_1819_);
v_res_1822_ = lean_isize_dec_le(v_a_boxed_1820_, v_b_boxed_1821_);
v_r_1823_ = lean_box(v_res_1822_);
return v_r_1823_;
}
}
LEAN_EXPORT size_t l_instMaxISize___lam__0(size_t v_x_1824_, size_t v_y_1825_){
_start:
{
uint8_t v___x_1826_; 
v___x_1826_ = lean_isize_dec_le(v_x_1824_, v_y_1825_);
if (v___x_1826_ == 0)
{
return v_x_1824_;
}
else
{
return v_y_1825_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxISize___lam__0___boxed(lean_object* v_x_1827_, lean_object* v_y_1828_){
_start:
{
size_t v_x_boxed_1829_; size_t v_y_boxed_1830_; size_t v_res_1831_; lean_object* v_r_1832_; 
v_x_boxed_1829_ = lean_unbox_usize(v_x_1827_);
lean_dec(v_x_1827_);
v_y_boxed_1830_ = lean_unbox_usize(v_y_1828_);
lean_dec(v_y_1828_);
v_res_1831_ = l_instMaxISize___lam__0(v_x_boxed_1829_, v_y_boxed_1830_);
v_r_1832_ = lean_box_usize(v_res_1831_);
return v_r_1832_;
}
}
LEAN_EXPORT size_t l_instMinISize___lam__0(size_t v_x_1835_, size_t v_y_1836_){
_start:
{
uint8_t v___x_1837_; 
v___x_1837_ = lean_isize_dec_le(v_x_1835_, v_y_1836_);
if (v___x_1837_ == 0)
{
return v_y_1836_;
}
else
{
return v_x_1835_;
}
}
}
LEAN_EXPORT lean_object* l_instMinISize___lam__0___boxed(lean_object* v_x_1838_, lean_object* v_y_1839_){
_start:
{
size_t v_x_boxed_1840_; size_t v_y_boxed_1841_; size_t v_res_1842_; lean_object* v_r_1843_; 
v_x_boxed_1840_ = lean_unbox_usize(v_x_1838_);
lean_dec(v_x_1838_);
v_y_boxed_1841_ = lean_unbox_usize(v_y_1839_);
lean_dec(v_y_1839_);
v_res_1842_ = l_instMinISize___lam__0(v_x_boxed_1840_, v_y_boxed_1841_);
v_r_1843_ = lean_box_usize(v_res_1842_);
return v_r_1843_;
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
