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
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_obj_once(&l_Int8_ofIntClamp___closed__1, &l_Int8_ofIntClamp___closed__1_once, _init_l_Int8_ofIntClamp___closed__1);
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
LEAN_EXPORT lean_object* l_Int8_ofIntClamp___boxed(lean_object* v_i_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Int8_ofIntClamp(v_i_119_);
lean_dec(v_i_119_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
LEAN_EXPORT uint8_t l_Int8_ofIntTruncate(lean_object* v_i_122_){
_start:
{
uint8_t v___x_123_; 
v___x_123_ = l_Int8_ofIntClamp(v_i_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Int8_ofIntTruncate___boxed(lean_object* v_i_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_Int8_ofIntTruncate(v_i_124_);
lean_dec(v_i_124_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT lean_object* l_Int8_add___boxed(lean_object* v_a_129_, lean_object* v_b_130_){
_start:
{
uint8_t v_a_boxed_131_; uint8_t v_b_boxed_132_; uint8_t v_res_133_; lean_object* v_r_134_; 
v_a_boxed_131_ = lean_unbox(v_a_129_);
v_b_boxed_132_ = lean_unbox(v_b_130_);
v_res_133_ = lean_int8_add(v_a_boxed_131_, v_b_boxed_132_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT lean_object* l_Int8_sub___boxed(lean_object* v_a_137_, lean_object* v_b_138_){
_start:
{
uint8_t v_a_boxed_139_; uint8_t v_b_boxed_140_; uint8_t v_res_141_; lean_object* v_r_142_; 
v_a_boxed_139_ = lean_unbox(v_a_137_);
v_b_boxed_140_ = lean_unbox(v_b_138_);
v_res_141_ = lean_int8_sub(v_a_boxed_139_, v_b_boxed_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT lean_object* l_Int8_mul___boxed(lean_object* v_a_145_, lean_object* v_b_146_){
_start:
{
uint8_t v_a_boxed_147_; uint8_t v_b_boxed_148_; uint8_t v_res_149_; lean_object* v_r_150_; 
v_a_boxed_147_ = lean_unbox(v_a_145_);
v_b_boxed_148_ = lean_unbox(v_b_146_);
v_res_149_ = lean_int8_mul(v_a_boxed_147_, v_b_boxed_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l_Int8_div___boxed(lean_object* v_a_153_, lean_object* v_b_154_){
_start:
{
uint8_t v_a_boxed_155_; uint8_t v_b_boxed_156_; uint8_t v_res_157_; lean_object* v_r_158_; 
v_a_boxed_155_ = lean_unbox(v_a_153_);
v_b_boxed_156_ = lean_unbox(v_b_154_);
v_res_157_ = lean_int8_div(v_a_boxed_155_, v_b_boxed_156_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
static uint8_t _init_l_Int8_pow___closed__0(void){
_start:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(1u);
v___x_160_ = lean_int8_of_nat(v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT uint8_t l_Int8_pow(uint8_t v_x_161_, lean_object* v_n_162_){
_start:
{
lean_object* v_zero_163_; uint8_t v_isZero_164_; 
v_zero_163_ = lean_unsigned_to_nat(0u);
v_isZero_164_ = lean_nat_dec_eq(v_n_162_, v_zero_163_);
if (v_isZero_164_ == 1)
{
uint8_t v___x_165_; 
v___x_165_ = lean_uint8_once(&l_Int8_pow___closed__0, &l_Int8_pow___closed__0_once, _init_l_Int8_pow___closed__0);
return v___x_165_;
}
else
{
lean_object* v_one_166_; lean_object* v_n_167_; uint8_t v___x_168_; uint8_t v___x_169_; 
v_one_166_ = lean_unsigned_to_nat(1u);
v_n_167_ = lean_nat_sub(v_n_162_, v_one_166_);
v___x_168_ = l_Int8_pow(v_x_161_, v_n_167_);
lean_dec(v_n_167_);
v___x_169_ = lean_int8_mul(v___x_168_, v_x_161_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Int8_pow___boxed(lean_object* v_x_170_, lean_object* v_n_171_){
_start:
{
uint8_t v_x_boxed_172_; uint8_t v_res_173_; lean_object* v_r_174_; 
v_x_boxed_172_ = lean_unbox(v_x_170_);
v_res_173_ = l_Int8_pow(v_x_boxed_172_, v_n_171_);
lean_dec(v_n_171_);
v_r_174_ = lean_box(v_res_173_);
return v_r_174_;
}
}
LEAN_EXPORT lean_object* l_Int8_mod___boxed(lean_object* v_a_177_, lean_object* v_b_178_){
_start:
{
uint8_t v_a_boxed_179_; uint8_t v_b_boxed_180_; uint8_t v_res_181_; lean_object* v_r_182_; 
v_a_boxed_179_ = lean_unbox(v_a_177_);
v_b_boxed_180_ = lean_unbox(v_b_178_);
v_res_181_ = lean_int8_mod(v_a_boxed_179_, v_b_boxed_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT lean_object* l_Int8_land___boxed(lean_object* v_a_185_, lean_object* v_b_186_){
_start:
{
uint8_t v_a_boxed_187_; uint8_t v_b_boxed_188_; uint8_t v_res_189_; lean_object* v_r_190_; 
v_a_boxed_187_ = lean_unbox(v_a_185_);
v_b_boxed_188_ = lean_unbox(v_b_186_);
v_res_189_ = lean_int8_land(v_a_boxed_187_, v_b_boxed_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
LEAN_EXPORT lean_object* l_Int8_lor___boxed(lean_object* v_a_193_, lean_object* v_b_194_){
_start:
{
uint8_t v_a_boxed_195_; uint8_t v_b_boxed_196_; uint8_t v_res_197_; lean_object* v_r_198_; 
v_a_boxed_195_ = lean_unbox(v_a_193_);
v_b_boxed_196_ = lean_unbox(v_b_194_);
v_res_197_ = lean_int8_lor(v_a_boxed_195_, v_b_boxed_196_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT lean_object* l_Int8_xor___boxed(lean_object* v_a_201_, lean_object* v_b_202_){
_start:
{
uint8_t v_a_boxed_203_; uint8_t v_b_boxed_204_; uint8_t v_res_205_; lean_object* v_r_206_; 
v_a_boxed_203_ = lean_unbox(v_a_201_);
v_b_boxed_204_ = lean_unbox(v_b_202_);
v_res_205_ = lean_int8_xor(v_a_boxed_203_, v_b_boxed_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT lean_object* l_Int8_shiftLeft___boxed(lean_object* v_a_209_, lean_object* v_b_210_){
_start:
{
uint8_t v_a_boxed_211_; uint8_t v_b_boxed_212_; uint8_t v_res_213_; lean_object* v_r_214_; 
v_a_boxed_211_ = lean_unbox(v_a_209_);
v_b_boxed_212_ = lean_unbox(v_b_210_);
v_res_213_ = lean_int8_shift_left(v_a_boxed_211_, v_b_boxed_212_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT lean_object* l_Int8_shiftRight___boxed(lean_object* v_a_217_, lean_object* v_b_218_){
_start:
{
uint8_t v_a_boxed_219_; uint8_t v_b_boxed_220_; uint8_t v_res_221_; lean_object* v_r_222_; 
v_a_boxed_219_ = lean_unbox(v_a_217_);
v_b_boxed_220_ = lean_unbox(v_b_218_);
v_res_221_ = lean_int8_shift_right(v_a_boxed_219_, v_b_boxed_220_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT lean_object* l_Int8_complement___boxed(lean_object* v_a_224_){
_start:
{
uint8_t v_a_boxed_225_; uint8_t v_res_226_; lean_object* v_r_227_; 
v_a_boxed_225_ = lean_unbox(v_a_224_);
v_res_226_ = lean_int8_complement(v_a_boxed_225_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l_Int8_abs___boxed(lean_object* v_a_229_){
_start:
{
uint8_t v_a_boxed_230_; uint8_t v_res_231_; lean_object* v_r_232_; 
v_a_boxed_230_ = lean_unbox(v_a_229_);
v_res_231_ = lean_int8_abs(v_a_boxed_230_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT lean_object* l_Int8_decEq___boxed(lean_object* v_a_235_, lean_object* v_b_236_){
_start:
{
uint8_t v_a_boxed_237_; uint8_t v_b_boxed_238_; uint8_t v_res_239_; lean_object* v_r_240_; 
v_a_boxed_237_ = lean_unbox(v_a_235_);
v_b_boxed_238_ = lean_unbox(v_b_236_);
v_res_239_ = lean_int8_dec_eq(v_a_boxed_237_, v_b_boxed_238_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
static uint8_t _init_l_instInhabitedInt8___closed__0(void){
_start:
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_int8_of_nat(v___x_241_);
return v___x_242_;
}
}
static uint8_t _init_l_instInhabitedInt8(void){
_start:
{
uint8_t v___x_243_; 
v___x_243_ = lean_uint8_once(&l_instInhabitedInt8___closed__0, &l_instInhabitedInt8___closed__0_once, _init_l_instInhabitedInt8___closed__0);
return v___x_243_;
}
}
static lean_object* _init_l_instLTInt8(void){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = lean_box(0);
return v___x_256_;
}
}
static lean_object* _init_l_instLEInt8(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_box(0);
return v___x_257_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt8(uint8_t v_a_270_, uint8_t v_b_271_){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = lean_int8_dec_eq(v_a_270_, v_b_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt8___boxed(lean_object* v_a_273_, lean_object* v_b_274_){
_start:
{
uint8_t v_a_boxed_275_; uint8_t v_b_boxed_276_; uint8_t v_res_277_; lean_object* v_r_278_; 
v_a_boxed_275_ = lean_unbox(v_a_273_);
v_b_boxed_276_ = lean_unbox(v_b_274_);
v_res_277_ = l_instDecidableEqInt8(v_a_boxed_275_, v_b_boxed_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt8___boxed(lean_object* v_b_280_){
_start:
{
uint8_t v_b_boxed_281_; uint8_t v_res_282_; lean_object* v_r_283_; 
v_b_boxed_281_ = lean_unbox(v_b_280_);
v_res_282_ = lean_bool_to_int8(v_b_boxed_281_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT uint8_t l_Int8_decLt___aux__1(uint8_t v_a_284_, uint8_t v_b_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_286_ = lean_unsigned_to_nat(8u);
v___x_287_ = lean_uint8_to_nat(v_a_284_);
v___x_288_ = lean_uint8_to_nat(v_b_285_);
v___x_289_ = l_BitVec_slt(v___x_286_, v___x_287_, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLt___aux__1___boxed(lean_object* v_a_290_, lean_object* v_b_291_){
_start:
{
uint8_t v_a_boxed_292_; uint8_t v_b_boxed_293_; uint8_t v_res_294_; lean_object* v_r_295_; 
v_a_boxed_292_ = lean_unbox(v_a_290_);
v_b_boxed_293_ = lean_unbox(v_b_291_);
v_res_294_ = l_Int8_decLt___aux__1(v_a_boxed_292_, v_b_boxed_293_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLt___boxed(lean_object* v_a_298_, lean_object* v_b_299_){
_start:
{
uint8_t v_a_boxed_300_; uint8_t v_b_boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_a_boxed_300_ = lean_unbox(v_a_298_);
v_b_boxed_301_ = lean_unbox(v_b_299_);
v_res_302_ = lean_int8_dec_lt(v_a_boxed_300_, v_b_boxed_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
LEAN_EXPORT uint8_t l_Int8_decLe___aux__1(uint8_t v_a_304_, uint8_t v_b_305_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_306_ = lean_unsigned_to_nat(8u);
v___x_307_ = lean_uint8_to_nat(v_a_304_);
v___x_308_ = lean_uint8_to_nat(v_b_305_);
v___x_309_ = l_BitVec_sle(v___x_306_, v___x_307_, v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLe___aux__1___boxed(lean_object* v_a_310_, lean_object* v_b_311_){
_start:
{
uint8_t v_a_boxed_312_; uint8_t v_b_boxed_313_; uint8_t v_res_314_; lean_object* v_r_315_; 
v_a_boxed_312_ = lean_unbox(v_a_310_);
v_b_boxed_313_ = lean_unbox(v_b_311_);
v_res_314_ = l_Int8_decLe___aux__1(v_a_boxed_312_, v_b_boxed_313_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT lean_object* l_Int8_decLe___boxed(lean_object* v_a_318_, lean_object* v_b_319_){
_start:
{
uint8_t v_a_boxed_320_; uint8_t v_b_boxed_321_; uint8_t v_res_322_; lean_object* v_r_323_; 
v_a_boxed_320_ = lean_unbox(v_a_318_);
v_b_boxed_321_ = lean_unbox(v_b_319_);
v_res_322_ = lean_int8_dec_le(v_a_boxed_320_, v_b_boxed_321_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT uint8_t l_instMaxInt8___lam__0(uint8_t v_x_324_, uint8_t v_y_325_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_int8_dec_le(v_x_324_, v_y_325_);
if (v___x_326_ == 0)
{
return v_x_324_;
}
else
{
return v_y_325_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt8___lam__0___boxed(lean_object* v_x_327_, lean_object* v_y_328_){
_start:
{
uint8_t v_x_boxed_329_; uint8_t v_y_boxed_330_; uint8_t v_res_331_; lean_object* v_r_332_; 
v_x_boxed_329_ = lean_unbox(v_x_327_);
v_y_boxed_330_ = lean_unbox(v_y_328_);
v_res_331_ = l_instMaxInt8___lam__0(v_x_boxed_329_, v_y_boxed_330_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT uint8_t l_instMinInt8___lam__0(uint8_t v_x_335_, uint8_t v_y_336_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = lean_int8_dec_le(v_x_335_, v_y_336_);
if (v___x_337_ == 0)
{
return v_y_336_;
}
else
{
return v_x_335_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt8___lam__0___boxed(lean_object* v_x_338_, lean_object* v_y_339_){
_start:
{
uint8_t v_x_boxed_340_; uint8_t v_y_boxed_341_; uint8_t v_res_342_; lean_object* v_r_343_; 
v_x_boxed_340_ = lean_unbox(v_x_338_);
v_y_boxed_341_ = lean_unbox(v_y_339_);
v_res_342_ = l_instMinInt8___lam__0(v_x_boxed_340_, v_y_boxed_341_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
static lean_object* _init_l_Int16_size(void){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = lean_unsigned_to_nat(65536u);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Int16_toBitVec(uint16_t v_x_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = lean_uint16_to_nat(v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Int16_toBitVec___boxed(lean_object* v_x_349_){
_start:
{
uint16_t v_x_boxed_350_; lean_object* v_res_351_; 
v_x_boxed_350_ = lean_unbox(v_x_349_);
v_res_351_ = l_Int16_toBitVec(v_x_boxed_350_);
return v_res_351_;
}
}
LEAN_EXPORT uint16_t l_UInt16_toInt16(uint16_t v_i_352_){
_start:
{
return v_i_352_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toInt16___boxed(lean_object* v_i_353_){
_start:
{
uint16_t v_i_boxed_354_; uint16_t v_res_355_; lean_object* v_r_356_; 
v_i_boxed_354_ = lean_unbox(v_i_353_);
v_res_355_ = l_UInt16_toInt16(v_i_boxed_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofInt___boxed(lean_object* v_i_358_){
_start:
{
uint16_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = lean_int16_of_int(v_i_358_);
lean_dec(v_i_358_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofNat___boxed(lean_object* v_n_362_){
_start:
{
uint16_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = lean_int16_of_nat(v_n_362_);
lean_dec(v_n_362_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT uint16_t l_Int_toInt16(lean_object* v_i_365_){
_start:
{
uint16_t v___x_366_; 
v___x_366_ = lean_int16_of_int(v_i_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt16___boxed(lean_object* v_i_367_){
_start:
{
uint16_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Int_toInt16(v_i_367_);
lean_dec(v_i_367_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT uint16_t l_Nat_toInt16(lean_object* v_n_370_){
_start:
{
uint16_t v___x_371_; 
v___x_371_ = lean_int16_of_nat(v_n_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt16___boxed(lean_object* v_n_372_){
_start:
{
uint16_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Nat_toInt16(v_n_372_);
lean_dec(v_n_372_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt___boxed(lean_object* v_i_376_){
_start:
{
uint16_t v_i_boxed_377_; lean_object* v_res_378_; 
v_i_boxed_377_ = lean_unbox(v_i_376_);
v_res_378_ = lean_int16_to_int(v_i_boxed_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg(uint16_t v_i_379_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_int16_to_int(v_i_379_);
v___x_381_ = l_Int_toNat(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg___boxed(lean_object* v_i_382_){
_start:
{
uint16_t v_i_boxed_383_; lean_object* v_res_384_; 
v_i_boxed_383_ = lean_unbox(v_i_382_);
v_res_384_ = l_Int16_toNatClampNeg(v_i_boxed_383_);
return v_res_384_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofBitVec(lean_object* v_b_385_){
_start:
{
uint16_t v___x_386_; 
v___x_386_ = lean_uint16_of_nat_mk(v_b_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofBitVec___boxed(lean_object* v_b_387_){
_start:
{
uint16_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_Int16_ofBitVec(v_b_387_);
v_r_389_ = lean_box(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt8___boxed(lean_object* v_a_391_){
_start:
{
uint16_t v_a_boxed_392_; uint8_t v_res_393_; lean_object* v_r_394_; 
v_a_boxed_392_ = lean_unbox(v_a_391_);
v_res_393_ = lean_int16_to_int8(v_a_boxed_392_);
v_r_394_ = lean_box(v_res_393_);
return v_r_394_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt16___boxed(lean_object* v_a_396_){
_start:
{
uint8_t v_a_boxed_397_; uint16_t v_res_398_; lean_object* v_r_399_; 
v_a_boxed_397_ = lean_unbox(v_a_396_);
v_res_398_ = lean_int8_to_int16(v_a_boxed_397_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT lean_object* l_Int16_neg___boxed(lean_object* v_i_401_){
_start:
{
uint16_t v_i_boxed_402_; uint16_t v_res_403_; lean_object* v_r_404_; 
v_i_boxed_402_ = lean_unbox(v_i_401_);
v_res_403_ = lean_int16_neg(v_i_boxed_402_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0(uint16_t v_i_405_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_int16_to_int(v_i_405_);
v___x_407_ = l_Int_repr(v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0___boxed(lean_object* v_i_408_){
_start:
{
uint16_t v_i_boxed_409_; lean_object* v_res_410_; 
v_i_boxed_409_ = lean_unbox(v_i_408_);
v_res_410_ = l_instToStringInt16___lam__0(v_i_boxed_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_instReprInt16___lam__0(uint16_t v_i_413_, lean_object* v_prec_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_415_ = lean_int16_to_int(v_i_413_);
v___x_416_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_417_ = lean_int_dec_lt(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = l_Int_repr(v___x_415_);
v___x_419_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = l_Int_repr(v___x_415_);
v___x_421_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
v___x_422_ = l_Repr_addAppParen(v___x_421_, v_prec_414_);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt16___lam__0___boxed(lean_object* v_i_423_, lean_object* v_prec_424_){
_start:
{
uint16_t v_i_boxed_425_; lean_object* v_res_426_; 
v_i_boxed_425_ = lean_unbox(v_i_423_);
v_res_426_ = l_instReprInt16___lam__0(v_i_boxed_425_, v_prec_424_);
lean_dec(v_prec_424_);
return v_res_426_;
}
}
static lean_object* _init_l_instReprAtomInt16(void){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_box(0);
return v___x_429_;
}
}
LEAN_EXPORT uint16_t l_Int16_instOfNat(lean_object* v_n_432_){
_start:
{
uint16_t v___x_433_; 
v___x_433_ = lean_int16_of_nat(v_n_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Int16_instOfNat___boxed(lean_object* v_n_434_){
_start:
{
uint16_t v_res_435_; lean_object* v_r_436_; 
v_res_435_ = l_Int16_instOfNat(v_n_434_);
lean_dec(v_n_434_);
v_r_436_ = lean_box(v_res_435_);
return v_r_436_;
}
}
static uint16_t _init_l_Int16_maxValue___closed__0(void){
_start:
{
lean_object* v___x_439_; uint16_t v___x_440_; 
v___x_439_ = lean_unsigned_to_nat(32767u);
v___x_440_ = lean_int16_of_nat(v___x_439_);
return v___x_440_;
}
}
static uint16_t _init_l_Int16_maxValue(void){
_start:
{
uint16_t v___x_441_; 
v___x_441_ = lean_uint16_once(&l_Int16_maxValue___closed__0, &l_Int16_maxValue___closed__0_once, _init_l_Int16_maxValue___closed__0);
return v___x_441_;
}
}
static uint16_t _init_l_Int16_minValue___closed__0(void){
_start:
{
lean_object* v___x_442_; uint16_t v___x_443_; 
v___x_442_ = lean_unsigned_to_nat(32768u);
v___x_443_ = lean_int16_of_nat(v___x_442_);
return v___x_443_;
}
}
static uint16_t _init_l_Int16_minValue___closed__1(void){
_start:
{
uint16_t v___x_444_; uint16_t v___x_445_; 
v___x_444_ = lean_uint16_once(&l_Int16_minValue___closed__0, &l_Int16_minValue___closed__0_once, _init_l_Int16_minValue___closed__0);
v___x_445_ = lean_int16_neg(v___x_444_);
return v___x_445_;
}
}
static uint16_t _init_l_Int16_minValue(void){
_start:
{
uint16_t v___x_446_; 
v___x_446_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
return v___x_446_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntLE___redArg(lean_object* v_i_447_){
_start:
{
uint16_t v___x_448_; 
v___x_448_ = lean_int16_of_int(v_i_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntLE___redArg___boxed(lean_object* v_i_449_){
_start:
{
uint16_t v_res_450_; lean_object* v_r_451_; 
v_res_450_ = l_Int16_ofIntLE___redArg(v_i_449_);
lean_dec(v_i_449_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntLE(lean_object* v_i_452_, lean_object* v___hl_453_, lean_object* v___hr_454_){
_start:
{
uint16_t v___x_455_; 
v___x_455_ = lean_int16_of_int(v_i_452_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntLE___boxed(lean_object* v_i_456_, lean_object* v___hl_457_, lean_object* v___hr_458_){
_start:
{
uint16_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_Int16_ofIntLE(v_i_456_, v___hl_457_, v___hr_458_);
lean_dec(v_i_456_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
static lean_object* _init_l_Int16_ofIntClamp___closed__0(void){
_start:
{
uint16_t v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
v___x_462_ = lean_int16_to_int(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Int16_ofIntClamp___closed__1(void){
_start:
{
uint16_t v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_uint16_once(&l_Int16_maxValue___closed__0, &l_Int16_maxValue___closed__0_once, _init_l_Int16_maxValue___closed__0);
v___x_464_ = lean_int16_to_int(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntClamp(lean_object* v_i_465_){
_start:
{
uint16_t v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_466_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
v___x_467_ = lean_obj_once(&l_Int16_ofIntClamp___closed__0, &l_Int16_ofIntClamp___closed__0_once, _init_l_Int16_ofIntClamp___closed__0);
v___x_468_ = lean_int_dec_le(v___x_467_, v_i_465_);
if (v___x_468_ == 0)
{
return v___x_466_;
}
else
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = lean_obj_once(&l_Int16_ofIntClamp___closed__1, &l_Int16_ofIntClamp___closed__1_once, _init_l_Int16_ofIntClamp___closed__1);
v___x_470_ = lean_int_dec_le(v_i_465_, v___x_469_);
if (v___x_470_ == 0)
{
return v___x_466_;
}
else
{
uint16_t v___x_471_; 
v___x_471_ = lean_int16_of_int(v_i_465_);
return v___x_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntClamp___boxed(lean_object* v_i_472_){
_start:
{
uint16_t v_res_473_; lean_object* v_r_474_; 
v_res_473_ = l_Int16_ofIntClamp(v_i_472_);
lean_dec(v_i_472_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT uint16_t l_Int16_ofIntTruncate(lean_object* v_i_475_){
_start:
{
uint16_t v___x_476_; 
v___x_476_ = l_Int16_ofIntClamp(v_i_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Int16_ofIntTruncate___boxed(lean_object* v_i_477_){
_start:
{
uint16_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l_Int16_ofIntTruncate(v_i_477_);
lean_dec(v_i_477_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT lean_object* l_Int16_add___boxed(lean_object* v_a_482_, lean_object* v_b_483_){
_start:
{
uint16_t v_a_boxed_484_; uint16_t v_b_boxed_485_; uint16_t v_res_486_; lean_object* v_r_487_; 
v_a_boxed_484_ = lean_unbox(v_a_482_);
v_b_boxed_485_ = lean_unbox(v_b_483_);
v_res_486_ = lean_int16_add(v_a_boxed_484_, v_b_boxed_485_);
v_r_487_ = lean_box(v_res_486_);
return v_r_487_;
}
}
LEAN_EXPORT lean_object* l_Int16_sub___boxed(lean_object* v_a_490_, lean_object* v_b_491_){
_start:
{
uint16_t v_a_boxed_492_; uint16_t v_b_boxed_493_; uint16_t v_res_494_; lean_object* v_r_495_; 
v_a_boxed_492_ = lean_unbox(v_a_490_);
v_b_boxed_493_ = lean_unbox(v_b_491_);
v_res_494_ = lean_int16_sub(v_a_boxed_492_, v_b_boxed_493_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
LEAN_EXPORT lean_object* l_Int16_mul___boxed(lean_object* v_a_498_, lean_object* v_b_499_){
_start:
{
uint16_t v_a_boxed_500_; uint16_t v_b_boxed_501_; uint16_t v_res_502_; lean_object* v_r_503_; 
v_a_boxed_500_ = lean_unbox(v_a_498_);
v_b_boxed_501_ = lean_unbox(v_b_499_);
v_res_502_ = lean_int16_mul(v_a_boxed_500_, v_b_boxed_501_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT lean_object* l_Int16_div___boxed(lean_object* v_a_506_, lean_object* v_b_507_){
_start:
{
uint16_t v_a_boxed_508_; uint16_t v_b_boxed_509_; uint16_t v_res_510_; lean_object* v_r_511_; 
v_a_boxed_508_ = lean_unbox(v_a_506_);
v_b_boxed_509_ = lean_unbox(v_b_507_);
v_res_510_ = lean_int16_div(v_a_boxed_508_, v_b_boxed_509_);
v_r_511_ = lean_box(v_res_510_);
return v_r_511_;
}
}
static uint16_t _init_l_Int16_pow___closed__0(void){
_start:
{
lean_object* v___x_512_; uint16_t v___x_513_; 
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_int16_of_nat(v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT uint16_t l_Int16_pow(uint16_t v_x_514_, lean_object* v_n_515_){
_start:
{
lean_object* v_zero_516_; uint8_t v_isZero_517_; 
v_zero_516_ = lean_unsigned_to_nat(0u);
v_isZero_517_ = lean_nat_dec_eq(v_n_515_, v_zero_516_);
if (v_isZero_517_ == 1)
{
uint16_t v___x_518_; 
v___x_518_ = lean_uint16_once(&l_Int16_pow___closed__0, &l_Int16_pow___closed__0_once, _init_l_Int16_pow___closed__0);
return v___x_518_;
}
else
{
lean_object* v_one_519_; lean_object* v_n_520_; uint16_t v___x_521_; uint16_t v___x_522_; 
v_one_519_ = lean_unsigned_to_nat(1u);
v_n_520_ = lean_nat_sub(v_n_515_, v_one_519_);
v___x_521_ = l_Int16_pow(v_x_514_, v_n_520_);
lean_dec(v_n_520_);
v___x_522_ = lean_int16_mul(v___x_521_, v_x_514_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l_Int16_pow___boxed(lean_object* v_x_523_, lean_object* v_n_524_){
_start:
{
uint16_t v_x_boxed_525_; uint16_t v_res_526_; lean_object* v_r_527_; 
v_x_boxed_525_ = lean_unbox(v_x_523_);
v_res_526_ = l_Int16_pow(v_x_boxed_525_, v_n_524_);
lean_dec(v_n_524_);
v_r_527_ = lean_box(v_res_526_);
return v_r_527_;
}
}
LEAN_EXPORT lean_object* l_Int16_mod___boxed(lean_object* v_a_530_, lean_object* v_b_531_){
_start:
{
uint16_t v_a_boxed_532_; uint16_t v_b_boxed_533_; uint16_t v_res_534_; lean_object* v_r_535_; 
v_a_boxed_532_ = lean_unbox(v_a_530_);
v_b_boxed_533_ = lean_unbox(v_b_531_);
v_res_534_ = lean_int16_mod(v_a_boxed_532_, v_b_boxed_533_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
LEAN_EXPORT lean_object* l_Int16_land___boxed(lean_object* v_a_538_, lean_object* v_b_539_){
_start:
{
uint16_t v_a_boxed_540_; uint16_t v_b_boxed_541_; uint16_t v_res_542_; lean_object* v_r_543_; 
v_a_boxed_540_ = lean_unbox(v_a_538_);
v_b_boxed_541_ = lean_unbox(v_b_539_);
v_res_542_ = lean_int16_land(v_a_boxed_540_, v_b_boxed_541_);
v_r_543_ = lean_box(v_res_542_);
return v_r_543_;
}
}
LEAN_EXPORT lean_object* l_Int16_lor___boxed(lean_object* v_a_546_, lean_object* v_b_547_){
_start:
{
uint16_t v_a_boxed_548_; uint16_t v_b_boxed_549_; uint16_t v_res_550_; lean_object* v_r_551_; 
v_a_boxed_548_ = lean_unbox(v_a_546_);
v_b_boxed_549_ = lean_unbox(v_b_547_);
v_res_550_ = lean_int16_lor(v_a_boxed_548_, v_b_boxed_549_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT lean_object* l_Int16_xor___boxed(lean_object* v_a_554_, lean_object* v_b_555_){
_start:
{
uint16_t v_a_boxed_556_; uint16_t v_b_boxed_557_; uint16_t v_res_558_; lean_object* v_r_559_; 
v_a_boxed_556_ = lean_unbox(v_a_554_);
v_b_boxed_557_ = lean_unbox(v_b_555_);
v_res_558_ = lean_int16_xor(v_a_boxed_556_, v_b_boxed_557_);
v_r_559_ = lean_box(v_res_558_);
return v_r_559_;
}
}
LEAN_EXPORT lean_object* l_Int16_shiftLeft___boxed(lean_object* v_a_562_, lean_object* v_b_563_){
_start:
{
uint16_t v_a_boxed_564_; uint16_t v_b_boxed_565_; uint16_t v_res_566_; lean_object* v_r_567_; 
v_a_boxed_564_ = lean_unbox(v_a_562_);
v_b_boxed_565_ = lean_unbox(v_b_563_);
v_res_566_ = lean_int16_shift_left(v_a_boxed_564_, v_b_boxed_565_);
v_r_567_ = lean_box(v_res_566_);
return v_r_567_;
}
}
LEAN_EXPORT lean_object* l_Int16_shiftRight___boxed(lean_object* v_a_570_, lean_object* v_b_571_){
_start:
{
uint16_t v_a_boxed_572_; uint16_t v_b_boxed_573_; uint16_t v_res_574_; lean_object* v_r_575_; 
v_a_boxed_572_ = lean_unbox(v_a_570_);
v_b_boxed_573_ = lean_unbox(v_b_571_);
v_res_574_ = lean_int16_shift_right(v_a_boxed_572_, v_b_boxed_573_);
v_r_575_ = lean_box(v_res_574_);
return v_r_575_;
}
}
LEAN_EXPORT lean_object* l_Int16_complement___boxed(lean_object* v_a_577_){
_start:
{
uint16_t v_a_boxed_578_; uint16_t v_res_579_; lean_object* v_r_580_; 
v_a_boxed_578_ = lean_unbox(v_a_577_);
v_res_579_ = lean_int16_complement(v_a_boxed_578_);
v_r_580_ = lean_box(v_res_579_);
return v_r_580_;
}
}
LEAN_EXPORT lean_object* l_Int16_abs___boxed(lean_object* v_a_582_){
_start:
{
uint16_t v_a_boxed_583_; uint16_t v_res_584_; lean_object* v_r_585_; 
v_a_boxed_583_ = lean_unbox(v_a_582_);
v_res_584_ = lean_int16_abs(v_a_boxed_583_);
v_r_585_ = lean_box(v_res_584_);
return v_r_585_;
}
}
LEAN_EXPORT lean_object* l_Int16_decEq___boxed(lean_object* v_a_588_, lean_object* v_b_589_){
_start:
{
uint16_t v_a_boxed_590_; uint16_t v_b_boxed_591_; uint8_t v_res_592_; lean_object* v_r_593_; 
v_a_boxed_590_ = lean_unbox(v_a_588_);
v_b_boxed_591_ = lean_unbox(v_b_589_);
v_res_592_ = lean_int16_dec_eq(v_a_boxed_590_, v_b_boxed_591_);
v_r_593_ = lean_box(v_res_592_);
return v_r_593_;
}
}
static uint16_t _init_l_instInhabitedInt16___closed__0(void){
_start:
{
lean_object* v___x_594_; uint16_t v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(0u);
v___x_595_ = lean_int16_of_nat(v___x_594_);
return v___x_595_;
}
}
static uint16_t _init_l_instInhabitedInt16(void){
_start:
{
uint16_t v___x_596_; 
v___x_596_ = lean_uint16_once(&l_instInhabitedInt16___closed__0, &l_instInhabitedInt16___closed__0_once, _init_l_instInhabitedInt16___closed__0);
return v___x_596_;
}
}
static lean_object* _init_l_instLTInt16(void){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lean_box(0);
return v___x_609_;
}
}
static lean_object* _init_l_instLEInt16(void){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = lean_box(0);
return v___x_610_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt16(uint16_t v_a_623_, uint16_t v_b_624_){
_start:
{
uint8_t v___x_625_; 
v___x_625_ = lean_int16_dec_eq(v_a_623_, v_b_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt16___boxed(lean_object* v_a_626_, lean_object* v_b_627_){
_start:
{
uint16_t v_a_boxed_628_; uint16_t v_b_boxed_629_; uint8_t v_res_630_; lean_object* v_r_631_; 
v_a_boxed_628_ = lean_unbox(v_a_626_);
v_b_boxed_629_ = lean_unbox(v_b_627_);
v_res_630_ = l_instDecidableEqInt16(v_a_boxed_628_, v_b_boxed_629_);
v_r_631_ = lean_box(v_res_630_);
return v_r_631_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt16___boxed(lean_object* v_b_633_){
_start:
{
uint8_t v_b_boxed_634_; uint16_t v_res_635_; lean_object* v_r_636_; 
v_b_boxed_634_ = lean_unbox(v_b_633_);
v_res_635_ = lean_bool_to_int16(v_b_boxed_634_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT uint8_t l_Int16_decLt___aux__1(uint16_t v_a_637_, uint16_t v_b_638_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_639_ = lean_unsigned_to_nat(16u);
v___x_640_ = lean_uint16_to_nat(v_a_637_);
v___x_641_ = lean_uint16_to_nat(v_b_638_);
v___x_642_ = l_BitVec_slt(v___x_639_, v___x_640_, v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLt___aux__1___boxed(lean_object* v_a_643_, lean_object* v_b_644_){
_start:
{
uint16_t v_a_boxed_645_; uint16_t v_b_boxed_646_; uint8_t v_res_647_; lean_object* v_r_648_; 
v_a_boxed_645_ = lean_unbox(v_a_643_);
v_b_boxed_646_ = lean_unbox(v_b_644_);
v_res_647_ = l_Int16_decLt___aux__1(v_a_boxed_645_, v_b_boxed_646_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLt___boxed(lean_object* v_a_651_, lean_object* v_b_652_){
_start:
{
uint16_t v_a_boxed_653_; uint16_t v_b_boxed_654_; uint8_t v_res_655_; lean_object* v_r_656_; 
v_a_boxed_653_ = lean_unbox(v_a_651_);
v_b_boxed_654_ = lean_unbox(v_b_652_);
v_res_655_ = lean_int16_dec_lt(v_a_boxed_653_, v_b_boxed_654_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT uint8_t l_Int16_decLe___aux__1(uint16_t v_a_657_, uint16_t v_b_658_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_659_ = lean_unsigned_to_nat(16u);
v___x_660_ = lean_uint16_to_nat(v_a_657_);
v___x_661_ = lean_uint16_to_nat(v_b_658_);
v___x_662_ = l_BitVec_sle(v___x_659_, v___x_660_, v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLe___aux__1___boxed(lean_object* v_a_663_, lean_object* v_b_664_){
_start:
{
uint16_t v_a_boxed_665_; uint16_t v_b_boxed_666_; uint8_t v_res_667_; lean_object* v_r_668_; 
v_a_boxed_665_ = lean_unbox(v_a_663_);
v_b_boxed_666_ = lean_unbox(v_b_664_);
v_res_667_ = l_Int16_decLe___aux__1(v_a_boxed_665_, v_b_boxed_666_);
v_r_668_ = lean_box(v_res_667_);
return v_r_668_;
}
}
LEAN_EXPORT lean_object* l_Int16_decLe___boxed(lean_object* v_a_671_, lean_object* v_b_672_){
_start:
{
uint16_t v_a_boxed_673_; uint16_t v_b_boxed_674_; uint8_t v_res_675_; lean_object* v_r_676_; 
v_a_boxed_673_ = lean_unbox(v_a_671_);
v_b_boxed_674_ = lean_unbox(v_b_672_);
v_res_675_ = lean_int16_dec_le(v_a_boxed_673_, v_b_boxed_674_);
v_r_676_ = lean_box(v_res_675_);
return v_r_676_;
}
}
LEAN_EXPORT uint16_t l_instMaxInt16___lam__0(uint16_t v_x_677_, uint16_t v_y_678_){
_start:
{
uint8_t v___x_679_; 
v___x_679_ = lean_int16_dec_le(v_x_677_, v_y_678_);
if (v___x_679_ == 0)
{
return v_x_677_;
}
else
{
return v_y_678_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt16___lam__0___boxed(lean_object* v_x_680_, lean_object* v_y_681_){
_start:
{
uint16_t v_x_boxed_682_; uint16_t v_y_boxed_683_; uint16_t v_res_684_; lean_object* v_r_685_; 
v_x_boxed_682_ = lean_unbox(v_x_680_);
v_y_boxed_683_ = lean_unbox(v_y_681_);
v_res_684_ = l_instMaxInt16___lam__0(v_x_boxed_682_, v_y_boxed_683_);
v_r_685_ = lean_box(v_res_684_);
return v_r_685_;
}
}
LEAN_EXPORT uint16_t l_instMinInt16___lam__0(uint16_t v_x_688_, uint16_t v_y_689_){
_start:
{
uint8_t v___x_690_; 
v___x_690_ = lean_int16_dec_le(v_x_688_, v_y_689_);
if (v___x_690_ == 0)
{
return v_y_689_;
}
else
{
return v_x_688_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt16___lam__0___boxed(lean_object* v_x_691_, lean_object* v_y_692_){
_start:
{
uint16_t v_x_boxed_693_; uint16_t v_y_boxed_694_; uint16_t v_res_695_; lean_object* v_r_696_; 
v_x_boxed_693_ = lean_unbox(v_x_691_);
v_y_boxed_694_ = lean_unbox(v_y_692_);
v_res_695_ = l_instMinInt16___lam__0(v_x_boxed_693_, v_y_boxed_694_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
static lean_object* _init_l_Int32_size(void){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = lean_cstr_to_nat("4294967296");
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Int32_toBitVec(uint32_t v_x_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = lean_uint32_to_nat(v_x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Int32_toBitVec___boxed(lean_object* v_x_702_){
_start:
{
uint32_t v_x_boxed_703_; lean_object* v_res_704_; 
v_x_boxed_703_ = lean_unbox_uint32(v_x_702_);
lean_dec(v_x_702_);
v_res_704_ = l_Int32_toBitVec(v_x_boxed_703_);
return v_res_704_;
}
}
LEAN_EXPORT uint32_t l_UInt32_toInt32(uint32_t v_i_705_){
_start:
{
return v_i_705_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toInt32___boxed(lean_object* v_i_706_){
_start:
{
uint32_t v_i_boxed_707_; uint32_t v_res_708_; lean_object* v_r_709_; 
v_i_boxed_707_ = lean_unbox_uint32(v_i_706_);
lean_dec(v_i_706_);
v_res_708_ = l_UInt32_toInt32(v_i_boxed_707_);
v_r_709_ = lean_box_uint32(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofInt___boxed(lean_object* v_i_711_){
_start:
{
uint32_t v_res_712_; lean_object* v_r_713_; 
v_res_712_ = lean_int32_of_int(v_i_711_);
lean_dec(v_i_711_);
v_r_713_ = lean_box_uint32(v_res_712_);
return v_r_713_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofNat___boxed(lean_object* v_n_715_){
_start:
{
uint32_t v_res_716_; lean_object* v_r_717_; 
v_res_716_ = lean_int32_of_nat(v_n_715_);
lean_dec(v_n_715_);
v_r_717_ = lean_box_uint32(v_res_716_);
return v_r_717_;
}
}
LEAN_EXPORT uint32_t l_Int_toInt32(lean_object* v_i_718_){
_start:
{
uint32_t v___x_719_; 
v___x_719_ = lean_int32_of_int(v_i_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt32___boxed(lean_object* v_i_720_){
_start:
{
uint32_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Int_toInt32(v_i_720_);
lean_dec(v_i_720_);
v_r_722_ = lean_box_uint32(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT uint32_t l_Nat_toInt32(lean_object* v_n_723_){
_start:
{
uint32_t v___x_724_; 
v___x_724_ = lean_int32_of_nat(v_n_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt32___boxed(lean_object* v_n_725_){
_start:
{
uint32_t v_res_726_; lean_object* v_r_727_; 
v_res_726_ = l_Nat_toInt32(v_n_725_);
lean_dec(v_n_725_);
v_r_727_ = lean_box_uint32(v_res_726_);
return v_r_727_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt___boxed(lean_object* v_i_729_){
_start:
{
uint32_t v_i_boxed_730_; lean_object* v_res_731_; 
v_i_boxed_730_ = lean_unbox_uint32(v_i_729_);
lean_dec(v_i_729_);
v_res_731_ = lean_int32_to_int(v_i_boxed_730_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg(uint32_t v_i_732_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = lean_int32_to_int(v_i_732_);
v___x_734_ = l_Int_toNat(v___x_733_);
lean_dec(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg___boxed(lean_object* v_i_735_){
_start:
{
uint32_t v_i_boxed_736_; lean_object* v_res_737_; 
v_i_boxed_736_ = lean_unbox_uint32(v_i_735_);
lean_dec(v_i_735_);
v_res_737_ = l_Int32_toNatClampNeg(v_i_boxed_736_);
return v_res_737_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofBitVec(lean_object* v_b_738_){
_start:
{
uint32_t v___x_739_; 
v___x_739_ = lean_uint32_of_nat_mk(v_b_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofBitVec___boxed(lean_object* v_b_740_){
_start:
{
uint32_t v_res_741_; lean_object* v_r_742_; 
v_res_741_ = l_Int32_ofBitVec(v_b_740_);
v_r_742_ = lean_box_uint32(v_res_741_);
return v_r_742_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt8___boxed(lean_object* v_a_744_){
_start:
{
uint32_t v_a_boxed_745_; uint8_t v_res_746_; lean_object* v_r_747_; 
v_a_boxed_745_ = lean_unbox_uint32(v_a_744_);
lean_dec(v_a_744_);
v_res_746_ = lean_int32_to_int8(v_a_boxed_745_);
v_r_747_ = lean_box(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt16___boxed(lean_object* v_a_749_){
_start:
{
uint32_t v_a_boxed_750_; uint16_t v_res_751_; lean_object* v_r_752_; 
v_a_boxed_750_ = lean_unbox_uint32(v_a_749_);
lean_dec(v_a_749_);
v_res_751_ = lean_int32_to_int16(v_a_boxed_750_);
v_r_752_ = lean_box(v_res_751_);
return v_r_752_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt32___boxed(lean_object* v_a_754_){
_start:
{
uint8_t v_a_boxed_755_; uint32_t v_res_756_; lean_object* v_r_757_; 
v_a_boxed_755_ = lean_unbox(v_a_754_);
v_res_756_ = lean_int8_to_int32(v_a_boxed_755_);
v_r_757_ = lean_box_uint32(v_res_756_);
return v_r_757_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt32___boxed(lean_object* v_a_759_){
_start:
{
uint16_t v_a_boxed_760_; uint32_t v_res_761_; lean_object* v_r_762_; 
v_a_boxed_760_ = lean_unbox(v_a_759_);
v_res_761_ = lean_int16_to_int32(v_a_boxed_760_);
v_r_762_ = lean_box_uint32(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT lean_object* l_Int32_neg___boxed(lean_object* v_i_764_){
_start:
{
uint32_t v_i_boxed_765_; uint32_t v_res_766_; lean_object* v_r_767_; 
v_i_boxed_765_ = lean_unbox_uint32(v_i_764_);
lean_dec(v_i_764_);
v_res_766_ = lean_int32_neg(v_i_boxed_765_);
v_r_767_ = lean_box_uint32(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0(uint32_t v_i_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_int32_to_int(v_i_768_);
v___x_770_ = l_Int_repr(v___x_769_);
lean_dec(v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0___boxed(lean_object* v_i_771_){
_start:
{
uint32_t v_i_boxed_772_; lean_object* v_res_773_; 
v_i_boxed_772_ = lean_unbox_uint32(v_i_771_);
lean_dec(v_i_771_);
v_res_773_ = l_instToStringInt32___lam__0(v_i_boxed_772_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_instReprInt32___lam__0(uint32_t v_i_776_, lean_object* v_prec_777_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_778_ = lean_int32_to_int(v_i_776_);
v___x_779_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_780_ = lean_int_dec_lt(v___x_778_, v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = l_Int_repr(v___x_778_);
lean_dec(v___x_778_);
v___x_782_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = l_Int_repr(v___x_778_);
lean_dec(v___x_778_);
v___x_784_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
v___x_785_ = l_Repr_addAppParen(v___x_784_, v_prec_777_);
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt32___lam__0___boxed(lean_object* v_i_786_, lean_object* v_prec_787_){
_start:
{
uint32_t v_i_boxed_788_; lean_object* v_res_789_; 
v_i_boxed_788_ = lean_unbox_uint32(v_i_786_);
lean_dec(v_i_786_);
v_res_789_ = l_instReprInt32___lam__0(v_i_boxed_788_, v_prec_787_);
lean_dec(v_prec_787_);
return v_res_789_;
}
}
static lean_object* _init_l_instReprAtomInt32(void){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = lean_box(0);
return v___x_792_;
}
}
LEAN_EXPORT uint32_t l_Int32_instOfNat(lean_object* v_n_795_){
_start:
{
uint32_t v___x_796_; 
v___x_796_ = lean_int32_of_nat(v_n_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Int32_instOfNat___boxed(lean_object* v_n_797_){
_start:
{
uint32_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_Int32_instOfNat(v_n_797_);
lean_dec(v_n_797_);
v_r_799_ = lean_box_uint32(v_res_798_);
return v_r_799_;
}
}
static uint32_t _init_l_Int32_maxValue___closed__0(void){
_start:
{
lean_object* v___x_802_; uint32_t v___x_803_; 
v___x_802_ = lean_unsigned_to_nat(2147483647u);
v___x_803_ = lean_int32_of_nat(v___x_802_);
return v___x_803_;
}
}
static uint32_t _init_l_Int32_maxValue(void){
_start:
{
uint32_t v___x_804_; 
v___x_804_ = lean_uint32_once(&l_Int32_maxValue___closed__0, &l_Int32_maxValue___closed__0_once, _init_l_Int32_maxValue___closed__0);
return v___x_804_;
}
}
static uint32_t _init_l_Int32_minValue___closed__0(void){
_start:
{
lean_object* v___x_805_; uint32_t v___x_806_; 
v___x_805_ = lean_unsigned_to_nat(2147483648u);
v___x_806_ = lean_int32_of_nat(v___x_805_);
return v___x_806_;
}
}
static uint32_t _init_l_Int32_minValue___closed__1(void){
_start:
{
uint32_t v___x_807_; uint32_t v___x_808_; 
v___x_807_ = lean_uint32_once(&l_Int32_minValue___closed__0, &l_Int32_minValue___closed__0_once, _init_l_Int32_minValue___closed__0);
v___x_808_ = lean_int32_neg(v___x_807_);
return v___x_808_;
}
}
static uint32_t _init_l_Int32_minValue(void){
_start:
{
uint32_t v___x_809_; 
v___x_809_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
return v___x_809_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntLE___redArg(lean_object* v_i_810_){
_start:
{
uint32_t v___x_811_; 
v___x_811_ = lean_int32_of_int(v_i_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntLE___redArg___boxed(lean_object* v_i_812_){
_start:
{
uint32_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l_Int32_ofIntLE___redArg(v_i_812_);
lean_dec(v_i_812_);
v_r_814_ = lean_box_uint32(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntLE(lean_object* v_i_815_, lean_object* v___hl_816_, lean_object* v___hr_817_){
_start:
{
uint32_t v___x_818_; 
v___x_818_ = lean_int32_of_int(v_i_815_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntLE___boxed(lean_object* v_i_819_, lean_object* v___hl_820_, lean_object* v___hr_821_){
_start:
{
uint32_t v_res_822_; lean_object* v_r_823_; 
v_res_822_ = l_Int32_ofIntLE(v_i_819_, v___hl_820_, v___hr_821_);
lean_dec(v_i_819_);
v_r_823_ = lean_box_uint32(v_res_822_);
return v_r_823_;
}
}
static lean_object* _init_l_Int32_ofIntClamp___closed__0(void){
_start:
{
uint32_t v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
v___x_825_ = lean_int32_to_int(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l_Int32_ofIntClamp___closed__1(void){
_start:
{
uint32_t v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_uint32_once(&l_Int32_maxValue___closed__0, &l_Int32_maxValue___closed__0_once, _init_l_Int32_maxValue___closed__0);
v___x_827_ = lean_int32_to_int(v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntClamp(lean_object* v_i_828_){
_start:
{
uint32_t v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_829_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
v___x_830_ = lean_obj_once(&l_Int32_ofIntClamp___closed__0, &l_Int32_ofIntClamp___closed__0_once, _init_l_Int32_ofIntClamp___closed__0);
v___x_831_ = lean_int_dec_le(v___x_830_, v_i_828_);
if (v___x_831_ == 0)
{
return v___x_829_;
}
else
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = lean_obj_once(&l_Int32_ofIntClamp___closed__1, &l_Int32_ofIntClamp___closed__1_once, _init_l_Int32_ofIntClamp___closed__1);
v___x_833_ = lean_int_dec_le(v_i_828_, v___x_832_);
if (v___x_833_ == 0)
{
return v___x_829_;
}
else
{
uint32_t v___x_834_; 
v___x_834_ = lean_int32_of_int(v_i_828_);
return v___x_834_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntClamp___boxed(lean_object* v_i_835_){
_start:
{
uint32_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Int32_ofIntClamp(v_i_835_);
lean_dec(v_i_835_);
v_r_837_ = lean_box_uint32(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT uint32_t l_Int32_ofIntTruncate(lean_object* v_i_838_){
_start:
{
uint32_t v___x_839_; 
v___x_839_ = l_Int32_ofIntClamp(v_i_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Int32_ofIntTruncate___boxed(lean_object* v_i_840_){
_start:
{
uint32_t v_res_841_; lean_object* v_r_842_; 
v_res_841_ = l_Int32_ofIntTruncate(v_i_840_);
lean_dec(v_i_840_);
v_r_842_ = lean_box_uint32(v_res_841_);
return v_r_842_;
}
}
LEAN_EXPORT lean_object* l_Int32_add___boxed(lean_object* v_a_845_, lean_object* v_b_846_){
_start:
{
uint32_t v_a_boxed_847_; uint32_t v_b_boxed_848_; uint32_t v_res_849_; lean_object* v_r_850_; 
v_a_boxed_847_ = lean_unbox_uint32(v_a_845_);
lean_dec(v_a_845_);
v_b_boxed_848_ = lean_unbox_uint32(v_b_846_);
lean_dec(v_b_846_);
v_res_849_ = lean_int32_add(v_a_boxed_847_, v_b_boxed_848_);
v_r_850_ = lean_box_uint32(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT lean_object* l_Int32_sub___boxed(lean_object* v_a_853_, lean_object* v_b_854_){
_start:
{
uint32_t v_a_boxed_855_; uint32_t v_b_boxed_856_; uint32_t v_res_857_; lean_object* v_r_858_; 
v_a_boxed_855_ = lean_unbox_uint32(v_a_853_);
lean_dec(v_a_853_);
v_b_boxed_856_ = lean_unbox_uint32(v_b_854_);
lean_dec(v_b_854_);
v_res_857_ = lean_int32_sub(v_a_boxed_855_, v_b_boxed_856_);
v_r_858_ = lean_box_uint32(v_res_857_);
return v_r_858_;
}
}
LEAN_EXPORT lean_object* l_Int32_mul___boxed(lean_object* v_a_861_, lean_object* v_b_862_){
_start:
{
uint32_t v_a_boxed_863_; uint32_t v_b_boxed_864_; uint32_t v_res_865_; lean_object* v_r_866_; 
v_a_boxed_863_ = lean_unbox_uint32(v_a_861_);
lean_dec(v_a_861_);
v_b_boxed_864_ = lean_unbox_uint32(v_b_862_);
lean_dec(v_b_862_);
v_res_865_ = lean_int32_mul(v_a_boxed_863_, v_b_boxed_864_);
v_r_866_ = lean_box_uint32(v_res_865_);
return v_r_866_;
}
}
LEAN_EXPORT lean_object* l_Int32_div___boxed(lean_object* v_a_869_, lean_object* v_b_870_){
_start:
{
uint32_t v_a_boxed_871_; uint32_t v_b_boxed_872_; uint32_t v_res_873_; lean_object* v_r_874_; 
v_a_boxed_871_ = lean_unbox_uint32(v_a_869_);
lean_dec(v_a_869_);
v_b_boxed_872_ = lean_unbox_uint32(v_b_870_);
lean_dec(v_b_870_);
v_res_873_ = lean_int32_div(v_a_boxed_871_, v_b_boxed_872_);
v_r_874_ = lean_box_uint32(v_res_873_);
return v_r_874_;
}
}
static uint32_t _init_l_Int32_pow___closed__0(void){
_start:
{
lean_object* v___x_875_; uint32_t v___x_876_; 
v___x_875_ = lean_unsigned_to_nat(1u);
v___x_876_ = lean_int32_of_nat(v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT uint32_t l_Int32_pow(uint32_t v_x_877_, lean_object* v_n_878_){
_start:
{
lean_object* v_zero_879_; uint8_t v_isZero_880_; 
v_zero_879_ = lean_unsigned_to_nat(0u);
v_isZero_880_ = lean_nat_dec_eq(v_n_878_, v_zero_879_);
if (v_isZero_880_ == 1)
{
uint32_t v___x_881_; 
v___x_881_ = lean_uint32_once(&l_Int32_pow___closed__0, &l_Int32_pow___closed__0_once, _init_l_Int32_pow___closed__0);
return v___x_881_;
}
else
{
lean_object* v_one_882_; lean_object* v_n_883_; uint32_t v___x_884_; uint32_t v___x_885_; 
v_one_882_ = lean_unsigned_to_nat(1u);
v_n_883_ = lean_nat_sub(v_n_878_, v_one_882_);
v___x_884_ = l_Int32_pow(v_x_877_, v_n_883_);
lean_dec(v_n_883_);
v___x_885_ = lean_int32_mul(v___x_884_, v_x_877_);
return v___x_885_;
}
}
}
LEAN_EXPORT lean_object* l_Int32_pow___boxed(lean_object* v_x_886_, lean_object* v_n_887_){
_start:
{
uint32_t v_x_boxed_888_; uint32_t v_res_889_; lean_object* v_r_890_; 
v_x_boxed_888_ = lean_unbox_uint32(v_x_886_);
lean_dec(v_x_886_);
v_res_889_ = l_Int32_pow(v_x_boxed_888_, v_n_887_);
lean_dec(v_n_887_);
v_r_890_ = lean_box_uint32(v_res_889_);
return v_r_890_;
}
}
LEAN_EXPORT lean_object* l_Int32_mod___boxed(lean_object* v_a_893_, lean_object* v_b_894_){
_start:
{
uint32_t v_a_boxed_895_; uint32_t v_b_boxed_896_; uint32_t v_res_897_; lean_object* v_r_898_; 
v_a_boxed_895_ = lean_unbox_uint32(v_a_893_);
lean_dec(v_a_893_);
v_b_boxed_896_ = lean_unbox_uint32(v_b_894_);
lean_dec(v_b_894_);
v_res_897_ = lean_int32_mod(v_a_boxed_895_, v_b_boxed_896_);
v_r_898_ = lean_box_uint32(v_res_897_);
return v_r_898_;
}
}
LEAN_EXPORT lean_object* l_Int32_land___boxed(lean_object* v_a_901_, lean_object* v_b_902_){
_start:
{
uint32_t v_a_boxed_903_; uint32_t v_b_boxed_904_; uint32_t v_res_905_; lean_object* v_r_906_; 
v_a_boxed_903_ = lean_unbox_uint32(v_a_901_);
lean_dec(v_a_901_);
v_b_boxed_904_ = lean_unbox_uint32(v_b_902_);
lean_dec(v_b_902_);
v_res_905_ = lean_int32_land(v_a_boxed_903_, v_b_boxed_904_);
v_r_906_ = lean_box_uint32(v_res_905_);
return v_r_906_;
}
}
LEAN_EXPORT lean_object* l_Int32_lor___boxed(lean_object* v_a_909_, lean_object* v_b_910_){
_start:
{
uint32_t v_a_boxed_911_; uint32_t v_b_boxed_912_; uint32_t v_res_913_; lean_object* v_r_914_; 
v_a_boxed_911_ = lean_unbox_uint32(v_a_909_);
lean_dec(v_a_909_);
v_b_boxed_912_ = lean_unbox_uint32(v_b_910_);
lean_dec(v_b_910_);
v_res_913_ = lean_int32_lor(v_a_boxed_911_, v_b_boxed_912_);
v_r_914_ = lean_box_uint32(v_res_913_);
return v_r_914_;
}
}
LEAN_EXPORT lean_object* l_Int32_xor___boxed(lean_object* v_a_917_, lean_object* v_b_918_){
_start:
{
uint32_t v_a_boxed_919_; uint32_t v_b_boxed_920_; uint32_t v_res_921_; lean_object* v_r_922_; 
v_a_boxed_919_ = lean_unbox_uint32(v_a_917_);
lean_dec(v_a_917_);
v_b_boxed_920_ = lean_unbox_uint32(v_b_918_);
lean_dec(v_b_918_);
v_res_921_ = lean_int32_xor(v_a_boxed_919_, v_b_boxed_920_);
v_r_922_ = lean_box_uint32(v_res_921_);
return v_r_922_;
}
}
LEAN_EXPORT lean_object* l_Int32_shiftLeft___boxed(lean_object* v_a_925_, lean_object* v_b_926_){
_start:
{
uint32_t v_a_boxed_927_; uint32_t v_b_boxed_928_; uint32_t v_res_929_; lean_object* v_r_930_; 
v_a_boxed_927_ = lean_unbox_uint32(v_a_925_);
lean_dec(v_a_925_);
v_b_boxed_928_ = lean_unbox_uint32(v_b_926_);
lean_dec(v_b_926_);
v_res_929_ = lean_int32_shift_left(v_a_boxed_927_, v_b_boxed_928_);
v_r_930_ = lean_box_uint32(v_res_929_);
return v_r_930_;
}
}
LEAN_EXPORT lean_object* l_Int32_shiftRight___boxed(lean_object* v_a_933_, lean_object* v_b_934_){
_start:
{
uint32_t v_a_boxed_935_; uint32_t v_b_boxed_936_; uint32_t v_res_937_; lean_object* v_r_938_; 
v_a_boxed_935_ = lean_unbox_uint32(v_a_933_);
lean_dec(v_a_933_);
v_b_boxed_936_ = lean_unbox_uint32(v_b_934_);
lean_dec(v_b_934_);
v_res_937_ = lean_int32_shift_right(v_a_boxed_935_, v_b_boxed_936_);
v_r_938_ = lean_box_uint32(v_res_937_);
return v_r_938_;
}
}
LEAN_EXPORT lean_object* l_Int32_complement___boxed(lean_object* v_a_940_){
_start:
{
uint32_t v_a_boxed_941_; uint32_t v_res_942_; lean_object* v_r_943_; 
v_a_boxed_941_ = lean_unbox_uint32(v_a_940_);
lean_dec(v_a_940_);
v_res_942_ = lean_int32_complement(v_a_boxed_941_);
v_r_943_ = lean_box_uint32(v_res_942_);
return v_r_943_;
}
}
LEAN_EXPORT lean_object* l_Int32_abs___boxed(lean_object* v_a_945_){
_start:
{
uint32_t v_a_boxed_946_; uint32_t v_res_947_; lean_object* v_r_948_; 
v_a_boxed_946_ = lean_unbox_uint32(v_a_945_);
lean_dec(v_a_945_);
v_res_947_ = lean_int32_abs(v_a_boxed_946_);
v_r_948_ = lean_box_uint32(v_res_947_);
return v_r_948_;
}
}
LEAN_EXPORT lean_object* l_Int32_decEq___boxed(lean_object* v_a_951_, lean_object* v_b_952_){
_start:
{
uint32_t v_a_boxed_953_; uint32_t v_b_boxed_954_; uint8_t v_res_955_; lean_object* v_r_956_; 
v_a_boxed_953_ = lean_unbox_uint32(v_a_951_);
lean_dec(v_a_951_);
v_b_boxed_954_ = lean_unbox_uint32(v_b_952_);
lean_dec(v_b_952_);
v_res_955_ = lean_int32_dec_eq(v_a_boxed_953_, v_b_boxed_954_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
static uint32_t _init_l_instInhabitedInt32___closed__0(void){
_start:
{
lean_object* v___x_957_; uint32_t v___x_958_; 
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = lean_int32_of_nat(v___x_957_);
return v___x_958_;
}
}
static uint32_t _init_l_instInhabitedInt32(void){
_start:
{
uint32_t v___x_959_; 
v___x_959_ = lean_uint32_once(&l_instInhabitedInt32___closed__0, &l_instInhabitedInt32___closed__0_once, _init_l_instInhabitedInt32___closed__0);
return v___x_959_;
}
}
static lean_object* _init_l_instLTInt32(void){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = lean_box(0);
return v___x_972_;
}
}
static lean_object* _init_l_instLEInt32(void){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = lean_box(0);
return v___x_973_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt32(uint32_t v_a_986_, uint32_t v_b_987_){
_start:
{
uint8_t v___x_988_; 
v___x_988_ = lean_int32_dec_eq(v_a_986_, v_b_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt32___boxed(lean_object* v_a_989_, lean_object* v_b_990_){
_start:
{
uint32_t v_a_boxed_991_; uint32_t v_b_boxed_992_; uint8_t v_res_993_; lean_object* v_r_994_; 
v_a_boxed_991_ = lean_unbox_uint32(v_a_989_);
lean_dec(v_a_989_);
v_b_boxed_992_ = lean_unbox_uint32(v_b_990_);
lean_dec(v_b_990_);
v_res_993_ = l_instDecidableEqInt32(v_a_boxed_991_, v_b_boxed_992_);
v_r_994_ = lean_box(v_res_993_);
return v_r_994_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt32___boxed(lean_object* v_b_996_){
_start:
{
uint8_t v_b_boxed_997_; uint32_t v_res_998_; lean_object* v_r_999_; 
v_b_boxed_997_ = lean_unbox(v_b_996_);
v_res_998_ = lean_bool_to_int32(v_b_boxed_997_);
v_r_999_ = lean_box_uint32(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT uint8_t l_Int32_decLt___aux__1(uint32_t v_a_1000_, uint32_t v_b_1001_){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1002_ = lean_unsigned_to_nat(32u);
v___x_1003_ = lean_uint32_to_nat(v_a_1000_);
v___x_1004_ = lean_uint32_to_nat(v_b_1001_);
v___x_1005_ = l_BitVec_slt(v___x_1002_, v___x_1003_, v___x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLt___aux__1___boxed(lean_object* v_a_1006_, lean_object* v_b_1007_){
_start:
{
uint32_t v_a_boxed_1008_; uint32_t v_b_boxed_1009_; uint8_t v_res_1010_; lean_object* v_r_1011_; 
v_a_boxed_1008_ = lean_unbox_uint32(v_a_1006_);
lean_dec(v_a_1006_);
v_b_boxed_1009_ = lean_unbox_uint32(v_b_1007_);
lean_dec(v_b_1007_);
v_res_1010_ = l_Int32_decLt___aux__1(v_a_boxed_1008_, v_b_boxed_1009_);
v_r_1011_ = lean_box(v_res_1010_);
return v_r_1011_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLt___boxed(lean_object* v_a_1014_, lean_object* v_b_1015_){
_start:
{
uint32_t v_a_boxed_1016_; uint32_t v_b_boxed_1017_; uint8_t v_res_1018_; lean_object* v_r_1019_; 
v_a_boxed_1016_ = lean_unbox_uint32(v_a_1014_);
lean_dec(v_a_1014_);
v_b_boxed_1017_ = lean_unbox_uint32(v_b_1015_);
lean_dec(v_b_1015_);
v_res_1018_ = lean_int32_dec_lt(v_a_boxed_1016_, v_b_boxed_1017_);
v_r_1019_ = lean_box(v_res_1018_);
return v_r_1019_;
}
}
LEAN_EXPORT uint8_t l_Int32_decLe___aux__1(uint32_t v_a_1020_, uint32_t v_b_1021_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1022_ = lean_unsigned_to_nat(32u);
v___x_1023_ = lean_uint32_to_nat(v_a_1020_);
v___x_1024_ = lean_uint32_to_nat(v_b_1021_);
v___x_1025_ = l_BitVec_sle(v___x_1022_, v___x_1023_, v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLe___aux__1___boxed(lean_object* v_a_1026_, lean_object* v_b_1027_){
_start:
{
uint32_t v_a_boxed_1028_; uint32_t v_b_boxed_1029_; uint8_t v_res_1030_; lean_object* v_r_1031_; 
v_a_boxed_1028_ = lean_unbox_uint32(v_a_1026_);
lean_dec(v_a_1026_);
v_b_boxed_1029_ = lean_unbox_uint32(v_b_1027_);
lean_dec(v_b_1027_);
v_res_1030_ = l_Int32_decLe___aux__1(v_a_boxed_1028_, v_b_boxed_1029_);
v_r_1031_ = lean_box(v_res_1030_);
return v_r_1031_;
}
}
LEAN_EXPORT lean_object* l_Int32_decLe___boxed(lean_object* v_a_1034_, lean_object* v_b_1035_){
_start:
{
uint32_t v_a_boxed_1036_; uint32_t v_b_boxed_1037_; uint8_t v_res_1038_; lean_object* v_r_1039_; 
v_a_boxed_1036_ = lean_unbox_uint32(v_a_1034_);
lean_dec(v_a_1034_);
v_b_boxed_1037_ = lean_unbox_uint32(v_b_1035_);
lean_dec(v_b_1035_);
v_res_1038_ = lean_int32_dec_le(v_a_boxed_1036_, v_b_boxed_1037_);
v_r_1039_ = lean_box(v_res_1038_);
return v_r_1039_;
}
}
LEAN_EXPORT uint32_t l_instMaxInt32___lam__0(uint32_t v_x_1040_, uint32_t v_y_1041_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = lean_int32_dec_le(v_x_1040_, v_y_1041_);
if (v___x_1042_ == 0)
{
return v_x_1040_;
}
else
{
return v_y_1041_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt32___lam__0___boxed(lean_object* v_x_1043_, lean_object* v_y_1044_){
_start:
{
uint32_t v_x_boxed_1045_; uint32_t v_y_boxed_1046_; uint32_t v_res_1047_; lean_object* v_r_1048_; 
v_x_boxed_1045_ = lean_unbox_uint32(v_x_1043_);
lean_dec(v_x_1043_);
v_y_boxed_1046_ = lean_unbox_uint32(v_y_1044_);
lean_dec(v_y_1044_);
v_res_1047_ = l_instMaxInt32___lam__0(v_x_boxed_1045_, v_y_boxed_1046_);
v_r_1048_ = lean_box_uint32(v_res_1047_);
return v_r_1048_;
}
}
LEAN_EXPORT uint32_t l_instMinInt32___lam__0(uint32_t v_x_1051_, uint32_t v_y_1052_){
_start:
{
uint8_t v___x_1053_; 
v___x_1053_ = lean_int32_dec_le(v_x_1051_, v_y_1052_);
if (v___x_1053_ == 0)
{
return v_y_1052_;
}
else
{
return v_x_1051_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt32___lam__0___boxed(lean_object* v_x_1054_, lean_object* v_y_1055_){
_start:
{
uint32_t v_x_boxed_1056_; uint32_t v_y_boxed_1057_; uint32_t v_res_1058_; lean_object* v_r_1059_; 
v_x_boxed_1056_ = lean_unbox_uint32(v_x_1054_);
lean_dec(v_x_1054_);
v_y_boxed_1057_ = lean_unbox_uint32(v_y_1055_);
lean_dec(v_y_1055_);
v_res_1058_ = l_instMinInt32___lam__0(v_x_boxed_1056_, v_y_boxed_1057_);
v_r_1059_ = lean_box_uint32(v_res_1058_);
return v_r_1059_;
}
}
static lean_object* _init_l_Int64_size___closed__0(void){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_cstr_to_nat("18446744073709551616");
return v___x_1062_;
}
}
static lean_object* _init_l_Int64_size(void){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_obj_once(&l_Int64_size___closed__0, &l_Int64_size___closed__0_once, _init_l_Int64_size___closed__0);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Int64_toBitVec(uint64_t v_x_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = lean_uint64_to_nat(v_x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Int64_toBitVec___boxed(lean_object* v_x_1066_){
_start:
{
uint64_t v_x_boxed_1067_; lean_object* v_res_1068_; 
v_x_boxed_1067_ = lean_unbox_uint64(v_x_1066_);
lean_dec_ref(v_x_1066_);
v_res_1068_ = l_Int64_toBitVec(v_x_boxed_1067_);
return v_res_1068_;
}
}
LEAN_EXPORT uint64_t l_UInt64_toInt64(uint64_t v_i_1069_){
_start:
{
return v_i_1069_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toInt64___boxed(lean_object* v_i_1070_){
_start:
{
uint64_t v_i_boxed_1071_; uint64_t v_res_1072_; lean_object* v_r_1073_; 
v_i_boxed_1071_ = lean_unbox_uint64(v_i_1070_);
lean_dec_ref(v_i_1070_);
v_res_1072_ = l_UInt64_toInt64(v_i_boxed_1071_);
v_r_1073_ = lean_box_uint64(v_res_1072_);
return v_r_1073_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofInt___boxed(lean_object* v_i_1075_){
_start:
{
uint64_t v_res_1076_; lean_object* v_r_1077_; 
v_res_1076_ = lean_int64_of_int(v_i_1075_);
lean_dec(v_i_1075_);
v_r_1077_ = lean_box_uint64(v_res_1076_);
return v_r_1077_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofNat___boxed(lean_object* v_n_1079_){
_start:
{
uint64_t v_res_1080_; lean_object* v_r_1081_; 
v_res_1080_ = lean_int64_of_nat(v_n_1079_);
lean_dec(v_n_1079_);
v_r_1081_ = lean_box_uint64(v_res_1080_);
return v_r_1081_;
}
}
LEAN_EXPORT uint64_t l_Int_toInt64(lean_object* v_i_1082_){
_start:
{
uint64_t v___x_1083_; 
v___x_1083_ = lean_int64_of_int(v_i_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Int_toInt64___boxed(lean_object* v_i_1084_){
_start:
{
uint64_t v_res_1085_; lean_object* v_r_1086_; 
v_res_1085_ = l_Int_toInt64(v_i_1084_);
lean_dec(v_i_1084_);
v_r_1086_ = lean_box_uint64(v_res_1085_);
return v_r_1086_;
}
}
LEAN_EXPORT uint64_t l_Nat_toInt64(lean_object* v_n_1087_){
_start:
{
uint64_t v___x_1088_; 
v___x_1088_ = lean_int64_of_nat(v_n_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Nat_toInt64___boxed(lean_object* v_n_1089_){
_start:
{
uint64_t v_res_1090_; lean_object* v_r_1091_; 
v_res_1090_ = l_Nat_toInt64(v_n_1089_);
lean_dec(v_n_1089_);
v_r_1091_ = lean_box_uint64(v_res_1090_);
return v_r_1091_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt___boxed(lean_object* v_i_1093_){
_start:
{
uint64_t v_i_boxed_1094_; lean_object* v_res_1095_; 
v_i_boxed_1094_ = lean_unbox_uint64(v_i_1093_);
lean_dec_ref(v_i_1093_);
v_res_1095_ = lean_int64_to_int_sint(v_i_boxed_1094_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg(uint64_t v_i_1096_){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = lean_int64_to_int_sint(v_i_1096_);
v___x_1098_ = l_Int_toNat(v___x_1097_);
lean_dec(v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg___boxed(lean_object* v_i_1099_){
_start:
{
uint64_t v_i_boxed_1100_; lean_object* v_res_1101_; 
v_i_boxed_1100_ = lean_unbox_uint64(v_i_1099_);
lean_dec_ref(v_i_1099_);
v_res_1101_ = l_Int64_toNatClampNeg(v_i_boxed_1100_);
return v_res_1101_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofBitVec(lean_object* v_b_1102_){
_start:
{
uint64_t v___x_1103_; 
v___x_1103_ = lean_uint64_of_nat_mk(v_b_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofBitVec___boxed(lean_object* v_b_1104_){
_start:
{
uint64_t v_res_1105_; lean_object* v_r_1106_; 
v_res_1105_ = l_Int64_ofBitVec(v_b_1104_);
v_r_1106_ = lean_box_uint64(v_res_1105_);
return v_r_1106_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt8___boxed(lean_object* v_a_1108_){
_start:
{
uint64_t v_a_boxed_1109_; uint8_t v_res_1110_; lean_object* v_r_1111_; 
v_a_boxed_1109_ = lean_unbox_uint64(v_a_1108_);
lean_dec_ref(v_a_1108_);
v_res_1110_ = lean_int64_to_int8(v_a_boxed_1109_);
v_r_1111_ = lean_box(v_res_1110_);
return v_r_1111_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt16___boxed(lean_object* v_a_1113_){
_start:
{
uint64_t v_a_boxed_1114_; uint16_t v_res_1115_; lean_object* v_r_1116_; 
v_a_boxed_1114_ = lean_unbox_uint64(v_a_1113_);
lean_dec_ref(v_a_1113_);
v_res_1115_ = lean_int64_to_int16(v_a_boxed_1114_);
v_r_1116_ = lean_box(v_res_1115_);
return v_r_1116_;
}
}
LEAN_EXPORT lean_object* l_Int64_toInt32___boxed(lean_object* v_a_1118_){
_start:
{
uint64_t v_a_boxed_1119_; uint32_t v_res_1120_; lean_object* v_r_1121_; 
v_a_boxed_1119_ = lean_unbox_uint64(v_a_1118_);
lean_dec_ref(v_a_1118_);
v_res_1120_ = lean_int64_to_int32(v_a_boxed_1119_);
v_r_1121_ = lean_box_uint32(v_res_1120_);
return v_r_1121_;
}
}
LEAN_EXPORT lean_object* l_Int8_toInt64___boxed(lean_object* v_a_1123_){
_start:
{
uint8_t v_a_boxed_1124_; uint64_t v_res_1125_; lean_object* v_r_1126_; 
v_a_boxed_1124_ = lean_unbox(v_a_1123_);
v_res_1125_ = lean_int8_to_int64(v_a_boxed_1124_);
v_r_1126_ = lean_box_uint64(v_res_1125_);
return v_r_1126_;
}
}
LEAN_EXPORT lean_object* l_Int16_toInt64___boxed(lean_object* v_a_1128_){
_start:
{
uint16_t v_a_boxed_1129_; uint64_t v_res_1130_; lean_object* v_r_1131_; 
v_a_boxed_1129_ = lean_unbox(v_a_1128_);
v_res_1130_ = lean_int16_to_int64(v_a_boxed_1129_);
v_r_1131_ = lean_box_uint64(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT lean_object* l_Int32_toInt64___boxed(lean_object* v_a_1133_){
_start:
{
uint32_t v_a_boxed_1134_; uint64_t v_res_1135_; lean_object* v_r_1136_; 
v_a_boxed_1134_ = lean_unbox_uint32(v_a_1133_);
lean_dec(v_a_1133_);
v_res_1135_ = lean_int32_to_int64(v_a_boxed_1134_);
v_r_1136_ = lean_box_uint64(v_res_1135_);
return v_r_1136_;
}
}
LEAN_EXPORT lean_object* l_Int64_neg___boxed(lean_object* v_i_1138_){
_start:
{
uint64_t v_i_boxed_1139_; uint64_t v_res_1140_; lean_object* v_r_1141_; 
v_i_boxed_1139_ = lean_unbox_uint64(v_i_1138_);
lean_dec_ref(v_i_1138_);
v_res_1140_ = lean_int64_neg(v_i_boxed_1139_);
v_r_1141_ = lean_box_uint64(v_res_1140_);
return v_r_1141_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0(uint64_t v_i_1142_){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_int64_to_int_sint(v_i_1142_);
v___x_1144_ = l_Int_repr(v___x_1143_);
lean_dec(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0___boxed(lean_object* v_i_1145_){
_start:
{
uint64_t v_i_boxed_1146_; lean_object* v_res_1147_; 
v_i_boxed_1146_ = lean_unbox_uint64(v_i_1145_);
lean_dec_ref(v_i_1145_);
v_res_1147_ = l_instToStringInt64___lam__0(v_i_boxed_1146_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_instReprInt64___lam__0(uint64_t v_i_1150_, lean_object* v_prec_1151_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1152_ = lean_int64_to_int_sint(v_i_1150_);
v___x_1153_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_1154_ = lean_int_dec_lt(v___x_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = l_Int_repr(v___x_1152_);
lean_dec(v___x_1152_);
v___x_1156_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1157_ = l_Int_repr(v___x_1152_);
lean_dec(v___x_1152_);
v___x_1158_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
v___x_1159_ = l_Repr_addAppParen(v___x_1158_, v_prec_1151_);
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l_instReprInt64___lam__0___boxed(lean_object* v_i_1160_, lean_object* v_prec_1161_){
_start:
{
uint64_t v_i_boxed_1162_; lean_object* v_res_1163_; 
v_i_boxed_1162_ = lean_unbox_uint64(v_i_1160_);
lean_dec_ref(v_i_1160_);
v_res_1163_ = l_instReprInt64___lam__0(v_i_boxed_1162_, v_prec_1161_);
lean_dec(v_prec_1161_);
return v_res_1163_;
}
}
static lean_object* _init_l_instReprAtomInt64(void){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_box(0);
return v___x_1166_;
}
}
LEAN_EXPORT uint64_t l_instHashableInt64___lam__0(uint64_t v_i_1167_){
_start:
{
return v_i_1167_;
}
}
LEAN_EXPORT lean_object* l_instHashableInt64___lam__0___boxed(lean_object* v_i_1168_){
_start:
{
uint64_t v_i_boxed_1169_; uint64_t v_res_1170_; lean_object* v_r_1171_; 
v_i_boxed_1169_ = lean_unbox_uint64(v_i_1168_);
lean_dec_ref(v_i_1168_);
v_res_1170_ = l_instHashableInt64___lam__0(v_i_boxed_1169_);
v_r_1171_ = lean_box_uint64(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT uint64_t l_Int64_instOfNat(lean_object* v_n_1174_){
_start:
{
uint64_t v___x_1175_; 
v___x_1175_ = lean_int64_of_nat(v_n_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Int64_instOfNat___boxed(lean_object* v_n_1176_){
_start:
{
uint64_t v_res_1177_; lean_object* v_r_1178_; 
v_res_1177_ = l_Int64_instOfNat(v_n_1176_);
lean_dec(v_n_1176_);
v_r_1178_ = lean_box_uint64(v_res_1177_);
return v_r_1178_;
}
}
static uint64_t _init_l_Int64_maxValue___closed__0(void){
_start:
{
lean_object* v___x_1181_; uint64_t v___x_1182_; 
v___x_1181_ = lean_cstr_to_nat("9223372036854775807");
v___x_1182_ = lean_int64_of_nat(v___x_1181_);
return v___x_1182_;
}
}
static uint64_t _init_l_Int64_maxValue(void){
_start:
{
uint64_t v___x_1183_; 
v___x_1183_ = lean_uint64_once(&l_Int64_maxValue___closed__0, &l_Int64_maxValue___closed__0_once, _init_l_Int64_maxValue___closed__0);
return v___x_1183_;
}
}
static lean_object* _init_l_Int64_minValue___closed__0(void){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_cstr_to_nat("9223372036854775808");
return v___x_1184_;
}
}
static uint64_t _init_l_Int64_minValue___closed__1(void){
_start:
{
lean_object* v___x_1185_; uint64_t v___x_1186_; 
v___x_1185_ = lean_obj_once(&l_Int64_minValue___closed__0, &l_Int64_minValue___closed__0_once, _init_l_Int64_minValue___closed__0);
v___x_1186_ = lean_int64_of_nat(v___x_1185_);
return v___x_1186_;
}
}
static uint64_t _init_l_Int64_minValue___closed__2(void){
_start:
{
uint64_t v___x_1187_; uint64_t v___x_1188_; 
v___x_1187_ = lean_uint64_once(&l_Int64_minValue___closed__1, &l_Int64_minValue___closed__1_once, _init_l_Int64_minValue___closed__1);
v___x_1188_ = lean_int64_neg(v___x_1187_);
return v___x_1188_;
}
}
static uint64_t _init_l_Int64_minValue(void){
_start:
{
uint64_t v___x_1189_; 
v___x_1189_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
return v___x_1189_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntLE___redArg(lean_object* v_i_1190_){
_start:
{
uint64_t v___x_1191_; 
v___x_1191_ = lean_int64_of_int(v_i_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntLE___redArg___boxed(lean_object* v_i_1192_){
_start:
{
uint64_t v_res_1193_; lean_object* v_r_1194_; 
v_res_1193_ = l_Int64_ofIntLE___redArg(v_i_1192_);
lean_dec(v_i_1192_);
v_r_1194_ = lean_box_uint64(v_res_1193_);
return v_r_1194_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntLE(lean_object* v_i_1195_, lean_object* v___hl_1196_, lean_object* v___hr_1197_){
_start:
{
uint64_t v___x_1198_; 
v___x_1198_ = lean_int64_of_int(v_i_1195_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntLE___boxed(lean_object* v_i_1199_, lean_object* v___hl_1200_, lean_object* v___hr_1201_){
_start:
{
uint64_t v_res_1202_; lean_object* v_r_1203_; 
v_res_1202_ = l_Int64_ofIntLE(v_i_1199_, v___hl_1200_, v___hr_1201_);
lean_dec(v_i_1199_);
v_r_1203_ = lean_box_uint64(v_res_1202_);
return v_r_1203_;
}
}
static lean_object* _init_l_Int64_ofIntClamp___closed__0(void){
_start:
{
uint64_t v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
v___x_1205_ = lean_int64_to_int_sint(v___x_1204_);
return v___x_1205_;
}
}
static lean_object* _init_l_Int64_ofIntClamp___closed__1(void){
_start:
{
uint64_t v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_uint64_once(&l_Int64_maxValue___closed__0, &l_Int64_maxValue___closed__0_once, _init_l_Int64_maxValue___closed__0);
v___x_1207_ = lean_int64_to_int_sint(v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntClamp(lean_object* v_i_1208_){
_start:
{
uint64_t v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1209_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
v___x_1210_ = lean_obj_once(&l_Int64_ofIntClamp___closed__0, &l_Int64_ofIntClamp___closed__0_once, _init_l_Int64_ofIntClamp___closed__0);
v___x_1211_ = lean_int_dec_le(v___x_1210_, v_i_1208_);
if (v___x_1211_ == 0)
{
return v___x_1209_;
}
else
{
lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1212_ = lean_obj_once(&l_Int64_ofIntClamp___closed__1, &l_Int64_ofIntClamp___closed__1_once, _init_l_Int64_ofIntClamp___closed__1);
v___x_1213_ = lean_int_dec_le(v_i_1208_, v___x_1212_);
if (v___x_1213_ == 0)
{
return v___x_1209_;
}
else
{
uint64_t v___x_1214_; 
v___x_1214_ = lean_int64_of_int(v_i_1208_);
return v___x_1214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntClamp___boxed(lean_object* v_i_1215_){
_start:
{
uint64_t v_res_1216_; lean_object* v_r_1217_; 
v_res_1216_ = l_Int64_ofIntClamp(v_i_1215_);
lean_dec(v_i_1215_);
v_r_1217_ = lean_box_uint64(v_res_1216_);
return v_r_1217_;
}
}
LEAN_EXPORT uint64_t l_Int64_ofIntTruncate(lean_object* v_i_1218_){
_start:
{
uint64_t v___x_1219_; 
v___x_1219_ = l_Int64_ofIntClamp(v_i_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Int64_ofIntTruncate___boxed(lean_object* v_i_1220_){
_start:
{
uint64_t v_res_1221_; lean_object* v_r_1222_; 
v_res_1221_ = l_Int64_ofIntTruncate(v_i_1220_);
lean_dec(v_i_1220_);
v_r_1222_ = lean_box_uint64(v_res_1221_);
return v_r_1222_;
}
}
LEAN_EXPORT lean_object* l_Int64_add___boxed(lean_object* v_a_1225_, lean_object* v_b_1226_){
_start:
{
uint64_t v_a_boxed_1227_; uint64_t v_b_boxed_1228_; uint64_t v_res_1229_; lean_object* v_r_1230_; 
v_a_boxed_1227_ = lean_unbox_uint64(v_a_1225_);
lean_dec_ref(v_a_1225_);
v_b_boxed_1228_ = lean_unbox_uint64(v_b_1226_);
lean_dec_ref(v_b_1226_);
v_res_1229_ = lean_int64_add(v_a_boxed_1227_, v_b_boxed_1228_);
v_r_1230_ = lean_box_uint64(v_res_1229_);
return v_r_1230_;
}
}
LEAN_EXPORT lean_object* l_Int64_sub___boxed(lean_object* v_a_1233_, lean_object* v_b_1234_){
_start:
{
uint64_t v_a_boxed_1235_; uint64_t v_b_boxed_1236_; uint64_t v_res_1237_; lean_object* v_r_1238_; 
v_a_boxed_1235_ = lean_unbox_uint64(v_a_1233_);
lean_dec_ref(v_a_1233_);
v_b_boxed_1236_ = lean_unbox_uint64(v_b_1234_);
lean_dec_ref(v_b_1234_);
v_res_1237_ = lean_int64_sub(v_a_boxed_1235_, v_b_boxed_1236_);
v_r_1238_ = lean_box_uint64(v_res_1237_);
return v_r_1238_;
}
}
LEAN_EXPORT lean_object* l_Int64_mul___boxed(lean_object* v_a_1241_, lean_object* v_b_1242_){
_start:
{
uint64_t v_a_boxed_1243_; uint64_t v_b_boxed_1244_; uint64_t v_res_1245_; lean_object* v_r_1246_; 
v_a_boxed_1243_ = lean_unbox_uint64(v_a_1241_);
lean_dec_ref(v_a_1241_);
v_b_boxed_1244_ = lean_unbox_uint64(v_b_1242_);
lean_dec_ref(v_b_1242_);
v_res_1245_ = lean_int64_mul(v_a_boxed_1243_, v_b_boxed_1244_);
v_r_1246_ = lean_box_uint64(v_res_1245_);
return v_r_1246_;
}
}
LEAN_EXPORT lean_object* l_Int64_div___boxed(lean_object* v_a_1249_, lean_object* v_b_1250_){
_start:
{
uint64_t v_a_boxed_1251_; uint64_t v_b_boxed_1252_; uint64_t v_res_1253_; lean_object* v_r_1254_; 
v_a_boxed_1251_ = lean_unbox_uint64(v_a_1249_);
lean_dec_ref(v_a_1249_);
v_b_boxed_1252_ = lean_unbox_uint64(v_b_1250_);
lean_dec_ref(v_b_1250_);
v_res_1253_ = lean_int64_div(v_a_boxed_1251_, v_b_boxed_1252_);
v_r_1254_ = lean_box_uint64(v_res_1253_);
return v_r_1254_;
}
}
static uint64_t _init_l_Int64_pow___closed__0(void){
_start:
{
lean_object* v___x_1255_; uint64_t v___x_1256_; 
v___x_1255_ = lean_unsigned_to_nat(1u);
v___x_1256_ = lean_int64_of_nat(v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT uint64_t l_Int64_pow(uint64_t v_x_1257_, lean_object* v_n_1258_){
_start:
{
lean_object* v_zero_1259_; uint8_t v_isZero_1260_; 
v_zero_1259_ = lean_unsigned_to_nat(0u);
v_isZero_1260_ = lean_nat_dec_eq(v_n_1258_, v_zero_1259_);
if (v_isZero_1260_ == 1)
{
uint64_t v___x_1261_; 
v___x_1261_ = lean_uint64_once(&l_Int64_pow___closed__0, &l_Int64_pow___closed__0_once, _init_l_Int64_pow___closed__0);
return v___x_1261_;
}
else
{
lean_object* v_one_1262_; lean_object* v_n_1263_; uint64_t v___x_1264_; uint64_t v___x_1265_; 
v_one_1262_ = lean_unsigned_to_nat(1u);
v_n_1263_ = lean_nat_sub(v_n_1258_, v_one_1262_);
v___x_1264_ = l_Int64_pow(v_x_1257_, v_n_1263_);
lean_dec(v_n_1263_);
v___x_1265_ = lean_int64_mul(v___x_1264_, v_x_1257_);
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l_Int64_pow___boxed(lean_object* v_x_1266_, lean_object* v_n_1267_){
_start:
{
uint64_t v_x_boxed_1268_; uint64_t v_res_1269_; lean_object* v_r_1270_; 
v_x_boxed_1268_ = lean_unbox_uint64(v_x_1266_);
lean_dec_ref(v_x_1266_);
v_res_1269_ = l_Int64_pow(v_x_boxed_1268_, v_n_1267_);
lean_dec(v_n_1267_);
v_r_1270_ = lean_box_uint64(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT lean_object* l_Int64_mod___boxed(lean_object* v_a_1273_, lean_object* v_b_1274_){
_start:
{
uint64_t v_a_boxed_1275_; uint64_t v_b_boxed_1276_; uint64_t v_res_1277_; lean_object* v_r_1278_; 
v_a_boxed_1275_ = lean_unbox_uint64(v_a_1273_);
lean_dec_ref(v_a_1273_);
v_b_boxed_1276_ = lean_unbox_uint64(v_b_1274_);
lean_dec_ref(v_b_1274_);
v_res_1277_ = lean_int64_mod(v_a_boxed_1275_, v_b_boxed_1276_);
v_r_1278_ = lean_box_uint64(v_res_1277_);
return v_r_1278_;
}
}
LEAN_EXPORT lean_object* l_Int64_land___boxed(lean_object* v_a_1281_, lean_object* v_b_1282_){
_start:
{
uint64_t v_a_boxed_1283_; uint64_t v_b_boxed_1284_; uint64_t v_res_1285_; lean_object* v_r_1286_; 
v_a_boxed_1283_ = lean_unbox_uint64(v_a_1281_);
lean_dec_ref(v_a_1281_);
v_b_boxed_1284_ = lean_unbox_uint64(v_b_1282_);
lean_dec_ref(v_b_1282_);
v_res_1285_ = lean_int64_land(v_a_boxed_1283_, v_b_boxed_1284_);
v_r_1286_ = lean_box_uint64(v_res_1285_);
return v_r_1286_;
}
}
LEAN_EXPORT lean_object* l_Int64_lor___boxed(lean_object* v_a_1289_, lean_object* v_b_1290_){
_start:
{
uint64_t v_a_boxed_1291_; uint64_t v_b_boxed_1292_; uint64_t v_res_1293_; lean_object* v_r_1294_; 
v_a_boxed_1291_ = lean_unbox_uint64(v_a_1289_);
lean_dec_ref(v_a_1289_);
v_b_boxed_1292_ = lean_unbox_uint64(v_b_1290_);
lean_dec_ref(v_b_1290_);
v_res_1293_ = lean_int64_lor(v_a_boxed_1291_, v_b_boxed_1292_);
v_r_1294_ = lean_box_uint64(v_res_1293_);
return v_r_1294_;
}
}
LEAN_EXPORT lean_object* l_Int64_xor___boxed(lean_object* v_a_1297_, lean_object* v_b_1298_){
_start:
{
uint64_t v_a_boxed_1299_; uint64_t v_b_boxed_1300_; uint64_t v_res_1301_; lean_object* v_r_1302_; 
v_a_boxed_1299_ = lean_unbox_uint64(v_a_1297_);
lean_dec_ref(v_a_1297_);
v_b_boxed_1300_ = lean_unbox_uint64(v_b_1298_);
lean_dec_ref(v_b_1298_);
v_res_1301_ = lean_int64_xor(v_a_boxed_1299_, v_b_boxed_1300_);
v_r_1302_ = lean_box_uint64(v_res_1301_);
return v_r_1302_;
}
}
LEAN_EXPORT lean_object* l_Int64_shiftLeft___boxed(lean_object* v_a_1305_, lean_object* v_b_1306_){
_start:
{
uint64_t v_a_boxed_1307_; uint64_t v_b_boxed_1308_; uint64_t v_res_1309_; lean_object* v_r_1310_; 
v_a_boxed_1307_ = lean_unbox_uint64(v_a_1305_);
lean_dec_ref(v_a_1305_);
v_b_boxed_1308_ = lean_unbox_uint64(v_b_1306_);
lean_dec_ref(v_b_1306_);
v_res_1309_ = lean_int64_shift_left(v_a_boxed_1307_, v_b_boxed_1308_);
v_r_1310_ = lean_box_uint64(v_res_1309_);
return v_r_1310_;
}
}
LEAN_EXPORT lean_object* l_Int64_shiftRight___boxed(lean_object* v_a_1313_, lean_object* v_b_1314_){
_start:
{
uint64_t v_a_boxed_1315_; uint64_t v_b_boxed_1316_; uint64_t v_res_1317_; lean_object* v_r_1318_; 
v_a_boxed_1315_ = lean_unbox_uint64(v_a_1313_);
lean_dec_ref(v_a_1313_);
v_b_boxed_1316_ = lean_unbox_uint64(v_b_1314_);
lean_dec_ref(v_b_1314_);
v_res_1317_ = lean_int64_shift_right(v_a_boxed_1315_, v_b_boxed_1316_);
v_r_1318_ = lean_box_uint64(v_res_1317_);
return v_r_1318_;
}
}
LEAN_EXPORT lean_object* l_Int64_complement___boxed(lean_object* v_a_1320_){
_start:
{
uint64_t v_a_boxed_1321_; uint64_t v_res_1322_; lean_object* v_r_1323_; 
v_a_boxed_1321_ = lean_unbox_uint64(v_a_1320_);
lean_dec_ref(v_a_1320_);
v_res_1322_ = lean_int64_complement(v_a_boxed_1321_);
v_r_1323_ = lean_box_uint64(v_res_1322_);
return v_r_1323_;
}
}
LEAN_EXPORT lean_object* l_Int64_abs___boxed(lean_object* v_a_1325_){
_start:
{
uint64_t v_a_boxed_1326_; uint64_t v_res_1327_; lean_object* v_r_1328_; 
v_a_boxed_1326_ = lean_unbox_uint64(v_a_1325_);
lean_dec_ref(v_a_1325_);
v_res_1327_ = lean_int64_abs(v_a_boxed_1326_);
v_r_1328_ = lean_box_uint64(v_res_1327_);
return v_r_1328_;
}
}
LEAN_EXPORT lean_object* l_Int64_decEq___boxed(lean_object* v_a_1331_, lean_object* v_b_1332_){
_start:
{
uint64_t v_a_boxed_1333_; uint64_t v_b_boxed_1334_; uint8_t v_res_1335_; lean_object* v_r_1336_; 
v_a_boxed_1333_ = lean_unbox_uint64(v_a_1331_);
lean_dec_ref(v_a_1331_);
v_b_boxed_1334_ = lean_unbox_uint64(v_b_1332_);
lean_dec_ref(v_b_1332_);
v_res_1335_ = lean_int64_dec_eq(v_a_boxed_1333_, v_b_boxed_1334_);
v_r_1336_ = lean_box(v_res_1335_);
return v_r_1336_;
}
}
static uint64_t _init_l_instInhabitedInt64___closed__0(void){
_start:
{
lean_object* v___x_1337_; uint64_t v___x_1338_; 
v___x_1337_ = lean_unsigned_to_nat(0u);
v___x_1338_ = lean_int64_of_nat(v___x_1337_);
return v___x_1338_;
}
}
static uint64_t _init_l_instInhabitedInt64(void){
_start:
{
uint64_t v___x_1339_; 
v___x_1339_ = lean_uint64_once(&l_instInhabitedInt64___closed__0, &l_instInhabitedInt64___closed__0_once, _init_l_instInhabitedInt64___closed__0);
return v___x_1339_;
}
}
static lean_object* _init_l_instLTInt64(void){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_box(0);
return v___x_1352_;
}
}
static lean_object* _init_l_instLEInt64(void){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_box(0);
return v___x_1353_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqInt64(uint64_t v_a_1366_, uint64_t v_b_1367_){
_start:
{
uint8_t v___x_1368_; 
v___x_1368_ = lean_int64_dec_eq(v_a_1366_, v_b_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqInt64___boxed(lean_object* v_a_1369_, lean_object* v_b_1370_){
_start:
{
uint64_t v_a_boxed_1371_; uint64_t v_b_boxed_1372_; uint8_t v_res_1373_; lean_object* v_r_1374_; 
v_a_boxed_1371_ = lean_unbox_uint64(v_a_1369_);
lean_dec_ref(v_a_1369_);
v_b_boxed_1372_ = lean_unbox_uint64(v_b_1370_);
lean_dec_ref(v_b_1370_);
v_res_1373_ = l_instDecidableEqInt64(v_a_boxed_1371_, v_b_boxed_1372_);
v_r_1374_ = lean_box(v_res_1373_);
return v_r_1374_;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt64___boxed(lean_object* v_b_1376_){
_start:
{
uint8_t v_b_boxed_1377_; uint64_t v_res_1378_; lean_object* v_r_1379_; 
v_b_boxed_1377_ = lean_unbox(v_b_1376_);
v_res_1378_ = lean_bool_to_int64(v_b_boxed_1377_);
v_r_1379_ = lean_box_uint64(v_res_1378_);
return v_r_1379_;
}
}
LEAN_EXPORT uint8_t l_Int64_decLt___aux__1(uint64_t v_a_1380_, uint64_t v_b_1381_){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1382_ = lean_unsigned_to_nat(64u);
v___x_1383_ = lean_uint64_to_nat(v_a_1380_);
v___x_1384_ = lean_uint64_to_nat(v_b_1381_);
v___x_1385_ = l_BitVec_slt(v___x_1382_, v___x_1383_, v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLt___aux__1___boxed(lean_object* v_a_1386_, lean_object* v_b_1387_){
_start:
{
uint64_t v_a_boxed_1388_; uint64_t v_b_boxed_1389_; uint8_t v_res_1390_; lean_object* v_r_1391_; 
v_a_boxed_1388_ = lean_unbox_uint64(v_a_1386_);
lean_dec_ref(v_a_1386_);
v_b_boxed_1389_ = lean_unbox_uint64(v_b_1387_);
lean_dec_ref(v_b_1387_);
v_res_1390_ = l_Int64_decLt___aux__1(v_a_boxed_1388_, v_b_boxed_1389_);
v_r_1391_ = lean_box(v_res_1390_);
return v_r_1391_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLt___boxed(lean_object* v_a_1394_, lean_object* v_b_1395_){
_start:
{
uint64_t v_a_boxed_1396_; uint64_t v_b_boxed_1397_; uint8_t v_res_1398_; lean_object* v_r_1399_; 
v_a_boxed_1396_ = lean_unbox_uint64(v_a_1394_);
lean_dec_ref(v_a_1394_);
v_b_boxed_1397_ = lean_unbox_uint64(v_b_1395_);
lean_dec_ref(v_b_1395_);
v_res_1398_ = lean_int64_dec_lt(v_a_boxed_1396_, v_b_boxed_1397_);
v_r_1399_ = lean_box(v_res_1398_);
return v_r_1399_;
}
}
LEAN_EXPORT uint8_t l_Int64_decLe___aux__1(uint64_t v_a_1400_, uint64_t v_b_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1402_ = lean_unsigned_to_nat(64u);
v___x_1403_ = lean_uint64_to_nat(v_a_1400_);
v___x_1404_ = lean_uint64_to_nat(v_b_1401_);
v___x_1405_ = l_BitVec_sle(v___x_1402_, v___x_1403_, v___x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLe___aux__1___boxed(lean_object* v_a_1406_, lean_object* v_b_1407_){
_start:
{
uint64_t v_a_boxed_1408_; uint64_t v_b_boxed_1409_; uint8_t v_res_1410_; lean_object* v_r_1411_; 
v_a_boxed_1408_ = lean_unbox_uint64(v_a_1406_);
lean_dec_ref(v_a_1406_);
v_b_boxed_1409_ = lean_unbox_uint64(v_b_1407_);
lean_dec_ref(v_b_1407_);
v_res_1410_ = l_Int64_decLe___aux__1(v_a_boxed_1408_, v_b_boxed_1409_);
v_r_1411_ = lean_box(v_res_1410_);
return v_r_1411_;
}
}
LEAN_EXPORT lean_object* l_Int64_decLe___boxed(lean_object* v_a_1414_, lean_object* v_b_1415_){
_start:
{
uint64_t v_a_boxed_1416_; uint64_t v_b_boxed_1417_; uint8_t v_res_1418_; lean_object* v_r_1419_; 
v_a_boxed_1416_ = lean_unbox_uint64(v_a_1414_);
lean_dec_ref(v_a_1414_);
v_b_boxed_1417_ = lean_unbox_uint64(v_b_1415_);
lean_dec_ref(v_b_1415_);
v_res_1418_ = lean_int64_dec_le(v_a_boxed_1416_, v_b_boxed_1417_);
v_r_1419_ = lean_box(v_res_1418_);
return v_r_1419_;
}
}
LEAN_EXPORT uint64_t l_instMaxInt64___lam__0(uint64_t v_x_1420_, uint64_t v_y_1421_){
_start:
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_int64_dec_le(v_x_1420_, v_y_1421_);
if (v___x_1422_ == 0)
{
return v_x_1420_;
}
else
{
return v_y_1421_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxInt64___lam__0___boxed(lean_object* v_x_1423_, lean_object* v_y_1424_){
_start:
{
uint64_t v_x_boxed_1425_; uint64_t v_y_boxed_1426_; uint64_t v_res_1427_; lean_object* v_r_1428_; 
v_x_boxed_1425_ = lean_unbox_uint64(v_x_1423_);
lean_dec_ref(v_x_1423_);
v_y_boxed_1426_ = lean_unbox_uint64(v_y_1424_);
lean_dec_ref(v_y_1424_);
v_res_1427_ = l_instMaxInt64___lam__0(v_x_boxed_1425_, v_y_boxed_1426_);
v_r_1428_ = lean_box_uint64(v_res_1427_);
return v_r_1428_;
}
}
LEAN_EXPORT uint64_t l_instMinInt64___lam__0(uint64_t v_x_1431_, uint64_t v_y_1432_){
_start:
{
uint8_t v___x_1433_; 
v___x_1433_ = lean_int64_dec_le(v_x_1431_, v_y_1432_);
if (v___x_1433_ == 0)
{
return v_y_1432_;
}
else
{
return v_x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_instMinInt64___lam__0___boxed(lean_object* v_x_1434_, lean_object* v_y_1435_){
_start:
{
uint64_t v_x_boxed_1436_; uint64_t v_y_boxed_1437_; uint64_t v_res_1438_; lean_object* v_r_1439_; 
v_x_boxed_1436_ = lean_unbox_uint64(v_x_1434_);
lean_dec_ref(v_x_1434_);
v_y_boxed_1437_ = lean_unbox_uint64(v_y_1435_);
lean_dec_ref(v_y_1435_);
v_res_1438_ = l_instMinInt64___lam__0(v_x_boxed_1436_, v_y_boxed_1437_);
v_r_1439_ = lean_box_uint64(v_res_1438_);
return v_r_1439_;
}
}
static lean_object* _init_l_ISize_size___closed__0(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = l_System_Platform_numBits;
v___x_1443_ = lean_unsigned_to_nat(2u);
v___x_1444_ = lean_nat_pow(v___x_1443_, v___x_1442_);
return v___x_1444_;
}
}
static lean_object* _init_l_ISize_size(void){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_obj_once(&l_ISize_size___closed__0, &l_ISize_size___closed__0_once, _init_l_ISize_size___closed__0);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_ISize_toBitVec(size_t v_x_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_usize_to_nat(v_x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_ISize_toBitVec___boxed(lean_object* v_x_1448_){
_start:
{
size_t v_x_boxed_1449_; lean_object* v_res_1450_; 
v_x_boxed_1449_ = lean_unbox_usize(v_x_1448_);
lean_dec(v_x_1448_);
v_res_1450_ = l_ISize_toBitVec(v_x_boxed_1449_);
return v_res_1450_;
}
}
LEAN_EXPORT size_t l_USize_toISize(size_t v_i_1451_){
_start:
{
return v_i_1451_;
}
}
LEAN_EXPORT lean_object* l_USize_toISize___boxed(lean_object* v_i_1452_){
_start:
{
size_t v_i_boxed_1453_; size_t v_res_1454_; lean_object* v_r_1455_; 
v_i_boxed_1453_ = lean_unbox_usize(v_i_1452_);
lean_dec(v_i_1452_);
v_res_1454_ = l_USize_toISize(v_i_boxed_1453_);
v_r_1455_ = lean_box_usize(v_res_1454_);
return v_r_1455_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofInt___boxed(lean_object* v_i_1457_){
_start:
{
size_t v_res_1458_; lean_object* v_r_1459_; 
v_res_1458_ = lean_isize_of_int(v_i_1457_);
lean_dec(v_i_1457_);
v_r_1459_ = lean_box_usize(v_res_1458_);
return v_r_1459_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofNat___boxed(lean_object* v_n_1461_){
_start:
{
size_t v_res_1462_; lean_object* v_r_1463_; 
v_res_1462_ = lean_isize_of_nat(v_n_1461_);
lean_dec(v_n_1461_);
v_r_1463_ = lean_box_usize(v_res_1462_);
return v_r_1463_;
}
}
LEAN_EXPORT size_t l_Int_toISize(lean_object* v_i_1464_){
_start:
{
size_t v___x_1465_; 
v___x_1465_ = lean_isize_of_int(v_i_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Int_toISize___boxed(lean_object* v_i_1466_){
_start:
{
size_t v_res_1467_; lean_object* v_r_1468_; 
v_res_1467_ = l_Int_toISize(v_i_1466_);
lean_dec(v_i_1466_);
v_r_1468_ = lean_box_usize(v_res_1467_);
return v_r_1468_;
}
}
LEAN_EXPORT size_t l_Nat_toISize(lean_object* v_n_1469_){
_start:
{
size_t v___x_1470_; 
v___x_1470_ = lean_isize_of_nat(v_n_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Nat_toISize___boxed(lean_object* v_n_1471_){
_start:
{
size_t v_res_1472_; lean_object* v_r_1473_; 
v_res_1472_ = l_Nat_toISize(v_n_1471_);
lean_dec(v_n_1471_);
v_r_1473_ = lean_box_usize(v_res_1472_);
return v_r_1473_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt___boxed(lean_object* v_i_1475_){
_start:
{
size_t v_i_boxed_1476_; lean_object* v_res_1477_; 
v_i_boxed_1476_ = lean_unbox_usize(v_i_1475_);
lean_dec(v_i_1475_);
v_res_1477_ = lean_isize_to_int(v_i_boxed_1476_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg(size_t v_i_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_isize_to_int(v_i_1478_);
v___x_1480_ = l_Int_toNat(v___x_1479_);
lean_dec(v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg___boxed(lean_object* v_i_1481_){
_start:
{
size_t v_i_boxed_1482_; lean_object* v_res_1483_; 
v_i_boxed_1482_ = lean_unbox_usize(v_i_1481_);
lean_dec(v_i_1481_);
v_res_1483_ = l_ISize_toNatClampNeg(v_i_boxed_1482_);
return v_res_1483_;
}
}
LEAN_EXPORT size_t l_ISize_ofBitVec(lean_object* v_b_1484_){
_start:
{
size_t v___x_1485_; 
v___x_1485_ = lean_usize_of_nat_mk(v_b_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofBitVec___boxed(lean_object* v_b_1486_){
_start:
{
size_t v_res_1487_; lean_object* v_r_1488_; 
v_res_1487_ = l_ISize_ofBitVec(v_b_1486_);
v_r_1488_ = lean_box_usize(v_res_1487_);
return v_r_1488_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt8___boxed(lean_object* v_a_1490_){
_start:
{
size_t v_a_boxed_1491_; uint8_t v_res_1492_; lean_object* v_r_1493_; 
v_a_boxed_1491_ = lean_unbox_usize(v_a_1490_);
lean_dec(v_a_1490_);
v_res_1492_ = lean_isize_to_int8(v_a_boxed_1491_);
v_r_1493_ = lean_box(v_res_1492_);
return v_r_1493_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt16___boxed(lean_object* v_a_1495_){
_start:
{
size_t v_a_boxed_1496_; uint16_t v_res_1497_; lean_object* v_r_1498_; 
v_a_boxed_1496_ = lean_unbox_usize(v_a_1495_);
lean_dec(v_a_1495_);
v_res_1497_ = lean_isize_to_int16(v_a_boxed_1496_);
v_r_1498_ = lean_box(v_res_1497_);
return v_r_1498_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt32___boxed(lean_object* v_a_1500_){
_start:
{
size_t v_a_boxed_1501_; uint32_t v_res_1502_; lean_object* v_r_1503_; 
v_a_boxed_1501_ = lean_unbox_usize(v_a_1500_);
lean_dec(v_a_1500_);
v_res_1502_ = lean_isize_to_int32(v_a_boxed_1501_);
v_r_1503_ = lean_box_uint32(v_res_1502_);
return v_r_1503_;
}
}
LEAN_EXPORT lean_object* l_ISize_toInt64___boxed(lean_object* v_a_1505_){
_start:
{
size_t v_a_boxed_1506_; uint64_t v_res_1507_; lean_object* v_r_1508_; 
v_a_boxed_1506_ = lean_unbox_usize(v_a_1505_);
lean_dec(v_a_1505_);
v_res_1507_ = lean_isize_to_int64(v_a_boxed_1506_);
v_r_1508_ = lean_box_uint64(v_res_1507_);
return v_r_1508_;
}
}
LEAN_EXPORT lean_object* l_Int8_toISize___boxed(lean_object* v_a_1510_){
_start:
{
uint8_t v_a_boxed_1511_; size_t v_res_1512_; lean_object* v_r_1513_; 
v_a_boxed_1511_ = lean_unbox(v_a_1510_);
v_res_1512_ = lean_int8_to_isize(v_a_boxed_1511_);
v_r_1513_ = lean_box_usize(v_res_1512_);
return v_r_1513_;
}
}
LEAN_EXPORT lean_object* l_Int16_toISize___boxed(lean_object* v_a_1515_){
_start:
{
uint16_t v_a_boxed_1516_; size_t v_res_1517_; lean_object* v_r_1518_; 
v_a_boxed_1516_ = lean_unbox(v_a_1515_);
v_res_1517_ = lean_int16_to_isize(v_a_boxed_1516_);
v_r_1518_ = lean_box_usize(v_res_1517_);
return v_r_1518_;
}
}
LEAN_EXPORT lean_object* l_Int32_toISize___boxed(lean_object* v_a_1520_){
_start:
{
uint32_t v_a_boxed_1521_; size_t v_res_1522_; lean_object* v_r_1523_; 
v_a_boxed_1521_ = lean_unbox_uint32(v_a_1520_);
lean_dec(v_a_1520_);
v_res_1522_ = lean_int32_to_isize(v_a_boxed_1521_);
v_r_1523_ = lean_box_usize(v_res_1522_);
return v_r_1523_;
}
}
LEAN_EXPORT lean_object* l_Int64_toISize___boxed(lean_object* v_a_1525_){
_start:
{
uint64_t v_a_boxed_1526_; size_t v_res_1527_; lean_object* v_r_1528_; 
v_a_boxed_1526_ = lean_unbox_uint64(v_a_1525_);
lean_dec_ref(v_a_1525_);
v_res_1527_ = lean_int64_to_isize(v_a_boxed_1526_);
v_r_1528_ = lean_box_usize(v_res_1527_);
return v_r_1528_;
}
}
LEAN_EXPORT lean_object* l_ISize_neg___boxed(lean_object* v_i_1530_){
_start:
{
size_t v_i_boxed_1531_; size_t v_res_1532_; lean_object* v_r_1533_; 
v_i_boxed_1531_ = lean_unbox_usize(v_i_1530_);
lean_dec(v_i_1530_);
v_res_1532_ = lean_isize_neg(v_i_boxed_1531_);
v_r_1533_ = lean_box_usize(v_res_1532_);
return v_r_1533_;
}
}
LEAN_EXPORT lean_object* l_instToStringISize___lam__0(size_t v_i_1534_){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = lean_isize_to_int(v_i_1534_);
v___x_1536_ = l_Int_repr(v___x_1535_);
lean_dec(v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_instToStringISize___lam__0___boxed(lean_object* v_i_1537_){
_start:
{
size_t v_i_boxed_1538_; lean_object* v_res_1539_; 
v_i_boxed_1538_ = lean_unbox_usize(v_i_1537_);
lean_dec(v_i_1537_);
v_res_1539_ = l_instToStringISize___lam__0(v_i_boxed_1538_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_instReprISize___lam__0(size_t v_i_1542_, lean_object* v_prec_1543_){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1544_ = lean_isize_to_int(v_i_1542_);
v___x_1545_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_1546_ = lean_int_dec_lt(v___x_1544_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = l_Int_repr(v___x_1544_);
lean_dec(v___x_1544_);
v___x_1548_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
return v___x_1548_;
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = l_Int_repr(v___x_1544_);
lean_dec(v___x_1544_);
v___x_1550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
v___x_1551_ = l_Repr_addAppParen(v___x_1550_, v_prec_1543_);
return v___x_1551_;
}
}
}
LEAN_EXPORT lean_object* l_instReprISize___lam__0___boxed(lean_object* v_i_1552_, lean_object* v_prec_1553_){
_start:
{
size_t v_i_boxed_1554_; lean_object* v_res_1555_; 
v_i_boxed_1554_ = lean_unbox_usize(v_i_1552_);
lean_dec(v_i_1552_);
v_res_1555_ = l_instReprISize___lam__0(v_i_boxed_1554_, v_prec_1553_);
lean_dec(v_prec_1553_);
return v_res_1555_;
}
}
static lean_object* _init_l_instReprAtomISize(void){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_box(0);
return v___x_1558_;
}
}
LEAN_EXPORT size_t l_ISize_instOfNat(lean_object* v_n_1561_){
_start:
{
size_t v___x_1562_; 
v___x_1562_ = lean_isize_of_nat(v_n_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_ISize_instOfNat___boxed(lean_object* v_n_1563_){
_start:
{
size_t v_res_1564_; lean_object* v_r_1565_; 
v_res_1564_ = l_ISize_instOfNat(v_n_1563_);
lean_dec(v_n_1563_);
v_r_1565_ = lean_box_usize(v_res_1564_);
return v_r_1565_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__0(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_unsigned_to_nat(2u);
v___x_1569_ = lean_nat_to_int(v___x_1568_);
return v___x_1569_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__1(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = lean_unsigned_to_nat(1u);
v___x_1571_ = l_System_Platform_numBits;
v___x_1572_ = lean_nat_sub(v___x_1571_, v___x_1570_);
return v___x_1572_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__2(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1573_ = lean_obj_once(&l_ISize_maxValue___closed__1, &l_ISize_maxValue___closed__1_once, _init_l_ISize_maxValue___closed__1);
v___x_1574_ = lean_obj_once(&l_ISize_maxValue___closed__0, &l_ISize_maxValue___closed__0_once, _init_l_ISize_maxValue___closed__0);
v___x_1575_ = l_Int_pow(v___x_1574_, v___x_1573_);
return v___x_1575_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__3(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_unsigned_to_nat(1u);
v___x_1577_ = lean_nat_to_int(v___x_1576_);
return v___x_1577_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__4(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1578_ = lean_obj_once(&l_ISize_maxValue___closed__3, &l_ISize_maxValue___closed__3_once, _init_l_ISize_maxValue___closed__3);
v___x_1579_ = lean_obj_once(&l_ISize_maxValue___closed__2, &l_ISize_maxValue___closed__2_once, _init_l_ISize_maxValue___closed__2);
v___x_1580_ = lean_int_sub(v___x_1579_, v___x_1578_);
return v___x_1580_;
}
}
static size_t _init_l_ISize_maxValue___closed__5(void){
_start:
{
lean_object* v___x_1581_; size_t v___x_1582_; 
v___x_1581_ = lean_obj_once(&l_ISize_maxValue___closed__4, &l_ISize_maxValue___closed__4_once, _init_l_ISize_maxValue___closed__4);
v___x_1582_ = lean_isize_of_int(v___x_1581_);
return v___x_1582_;
}
}
static size_t _init_l_ISize_maxValue(void){
_start:
{
size_t v___x_1583_; 
v___x_1583_ = lean_usize_once(&l_ISize_maxValue___closed__5, &l_ISize_maxValue___closed__5_once, _init_l_ISize_maxValue___closed__5);
return v___x_1583_;
}
}
static lean_object* _init_l_ISize_minValue___closed__0(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_obj_once(&l_ISize_maxValue___closed__2, &l_ISize_maxValue___closed__2_once, _init_l_ISize_maxValue___closed__2);
v___x_1585_ = lean_int_neg(v___x_1584_);
return v___x_1585_;
}
}
static size_t _init_l_ISize_minValue___closed__1(void){
_start:
{
lean_object* v___x_1586_; size_t v___x_1587_; 
v___x_1586_ = lean_obj_once(&l_ISize_minValue___closed__0, &l_ISize_minValue___closed__0_once, _init_l_ISize_minValue___closed__0);
v___x_1587_ = lean_isize_of_int(v___x_1586_);
return v___x_1587_;
}
}
static size_t _init_l_ISize_minValue(void){
_start:
{
size_t v___x_1588_; 
v___x_1588_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
return v___x_1588_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntLE___redArg(lean_object* v_i_1589_){
_start:
{
size_t v___x_1590_; 
v___x_1590_ = lean_isize_of_int(v_i_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntLE___redArg___boxed(lean_object* v_i_1591_){
_start:
{
size_t v_res_1592_; lean_object* v_r_1593_; 
v_res_1592_ = l_ISize_ofIntLE___redArg(v_i_1591_);
lean_dec(v_i_1591_);
v_r_1593_ = lean_box_usize(v_res_1592_);
return v_r_1593_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntLE(lean_object* v_i_1594_, lean_object* v___hl_1595_, lean_object* v___hr_1596_){
_start:
{
size_t v___x_1597_; 
v___x_1597_ = lean_isize_of_int(v_i_1594_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntLE___boxed(lean_object* v_i_1598_, lean_object* v___hl_1599_, lean_object* v___hr_1600_){
_start:
{
size_t v_res_1601_; lean_object* v_r_1602_; 
v_res_1601_ = l_ISize_ofIntLE(v_i_1598_, v___hl_1599_, v___hr_1600_);
lean_dec(v_i_1598_);
v_r_1602_ = lean_box_usize(v_res_1601_);
return v_r_1602_;
}
}
static lean_object* _init_l_ISize_ofIntClamp___closed__0(void){
_start:
{
size_t v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
v___x_1604_ = lean_isize_to_int(v___x_1603_);
return v___x_1604_;
}
}
static lean_object* _init_l_ISize_ofIntClamp___closed__1(void){
_start:
{
size_t v___x_1605_; lean_object* v___x_1606_; 
v___x_1605_ = lean_usize_once(&l_ISize_maxValue___closed__5, &l_ISize_maxValue___closed__5_once, _init_l_ISize_maxValue___closed__5);
v___x_1606_ = lean_isize_to_int(v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntClamp(lean_object* v_i_1607_){
_start:
{
size_t v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1608_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
v___x_1609_ = lean_obj_once(&l_ISize_ofIntClamp___closed__0, &l_ISize_ofIntClamp___closed__0_once, _init_l_ISize_ofIntClamp___closed__0);
v___x_1610_ = lean_int_dec_le(v___x_1609_, v_i_1607_);
if (v___x_1610_ == 0)
{
return v___x_1608_;
}
else
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = lean_obj_once(&l_ISize_ofIntClamp___closed__1, &l_ISize_ofIntClamp___closed__1_once, _init_l_ISize_ofIntClamp___closed__1);
v___x_1612_ = lean_int_dec_le(v_i_1607_, v___x_1611_);
if (v___x_1612_ == 0)
{
return v___x_1608_;
}
else
{
size_t v___x_1613_; 
v___x_1613_ = lean_isize_of_int(v_i_1607_);
return v___x_1613_;
}
}
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntClamp___boxed(lean_object* v_i_1614_){
_start:
{
size_t v_res_1615_; lean_object* v_r_1616_; 
v_res_1615_ = l_ISize_ofIntClamp(v_i_1614_);
lean_dec(v_i_1614_);
v_r_1616_ = lean_box_usize(v_res_1615_);
return v_r_1616_;
}
}
LEAN_EXPORT size_t l_ISize_ofIntTruncate(lean_object* v_i_1617_){
_start:
{
size_t v___x_1618_; 
v___x_1618_ = l_ISize_ofIntClamp(v_i_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_ISize_ofIntTruncate___boxed(lean_object* v_i_1619_){
_start:
{
size_t v_res_1620_; lean_object* v_r_1621_; 
v_res_1620_ = l_ISize_ofIntTruncate(v_i_1619_);
lean_dec(v_i_1619_);
v_r_1621_ = lean_box_usize(v_res_1620_);
return v_r_1621_;
}
}
LEAN_EXPORT lean_object* l_ISize_add___boxed(lean_object* v_a_1624_, lean_object* v_b_1625_){
_start:
{
size_t v_a_boxed_1626_; size_t v_b_boxed_1627_; size_t v_res_1628_; lean_object* v_r_1629_; 
v_a_boxed_1626_ = lean_unbox_usize(v_a_1624_);
lean_dec(v_a_1624_);
v_b_boxed_1627_ = lean_unbox_usize(v_b_1625_);
lean_dec(v_b_1625_);
v_res_1628_ = lean_isize_add(v_a_boxed_1626_, v_b_boxed_1627_);
v_r_1629_ = lean_box_usize(v_res_1628_);
return v_r_1629_;
}
}
LEAN_EXPORT lean_object* l_ISize_sub___boxed(lean_object* v_a_1632_, lean_object* v_b_1633_){
_start:
{
size_t v_a_boxed_1634_; size_t v_b_boxed_1635_; size_t v_res_1636_; lean_object* v_r_1637_; 
v_a_boxed_1634_ = lean_unbox_usize(v_a_1632_);
lean_dec(v_a_1632_);
v_b_boxed_1635_ = lean_unbox_usize(v_b_1633_);
lean_dec(v_b_1633_);
v_res_1636_ = lean_isize_sub(v_a_boxed_1634_, v_b_boxed_1635_);
v_r_1637_ = lean_box_usize(v_res_1636_);
return v_r_1637_;
}
}
LEAN_EXPORT lean_object* l_ISize_mul___boxed(lean_object* v_a_1640_, lean_object* v_b_1641_){
_start:
{
size_t v_a_boxed_1642_; size_t v_b_boxed_1643_; size_t v_res_1644_; lean_object* v_r_1645_; 
v_a_boxed_1642_ = lean_unbox_usize(v_a_1640_);
lean_dec(v_a_1640_);
v_b_boxed_1643_ = lean_unbox_usize(v_b_1641_);
lean_dec(v_b_1641_);
v_res_1644_ = lean_isize_mul(v_a_boxed_1642_, v_b_boxed_1643_);
v_r_1645_ = lean_box_usize(v_res_1644_);
return v_r_1645_;
}
}
LEAN_EXPORT lean_object* l_ISize_div___boxed(lean_object* v_a_1648_, lean_object* v_b_1649_){
_start:
{
size_t v_a_boxed_1650_; size_t v_b_boxed_1651_; size_t v_res_1652_; lean_object* v_r_1653_; 
v_a_boxed_1650_ = lean_unbox_usize(v_a_1648_);
lean_dec(v_a_1648_);
v_b_boxed_1651_ = lean_unbox_usize(v_b_1649_);
lean_dec(v_b_1649_);
v_res_1652_ = lean_isize_div(v_a_boxed_1650_, v_b_boxed_1651_);
v_r_1653_ = lean_box_usize(v_res_1652_);
return v_r_1653_;
}
}
static size_t _init_l_ISize_pow___closed__0(void){
_start:
{
lean_object* v___x_1654_; size_t v___x_1655_; 
v___x_1654_ = lean_unsigned_to_nat(1u);
v___x_1655_ = lean_isize_of_nat(v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT size_t l_ISize_pow(size_t v_x_1656_, lean_object* v_n_1657_){
_start:
{
lean_object* v_zero_1658_; uint8_t v_isZero_1659_; 
v_zero_1658_ = lean_unsigned_to_nat(0u);
v_isZero_1659_ = lean_nat_dec_eq(v_n_1657_, v_zero_1658_);
if (v_isZero_1659_ == 1)
{
size_t v___x_1660_; 
v___x_1660_ = lean_usize_once(&l_ISize_pow___closed__0, &l_ISize_pow___closed__0_once, _init_l_ISize_pow___closed__0);
return v___x_1660_;
}
else
{
lean_object* v_one_1661_; lean_object* v_n_1662_; size_t v___x_1663_; size_t v___x_1664_; 
v_one_1661_ = lean_unsigned_to_nat(1u);
v_n_1662_ = lean_nat_sub(v_n_1657_, v_one_1661_);
v___x_1663_ = l_ISize_pow(v_x_1656_, v_n_1662_);
lean_dec(v_n_1662_);
v___x_1664_ = lean_isize_mul(v___x_1663_, v_x_1656_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l_ISize_pow___boxed(lean_object* v_x_1665_, lean_object* v_n_1666_){
_start:
{
size_t v_x_boxed_1667_; size_t v_res_1668_; lean_object* v_r_1669_; 
v_x_boxed_1667_ = lean_unbox_usize(v_x_1665_);
lean_dec(v_x_1665_);
v_res_1668_ = l_ISize_pow(v_x_boxed_1667_, v_n_1666_);
lean_dec(v_n_1666_);
v_r_1669_ = lean_box_usize(v_res_1668_);
return v_r_1669_;
}
}
LEAN_EXPORT lean_object* l_ISize_mod___boxed(lean_object* v_a_1672_, lean_object* v_b_1673_){
_start:
{
size_t v_a_boxed_1674_; size_t v_b_boxed_1675_; size_t v_res_1676_; lean_object* v_r_1677_; 
v_a_boxed_1674_ = lean_unbox_usize(v_a_1672_);
lean_dec(v_a_1672_);
v_b_boxed_1675_ = lean_unbox_usize(v_b_1673_);
lean_dec(v_b_1673_);
v_res_1676_ = lean_isize_mod(v_a_boxed_1674_, v_b_boxed_1675_);
v_r_1677_ = lean_box_usize(v_res_1676_);
return v_r_1677_;
}
}
LEAN_EXPORT lean_object* l_ISize_land___boxed(lean_object* v_a_1680_, lean_object* v_b_1681_){
_start:
{
size_t v_a_boxed_1682_; size_t v_b_boxed_1683_; size_t v_res_1684_; lean_object* v_r_1685_; 
v_a_boxed_1682_ = lean_unbox_usize(v_a_1680_);
lean_dec(v_a_1680_);
v_b_boxed_1683_ = lean_unbox_usize(v_b_1681_);
lean_dec(v_b_1681_);
v_res_1684_ = lean_isize_land(v_a_boxed_1682_, v_b_boxed_1683_);
v_r_1685_ = lean_box_usize(v_res_1684_);
return v_r_1685_;
}
}
LEAN_EXPORT lean_object* l_ISize_lor___boxed(lean_object* v_a_1688_, lean_object* v_b_1689_){
_start:
{
size_t v_a_boxed_1690_; size_t v_b_boxed_1691_; size_t v_res_1692_; lean_object* v_r_1693_; 
v_a_boxed_1690_ = lean_unbox_usize(v_a_1688_);
lean_dec(v_a_1688_);
v_b_boxed_1691_ = lean_unbox_usize(v_b_1689_);
lean_dec(v_b_1689_);
v_res_1692_ = lean_isize_lor(v_a_boxed_1690_, v_b_boxed_1691_);
v_r_1693_ = lean_box_usize(v_res_1692_);
return v_r_1693_;
}
}
LEAN_EXPORT lean_object* l_ISize_xor___boxed(lean_object* v_a_1696_, lean_object* v_b_1697_){
_start:
{
size_t v_a_boxed_1698_; size_t v_b_boxed_1699_; size_t v_res_1700_; lean_object* v_r_1701_; 
v_a_boxed_1698_ = lean_unbox_usize(v_a_1696_);
lean_dec(v_a_1696_);
v_b_boxed_1699_ = lean_unbox_usize(v_b_1697_);
lean_dec(v_b_1697_);
v_res_1700_ = lean_isize_xor(v_a_boxed_1698_, v_b_boxed_1699_);
v_r_1701_ = lean_box_usize(v_res_1700_);
return v_r_1701_;
}
}
LEAN_EXPORT lean_object* l_ISize_shiftLeft___boxed(lean_object* v_a_1704_, lean_object* v_b_1705_){
_start:
{
size_t v_a_boxed_1706_; size_t v_b_boxed_1707_; size_t v_res_1708_; lean_object* v_r_1709_; 
v_a_boxed_1706_ = lean_unbox_usize(v_a_1704_);
lean_dec(v_a_1704_);
v_b_boxed_1707_ = lean_unbox_usize(v_b_1705_);
lean_dec(v_b_1705_);
v_res_1708_ = lean_isize_shift_left(v_a_boxed_1706_, v_b_boxed_1707_);
v_r_1709_ = lean_box_usize(v_res_1708_);
return v_r_1709_;
}
}
LEAN_EXPORT lean_object* l_ISize_shiftRight___boxed(lean_object* v_a_1712_, lean_object* v_b_1713_){
_start:
{
size_t v_a_boxed_1714_; size_t v_b_boxed_1715_; size_t v_res_1716_; lean_object* v_r_1717_; 
v_a_boxed_1714_ = lean_unbox_usize(v_a_1712_);
lean_dec(v_a_1712_);
v_b_boxed_1715_ = lean_unbox_usize(v_b_1713_);
lean_dec(v_b_1713_);
v_res_1716_ = lean_isize_shift_right(v_a_boxed_1714_, v_b_boxed_1715_);
v_r_1717_ = lean_box_usize(v_res_1716_);
return v_r_1717_;
}
}
LEAN_EXPORT lean_object* l_ISize_complement___boxed(lean_object* v_a_1719_){
_start:
{
size_t v_a_boxed_1720_; size_t v_res_1721_; lean_object* v_r_1722_; 
v_a_boxed_1720_ = lean_unbox_usize(v_a_1719_);
lean_dec(v_a_1719_);
v_res_1721_ = lean_isize_complement(v_a_boxed_1720_);
v_r_1722_ = lean_box_usize(v_res_1721_);
return v_r_1722_;
}
}
LEAN_EXPORT lean_object* l_ISize_abs___boxed(lean_object* v_a_1724_){
_start:
{
size_t v_a_boxed_1725_; size_t v_res_1726_; lean_object* v_r_1727_; 
v_a_boxed_1725_ = lean_unbox_usize(v_a_1724_);
lean_dec(v_a_1724_);
v_res_1726_ = lean_isize_abs(v_a_boxed_1725_);
v_r_1727_ = lean_box_usize(v_res_1726_);
return v_r_1727_;
}
}
LEAN_EXPORT lean_object* l_ISize_decEq___boxed(lean_object* v_a_1730_, lean_object* v_b_1731_){
_start:
{
size_t v_a_boxed_1732_; size_t v_b_boxed_1733_; uint8_t v_res_1734_; lean_object* v_r_1735_; 
v_a_boxed_1732_ = lean_unbox_usize(v_a_1730_);
lean_dec(v_a_1730_);
v_b_boxed_1733_ = lean_unbox_usize(v_b_1731_);
lean_dec(v_b_1731_);
v_res_1734_ = lean_isize_dec_eq(v_a_boxed_1732_, v_b_boxed_1733_);
v_r_1735_ = lean_box(v_res_1734_);
return v_r_1735_;
}
}
static size_t _init_l_instInhabitedISize___closed__0(void){
_start:
{
lean_object* v___x_1736_; size_t v___x_1737_; 
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = lean_isize_of_nat(v___x_1736_);
return v___x_1737_;
}
}
static size_t _init_l_instInhabitedISize(void){
_start:
{
size_t v___x_1738_; 
v___x_1738_ = lean_usize_once(&l_instInhabitedISize___closed__0, &l_instInhabitedISize___closed__0_once, _init_l_instInhabitedISize___closed__0);
return v___x_1738_;
}
}
static lean_object* _init_l_instLTISize(void){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = lean_box(0);
return v___x_1751_;
}
}
static lean_object* _init_l_instLEISize(void){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_box(0);
return v___x_1752_;
}
}
LEAN_EXPORT uint8_t l_instDecidableEqISize(size_t v_a_1765_, size_t v_b_1766_){
_start:
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_isize_dec_eq(v_a_1765_, v_b_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_instDecidableEqISize___boxed(lean_object* v_a_1768_, lean_object* v_b_1769_){
_start:
{
size_t v_a_boxed_1770_; size_t v_b_boxed_1771_; uint8_t v_res_1772_; lean_object* v_r_1773_; 
v_a_boxed_1770_ = lean_unbox_usize(v_a_1768_);
lean_dec(v_a_1768_);
v_b_boxed_1771_ = lean_unbox_usize(v_b_1769_);
lean_dec(v_b_1769_);
v_res_1772_ = l_instDecidableEqISize(v_a_boxed_1770_, v_b_boxed_1771_);
v_r_1773_ = lean_box(v_res_1772_);
return v_r_1773_;
}
}
LEAN_EXPORT lean_object* l_Bool_toISize___boxed(lean_object* v_b_1775_){
_start:
{
uint8_t v_b_boxed_1776_; size_t v_res_1777_; lean_object* v_r_1778_; 
v_b_boxed_1776_ = lean_unbox(v_b_1775_);
v_res_1777_ = lean_bool_to_isize(v_b_boxed_1776_);
v_r_1778_ = lean_box_usize(v_res_1777_);
return v_r_1778_;
}
}
LEAN_EXPORT uint8_t l_ISize_decLt___aux__1(size_t v_a_1779_, size_t v_b_1780_){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1781_ = l_System_Platform_numBits;
v___x_1782_ = lean_usize_to_nat(v_a_1779_);
v___x_1783_ = lean_usize_to_nat(v_b_1780_);
v___x_1784_ = l_BitVec_slt(v___x_1781_, v___x_1782_, v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLt___aux__1___boxed(lean_object* v_a_1785_, lean_object* v_b_1786_){
_start:
{
size_t v_a_boxed_1787_; size_t v_b_boxed_1788_; uint8_t v_res_1789_; lean_object* v_r_1790_; 
v_a_boxed_1787_ = lean_unbox_usize(v_a_1785_);
lean_dec(v_a_1785_);
v_b_boxed_1788_ = lean_unbox_usize(v_b_1786_);
lean_dec(v_b_1786_);
v_res_1789_ = l_ISize_decLt___aux__1(v_a_boxed_1787_, v_b_boxed_1788_);
v_r_1790_ = lean_box(v_res_1789_);
return v_r_1790_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLt___boxed(lean_object* v_a_1793_, lean_object* v_b_1794_){
_start:
{
size_t v_a_boxed_1795_; size_t v_b_boxed_1796_; uint8_t v_res_1797_; lean_object* v_r_1798_; 
v_a_boxed_1795_ = lean_unbox_usize(v_a_1793_);
lean_dec(v_a_1793_);
v_b_boxed_1796_ = lean_unbox_usize(v_b_1794_);
lean_dec(v_b_1794_);
v_res_1797_ = lean_isize_dec_lt(v_a_boxed_1795_, v_b_boxed_1796_);
v_r_1798_ = lean_box(v_res_1797_);
return v_r_1798_;
}
}
LEAN_EXPORT uint8_t l_ISize_decLe___aux__1(size_t v_a_1799_, size_t v_b_1800_){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1801_ = l_System_Platform_numBits;
v___x_1802_ = lean_usize_to_nat(v_a_1799_);
v___x_1803_ = lean_usize_to_nat(v_b_1800_);
v___x_1804_ = l_BitVec_sle(v___x_1801_, v___x_1802_, v___x_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLe___aux__1___boxed(lean_object* v_a_1805_, lean_object* v_b_1806_){
_start:
{
size_t v_a_boxed_1807_; size_t v_b_boxed_1808_; uint8_t v_res_1809_; lean_object* v_r_1810_; 
v_a_boxed_1807_ = lean_unbox_usize(v_a_1805_);
lean_dec(v_a_1805_);
v_b_boxed_1808_ = lean_unbox_usize(v_b_1806_);
lean_dec(v_b_1806_);
v_res_1809_ = l_ISize_decLe___aux__1(v_a_boxed_1807_, v_b_boxed_1808_);
v_r_1810_ = lean_box(v_res_1809_);
return v_r_1810_;
}
}
LEAN_EXPORT lean_object* l_ISize_decLe___boxed(lean_object* v_a_1813_, lean_object* v_b_1814_){
_start:
{
size_t v_a_boxed_1815_; size_t v_b_boxed_1816_; uint8_t v_res_1817_; lean_object* v_r_1818_; 
v_a_boxed_1815_ = lean_unbox_usize(v_a_1813_);
lean_dec(v_a_1813_);
v_b_boxed_1816_ = lean_unbox_usize(v_b_1814_);
lean_dec(v_b_1814_);
v_res_1817_ = lean_isize_dec_le(v_a_boxed_1815_, v_b_boxed_1816_);
v_r_1818_ = lean_box(v_res_1817_);
return v_r_1818_;
}
}
LEAN_EXPORT size_t l_instMaxISize___lam__0(size_t v_x_1819_, size_t v_y_1820_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_isize_dec_le(v_x_1819_, v_y_1820_);
if (v___x_1821_ == 0)
{
return v_x_1819_;
}
else
{
return v_y_1820_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxISize___lam__0___boxed(lean_object* v_x_1822_, lean_object* v_y_1823_){
_start:
{
size_t v_x_boxed_1824_; size_t v_y_boxed_1825_; size_t v_res_1826_; lean_object* v_r_1827_; 
v_x_boxed_1824_ = lean_unbox_usize(v_x_1822_);
lean_dec(v_x_1822_);
v_y_boxed_1825_ = lean_unbox_usize(v_y_1823_);
lean_dec(v_y_1823_);
v_res_1826_ = l_instMaxISize___lam__0(v_x_boxed_1824_, v_y_boxed_1825_);
v_r_1827_ = lean_box_usize(v_res_1826_);
return v_r_1827_;
}
}
LEAN_EXPORT size_t l_instMinISize___lam__0(size_t v_x_1830_, size_t v_y_1831_){
_start:
{
uint8_t v___x_1832_; 
v___x_1832_ = lean_isize_dec_le(v_x_1830_, v_y_1831_);
if (v___x_1832_ == 0)
{
return v_y_1831_;
}
else
{
return v_x_1830_;
}
}
}
LEAN_EXPORT lean_object* l_instMinISize___lam__0___boxed(lean_object* v_x_1833_, lean_object* v_y_1834_){
_start:
{
size_t v_x_boxed_1835_; size_t v_y_boxed_1836_; size_t v_res_1837_; lean_object* v_r_1838_; 
v_x_boxed_1835_ = lean_unbox_usize(v_x_1833_);
lean_dec(v_x_1833_);
v_y_boxed_1836_ = lean_unbox_usize(v_y_1834_);
lean_dec(v_y_1834_);
v_res_1837_ = l_instMinISize___lam__0(v_x_boxed_1835_, v_y_boxed_1836_);
v_r_1838_ = lean_box_usize(v_res_1837_);
return v_r_1838_;
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
