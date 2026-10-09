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
lean_object* lean_usize_to_nat(size_t);
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
LEAN_EXPORT lean_object* l_ISize_toBitVec32___redArg(size_t);
LEAN_EXPORT lean_object* l_ISize_toBitVec32___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ISize_toBitVec32(size_t, lean_object*);
LEAN_EXPORT lean_object* l_ISize_toBitVec32___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ISize_toBitVec64___redArg(size_t);
LEAN_EXPORT lean_object* l_ISize_toBitVec64___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ISize_toBitVec64(size_t, lean_object*);
LEAN_EXPORT lean_object* l_ISize_toBitVec64___boxed(lean_object*, lean_object*);
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
lean_object* l_Int8_toBitVec(uint8_t v_x_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_uint8_to_nat(v_x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Int8_toBitVec_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_2_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Int8_toBitVec(v_x_2_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Int8_toBitVec___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Int8_toBitVec(v_x_boxed_6_);
return v_res_7_;
}
}
uint8_t l_UInt8_toInt8(uint8_t v_i_8_){
_start:
{
return v_i_8_;
}
}
LEAN_EXPORT void l_UInt8_toInt8_0interp(lean_interpreter_value* stack)
{
uint8_t v_i_8_ = stack[0].m_num;
uint8_t v_res_9_;
v_res_9_ = l_UInt8_toInt8(v_i_8_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_UInt8_toInt8___boxed(lean_object* v_i_10_){
_start:
{
uint8_t v_i_boxed_11_; uint8_t v_res_12_; lean_object* v_r_13_; 
v_i_boxed_11_ = lean_unbox(v_i_10_);
v_res_12_ = l_UInt8_toInt8(v_i_boxed_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT void l_Int8_ofInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_14_ = stack[0].m_obj;
uint8_t v_res_15_;
v_res_15_ = lean_int8_of_int(v_i_14_);
stack->m_num = v_res_15_;
}
LEAN_EXPORT lean_object* l_Int8_ofInt___boxed(lean_object* v_i_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = lean_int8_of_int(v_i_16_);
lean_dec(v_i_16_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT void l_Int8_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_19_ = stack[0].m_obj;
uint8_t v_res_20_;
v_res_20_ = lean_int8_of_nat(v_n_19_);
stack->m_num = v_res_20_;
}
LEAN_EXPORT lean_object* l_Int8_ofNat___boxed(lean_object* v_n_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = lean_int8_of_nat(v_n_21_);
lean_dec(v_n_21_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
uint8_t l_Int_toInt8(lean_object* v_i_24_){
_start:
{
uint8_t v___x_25_; 
v___x_25_ = lean_int8_of_int(v_i_24_);
return v___x_25_;
}
}
LEAN_EXPORT void l_Int_toInt8_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_24_ = stack[0].m_obj;
uint8_t v_res_26_;
v_res_26_ = l_Int_toInt8(v_i_24_);
stack->m_num = v_res_26_;
}
LEAN_EXPORT lean_object* l_Int_toInt8___boxed(lean_object* v_i_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Int_toInt8(v_i_27_);
lean_dec(v_i_27_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
uint8_t l_Nat_toInt8(lean_object* v_n_30_){
_start:
{
uint8_t v___x_31_; 
v___x_31_ = lean_int8_of_nat(v_n_30_);
return v___x_31_;
}
}
LEAN_EXPORT void l_Nat_toInt8_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_30_ = stack[0].m_obj;
uint8_t v_res_32_;
v_res_32_ = l_Nat_toInt8(v_n_30_);
stack->m_num = v_res_32_;
}
LEAN_EXPORT lean_object* l_Nat_toInt8___boxed(lean_object* v_n_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Nat_toInt8(v_n_33_);
lean_dec(v_n_33_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
LEAN_EXPORT void l_Int8_toInt_0interp(lean_interpreter_value* stack)
{
uint8_t v_i_36_ = stack[0].m_num;
lean_object* v_res_37_;
v_res_37_ = lean_int8_to_int(v_i_36_);
stack->m_obj
 = v_res_37_;
}
LEAN_EXPORT lean_object* l_Int8_toInt___boxed(lean_object* v_i_38_){
_start:
{
uint8_t v_i_boxed_39_; lean_object* v_res_40_; 
v_i_boxed_39_ = lean_unbox(v_i_38_);
v_res_40_ = lean_int8_to_int(v_i_boxed_39_);
return v_res_40_;
}
}
lean_object* l_Int8_toNatClampNeg(uint8_t v_i_41_){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_int8_to_int(v_i_41_);
v___x_43_ = l_Int_toNat(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT void l_Int8_toNatClampNeg_0interp(lean_interpreter_value* stack)
{
uint8_t v_i_41_ = stack[0].m_num;
lean_object* v_res_44_;
v_res_44_ = l_Int8_toNatClampNeg(v_i_41_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Int8_toNatClampNeg___boxed(lean_object* v_i_45_){
_start:
{
uint8_t v_i_boxed_46_; lean_object* v_res_47_; 
v_i_boxed_46_ = lean_unbox(v_i_45_);
v_res_47_ = l_Int8_toNatClampNeg(v_i_boxed_46_);
return v_res_47_;
}
}
uint8_t l_Int8_ofBitVec(lean_object* v_b_48_){
_start:
{
uint8_t v___x_49_; 
v___x_49_ = lean_uint8_of_nat_mk(v_b_48_);
return v___x_49_;
}
}
LEAN_EXPORT void l_Int8_ofBitVec_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_48_ = stack[0].m_obj;
uint8_t v_res_50_;
v_res_50_ = l_Int8_ofBitVec(v_b_48_);
stack->m_num = v_res_50_;
}
LEAN_EXPORT lean_object* l_Int8_ofBitVec___boxed(lean_object* v_b_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Int8_ofBitVec(v_b_51_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT void l_Int8_neg_0interp(lean_interpreter_value* stack)
{
uint8_t v_i_54_ = stack[0].m_num;
uint8_t v_res_55_;
v_res_55_ = lean_int8_neg(v_i_54_);
stack->m_num = v_res_55_;
}
LEAN_EXPORT lean_object* l_Int8_neg___boxed(lean_object* v_i_56_){
_start:
{
uint8_t v_i_boxed_57_; uint8_t v_res_58_; lean_object* v_r_59_; 
v_i_boxed_57_ = lean_unbox(v_i_56_);
v_res_58_ = lean_int8_neg(v_i_boxed_57_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
lean_object* l_instToStringInt8___lam__0(uint8_t v_i_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_int8_to_int(v_i_60_);
v___x_62_ = l_Int_repr(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT void l_instToStringInt8___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_i_60_ = stack[0].m_num;
lean_object* v_res_63_;
v_res_63_ = l_instToStringInt8___lam__0(v_i_60_);
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l_instToStringInt8___lam__0___boxed(lean_object* v_i_64_){
_start:
{
uint8_t v_i_boxed_65_; lean_object* v_res_66_; 
v_i_boxed_65_ = lean_unbox(v_i_64_);
v_res_66_ = l_instToStringInt8___lam__0(v_i_boxed_65_);
return v_res_66_;
}
}
static lean_object* _init_l_instReprInt8___lam__0___closed__0(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_nat_to_int(v___x_69_);
return v___x_70_;
}
}
lean_object* l_instReprInt8___lam__0(uint8_t v_i_71_, lean_object* v_prec_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_73_ = lean_int8_to_int(v_i_71_);
v___x_74_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
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
LEAN_EXPORT void l_instReprInt8___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_i_71_ = stack[0].m_num;
lean_object* v_prec_72_ = stack[1].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_instReprInt8___lam__0(v_i_71_, v_prec_72_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_instReprInt8___lam__0___boxed(lean_object* v_i_82_, lean_object* v_prec_83_){
_start:
{
uint8_t v_i_boxed_84_; lean_object* v_res_85_; 
v_i_boxed_84_ = lean_unbox(v_i_82_);
v_res_85_ = l_instReprInt8___lam__0(v_i_boxed_84_, v_prec_83_);
lean_dec(v_prec_83_);
return v_res_85_;
}
}
static lean_object* _init_l_instReprAtomInt8(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(0);
return v___x_88_;
}
}
uint8_t l_Int8_instOfNat(lean_object* v_n_91_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = lean_int8_of_nat(v_n_91_);
return v___x_92_;
}
}
LEAN_EXPORT void l_Int8_instOfNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_91_ = stack[0].m_obj;
uint8_t v_res_93_;
v_res_93_ = l_Int8_instOfNat(v_n_91_);
stack->m_num = v_res_93_;
}
LEAN_EXPORT lean_object* l_Int8_instOfNat___boxed(lean_object* v_n_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Int8_instOfNat(v_n_94_);
lean_dec(v_n_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
static uint8_t _init_l_Int8_maxValue___closed__0(void){
_start:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(127u);
v___x_100_ = lean_int8_of_nat(v___x_99_);
return v___x_100_;
}
}
static uint8_t _init_l_Int8_maxValue(void){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lean_uint8_once(&l_Int8_maxValue___closed__0, &l_Int8_maxValue___closed__0_once, _init_l_Int8_maxValue___closed__0);
return v___x_101_;
}
}
static uint8_t _init_l_Int8_minValue___closed__0(void){
_start:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(128u);
v___x_103_ = lean_int8_of_nat(v___x_102_);
return v___x_103_;
}
}
static uint8_t _init_l_Int8_minValue___closed__1(void){
_start:
{
uint8_t v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_uint8_once(&l_Int8_minValue___closed__0, &l_Int8_minValue___closed__0_once, _init_l_Int8_minValue___closed__0);
v___x_105_ = lean_int8_neg(v___x_104_);
return v___x_105_;
}
}
static uint8_t _init_l_Int8_minValue(void){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = lean_uint8_once(&l_Int8_minValue___closed__1, &l_Int8_minValue___closed__1_once, _init_l_Int8_minValue___closed__1);
return v___x_106_;
}
}
uint8_t l_Int8_ofIntLE___redArg(lean_object* v_i_107_){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = lean_int8_of_int(v_i_107_);
return v___x_108_;
}
}
LEAN_EXPORT void l_Int8_ofIntLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_107_ = stack[0].m_obj;
uint8_t v_res_109_;
v_res_109_ = l_Int8_ofIntLE___redArg(v_i_107_);
stack->m_num = v_res_109_;
}
LEAN_EXPORT lean_object* l_Int8_ofIntLE___redArg___boxed(lean_object* v_i_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Int8_ofIntLE___redArg(v_i_110_);
lean_dec(v_i_110_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
uint8_t l_Int8_ofIntLE(lean_object* v_i_113_, lean_object* v___hl_114_, lean_object* v___hr_115_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = lean_int8_of_int(v_i_113_);
return v___x_116_;
}
}
LEAN_EXPORT void l_Int8_ofIntLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_113_ = stack[0].m_obj;
uint8_t v_res_117_;
v_res_117_ = l_Int8_ofIntLE(v_i_113_, lean_box(0), lean_box(0));
stack->m_num = v_res_117_;
}
LEAN_EXPORT lean_object* l_Int8_ofIntLE___boxed(lean_object* v_i_118_, lean_object* v___hl_119_, lean_object* v___hr_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Int8_ofIntLE(v_i_118_, v___hl_119_, v___hr_120_);
lean_dec(v_i_118_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
static lean_object* _init_l_Int8_ofIntClamp___closed__0(void){
_start:
{
uint8_t v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_uint8_once(&l_Int8_minValue___closed__1, &l_Int8_minValue___closed__1_once, _init_l_Int8_minValue___closed__1);
v___x_124_ = lean_int8_to_int(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Int8_ofIntClamp___closed__1(void){
_start:
{
uint8_t v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_uint8_once(&l_Int8_maxValue___closed__0, &l_Int8_maxValue___closed__0_once, _init_l_Int8_maxValue___closed__0);
v___x_126_ = lean_int8_to_int(v___x_125_);
return v___x_126_;
}
}
uint8_t l_Int8_ofIntClamp(lean_object* v_i_127_){
_start:
{
uint8_t v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_128_ = lean_uint8_once(&l_Int8_minValue___closed__1, &l_Int8_minValue___closed__1_once, _init_l_Int8_minValue___closed__1);
v___x_129_ = lean_obj_once(&l_Int8_ofIntClamp___closed__0, &l_Int8_ofIntClamp___closed__0_once, _init_l_Int8_ofIntClamp___closed__0);
v___x_130_ = lean_int_dec_le(v___x_129_, v_i_127_);
if (v___x_130_ == 0)
{
return v___x_128_;
}
else
{
uint8_t v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = lean_uint8_once(&l_Int8_maxValue___closed__0, &l_Int8_maxValue___closed__0_once, _init_l_Int8_maxValue___closed__0);
v___x_132_ = lean_obj_once(&l_Int8_ofIntClamp___closed__1, &l_Int8_ofIntClamp___closed__1_once, _init_l_Int8_ofIntClamp___closed__1);
v___x_133_ = lean_int_dec_le(v_i_127_, v___x_132_);
if (v___x_133_ == 0)
{
return v___x_131_;
}
else
{
uint8_t v___x_134_; 
v___x_134_ = lean_int8_of_int(v_i_127_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT void l_Int8_ofIntClamp_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_127_ = stack[0].m_obj;
uint8_t v_res_135_;
v_res_135_ = l_Int8_ofIntClamp(v_i_127_);
stack->m_num = v_res_135_;
}
LEAN_EXPORT lean_object* l_Int8_ofIntClamp___boxed(lean_object* v_i_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Int8_ofIntClamp(v_i_136_);
lean_dec(v_i_136_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
uint8_t l_Int8_ofIntTruncate(lean_object* v_i_139_){
_start:
{
uint8_t v___x_140_; 
v___x_140_ = l_Int8_ofIntClamp(v_i_139_);
return v___x_140_;
}
}
LEAN_EXPORT void l_Int8_ofIntTruncate_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_139_ = stack[0].m_obj;
uint8_t v_res_141_;
v_res_141_ = l_Int8_ofIntTruncate(v_i_139_);
stack->m_num = v_res_141_;
}
LEAN_EXPORT lean_object* l_Int8_ofIntTruncate___boxed(lean_object* v_i_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Int8_ofIntTruncate(v_i_142_);
lean_dec(v_i_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT void l_Int8_add_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_145_ = stack[0].m_num;
uint8_t v_b_146_ = stack[1].m_num;
uint8_t v_res_147_;
v_res_147_ = lean_int8_add(v_a_145_, v_b_146_);
stack->m_num = v_res_147_;
}
LEAN_EXPORT lean_object* l_Int8_add___boxed(lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
uint8_t v_a_boxed_150_; uint8_t v_b_boxed_151_; uint8_t v_res_152_; lean_object* v_r_153_; 
v_a_boxed_150_ = lean_unbox(v_a_148_);
v_b_boxed_151_ = lean_unbox(v_b_149_);
v_res_152_ = lean_int8_add(v_a_boxed_150_, v_b_boxed_151_);
v_r_153_ = lean_box(v_res_152_);
return v_r_153_;
}
}
LEAN_EXPORT void l_Int8_sub_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_154_ = stack[0].m_num;
uint8_t v_b_155_ = stack[1].m_num;
uint8_t v_res_156_;
v_res_156_ = lean_int8_sub(v_a_154_, v_b_155_);
stack->m_num = v_res_156_;
}
LEAN_EXPORT lean_object* l_Int8_sub___boxed(lean_object* v_a_157_, lean_object* v_b_158_){
_start:
{
uint8_t v_a_boxed_159_; uint8_t v_b_boxed_160_; uint8_t v_res_161_; lean_object* v_r_162_; 
v_a_boxed_159_ = lean_unbox(v_a_157_);
v_b_boxed_160_ = lean_unbox(v_b_158_);
v_res_161_ = lean_int8_sub(v_a_boxed_159_, v_b_boxed_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT void l_Int8_mul_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_163_ = stack[0].m_num;
uint8_t v_b_164_ = stack[1].m_num;
uint8_t v_res_165_;
v_res_165_ = lean_int8_mul(v_a_163_, v_b_164_);
stack->m_num = v_res_165_;
}
LEAN_EXPORT lean_object* l_Int8_mul___boxed(lean_object* v_a_166_, lean_object* v_b_167_){
_start:
{
uint8_t v_a_boxed_168_; uint8_t v_b_boxed_169_; uint8_t v_res_170_; lean_object* v_r_171_; 
v_a_boxed_168_ = lean_unbox(v_a_166_);
v_b_boxed_169_ = lean_unbox(v_b_167_);
v_res_170_ = lean_int8_mul(v_a_boxed_168_, v_b_boxed_169_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT void l_Int8_div_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_172_ = stack[0].m_num;
uint8_t v_b_173_ = stack[1].m_num;
uint8_t v_res_174_;
v_res_174_ = lean_int8_div(v_a_172_, v_b_173_);
stack->m_num = v_res_174_;
}
LEAN_EXPORT lean_object* l_Int8_div___boxed(lean_object* v_a_175_, lean_object* v_b_176_){
_start:
{
uint8_t v_a_boxed_177_; uint8_t v_b_boxed_178_; uint8_t v_res_179_; lean_object* v_r_180_; 
v_a_boxed_177_ = lean_unbox(v_a_175_);
v_b_boxed_178_ = lean_unbox(v_b_176_);
v_res_179_ = lean_int8_div(v_a_boxed_177_, v_b_boxed_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
static uint8_t _init_l_Int8_pow___closed__0(void){
_start:
{
lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_int8_of_nat(v___x_181_);
return v___x_182_;
}
}
uint8_t l_Int8_pow(uint8_t v_x_183_, lean_object* v_n_184_){
_start:
{
lean_object* v_zero_185_; uint8_t v_isZero_186_; 
v_zero_185_ = lean_unsigned_to_nat(0u);
v_isZero_186_ = lean_nat_dec_eq(v_n_184_, v_zero_185_);
if (v_isZero_186_ == 1)
{
uint8_t v___x_187_; 
v___x_187_ = lean_uint8_once(&l_Int8_pow___closed__0, &l_Int8_pow___closed__0_once, _init_l_Int8_pow___closed__0);
return v___x_187_;
}
else
{
lean_object* v_one_188_; lean_object* v_n_189_; uint8_t v___x_190_; uint8_t v___x_191_; 
v_one_188_ = lean_unsigned_to_nat(1u);
v_n_189_ = lean_nat_sub(v_n_184_, v_one_188_);
v___x_190_ = l_Int8_pow(v_x_183_, v_n_189_);
lean_dec(v_n_189_);
v___x_191_ = lean_int8_mul(v___x_190_, v_x_183_);
return v___x_191_;
}
}
}
LEAN_EXPORT void l_Int8_pow_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_183_ = stack[0].m_num;
lean_object* v_n_184_ = stack[1].m_obj;
uint8_t v_res_192_;
v_res_192_ = l_Int8_pow(v_x_183_, v_n_184_);
stack->m_num = v_res_192_;
}
LEAN_EXPORT lean_object* l_Int8_pow___boxed(lean_object* v_x_193_, lean_object* v_n_194_){
_start:
{
uint8_t v_x_boxed_195_; uint8_t v_res_196_; lean_object* v_r_197_; 
v_x_boxed_195_ = lean_unbox(v_x_193_);
v_res_196_ = l_Int8_pow(v_x_boxed_195_, v_n_194_);
lean_dec(v_n_194_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT void l_Int8_mod_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_198_ = stack[0].m_num;
uint8_t v_b_199_ = stack[1].m_num;
uint8_t v_res_200_;
v_res_200_ = lean_int8_mod(v_a_198_, v_b_199_);
stack->m_num = v_res_200_;
}
LEAN_EXPORT lean_object* l_Int8_mod___boxed(lean_object* v_a_201_, lean_object* v_b_202_){
_start:
{
uint8_t v_a_boxed_203_; uint8_t v_b_boxed_204_; uint8_t v_res_205_; lean_object* v_r_206_; 
v_a_boxed_203_ = lean_unbox(v_a_201_);
v_b_boxed_204_ = lean_unbox(v_b_202_);
v_res_205_ = lean_int8_mod(v_a_boxed_203_, v_b_boxed_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT void l_Int8_land_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_207_ = stack[0].m_num;
uint8_t v_b_208_ = stack[1].m_num;
uint8_t v_res_209_;
v_res_209_ = lean_int8_land(v_a_207_, v_b_208_);
stack->m_num = v_res_209_;
}
LEAN_EXPORT lean_object* l_Int8_land___boxed(lean_object* v_a_210_, lean_object* v_b_211_){
_start:
{
uint8_t v_a_boxed_212_; uint8_t v_b_boxed_213_; uint8_t v_res_214_; lean_object* v_r_215_; 
v_a_boxed_212_ = lean_unbox(v_a_210_);
v_b_boxed_213_ = lean_unbox(v_b_211_);
v_res_214_ = lean_int8_land(v_a_boxed_212_, v_b_boxed_213_);
v_r_215_ = lean_box(v_res_214_);
return v_r_215_;
}
}
LEAN_EXPORT void l_Int8_lor_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_216_ = stack[0].m_num;
uint8_t v_b_217_ = stack[1].m_num;
uint8_t v_res_218_;
v_res_218_ = lean_int8_lor(v_a_216_, v_b_217_);
stack->m_num = v_res_218_;
}
LEAN_EXPORT lean_object* l_Int8_lor___boxed(lean_object* v_a_219_, lean_object* v_b_220_){
_start:
{
uint8_t v_a_boxed_221_; uint8_t v_b_boxed_222_; uint8_t v_res_223_; lean_object* v_r_224_; 
v_a_boxed_221_ = lean_unbox(v_a_219_);
v_b_boxed_222_ = lean_unbox(v_b_220_);
v_res_223_ = lean_int8_lor(v_a_boxed_221_, v_b_boxed_222_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
LEAN_EXPORT void l_Int8_xor_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_225_ = stack[0].m_num;
uint8_t v_b_226_ = stack[1].m_num;
uint8_t v_res_227_;
v_res_227_ = lean_int8_xor(v_a_225_, v_b_226_);
stack->m_num = v_res_227_;
}
LEAN_EXPORT lean_object* l_Int8_xor___boxed(lean_object* v_a_228_, lean_object* v_b_229_){
_start:
{
uint8_t v_a_boxed_230_; uint8_t v_b_boxed_231_; uint8_t v_res_232_; lean_object* v_r_233_; 
v_a_boxed_230_ = lean_unbox(v_a_228_);
v_b_boxed_231_ = lean_unbox(v_b_229_);
v_res_232_ = lean_int8_xor(v_a_boxed_230_, v_b_boxed_231_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
LEAN_EXPORT void l_Int8_shiftLeft_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_234_ = stack[0].m_num;
uint8_t v_b_235_ = stack[1].m_num;
uint8_t v_res_236_;
v_res_236_ = lean_int8_shift_left(v_a_234_, v_b_235_);
stack->m_num = v_res_236_;
}
LEAN_EXPORT lean_object* l_Int8_shiftLeft___boxed(lean_object* v_a_237_, lean_object* v_b_238_){
_start:
{
uint8_t v_a_boxed_239_; uint8_t v_b_boxed_240_; uint8_t v_res_241_; lean_object* v_r_242_; 
v_a_boxed_239_ = lean_unbox(v_a_237_);
v_b_boxed_240_ = lean_unbox(v_b_238_);
v_res_241_ = lean_int8_shift_left(v_a_boxed_239_, v_b_boxed_240_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT void l_Int8_shiftRight_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_243_ = stack[0].m_num;
uint8_t v_b_244_ = stack[1].m_num;
uint8_t v_res_245_;
v_res_245_ = lean_int8_shift_right(v_a_243_, v_b_244_);
stack->m_num = v_res_245_;
}
LEAN_EXPORT lean_object* l_Int8_shiftRight___boxed(lean_object* v_a_246_, lean_object* v_b_247_){
_start:
{
uint8_t v_a_boxed_248_; uint8_t v_b_boxed_249_; uint8_t v_res_250_; lean_object* v_r_251_; 
v_a_boxed_248_ = lean_unbox(v_a_246_);
v_b_boxed_249_ = lean_unbox(v_b_247_);
v_res_250_ = lean_int8_shift_right(v_a_boxed_248_, v_b_boxed_249_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT void l_Int8_complement_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_252_ = stack[0].m_num;
uint8_t v_res_253_;
v_res_253_ = lean_int8_complement(v_a_252_);
stack->m_num = v_res_253_;
}
LEAN_EXPORT lean_object* l_Int8_complement___boxed(lean_object* v_a_254_){
_start:
{
uint8_t v_a_boxed_255_; uint8_t v_res_256_; lean_object* v_r_257_; 
v_a_boxed_255_ = lean_unbox(v_a_254_);
v_res_256_ = lean_int8_complement(v_a_boxed_255_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT void l_Int8_abs_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_258_ = stack[0].m_num;
uint8_t v_res_259_;
v_res_259_ = lean_int8_abs(v_a_258_);
stack->m_num = v_res_259_;
}
LEAN_EXPORT lean_object* l_Int8_abs___boxed(lean_object* v_a_260_){
_start:
{
uint8_t v_a_boxed_261_; uint8_t v_res_262_; lean_object* v_r_263_; 
v_a_boxed_261_ = lean_unbox(v_a_260_);
v_res_262_ = lean_int8_abs(v_a_boxed_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT void l_Int8_decEq_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_264_ = stack[0].m_num;
uint8_t v_b_265_ = stack[1].m_num;
uint8_t v_res_266_;
v_res_266_ = lean_int8_dec_eq(v_a_264_, v_b_265_);
stack->m_num = v_res_266_;
}
LEAN_EXPORT lean_object* l_Int8_decEq___boxed(lean_object* v_a_267_, lean_object* v_b_268_){
_start:
{
uint8_t v_a_boxed_269_; uint8_t v_b_boxed_270_; uint8_t v_res_271_; lean_object* v_r_272_; 
v_a_boxed_269_ = lean_unbox(v_a_267_);
v_b_boxed_270_ = lean_unbox(v_b_268_);
v_res_271_ = lean_int8_dec_eq(v_a_boxed_269_, v_b_boxed_270_);
v_r_272_ = lean_box(v_res_271_);
return v_r_272_;
}
}
static uint8_t _init_l_instInhabitedInt8___closed__0(void){
_start:
{
lean_object* v___x_273_; uint8_t v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_int8_of_nat(v___x_273_);
return v___x_274_;
}
}
static uint8_t _init_l_instInhabitedInt8(void){
_start:
{
uint8_t v___x_275_; 
v___x_275_ = lean_uint8_once(&l_instInhabitedInt8___closed__0, &l_instInhabitedInt8___closed__0_once, _init_l_instInhabitedInt8___closed__0);
return v___x_275_;
}
}
static lean_object* _init_l_instLTInt8(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_box(0);
return v___x_288_;
}
}
static lean_object* _init_l_instLEInt8(void){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = lean_box(0);
return v___x_289_;
}
}
uint8_t l_instDecidableEqInt8(uint8_t v_a_302_, uint8_t v_b_303_){
_start:
{
uint8_t v___x_304_; 
v___x_304_ = lean_int8_dec_eq(v_a_302_, v_b_303_);
return v___x_304_;
}
}
LEAN_EXPORT void l_instDecidableEqInt8_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_302_ = stack[0].m_num;
uint8_t v_b_303_ = stack[1].m_num;
uint8_t v_res_305_;
v_res_305_ = l_instDecidableEqInt8(v_a_302_, v_b_303_);
stack->m_num = v_res_305_;
}
LEAN_EXPORT lean_object* l_instDecidableEqInt8___boxed(lean_object* v_a_306_, lean_object* v_b_307_){
_start:
{
uint8_t v_a_boxed_308_; uint8_t v_b_boxed_309_; uint8_t v_res_310_; lean_object* v_r_311_; 
v_a_boxed_308_ = lean_unbox(v_a_306_);
v_b_boxed_309_ = lean_unbox(v_b_307_);
v_res_310_ = l_instDecidableEqInt8(v_a_boxed_308_, v_b_boxed_309_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT void l_Bool_toInt8_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_312_ = stack[0].m_num;
uint8_t v_res_313_;
v_res_313_ = lean_bool_to_int8(v_b_312_);
stack->m_num = v_res_313_;
}
LEAN_EXPORT lean_object* l_Bool_toInt8___boxed(lean_object* v_b_314_){
_start:
{
uint8_t v_b_boxed_315_; uint8_t v_res_316_; lean_object* v_r_317_; 
v_b_boxed_315_ = lean_unbox(v_b_314_);
v_res_316_ = lean_bool_to_int8(v_b_boxed_315_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
uint8_t l_Int8_decLt___aux__1(uint8_t v_a_318_, uint8_t v_b_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_320_ = lean_unsigned_to_nat(8u);
v___x_321_ = lean_uint8_to_nat(v_a_318_);
v___x_322_ = lean_uint8_to_nat(v_b_319_);
v___x_323_ = l_BitVec_slt(v___x_320_, v___x_321_, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT void l_Int8_decLt___aux__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_318_ = stack[0].m_num;
uint8_t v_b_319_ = stack[1].m_num;
uint8_t v_res_324_;
v_res_324_ = l_Int8_decLt___aux__1(v_a_318_, v_b_319_);
stack->m_num = v_res_324_;
}
LEAN_EXPORT lean_object* l_Int8_decLt___aux__1___boxed(lean_object* v_a_325_, lean_object* v_b_326_){
_start:
{
uint8_t v_a_boxed_327_; uint8_t v_b_boxed_328_; uint8_t v_res_329_; lean_object* v_r_330_; 
v_a_boxed_327_ = lean_unbox(v_a_325_);
v_b_boxed_328_ = lean_unbox(v_b_326_);
v_res_329_ = l_Int8_decLt___aux__1(v_a_boxed_327_, v_b_boxed_328_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT void l_Int8_decLt_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_331_ = stack[0].m_num;
uint8_t v_b_332_ = stack[1].m_num;
uint8_t v_res_333_;
v_res_333_ = lean_int8_dec_lt(v_a_331_, v_b_332_);
stack->m_num = v_res_333_;
}
LEAN_EXPORT lean_object* l_Int8_decLt___boxed(lean_object* v_a_334_, lean_object* v_b_335_){
_start:
{
uint8_t v_a_boxed_336_; uint8_t v_b_boxed_337_; uint8_t v_res_338_; lean_object* v_r_339_; 
v_a_boxed_336_ = lean_unbox(v_a_334_);
v_b_boxed_337_ = lean_unbox(v_b_335_);
v_res_338_ = lean_int8_dec_lt(v_a_boxed_336_, v_b_boxed_337_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
uint8_t l_Int8_decLe___aux__1(uint8_t v_a_340_, uint8_t v_b_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_342_ = lean_unsigned_to_nat(8u);
v___x_343_ = lean_uint8_to_nat(v_a_340_);
v___x_344_ = lean_uint8_to_nat(v_b_341_);
v___x_345_ = l_BitVec_sle(v___x_342_, v___x_343_, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT void l_Int8_decLe___aux__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_340_ = stack[0].m_num;
uint8_t v_b_341_ = stack[1].m_num;
uint8_t v_res_346_;
v_res_346_ = l_Int8_decLe___aux__1(v_a_340_, v_b_341_);
stack->m_num = v_res_346_;
}
LEAN_EXPORT lean_object* l_Int8_decLe___aux__1___boxed(lean_object* v_a_347_, lean_object* v_b_348_){
_start:
{
uint8_t v_a_boxed_349_; uint8_t v_b_boxed_350_; uint8_t v_res_351_; lean_object* v_r_352_; 
v_a_boxed_349_ = lean_unbox(v_a_347_);
v_b_boxed_350_ = lean_unbox(v_b_348_);
v_res_351_ = l_Int8_decLe___aux__1(v_a_boxed_349_, v_b_boxed_350_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT void l_Int8_decLe_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_353_ = stack[0].m_num;
uint8_t v_b_354_ = stack[1].m_num;
uint8_t v_res_355_;
v_res_355_ = lean_int8_dec_le(v_a_353_, v_b_354_);
stack->m_num = v_res_355_;
}
LEAN_EXPORT lean_object* l_Int8_decLe___boxed(lean_object* v_a_356_, lean_object* v_b_357_){
_start:
{
uint8_t v_a_boxed_358_; uint8_t v_b_boxed_359_; uint8_t v_res_360_; lean_object* v_r_361_; 
v_a_boxed_358_ = lean_unbox(v_a_356_);
v_b_boxed_359_ = lean_unbox(v_b_357_);
v_res_360_ = lean_int8_dec_le(v_a_boxed_358_, v_b_boxed_359_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
uint8_t l_instMaxInt8___lam__0(uint8_t v_x_362_, uint8_t v_y_363_){
_start:
{
uint8_t v___x_364_; 
v___x_364_ = lean_int8_dec_le(v_x_362_, v_y_363_);
if (v___x_364_ == 0)
{
return v_x_362_;
}
else
{
return v_y_363_;
}
}
}
LEAN_EXPORT void l_instMaxInt8___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_362_ = stack[0].m_num;
uint8_t v_y_363_ = stack[1].m_num;
uint8_t v_res_365_;
v_res_365_ = l_instMaxInt8___lam__0(v_x_362_, v_y_363_);
stack->m_num = v_res_365_;
}
LEAN_EXPORT lean_object* l_instMaxInt8___lam__0___boxed(lean_object* v_x_366_, lean_object* v_y_367_){
_start:
{
uint8_t v_x_boxed_368_; uint8_t v_y_boxed_369_; uint8_t v_res_370_; lean_object* v_r_371_; 
v_x_boxed_368_ = lean_unbox(v_x_366_);
v_y_boxed_369_ = lean_unbox(v_y_367_);
v_res_370_ = l_instMaxInt8___lam__0(v_x_boxed_368_, v_y_boxed_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
uint8_t l_instMinInt8___lam__0(uint8_t v_x_374_, uint8_t v_y_375_){
_start:
{
uint8_t v___x_376_; 
v___x_376_ = lean_int8_dec_le(v_x_374_, v_y_375_);
if (v___x_376_ == 0)
{
return v_y_375_;
}
else
{
return v_x_374_;
}
}
}
LEAN_EXPORT void l_instMinInt8___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_374_ = stack[0].m_num;
uint8_t v_y_375_ = stack[1].m_num;
uint8_t v_res_377_;
v_res_377_ = l_instMinInt8___lam__0(v_x_374_, v_y_375_);
stack->m_num = v_res_377_;
}
LEAN_EXPORT lean_object* l_instMinInt8___lam__0___boxed(lean_object* v_x_378_, lean_object* v_y_379_){
_start:
{
uint8_t v_x_boxed_380_; uint8_t v_y_boxed_381_; uint8_t v_res_382_; lean_object* v_r_383_; 
v_x_boxed_380_ = lean_unbox(v_x_378_);
v_y_boxed_381_ = lean_unbox(v_y_379_);
v_res_382_ = l_instMinInt8___lam__0(v_x_boxed_380_, v_y_boxed_381_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
static lean_object* _init_l_Int16_size(void){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_unsigned_to_nat(65536u);
return v___x_386_;
}
}
lean_object* l_Int16_toBitVec(uint16_t v_x_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_uint16_to_nat(v_x_387_);
return v___x_388_;
}
}
LEAN_EXPORT void l_Int16_toBitVec_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_387_ = stack[0].m_num;
lean_object* v_res_389_;
v_res_389_ = l_Int16_toBitVec(v_x_387_);
stack->m_obj
 = v_res_389_;
}
LEAN_EXPORT lean_object* l_Int16_toBitVec___boxed(lean_object* v_x_390_){
_start:
{
uint16_t v_x_boxed_391_; lean_object* v_res_392_; 
v_x_boxed_391_ = lean_unbox(v_x_390_);
v_res_392_ = l_Int16_toBitVec(v_x_boxed_391_);
return v_res_392_;
}
}
uint16_t l_UInt16_toInt16(uint16_t v_i_393_){
_start:
{
return v_i_393_;
}
}
LEAN_EXPORT void l_UInt16_toInt16_0interp(lean_interpreter_value* stack)
{
uint16_t v_i_393_ = stack[0].m_num;
uint16_t v_res_394_;
v_res_394_ = l_UInt16_toInt16(v_i_393_);
stack->m_num = v_res_394_;
}
LEAN_EXPORT lean_object* l_UInt16_toInt16___boxed(lean_object* v_i_395_){
_start:
{
uint16_t v_i_boxed_396_; uint16_t v_res_397_; lean_object* v_r_398_; 
v_i_boxed_396_ = lean_unbox(v_i_395_);
v_res_397_ = l_UInt16_toInt16(v_i_boxed_396_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT void l_Int16_ofInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_399_ = stack[0].m_obj;
uint16_t v_res_400_;
v_res_400_ = lean_int16_of_int(v_i_399_);
stack->m_num = v_res_400_;
}
LEAN_EXPORT lean_object* l_Int16_ofInt___boxed(lean_object* v_i_401_){
_start:
{
uint16_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = lean_int16_of_int(v_i_401_);
lean_dec(v_i_401_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT void l_Int16_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_404_ = stack[0].m_obj;
uint16_t v_res_405_;
v_res_405_ = lean_int16_of_nat(v_n_404_);
stack->m_num = v_res_405_;
}
LEAN_EXPORT lean_object* l_Int16_ofNat___boxed(lean_object* v_n_406_){
_start:
{
uint16_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = lean_int16_of_nat(v_n_406_);
lean_dec(v_n_406_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
uint16_t l_Int_toInt16(lean_object* v_i_409_){
_start:
{
uint16_t v___x_410_; 
v___x_410_ = lean_int16_of_int(v_i_409_);
return v___x_410_;
}
}
LEAN_EXPORT void l_Int_toInt16_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_409_ = stack[0].m_obj;
uint16_t v_res_411_;
v_res_411_ = l_Int_toInt16(v_i_409_);
stack->m_num = v_res_411_;
}
LEAN_EXPORT lean_object* l_Int_toInt16___boxed(lean_object* v_i_412_){
_start:
{
uint16_t v_res_413_; lean_object* v_r_414_; 
v_res_413_ = l_Int_toInt16(v_i_412_);
lean_dec(v_i_412_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
uint16_t l_Nat_toInt16(lean_object* v_n_415_){
_start:
{
uint16_t v___x_416_; 
v___x_416_ = lean_int16_of_nat(v_n_415_);
return v___x_416_;
}
}
LEAN_EXPORT void l_Nat_toInt16_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_415_ = stack[0].m_obj;
uint16_t v_res_417_;
v_res_417_ = l_Nat_toInt16(v_n_415_);
stack->m_num = v_res_417_;
}
LEAN_EXPORT lean_object* l_Nat_toInt16___boxed(lean_object* v_n_418_){
_start:
{
uint16_t v_res_419_; lean_object* v_r_420_; 
v_res_419_ = l_Nat_toInt16(v_n_418_);
lean_dec(v_n_418_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT void l_Int16_toInt_0interp(lean_interpreter_value* stack)
{
uint16_t v_i_421_ = stack[0].m_num;
lean_object* v_res_422_;
v_res_422_ = lean_int16_to_int(v_i_421_);
stack->m_obj
 = v_res_422_;
}
LEAN_EXPORT lean_object* l_Int16_toInt___boxed(lean_object* v_i_423_){
_start:
{
uint16_t v_i_boxed_424_; lean_object* v_res_425_; 
v_i_boxed_424_ = lean_unbox(v_i_423_);
v_res_425_ = lean_int16_to_int(v_i_boxed_424_);
return v_res_425_;
}
}
lean_object* l_Int16_toNatClampNeg(uint16_t v_i_426_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_int16_to_int(v_i_426_);
v___x_428_ = l_Int_toNat(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT void l_Int16_toNatClampNeg_0interp(lean_interpreter_value* stack)
{
uint16_t v_i_426_ = stack[0].m_num;
lean_object* v_res_429_;
v_res_429_ = l_Int16_toNatClampNeg(v_i_426_);
stack->m_obj
 = v_res_429_;
}
LEAN_EXPORT lean_object* l_Int16_toNatClampNeg___boxed(lean_object* v_i_430_){
_start:
{
uint16_t v_i_boxed_431_; lean_object* v_res_432_; 
v_i_boxed_431_ = lean_unbox(v_i_430_);
v_res_432_ = l_Int16_toNatClampNeg(v_i_boxed_431_);
return v_res_432_;
}
}
uint16_t l_Int16_ofBitVec(lean_object* v_b_433_){
_start:
{
uint16_t v___x_434_; 
v___x_434_ = lean_uint16_of_nat_mk(v_b_433_);
return v___x_434_;
}
}
LEAN_EXPORT void l_Int16_ofBitVec_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_433_ = stack[0].m_obj;
uint16_t v_res_435_;
v_res_435_ = l_Int16_ofBitVec(v_b_433_);
stack->m_num = v_res_435_;
}
LEAN_EXPORT lean_object* l_Int16_ofBitVec___boxed(lean_object* v_b_436_){
_start:
{
uint16_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Int16_ofBitVec(v_b_436_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT void l_Int16_toInt8_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_439_ = stack[0].m_num;
uint8_t v_res_440_;
v_res_440_ = lean_int16_to_int8(v_a_439_);
stack->m_num = v_res_440_;
}
LEAN_EXPORT lean_object* l_Int16_toInt8___boxed(lean_object* v_a_441_){
_start:
{
uint16_t v_a_boxed_442_; uint8_t v_res_443_; lean_object* v_r_444_; 
v_a_boxed_442_ = lean_unbox(v_a_441_);
v_res_443_ = lean_int16_to_int8(v_a_boxed_442_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT void l_Int8_toInt16_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_445_ = stack[0].m_num;
uint16_t v_res_446_;
v_res_446_ = lean_int8_to_int16(v_a_445_);
stack->m_num = v_res_446_;
}
LEAN_EXPORT lean_object* l_Int8_toInt16___boxed(lean_object* v_a_447_){
_start:
{
uint8_t v_a_boxed_448_; uint16_t v_res_449_; lean_object* v_r_450_; 
v_a_boxed_448_ = lean_unbox(v_a_447_);
v_res_449_ = lean_int8_to_int16(v_a_boxed_448_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT void l_Int16_neg_0interp(lean_interpreter_value* stack)
{
uint16_t v_i_451_ = stack[0].m_num;
uint16_t v_res_452_;
v_res_452_ = lean_int16_neg(v_i_451_);
stack->m_num = v_res_452_;
}
LEAN_EXPORT lean_object* l_Int16_neg___boxed(lean_object* v_i_453_){
_start:
{
uint16_t v_i_boxed_454_; uint16_t v_res_455_; lean_object* v_r_456_; 
v_i_boxed_454_ = lean_unbox(v_i_453_);
v_res_455_ = lean_int16_neg(v_i_boxed_454_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
lean_object* l_instToStringInt16___lam__0(uint16_t v_i_457_){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = lean_int16_to_int(v_i_457_);
v___x_459_ = l_Int_repr(v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT void l_instToStringInt16___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_i_457_ = stack[0].m_num;
lean_object* v_res_460_;
v_res_460_ = l_instToStringInt16___lam__0(v_i_457_);
stack->m_obj
 = v_res_460_;
}
LEAN_EXPORT lean_object* l_instToStringInt16___lam__0___boxed(lean_object* v_i_461_){
_start:
{
uint16_t v_i_boxed_462_; lean_object* v_res_463_; 
v_i_boxed_462_ = lean_unbox(v_i_461_);
v_res_463_ = l_instToStringInt16___lam__0(v_i_boxed_462_);
return v_res_463_;
}
}
lean_object* l_instReprInt16___lam__0(uint16_t v_i_466_, lean_object* v_prec_467_){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_468_ = lean_int16_to_int(v_i_466_);
v___x_469_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_470_ = lean_int_dec_lt(v___x_468_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = l_Int_repr(v___x_468_);
v___x_472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = l_Int_repr(v___x_468_);
v___x_474_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
v___x_475_ = l_Repr_addAppParen(v___x_474_, v_prec_467_);
return v___x_475_;
}
}
}
LEAN_EXPORT void l_instReprInt16___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_i_466_ = stack[0].m_num;
lean_object* v_prec_467_ = stack[1].m_obj;
lean_object* v_res_476_;
v_res_476_ = l_instReprInt16___lam__0(v_i_466_, v_prec_467_);
stack->m_obj
 = v_res_476_;
}
LEAN_EXPORT lean_object* l_instReprInt16___lam__0___boxed(lean_object* v_i_477_, lean_object* v_prec_478_){
_start:
{
uint16_t v_i_boxed_479_; lean_object* v_res_480_; 
v_i_boxed_479_ = lean_unbox(v_i_477_);
v_res_480_ = l_instReprInt16___lam__0(v_i_boxed_479_, v_prec_478_);
lean_dec(v_prec_478_);
return v_res_480_;
}
}
static lean_object* _init_l_instReprAtomInt16(void){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = lean_box(0);
return v___x_483_;
}
}
uint16_t l_Int16_instOfNat(lean_object* v_n_486_){
_start:
{
uint16_t v___x_487_; 
v___x_487_ = lean_int16_of_nat(v_n_486_);
return v___x_487_;
}
}
LEAN_EXPORT void l_Int16_instOfNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_486_ = stack[0].m_obj;
uint16_t v_res_488_;
v_res_488_ = l_Int16_instOfNat(v_n_486_);
stack->m_num = v_res_488_;
}
LEAN_EXPORT lean_object* l_Int16_instOfNat___boxed(lean_object* v_n_489_){
_start:
{
uint16_t v_res_490_; lean_object* v_r_491_; 
v_res_490_ = l_Int16_instOfNat(v_n_489_);
lean_dec(v_n_489_);
v_r_491_ = lean_box(v_res_490_);
return v_r_491_;
}
}
static uint16_t _init_l_Int16_maxValue___closed__0(void){
_start:
{
lean_object* v___x_494_; uint16_t v___x_495_; 
v___x_494_ = lean_unsigned_to_nat(32767u);
v___x_495_ = lean_int16_of_nat(v___x_494_);
return v___x_495_;
}
}
static uint16_t _init_l_Int16_maxValue(void){
_start:
{
uint16_t v___x_496_; 
v___x_496_ = lean_uint16_once(&l_Int16_maxValue___closed__0, &l_Int16_maxValue___closed__0_once, _init_l_Int16_maxValue___closed__0);
return v___x_496_;
}
}
static uint16_t _init_l_Int16_minValue___closed__0(void){
_start:
{
lean_object* v___x_497_; uint16_t v___x_498_; 
v___x_497_ = lean_unsigned_to_nat(32768u);
v___x_498_ = lean_int16_of_nat(v___x_497_);
return v___x_498_;
}
}
static uint16_t _init_l_Int16_minValue___closed__1(void){
_start:
{
uint16_t v___x_499_; uint16_t v___x_500_; 
v___x_499_ = lean_uint16_once(&l_Int16_minValue___closed__0, &l_Int16_minValue___closed__0_once, _init_l_Int16_minValue___closed__0);
v___x_500_ = lean_int16_neg(v___x_499_);
return v___x_500_;
}
}
static uint16_t _init_l_Int16_minValue(void){
_start:
{
uint16_t v___x_501_; 
v___x_501_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
return v___x_501_;
}
}
uint16_t l_Int16_ofIntLE___redArg(lean_object* v_i_502_){
_start:
{
uint16_t v___x_503_; 
v___x_503_ = lean_int16_of_int(v_i_502_);
return v___x_503_;
}
}
LEAN_EXPORT void l_Int16_ofIntLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_502_ = stack[0].m_obj;
uint16_t v_res_504_;
v_res_504_ = l_Int16_ofIntLE___redArg(v_i_502_);
stack->m_num = v_res_504_;
}
LEAN_EXPORT lean_object* l_Int16_ofIntLE___redArg___boxed(lean_object* v_i_505_){
_start:
{
uint16_t v_res_506_; lean_object* v_r_507_; 
v_res_506_ = l_Int16_ofIntLE___redArg(v_i_505_);
lean_dec(v_i_505_);
v_r_507_ = lean_box(v_res_506_);
return v_r_507_;
}
}
uint16_t l_Int16_ofIntLE(lean_object* v_i_508_, lean_object* v___hl_509_, lean_object* v___hr_510_){
_start:
{
uint16_t v___x_511_; 
v___x_511_ = lean_int16_of_int(v_i_508_);
return v___x_511_;
}
}
LEAN_EXPORT void l_Int16_ofIntLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_508_ = stack[0].m_obj;
uint16_t v_res_512_;
v_res_512_ = l_Int16_ofIntLE(v_i_508_, lean_box(0), lean_box(0));
stack->m_num = v_res_512_;
}
LEAN_EXPORT lean_object* l_Int16_ofIntLE___boxed(lean_object* v_i_513_, lean_object* v___hl_514_, lean_object* v___hr_515_){
_start:
{
uint16_t v_res_516_; lean_object* v_r_517_; 
v_res_516_ = l_Int16_ofIntLE(v_i_513_, v___hl_514_, v___hr_515_);
lean_dec(v_i_513_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
static lean_object* _init_l_Int16_ofIntClamp___closed__0(void){
_start:
{
uint16_t v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
v___x_519_ = lean_int16_to_int(v___x_518_);
return v___x_519_;
}
}
static lean_object* _init_l_Int16_ofIntClamp___closed__1(void){
_start:
{
uint16_t v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_uint16_once(&l_Int16_maxValue___closed__0, &l_Int16_maxValue___closed__0_once, _init_l_Int16_maxValue___closed__0);
v___x_521_ = lean_int16_to_int(v___x_520_);
return v___x_521_;
}
}
uint16_t l_Int16_ofIntClamp(lean_object* v_i_522_){
_start:
{
uint16_t v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_uint16_once(&l_Int16_minValue___closed__1, &l_Int16_minValue___closed__1_once, _init_l_Int16_minValue___closed__1);
v___x_524_ = lean_obj_once(&l_Int16_ofIntClamp___closed__0, &l_Int16_ofIntClamp___closed__0_once, _init_l_Int16_ofIntClamp___closed__0);
v___x_525_ = lean_int_dec_le(v___x_524_, v_i_522_);
if (v___x_525_ == 0)
{
return v___x_523_;
}
else
{
uint16_t v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_526_ = lean_uint16_once(&l_Int16_maxValue___closed__0, &l_Int16_maxValue___closed__0_once, _init_l_Int16_maxValue___closed__0);
v___x_527_ = lean_obj_once(&l_Int16_ofIntClamp___closed__1, &l_Int16_ofIntClamp___closed__1_once, _init_l_Int16_ofIntClamp___closed__1);
v___x_528_ = lean_int_dec_le(v_i_522_, v___x_527_);
if (v___x_528_ == 0)
{
return v___x_526_;
}
else
{
uint16_t v___x_529_; 
v___x_529_ = lean_int16_of_int(v_i_522_);
return v___x_529_;
}
}
}
}
LEAN_EXPORT void l_Int16_ofIntClamp_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_522_ = stack[0].m_obj;
uint16_t v_res_530_;
v_res_530_ = l_Int16_ofIntClamp(v_i_522_);
stack->m_num = v_res_530_;
}
LEAN_EXPORT lean_object* l_Int16_ofIntClamp___boxed(lean_object* v_i_531_){
_start:
{
uint16_t v_res_532_; lean_object* v_r_533_; 
v_res_532_ = l_Int16_ofIntClamp(v_i_531_);
lean_dec(v_i_531_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
uint16_t l_Int16_ofIntTruncate(lean_object* v_i_534_){
_start:
{
uint16_t v___x_535_; 
v___x_535_ = l_Int16_ofIntClamp(v_i_534_);
return v___x_535_;
}
}
LEAN_EXPORT void l_Int16_ofIntTruncate_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_534_ = stack[0].m_obj;
uint16_t v_res_536_;
v_res_536_ = l_Int16_ofIntTruncate(v_i_534_);
stack->m_num = v_res_536_;
}
LEAN_EXPORT lean_object* l_Int16_ofIntTruncate___boxed(lean_object* v_i_537_){
_start:
{
uint16_t v_res_538_; lean_object* v_r_539_; 
v_res_538_ = l_Int16_ofIntTruncate(v_i_537_);
lean_dec(v_i_537_);
v_r_539_ = lean_box(v_res_538_);
return v_r_539_;
}
}
LEAN_EXPORT void l_Int16_add_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_540_ = stack[0].m_num;
uint16_t v_b_541_ = stack[1].m_num;
uint16_t v_res_542_;
v_res_542_ = lean_int16_add(v_a_540_, v_b_541_);
stack->m_num = v_res_542_;
}
LEAN_EXPORT lean_object* l_Int16_add___boxed(lean_object* v_a_543_, lean_object* v_b_544_){
_start:
{
uint16_t v_a_boxed_545_; uint16_t v_b_boxed_546_; uint16_t v_res_547_; lean_object* v_r_548_; 
v_a_boxed_545_ = lean_unbox(v_a_543_);
v_b_boxed_546_ = lean_unbox(v_b_544_);
v_res_547_ = lean_int16_add(v_a_boxed_545_, v_b_boxed_546_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT void l_Int16_sub_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_549_ = stack[0].m_num;
uint16_t v_b_550_ = stack[1].m_num;
uint16_t v_res_551_;
v_res_551_ = lean_int16_sub(v_a_549_, v_b_550_);
stack->m_num = v_res_551_;
}
LEAN_EXPORT lean_object* l_Int16_sub___boxed(lean_object* v_a_552_, lean_object* v_b_553_){
_start:
{
uint16_t v_a_boxed_554_; uint16_t v_b_boxed_555_; uint16_t v_res_556_; lean_object* v_r_557_; 
v_a_boxed_554_ = lean_unbox(v_a_552_);
v_b_boxed_555_ = lean_unbox(v_b_553_);
v_res_556_ = lean_int16_sub(v_a_boxed_554_, v_b_boxed_555_);
v_r_557_ = lean_box(v_res_556_);
return v_r_557_;
}
}
LEAN_EXPORT void l_Int16_mul_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_558_ = stack[0].m_num;
uint16_t v_b_559_ = stack[1].m_num;
uint16_t v_res_560_;
v_res_560_ = lean_int16_mul(v_a_558_, v_b_559_);
stack->m_num = v_res_560_;
}
LEAN_EXPORT lean_object* l_Int16_mul___boxed(lean_object* v_a_561_, lean_object* v_b_562_){
_start:
{
uint16_t v_a_boxed_563_; uint16_t v_b_boxed_564_; uint16_t v_res_565_; lean_object* v_r_566_; 
v_a_boxed_563_ = lean_unbox(v_a_561_);
v_b_boxed_564_ = lean_unbox(v_b_562_);
v_res_565_ = lean_int16_mul(v_a_boxed_563_, v_b_boxed_564_);
v_r_566_ = lean_box(v_res_565_);
return v_r_566_;
}
}
LEAN_EXPORT void l_Int16_div_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_567_ = stack[0].m_num;
uint16_t v_b_568_ = stack[1].m_num;
uint16_t v_res_569_;
v_res_569_ = lean_int16_div(v_a_567_, v_b_568_);
stack->m_num = v_res_569_;
}
LEAN_EXPORT lean_object* l_Int16_div___boxed(lean_object* v_a_570_, lean_object* v_b_571_){
_start:
{
uint16_t v_a_boxed_572_; uint16_t v_b_boxed_573_; uint16_t v_res_574_; lean_object* v_r_575_; 
v_a_boxed_572_ = lean_unbox(v_a_570_);
v_b_boxed_573_ = lean_unbox(v_b_571_);
v_res_574_ = lean_int16_div(v_a_boxed_572_, v_b_boxed_573_);
v_r_575_ = lean_box(v_res_574_);
return v_r_575_;
}
}
static uint16_t _init_l_Int16_pow___closed__0(void){
_start:
{
lean_object* v___x_576_; uint16_t v___x_577_; 
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_int16_of_nat(v___x_576_);
return v___x_577_;
}
}
uint16_t l_Int16_pow(uint16_t v_x_578_, lean_object* v_n_579_){
_start:
{
lean_object* v_zero_580_; uint8_t v_isZero_581_; 
v_zero_580_ = lean_unsigned_to_nat(0u);
v_isZero_581_ = lean_nat_dec_eq(v_n_579_, v_zero_580_);
if (v_isZero_581_ == 1)
{
uint16_t v___x_582_; 
v___x_582_ = lean_uint16_once(&l_Int16_pow___closed__0, &l_Int16_pow___closed__0_once, _init_l_Int16_pow___closed__0);
return v___x_582_;
}
else
{
lean_object* v_one_583_; lean_object* v_n_584_; uint16_t v___x_585_; uint16_t v___x_586_; 
v_one_583_ = lean_unsigned_to_nat(1u);
v_n_584_ = lean_nat_sub(v_n_579_, v_one_583_);
v___x_585_ = l_Int16_pow(v_x_578_, v_n_584_);
lean_dec(v_n_584_);
v___x_586_ = lean_int16_mul(v___x_585_, v_x_578_);
return v___x_586_;
}
}
}
LEAN_EXPORT void l_Int16_pow_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_578_ = stack[0].m_num;
lean_object* v_n_579_ = stack[1].m_obj;
uint16_t v_res_587_;
v_res_587_ = l_Int16_pow(v_x_578_, v_n_579_);
stack->m_num = v_res_587_;
}
LEAN_EXPORT lean_object* l_Int16_pow___boxed(lean_object* v_x_588_, lean_object* v_n_589_){
_start:
{
uint16_t v_x_boxed_590_; uint16_t v_res_591_; lean_object* v_r_592_; 
v_x_boxed_590_ = lean_unbox(v_x_588_);
v_res_591_ = l_Int16_pow(v_x_boxed_590_, v_n_589_);
lean_dec(v_n_589_);
v_r_592_ = lean_box(v_res_591_);
return v_r_592_;
}
}
LEAN_EXPORT void l_Int16_mod_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_593_ = stack[0].m_num;
uint16_t v_b_594_ = stack[1].m_num;
uint16_t v_res_595_;
v_res_595_ = lean_int16_mod(v_a_593_, v_b_594_);
stack->m_num = v_res_595_;
}
LEAN_EXPORT lean_object* l_Int16_mod___boxed(lean_object* v_a_596_, lean_object* v_b_597_){
_start:
{
uint16_t v_a_boxed_598_; uint16_t v_b_boxed_599_; uint16_t v_res_600_; lean_object* v_r_601_; 
v_a_boxed_598_ = lean_unbox(v_a_596_);
v_b_boxed_599_ = lean_unbox(v_b_597_);
v_res_600_ = lean_int16_mod(v_a_boxed_598_, v_b_boxed_599_);
v_r_601_ = lean_box(v_res_600_);
return v_r_601_;
}
}
LEAN_EXPORT void l_Int16_land_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_602_ = stack[0].m_num;
uint16_t v_b_603_ = stack[1].m_num;
uint16_t v_res_604_;
v_res_604_ = lean_int16_land(v_a_602_, v_b_603_);
stack->m_num = v_res_604_;
}
LEAN_EXPORT lean_object* l_Int16_land___boxed(lean_object* v_a_605_, lean_object* v_b_606_){
_start:
{
uint16_t v_a_boxed_607_; uint16_t v_b_boxed_608_; uint16_t v_res_609_; lean_object* v_r_610_; 
v_a_boxed_607_ = lean_unbox(v_a_605_);
v_b_boxed_608_ = lean_unbox(v_b_606_);
v_res_609_ = lean_int16_land(v_a_boxed_607_, v_b_boxed_608_);
v_r_610_ = lean_box(v_res_609_);
return v_r_610_;
}
}
LEAN_EXPORT void l_Int16_lor_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_611_ = stack[0].m_num;
uint16_t v_b_612_ = stack[1].m_num;
uint16_t v_res_613_;
v_res_613_ = lean_int16_lor(v_a_611_, v_b_612_);
stack->m_num = v_res_613_;
}
LEAN_EXPORT lean_object* l_Int16_lor___boxed(lean_object* v_a_614_, lean_object* v_b_615_){
_start:
{
uint16_t v_a_boxed_616_; uint16_t v_b_boxed_617_; uint16_t v_res_618_; lean_object* v_r_619_; 
v_a_boxed_616_ = lean_unbox(v_a_614_);
v_b_boxed_617_ = lean_unbox(v_b_615_);
v_res_618_ = lean_int16_lor(v_a_boxed_616_, v_b_boxed_617_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
LEAN_EXPORT void l_Int16_xor_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_620_ = stack[0].m_num;
uint16_t v_b_621_ = stack[1].m_num;
uint16_t v_res_622_;
v_res_622_ = lean_int16_xor(v_a_620_, v_b_621_);
stack->m_num = v_res_622_;
}
LEAN_EXPORT lean_object* l_Int16_xor___boxed(lean_object* v_a_623_, lean_object* v_b_624_){
_start:
{
uint16_t v_a_boxed_625_; uint16_t v_b_boxed_626_; uint16_t v_res_627_; lean_object* v_r_628_; 
v_a_boxed_625_ = lean_unbox(v_a_623_);
v_b_boxed_626_ = lean_unbox(v_b_624_);
v_res_627_ = lean_int16_xor(v_a_boxed_625_, v_b_boxed_626_);
v_r_628_ = lean_box(v_res_627_);
return v_r_628_;
}
}
LEAN_EXPORT void l_Int16_shiftLeft_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_629_ = stack[0].m_num;
uint16_t v_b_630_ = stack[1].m_num;
uint16_t v_res_631_;
v_res_631_ = lean_int16_shift_left(v_a_629_, v_b_630_);
stack->m_num = v_res_631_;
}
LEAN_EXPORT lean_object* l_Int16_shiftLeft___boxed(lean_object* v_a_632_, lean_object* v_b_633_){
_start:
{
uint16_t v_a_boxed_634_; uint16_t v_b_boxed_635_; uint16_t v_res_636_; lean_object* v_r_637_; 
v_a_boxed_634_ = lean_unbox(v_a_632_);
v_b_boxed_635_ = lean_unbox(v_b_633_);
v_res_636_ = lean_int16_shift_left(v_a_boxed_634_, v_b_boxed_635_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT void l_Int16_shiftRight_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_638_ = stack[0].m_num;
uint16_t v_b_639_ = stack[1].m_num;
uint16_t v_res_640_;
v_res_640_ = lean_int16_shift_right(v_a_638_, v_b_639_);
stack->m_num = v_res_640_;
}
LEAN_EXPORT lean_object* l_Int16_shiftRight___boxed(lean_object* v_a_641_, lean_object* v_b_642_){
_start:
{
uint16_t v_a_boxed_643_; uint16_t v_b_boxed_644_; uint16_t v_res_645_; lean_object* v_r_646_; 
v_a_boxed_643_ = lean_unbox(v_a_641_);
v_b_boxed_644_ = lean_unbox(v_b_642_);
v_res_645_ = lean_int16_shift_right(v_a_boxed_643_, v_b_boxed_644_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT void l_Int16_complement_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_647_ = stack[0].m_num;
uint16_t v_res_648_;
v_res_648_ = lean_int16_complement(v_a_647_);
stack->m_num = v_res_648_;
}
LEAN_EXPORT lean_object* l_Int16_complement___boxed(lean_object* v_a_649_){
_start:
{
uint16_t v_a_boxed_650_; uint16_t v_res_651_; lean_object* v_r_652_; 
v_a_boxed_650_ = lean_unbox(v_a_649_);
v_res_651_ = lean_int16_complement(v_a_boxed_650_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT void l_Int16_abs_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_653_ = stack[0].m_num;
uint16_t v_res_654_;
v_res_654_ = lean_int16_abs(v_a_653_);
stack->m_num = v_res_654_;
}
LEAN_EXPORT lean_object* l_Int16_abs___boxed(lean_object* v_a_655_){
_start:
{
uint16_t v_a_boxed_656_; uint16_t v_res_657_; lean_object* v_r_658_; 
v_a_boxed_656_ = lean_unbox(v_a_655_);
v_res_657_ = lean_int16_abs(v_a_boxed_656_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT void l_Int16_decEq_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_659_ = stack[0].m_num;
uint16_t v_b_660_ = stack[1].m_num;
uint8_t v_res_661_;
v_res_661_ = lean_int16_dec_eq(v_a_659_, v_b_660_);
stack->m_num = v_res_661_;
}
LEAN_EXPORT lean_object* l_Int16_decEq___boxed(lean_object* v_a_662_, lean_object* v_b_663_){
_start:
{
uint16_t v_a_boxed_664_; uint16_t v_b_boxed_665_; uint8_t v_res_666_; lean_object* v_r_667_; 
v_a_boxed_664_ = lean_unbox(v_a_662_);
v_b_boxed_665_ = lean_unbox(v_b_663_);
v_res_666_ = lean_int16_dec_eq(v_a_boxed_664_, v_b_boxed_665_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
static uint16_t _init_l_instInhabitedInt16___closed__0(void){
_start:
{
lean_object* v___x_668_; uint16_t v___x_669_; 
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_int16_of_nat(v___x_668_);
return v___x_669_;
}
}
static uint16_t _init_l_instInhabitedInt16(void){
_start:
{
uint16_t v___x_670_; 
v___x_670_ = lean_uint16_once(&l_instInhabitedInt16___closed__0, &l_instInhabitedInt16___closed__0_once, _init_l_instInhabitedInt16___closed__0);
return v___x_670_;
}
}
static lean_object* _init_l_instLTInt16(void){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = lean_box(0);
return v___x_683_;
}
}
static lean_object* _init_l_instLEInt16(void){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = lean_box(0);
return v___x_684_;
}
}
uint8_t l_instDecidableEqInt16(uint16_t v_a_697_, uint16_t v_b_698_){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = lean_int16_dec_eq(v_a_697_, v_b_698_);
return v___x_699_;
}
}
LEAN_EXPORT void l_instDecidableEqInt16_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_697_ = stack[0].m_num;
uint16_t v_b_698_ = stack[1].m_num;
uint8_t v_res_700_;
v_res_700_ = l_instDecidableEqInt16(v_a_697_, v_b_698_);
stack->m_num = v_res_700_;
}
LEAN_EXPORT lean_object* l_instDecidableEqInt16___boxed(lean_object* v_a_701_, lean_object* v_b_702_){
_start:
{
uint16_t v_a_boxed_703_; uint16_t v_b_boxed_704_; uint8_t v_res_705_; lean_object* v_r_706_; 
v_a_boxed_703_ = lean_unbox(v_a_701_);
v_b_boxed_704_ = lean_unbox(v_b_702_);
v_res_705_ = l_instDecidableEqInt16(v_a_boxed_703_, v_b_boxed_704_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT void l_Bool_toInt16_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_707_ = stack[0].m_num;
uint16_t v_res_708_;
v_res_708_ = lean_bool_to_int16(v_b_707_);
stack->m_num = v_res_708_;
}
LEAN_EXPORT lean_object* l_Bool_toInt16___boxed(lean_object* v_b_709_){
_start:
{
uint8_t v_b_boxed_710_; uint16_t v_res_711_; lean_object* v_r_712_; 
v_b_boxed_710_ = lean_unbox(v_b_709_);
v_res_711_ = lean_bool_to_int16(v_b_boxed_710_);
v_r_712_ = lean_box(v_res_711_);
return v_r_712_;
}
}
uint8_t l_Int16_decLt___aux__1(uint16_t v_a_713_, uint16_t v_b_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; uint8_t v___x_718_; 
v___x_715_ = lean_unsigned_to_nat(16u);
v___x_716_ = lean_uint16_to_nat(v_a_713_);
v___x_717_ = lean_uint16_to_nat(v_b_714_);
v___x_718_ = l_BitVec_slt(v___x_715_, v___x_716_, v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT void l_Int16_decLt___aux__1_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_713_ = stack[0].m_num;
uint16_t v_b_714_ = stack[1].m_num;
uint8_t v_res_719_;
v_res_719_ = l_Int16_decLt___aux__1(v_a_713_, v_b_714_);
stack->m_num = v_res_719_;
}
LEAN_EXPORT lean_object* l_Int16_decLt___aux__1___boxed(lean_object* v_a_720_, lean_object* v_b_721_){
_start:
{
uint16_t v_a_boxed_722_; uint16_t v_b_boxed_723_; uint8_t v_res_724_; lean_object* v_r_725_; 
v_a_boxed_722_ = lean_unbox(v_a_720_);
v_b_boxed_723_ = lean_unbox(v_b_721_);
v_res_724_ = l_Int16_decLt___aux__1(v_a_boxed_722_, v_b_boxed_723_);
v_r_725_ = lean_box(v_res_724_);
return v_r_725_;
}
}
LEAN_EXPORT void l_Int16_decLt_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_726_ = stack[0].m_num;
uint16_t v_b_727_ = stack[1].m_num;
uint8_t v_res_728_;
v_res_728_ = lean_int16_dec_lt(v_a_726_, v_b_727_);
stack->m_num = v_res_728_;
}
LEAN_EXPORT lean_object* l_Int16_decLt___boxed(lean_object* v_a_729_, lean_object* v_b_730_){
_start:
{
uint16_t v_a_boxed_731_; uint16_t v_b_boxed_732_; uint8_t v_res_733_; lean_object* v_r_734_; 
v_a_boxed_731_ = lean_unbox(v_a_729_);
v_b_boxed_732_ = lean_unbox(v_b_730_);
v_res_733_ = lean_int16_dec_lt(v_a_boxed_731_, v_b_boxed_732_);
v_r_734_ = lean_box(v_res_733_);
return v_r_734_;
}
}
uint8_t l_Int16_decLe___aux__1(uint16_t v_a_735_, uint16_t v_b_736_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_737_ = lean_unsigned_to_nat(16u);
v___x_738_ = lean_uint16_to_nat(v_a_735_);
v___x_739_ = lean_uint16_to_nat(v_b_736_);
v___x_740_ = l_BitVec_sle(v___x_737_, v___x_738_, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT void l_Int16_decLe___aux__1_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_735_ = stack[0].m_num;
uint16_t v_b_736_ = stack[1].m_num;
uint8_t v_res_741_;
v_res_741_ = l_Int16_decLe___aux__1(v_a_735_, v_b_736_);
stack->m_num = v_res_741_;
}
LEAN_EXPORT lean_object* l_Int16_decLe___aux__1___boxed(lean_object* v_a_742_, lean_object* v_b_743_){
_start:
{
uint16_t v_a_boxed_744_; uint16_t v_b_boxed_745_; uint8_t v_res_746_; lean_object* v_r_747_; 
v_a_boxed_744_ = lean_unbox(v_a_742_);
v_b_boxed_745_ = lean_unbox(v_b_743_);
v_res_746_ = l_Int16_decLe___aux__1(v_a_boxed_744_, v_b_boxed_745_);
v_r_747_ = lean_box(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT void l_Int16_decLe_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_748_ = stack[0].m_num;
uint16_t v_b_749_ = stack[1].m_num;
uint8_t v_res_750_;
v_res_750_ = lean_int16_dec_le(v_a_748_, v_b_749_);
stack->m_num = v_res_750_;
}
LEAN_EXPORT lean_object* l_Int16_decLe___boxed(lean_object* v_a_751_, lean_object* v_b_752_){
_start:
{
uint16_t v_a_boxed_753_; uint16_t v_b_boxed_754_; uint8_t v_res_755_; lean_object* v_r_756_; 
v_a_boxed_753_ = lean_unbox(v_a_751_);
v_b_boxed_754_ = lean_unbox(v_b_752_);
v_res_755_ = lean_int16_dec_le(v_a_boxed_753_, v_b_boxed_754_);
v_r_756_ = lean_box(v_res_755_);
return v_r_756_;
}
}
uint16_t l_instMaxInt16___lam__0(uint16_t v_x_757_, uint16_t v_y_758_){
_start:
{
uint8_t v___x_759_; 
v___x_759_ = lean_int16_dec_le(v_x_757_, v_y_758_);
if (v___x_759_ == 0)
{
return v_x_757_;
}
else
{
return v_y_758_;
}
}
}
LEAN_EXPORT void l_instMaxInt16___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_757_ = stack[0].m_num;
uint16_t v_y_758_ = stack[1].m_num;
uint16_t v_res_760_;
v_res_760_ = l_instMaxInt16___lam__0(v_x_757_, v_y_758_);
stack->m_num = v_res_760_;
}
LEAN_EXPORT lean_object* l_instMaxInt16___lam__0___boxed(lean_object* v_x_761_, lean_object* v_y_762_){
_start:
{
uint16_t v_x_boxed_763_; uint16_t v_y_boxed_764_; uint16_t v_res_765_; lean_object* v_r_766_; 
v_x_boxed_763_ = lean_unbox(v_x_761_);
v_y_boxed_764_ = lean_unbox(v_y_762_);
v_res_765_ = l_instMaxInt16___lam__0(v_x_boxed_763_, v_y_boxed_764_);
v_r_766_ = lean_box(v_res_765_);
return v_r_766_;
}
}
uint16_t l_instMinInt16___lam__0(uint16_t v_x_769_, uint16_t v_y_770_){
_start:
{
uint8_t v___x_771_; 
v___x_771_ = lean_int16_dec_le(v_x_769_, v_y_770_);
if (v___x_771_ == 0)
{
return v_y_770_;
}
else
{
return v_x_769_;
}
}
}
LEAN_EXPORT void l_instMinInt16___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_769_ = stack[0].m_num;
uint16_t v_y_770_ = stack[1].m_num;
uint16_t v_res_772_;
v_res_772_ = l_instMinInt16___lam__0(v_x_769_, v_y_770_);
stack->m_num = v_res_772_;
}
LEAN_EXPORT lean_object* l_instMinInt16___lam__0___boxed(lean_object* v_x_773_, lean_object* v_y_774_){
_start:
{
uint16_t v_x_boxed_775_; uint16_t v_y_boxed_776_; uint16_t v_res_777_; lean_object* v_r_778_; 
v_x_boxed_775_ = lean_unbox(v_x_773_);
v_y_boxed_776_ = lean_unbox(v_y_774_);
v_res_777_ = l_instMinInt16___lam__0(v_x_boxed_775_, v_y_boxed_776_);
v_r_778_ = lean_box(v_res_777_);
return v_r_778_;
}
}
static lean_object* _init_l_Int32_size(void){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = lean_cstr_to_nat("4294967296");
return v___x_781_;
}
}
lean_object* l_Int32_toBitVec(uint32_t v_x_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = lean_uint32_to_nat(v_x_782_);
return v___x_783_;
}
}
LEAN_EXPORT void l_Int32_toBitVec_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_782_ = stack[0].m_num;
lean_object* v_res_784_;
v_res_784_ = l_Int32_toBitVec(v_x_782_);
stack->m_obj
 = v_res_784_;
}
LEAN_EXPORT lean_object* l_Int32_toBitVec___boxed(lean_object* v_x_785_){
_start:
{
uint32_t v_x_boxed_786_; lean_object* v_res_787_; 
v_x_boxed_786_ = lean_unbox_uint32(v_x_785_);
lean_dec(v_x_785_);
v_res_787_ = l_Int32_toBitVec(v_x_boxed_786_);
return v_res_787_;
}
}
uint32_t l_UInt32_toInt32(uint32_t v_i_788_){
_start:
{
return v_i_788_;
}
}
LEAN_EXPORT void l_UInt32_toInt32_0interp(lean_interpreter_value* stack)
{
uint32_t v_i_788_ = stack[0].m_num;
uint32_t v_res_789_;
v_res_789_ = l_UInt32_toInt32(v_i_788_);
stack->m_num = v_res_789_;
}
LEAN_EXPORT lean_object* l_UInt32_toInt32___boxed(lean_object* v_i_790_){
_start:
{
uint32_t v_i_boxed_791_; uint32_t v_res_792_; lean_object* v_r_793_; 
v_i_boxed_791_ = lean_unbox_uint32(v_i_790_);
lean_dec(v_i_790_);
v_res_792_ = l_UInt32_toInt32(v_i_boxed_791_);
v_r_793_ = lean_box_uint32(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT void l_Int32_ofInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_794_ = stack[0].m_obj;
uint32_t v_res_795_;
v_res_795_ = lean_int32_of_int(v_i_794_);
stack->m_num = v_res_795_;
}
LEAN_EXPORT lean_object* l_Int32_ofInt___boxed(lean_object* v_i_796_){
_start:
{
uint32_t v_res_797_; lean_object* v_r_798_; 
v_res_797_ = lean_int32_of_int(v_i_796_);
lean_dec(v_i_796_);
v_r_798_ = lean_box_uint32(v_res_797_);
return v_r_798_;
}
}
LEAN_EXPORT void l_Int32_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_799_ = stack[0].m_obj;
uint32_t v_res_800_;
v_res_800_ = lean_int32_of_nat(v_n_799_);
stack->m_num = v_res_800_;
}
LEAN_EXPORT lean_object* l_Int32_ofNat___boxed(lean_object* v_n_801_){
_start:
{
uint32_t v_res_802_; lean_object* v_r_803_; 
v_res_802_ = lean_int32_of_nat(v_n_801_);
lean_dec(v_n_801_);
v_r_803_ = lean_box_uint32(v_res_802_);
return v_r_803_;
}
}
uint32_t l_Int_toInt32(lean_object* v_i_804_){
_start:
{
uint32_t v___x_805_; 
v___x_805_ = lean_int32_of_int(v_i_804_);
return v___x_805_;
}
}
LEAN_EXPORT void l_Int_toInt32_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_804_ = stack[0].m_obj;
uint32_t v_res_806_;
v_res_806_ = l_Int_toInt32(v_i_804_);
stack->m_num = v_res_806_;
}
LEAN_EXPORT lean_object* l_Int_toInt32___boxed(lean_object* v_i_807_){
_start:
{
uint32_t v_res_808_; lean_object* v_r_809_; 
v_res_808_ = l_Int_toInt32(v_i_807_);
lean_dec(v_i_807_);
v_r_809_ = lean_box_uint32(v_res_808_);
return v_r_809_;
}
}
uint32_t l_Nat_toInt32(lean_object* v_n_810_){
_start:
{
uint32_t v___x_811_; 
v___x_811_ = lean_int32_of_nat(v_n_810_);
return v___x_811_;
}
}
LEAN_EXPORT void l_Nat_toInt32_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_810_ = stack[0].m_obj;
uint32_t v_res_812_;
v_res_812_ = l_Nat_toInt32(v_n_810_);
stack->m_num = v_res_812_;
}
LEAN_EXPORT lean_object* l_Nat_toInt32___boxed(lean_object* v_n_813_){
_start:
{
uint32_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l_Nat_toInt32(v_n_813_);
lean_dec(v_n_813_);
v_r_815_ = lean_box_uint32(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT void l_Int32_toInt_0interp(lean_interpreter_value* stack)
{
uint32_t v_i_816_ = stack[0].m_num;
lean_object* v_res_817_;
v_res_817_ = lean_int32_to_int(v_i_816_);
stack->m_obj
 = v_res_817_;
}
LEAN_EXPORT lean_object* l_Int32_toInt___boxed(lean_object* v_i_818_){
_start:
{
uint32_t v_i_boxed_819_; lean_object* v_res_820_; 
v_i_boxed_819_ = lean_unbox_uint32(v_i_818_);
lean_dec(v_i_818_);
v_res_820_ = lean_int32_to_int(v_i_boxed_819_);
return v_res_820_;
}
}
lean_object* l_Int32_toNatClampNeg(uint32_t v_i_821_){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = lean_int32_to_int(v_i_821_);
v___x_823_ = l_Int_toNat(v___x_822_);
lean_dec(v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT void l_Int32_toNatClampNeg_0interp(lean_interpreter_value* stack)
{
uint32_t v_i_821_ = stack[0].m_num;
lean_object* v_res_824_;
v_res_824_ = l_Int32_toNatClampNeg(v_i_821_);
stack->m_obj
 = v_res_824_;
}
LEAN_EXPORT lean_object* l_Int32_toNatClampNeg___boxed(lean_object* v_i_825_){
_start:
{
uint32_t v_i_boxed_826_; lean_object* v_res_827_; 
v_i_boxed_826_ = lean_unbox_uint32(v_i_825_);
lean_dec(v_i_825_);
v_res_827_ = l_Int32_toNatClampNeg(v_i_boxed_826_);
return v_res_827_;
}
}
uint32_t l_Int32_ofBitVec(lean_object* v_b_828_){
_start:
{
uint32_t v___x_829_; 
v___x_829_ = lean_uint32_of_nat_mk(v_b_828_);
return v___x_829_;
}
}
LEAN_EXPORT void l_Int32_ofBitVec_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_828_ = stack[0].m_obj;
uint32_t v_res_830_;
v_res_830_ = l_Int32_ofBitVec(v_b_828_);
stack->m_num = v_res_830_;
}
LEAN_EXPORT lean_object* l_Int32_ofBitVec___boxed(lean_object* v_b_831_){
_start:
{
uint32_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Int32_ofBitVec(v_b_831_);
v_r_833_ = lean_box_uint32(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT void l_Int32_toInt8_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_834_ = stack[0].m_num;
uint8_t v_res_835_;
v_res_835_ = lean_int32_to_int8(v_a_834_);
stack->m_num = v_res_835_;
}
LEAN_EXPORT lean_object* l_Int32_toInt8___boxed(lean_object* v_a_836_){
_start:
{
uint32_t v_a_boxed_837_; uint8_t v_res_838_; lean_object* v_r_839_; 
v_a_boxed_837_ = lean_unbox_uint32(v_a_836_);
lean_dec(v_a_836_);
v_res_838_ = lean_int32_to_int8(v_a_boxed_837_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT void l_Int32_toInt16_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_840_ = stack[0].m_num;
uint16_t v_res_841_;
v_res_841_ = lean_int32_to_int16(v_a_840_);
stack->m_num = v_res_841_;
}
LEAN_EXPORT lean_object* l_Int32_toInt16___boxed(lean_object* v_a_842_){
_start:
{
uint32_t v_a_boxed_843_; uint16_t v_res_844_; lean_object* v_r_845_; 
v_a_boxed_843_ = lean_unbox_uint32(v_a_842_);
lean_dec(v_a_842_);
v_res_844_ = lean_int32_to_int16(v_a_boxed_843_);
v_r_845_ = lean_box(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT void l_Int8_toInt32_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_846_ = stack[0].m_num;
uint32_t v_res_847_;
v_res_847_ = lean_int8_to_int32(v_a_846_);
stack->m_num = v_res_847_;
}
LEAN_EXPORT lean_object* l_Int8_toInt32___boxed(lean_object* v_a_848_){
_start:
{
uint8_t v_a_boxed_849_; uint32_t v_res_850_; lean_object* v_r_851_; 
v_a_boxed_849_ = lean_unbox(v_a_848_);
v_res_850_ = lean_int8_to_int32(v_a_boxed_849_);
v_r_851_ = lean_box_uint32(v_res_850_);
return v_r_851_;
}
}
LEAN_EXPORT void l_Int16_toInt32_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_852_ = stack[0].m_num;
uint32_t v_res_853_;
v_res_853_ = lean_int16_to_int32(v_a_852_);
stack->m_num = v_res_853_;
}
LEAN_EXPORT lean_object* l_Int16_toInt32___boxed(lean_object* v_a_854_){
_start:
{
uint16_t v_a_boxed_855_; uint32_t v_res_856_; lean_object* v_r_857_; 
v_a_boxed_855_ = lean_unbox(v_a_854_);
v_res_856_ = lean_int16_to_int32(v_a_boxed_855_);
v_r_857_ = lean_box_uint32(v_res_856_);
return v_r_857_;
}
}
LEAN_EXPORT void l_Int32_neg_0interp(lean_interpreter_value* stack)
{
uint32_t v_i_858_ = stack[0].m_num;
uint32_t v_res_859_;
v_res_859_ = lean_int32_neg(v_i_858_);
stack->m_num = v_res_859_;
}
LEAN_EXPORT lean_object* l_Int32_neg___boxed(lean_object* v_i_860_){
_start:
{
uint32_t v_i_boxed_861_; uint32_t v_res_862_; lean_object* v_r_863_; 
v_i_boxed_861_ = lean_unbox_uint32(v_i_860_);
lean_dec(v_i_860_);
v_res_862_ = lean_int32_neg(v_i_boxed_861_);
v_r_863_ = lean_box_uint32(v_res_862_);
return v_r_863_;
}
}
lean_object* l_instToStringInt32___lam__0(uint32_t v_i_864_){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_int32_to_int(v_i_864_);
v___x_866_ = l_Int_repr(v___x_865_);
lean_dec(v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT void l_instToStringInt32___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_i_864_ = stack[0].m_num;
lean_object* v_res_867_;
v_res_867_ = l_instToStringInt32___lam__0(v_i_864_);
stack->m_obj
 = v_res_867_;
}
LEAN_EXPORT lean_object* l_instToStringInt32___lam__0___boxed(lean_object* v_i_868_){
_start:
{
uint32_t v_i_boxed_869_; lean_object* v_res_870_; 
v_i_boxed_869_ = lean_unbox_uint32(v_i_868_);
lean_dec(v_i_868_);
v_res_870_ = l_instToStringInt32___lam__0(v_i_boxed_869_);
return v_res_870_;
}
}
lean_object* l_instReprInt32___lam__0(uint32_t v_i_873_, lean_object* v_prec_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_875_ = lean_int32_to_int(v_i_873_);
v___x_876_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_877_ = lean_int_dec_lt(v___x_875_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = l_Int_repr(v___x_875_);
lean_dec(v___x_875_);
v___x_879_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = l_Int_repr(v___x_875_);
lean_dec(v___x_875_);
v___x_881_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
v___x_882_ = l_Repr_addAppParen(v___x_881_, v_prec_874_);
return v___x_882_;
}
}
}
LEAN_EXPORT void l_instReprInt32___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_i_873_ = stack[0].m_num;
lean_object* v_prec_874_ = stack[1].m_obj;
lean_object* v_res_883_;
v_res_883_ = l_instReprInt32___lam__0(v_i_873_, v_prec_874_);
stack->m_obj
 = v_res_883_;
}
LEAN_EXPORT lean_object* l_instReprInt32___lam__0___boxed(lean_object* v_i_884_, lean_object* v_prec_885_){
_start:
{
uint32_t v_i_boxed_886_; lean_object* v_res_887_; 
v_i_boxed_886_ = lean_unbox_uint32(v_i_884_);
lean_dec(v_i_884_);
v_res_887_ = l_instReprInt32___lam__0(v_i_boxed_886_, v_prec_885_);
lean_dec(v_prec_885_);
return v_res_887_;
}
}
static lean_object* _init_l_instReprAtomInt32(void){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = lean_box(0);
return v___x_890_;
}
}
uint32_t l_Int32_instOfNat(lean_object* v_n_893_){
_start:
{
uint32_t v___x_894_; 
v___x_894_ = lean_int32_of_nat(v_n_893_);
return v___x_894_;
}
}
LEAN_EXPORT void l_Int32_instOfNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_893_ = stack[0].m_obj;
uint32_t v_res_895_;
v_res_895_ = l_Int32_instOfNat(v_n_893_);
stack->m_num = v_res_895_;
}
LEAN_EXPORT lean_object* l_Int32_instOfNat___boxed(lean_object* v_n_896_){
_start:
{
uint32_t v_res_897_; lean_object* v_r_898_; 
v_res_897_ = l_Int32_instOfNat(v_n_896_);
lean_dec(v_n_896_);
v_r_898_ = lean_box_uint32(v_res_897_);
return v_r_898_;
}
}
static uint32_t _init_l_Int32_maxValue___closed__0(void){
_start:
{
lean_object* v___x_901_; uint32_t v___x_902_; 
v___x_901_ = lean_unsigned_to_nat(2147483647u);
v___x_902_ = lean_int32_of_nat(v___x_901_);
return v___x_902_;
}
}
static uint32_t _init_l_Int32_maxValue(void){
_start:
{
uint32_t v___x_903_; 
v___x_903_ = lean_uint32_once(&l_Int32_maxValue___closed__0, &l_Int32_maxValue___closed__0_once, _init_l_Int32_maxValue___closed__0);
return v___x_903_;
}
}
static uint32_t _init_l_Int32_minValue___closed__0(void){
_start:
{
lean_object* v___x_904_; uint32_t v___x_905_; 
v___x_904_ = lean_unsigned_to_nat(2147483648u);
v___x_905_ = lean_int32_of_nat(v___x_904_);
return v___x_905_;
}
}
static uint32_t _init_l_Int32_minValue___closed__1(void){
_start:
{
uint32_t v___x_906_; uint32_t v___x_907_; 
v___x_906_ = lean_uint32_once(&l_Int32_minValue___closed__0, &l_Int32_minValue___closed__0_once, _init_l_Int32_minValue___closed__0);
v___x_907_ = lean_int32_neg(v___x_906_);
return v___x_907_;
}
}
static uint32_t _init_l_Int32_minValue(void){
_start:
{
uint32_t v___x_908_; 
v___x_908_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
return v___x_908_;
}
}
uint32_t l_Int32_ofIntLE___redArg(lean_object* v_i_909_){
_start:
{
uint32_t v___x_910_; 
v___x_910_ = lean_int32_of_int(v_i_909_);
return v___x_910_;
}
}
LEAN_EXPORT void l_Int32_ofIntLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_909_ = stack[0].m_obj;
uint32_t v_res_911_;
v_res_911_ = l_Int32_ofIntLE___redArg(v_i_909_);
stack->m_num = v_res_911_;
}
LEAN_EXPORT lean_object* l_Int32_ofIntLE___redArg___boxed(lean_object* v_i_912_){
_start:
{
uint32_t v_res_913_; lean_object* v_r_914_; 
v_res_913_ = l_Int32_ofIntLE___redArg(v_i_912_);
lean_dec(v_i_912_);
v_r_914_ = lean_box_uint32(v_res_913_);
return v_r_914_;
}
}
uint32_t l_Int32_ofIntLE(lean_object* v_i_915_, lean_object* v___hl_916_, lean_object* v___hr_917_){
_start:
{
uint32_t v___x_918_; 
v___x_918_ = lean_int32_of_int(v_i_915_);
return v___x_918_;
}
}
LEAN_EXPORT void l_Int32_ofIntLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_915_ = stack[0].m_obj;
uint32_t v_res_919_;
v_res_919_ = l_Int32_ofIntLE(v_i_915_, lean_box(0), lean_box(0));
stack->m_num = v_res_919_;
}
LEAN_EXPORT lean_object* l_Int32_ofIntLE___boxed(lean_object* v_i_920_, lean_object* v___hl_921_, lean_object* v___hr_922_){
_start:
{
uint32_t v_res_923_; lean_object* v_r_924_; 
v_res_923_ = l_Int32_ofIntLE(v_i_920_, v___hl_921_, v___hr_922_);
lean_dec(v_i_920_);
v_r_924_ = lean_box_uint32(v_res_923_);
return v_r_924_;
}
}
static lean_object* _init_l_Int32_ofIntClamp___closed__0(void){
_start:
{
uint32_t v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
v___x_926_ = lean_int32_to_int(v___x_925_);
return v___x_926_;
}
}
static lean_object* _init_l_Int32_ofIntClamp___closed__1(void){
_start:
{
uint32_t v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_uint32_once(&l_Int32_maxValue___closed__0, &l_Int32_maxValue___closed__0_once, _init_l_Int32_maxValue___closed__0);
v___x_928_ = lean_int32_to_int(v___x_927_);
return v___x_928_;
}
}
uint32_t l_Int32_ofIntClamp(lean_object* v_i_929_){
_start:
{
uint32_t v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_930_ = lean_uint32_once(&l_Int32_minValue___closed__1, &l_Int32_minValue___closed__1_once, _init_l_Int32_minValue___closed__1);
v___x_931_ = lean_obj_once(&l_Int32_ofIntClamp___closed__0, &l_Int32_ofIntClamp___closed__0_once, _init_l_Int32_ofIntClamp___closed__0);
v___x_932_ = lean_int_dec_le(v___x_931_, v_i_929_);
if (v___x_932_ == 0)
{
return v___x_930_;
}
else
{
uint32_t v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_933_ = lean_uint32_once(&l_Int32_maxValue___closed__0, &l_Int32_maxValue___closed__0_once, _init_l_Int32_maxValue___closed__0);
v___x_934_ = lean_obj_once(&l_Int32_ofIntClamp___closed__1, &l_Int32_ofIntClamp___closed__1_once, _init_l_Int32_ofIntClamp___closed__1);
v___x_935_ = lean_int_dec_le(v_i_929_, v___x_934_);
if (v___x_935_ == 0)
{
return v___x_933_;
}
else
{
uint32_t v___x_936_; 
v___x_936_ = lean_int32_of_int(v_i_929_);
return v___x_936_;
}
}
}
}
LEAN_EXPORT void l_Int32_ofIntClamp_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_929_ = stack[0].m_obj;
uint32_t v_res_937_;
v_res_937_ = l_Int32_ofIntClamp(v_i_929_);
stack->m_num = v_res_937_;
}
LEAN_EXPORT lean_object* l_Int32_ofIntClamp___boxed(lean_object* v_i_938_){
_start:
{
uint32_t v_res_939_; lean_object* v_r_940_; 
v_res_939_ = l_Int32_ofIntClamp(v_i_938_);
lean_dec(v_i_938_);
v_r_940_ = lean_box_uint32(v_res_939_);
return v_r_940_;
}
}
uint32_t l_Int32_ofIntTruncate(lean_object* v_i_941_){
_start:
{
uint32_t v___x_942_; 
v___x_942_ = l_Int32_ofIntClamp(v_i_941_);
return v___x_942_;
}
}
LEAN_EXPORT void l_Int32_ofIntTruncate_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_941_ = stack[0].m_obj;
uint32_t v_res_943_;
v_res_943_ = l_Int32_ofIntTruncate(v_i_941_);
stack->m_num = v_res_943_;
}
LEAN_EXPORT lean_object* l_Int32_ofIntTruncate___boxed(lean_object* v_i_944_){
_start:
{
uint32_t v_res_945_; lean_object* v_r_946_; 
v_res_945_ = l_Int32_ofIntTruncate(v_i_944_);
lean_dec(v_i_944_);
v_r_946_ = lean_box_uint32(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT void l_Int32_add_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_947_ = stack[0].m_num;
uint32_t v_b_948_ = stack[1].m_num;
uint32_t v_res_949_;
v_res_949_ = lean_int32_add(v_a_947_, v_b_948_);
stack->m_num = v_res_949_;
}
LEAN_EXPORT lean_object* l_Int32_add___boxed(lean_object* v_a_950_, lean_object* v_b_951_){
_start:
{
uint32_t v_a_boxed_952_; uint32_t v_b_boxed_953_; uint32_t v_res_954_; lean_object* v_r_955_; 
v_a_boxed_952_ = lean_unbox_uint32(v_a_950_);
lean_dec(v_a_950_);
v_b_boxed_953_ = lean_unbox_uint32(v_b_951_);
lean_dec(v_b_951_);
v_res_954_ = lean_int32_add(v_a_boxed_952_, v_b_boxed_953_);
v_r_955_ = lean_box_uint32(v_res_954_);
return v_r_955_;
}
}
LEAN_EXPORT void l_Int32_sub_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_956_ = stack[0].m_num;
uint32_t v_b_957_ = stack[1].m_num;
uint32_t v_res_958_;
v_res_958_ = lean_int32_sub(v_a_956_, v_b_957_);
stack->m_num = v_res_958_;
}
LEAN_EXPORT lean_object* l_Int32_sub___boxed(lean_object* v_a_959_, lean_object* v_b_960_){
_start:
{
uint32_t v_a_boxed_961_; uint32_t v_b_boxed_962_; uint32_t v_res_963_; lean_object* v_r_964_; 
v_a_boxed_961_ = lean_unbox_uint32(v_a_959_);
lean_dec(v_a_959_);
v_b_boxed_962_ = lean_unbox_uint32(v_b_960_);
lean_dec(v_b_960_);
v_res_963_ = lean_int32_sub(v_a_boxed_961_, v_b_boxed_962_);
v_r_964_ = lean_box_uint32(v_res_963_);
return v_r_964_;
}
}
LEAN_EXPORT void l_Int32_mul_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_965_ = stack[0].m_num;
uint32_t v_b_966_ = stack[1].m_num;
uint32_t v_res_967_;
v_res_967_ = lean_int32_mul(v_a_965_, v_b_966_);
stack->m_num = v_res_967_;
}
LEAN_EXPORT lean_object* l_Int32_mul___boxed(lean_object* v_a_968_, lean_object* v_b_969_){
_start:
{
uint32_t v_a_boxed_970_; uint32_t v_b_boxed_971_; uint32_t v_res_972_; lean_object* v_r_973_; 
v_a_boxed_970_ = lean_unbox_uint32(v_a_968_);
lean_dec(v_a_968_);
v_b_boxed_971_ = lean_unbox_uint32(v_b_969_);
lean_dec(v_b_969_);
v_res_972_ = lean_int32_mul(v_a_boxed_970_, v_b_boxed_971_);
v_r_973_ = lean_box_uint32(v_res_972_);
return v_r_973_;
}
}
LEAN_EXPORT void l_Int32_div_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_974_ = stack[0].m_num;
uint32_t v_b_975_ = stack[1].m_num;
uint32_t v_res_976_;
v_res_976_ = lean_int32_div(v_a_974_, v_b_975_);
stack->m_num = v_res_976_;
}
LEAN_EXPORT lean_object* l_Int32_div___boxed(lean_object* v_a_977_, lean_object* v_b_978_){
_start:
{
uint32_t v_a_boxed_979_; uint32_t v_b_boxed_980_; uint32_t v_res_981_; lean_object* v_r_982_; 
v_a_boxed_979_ = lean_unbox_uint32(v_a_977_);
lean_dec(v_a_977_);
v_b_boxed_980_ = lean_unbox_uint32(v_b_978_);
lean_dec(v_b_978_);
v_res_981_ = lean_int32_div(v_a_boxed_979_, v_b_boxed_980_);
v_r_982_ = lean_box_uint32(v_res_981_);
return v_r_982_;
}
}
static uint32_t _init_l_Int32_pow___closed__0(void){
_start:
{
lean_object* v___x_983_; uint32_t v___x_984_; 
v___x_983_ = lean_unsigned_to_nat(1u);
v___x_984_ = lean_int32_of_nat(v___x_983_);
return v___x_984_;
}
}
uint32_t l_Int32_pow(uint32_t v_x_985_, lean_object* v_n_986_){
_start:
{
lean_object* v_zero_987_; uint8_t v_isZero_988_; 
v_zero_987_ = lean_unsigned_to_nat(0u);
v_isZero_988_ = lean_nat_dec_eq(v_n_986_, v_zero_987_);
if (v_isZero_988_ == 1)
{
uint32_t v___x_989_; 
v___x_989_ = lean_uint32_once(&l_Int32_pow___closed__0, &l_Int32_pow___closed__0_once, _init_l_Int32_pow___closed__0);
return v___x_989_;
}
else
{
lean_object* v_one_990_; lean_object* v_n_991_; uint32_t v___x_992_; uint32_t v___x_993_; 
v_one_990_ = lean_unsigned_to_nat(1u);
v_n_991_ = lean_nat_sub(v_n_986_, v_one_990_);
v___x_992_ = l_Int32_pow(v_x_985_, v_n_991_);
lean_dec(v_n_991_);
v___x_993_ = lean_int32_mul(v___x_992_, v_x_985_);
return v___x_993_;
}
}
}
LEAN_EXPORT void l_Int32_pow_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_985_ = stack[0].m_num;
lean_object* v_n_986_ = stack[1].m_obj;
uint32_t v_res_994_;
v_res_994_ = l_Int32_pow(v_x_985_, v_n_986_);
stack->m_num = v_res_994_;
}
LEAN_EXPORT lean_object* l_Int32_pow___boxed(lean_object* v_x_995_, lean_object* v_n_996_){
_start:
{
uint32_t v_x_boxed_997_; uint32_t v_res_998_; lean_object* v_r_999_; 
v_x_boxed_997_ = lean_unbox_uint32(v_x_995_);
lean_dec(v_x_995_);
v_res_998_ = l_Int32_pow(v_x_boxed_997_, v_n_996_);
lean_dec(v_n_996_);
v_r_999_ = lean_box_uint32(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT void l_Int32_mod_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1000_ = stack[0].m_num;
uint32_t v_b_1001_ = stack[1].m_num;
uint32_t v_res_1002_;
v_res_1002_ = lean_int32_mod(v_a_1000_, v_b_1001_);
stack->m_num = v_res_1002_;
}
LEAN_EXPORT lean_object* l_Int32_mod___boxed(lean_object* v_a_1003_, lean_object* v_b_1004_){
_start:
{
uint32_t v_a_boxed_1005_; uint32_t v_b_boxed_1006_; uint32_t v_res_1007_; lean_object* v_r_1008_; 
v_a_boxed_1005_ = lean_unbox_uint32(v_a_1003_);
lean_dec(v_a_1003_);
v_b_boxed_1006_ = lean_unbox_uint32(v_b_1004_);
lean_dec(v_b_1004_);
v_res_1007_ = lean_int32_mod(v_a_boxed_1005_, v_b_boxed_1006_);
v_r_1008_ = lean_box_uint32(v_res_1007_);
return v_r_1008_;
}
}
LEAN_EXPORT void l_Int32_land_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1009_ = stack[0].m_num;
uint32_t v_b_1010_ = stack[1].m_num;
uint32_t v_res_1011_;
v_res_1011_ = lean_int32_land(v_a_1009_, v_b_1010_);
stack->m_num = v_res_1011_;
}
LEAN_EXPORT lean_object* l_Int32_land___boxed(lean_object* v_a_1012_, lean_object* v_b_1013_){
_start:
{
uint32_t v_a_boxed_1014_; uint32_t v_b_boxed_1015_; uint32_t v_res_1016_; lean_object* v_r_1017_; 
v_a_boxed_1014_ = lean_unbox_uint32(v_a_1012_);
lean_dec(v_a_1012_);
v_b_boxed_1015_ = lean_unbox_uint32(v_b_1013_);
lean_dec(v_b_1013_);
v_res_1016_ = lean_int32_land(v_a_boxed_1014_, v_b_boxed_1015_);
v_r_1017_ = lean_box_uint32(v_res_1016_);
return v_r_1017_;
}
}
LEAN_EXPORT void l_Int32_lor_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1018_ = stack[0].m_num;
uint32_t v_b_1019_ = stack[1].m_num;
uint32_t v_res_1020_;
v_res_1020_ = lean_int32_lor(v_a_1018_, v_b_1019_);
stack->m_num = v_res_1020_;
}
LEAN_EXPORT lean_object* l_Int32_lor___boxed(lean_object* v_a_1021_, lean_object* v_b_1022_){
_start:
{
uint32_t v_a_boxed_1023_; uint32_t v_b_boxed_1024_; uint32_t v_res_1025_; lean_object* v_r_1026_; 
v_a_boxed_1023_ = lean_unbox_uint32(v_a_1021_);
lean_dec(v_a_1021_);
v_b_boxed_1024_ = lean_unbox_uint32(v_b_1022_);
lean_dec(v_b_1022_);
v_res_1025_ = lean_int32_lor(v_a_boxed_1023_, v_b_boxed_1024_);
v_r_1026_ = lean_box_uint32(v_res_1025_);
return v_r_1026_;
}
}
LEAN_EXPORT void l_Int32_xor_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1027_ = stack[0].m_num;
uint32_t v_b_1028_ = stack[1].m_num;
uint32_t v_res_1029_;
v_res_1029_ = lean_int32_xor(v_a_1027_, v_b_1028_);
stack->m_num = v_res_1029_;
}
LEAN_EXPORT lean_object* l_Int32_xor___boxed(lean_object* v_a_1030_, lean_object* v_b_1031_){
_start:
{
uint32_t v_a_boxed_1032_; uint32_t v_b_boxed_1033_; uint32_t v_res_1034_; lean_object* v_r_1035_; 
v_a_boxed_1032_ = lean_unbox_uint32(v_a_1030_);
lean_dec(v_a_1030_);
v_b_boxed_1033_ = lean_unbox_uint32(v_b_1031_);
lean_dec(v_b_1031_);
v_res_1034_ = lean_int32_xor(v_a_boxed_1032_, v_b_boxed_1033_);
v_r_1035_ = lean_box_uint32(v_res_1034_);
return v_r_1035_;
}
}
LEAN_EXPORT void l_Int32_shiftLeft_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1036_ = stack[0].m_num;
uint32_t v_b_1037_ = stack[1].m_num;
uint32_t v_res_1038_;
v_res_1038_ = lean_int32_shift_left(v_a_1036_, v_b_1037_);
stack->m_num = v_res_1038_;
}
LEAN_EXPORT lean_object* l_Int32_shiftLeft___boxed(lean_object* v_a_1039_, lean_object* v_b_1040_){
_start:
{
uint32_t v_a_boxed_1041_; uint32_t v_b_boxed_1042_; uint32_t v_res_1043_; lean_object* v_r_1044_; 
v_a_boxed_1041_ = lean_unbox_uint32(v_a_1039_);
lean_dec(v_a_1039_);
v_b_boxed_1042_ = lean_unbox_uint32(v_b_1040_);
lean_dec(v_b_1040_);
v_res_1043_ = lean_int32_shift_left(v_a_boxed_1041_, v_b_boxed_1042_);
v_r_1044_ = lean_box_uint32(v_res_1043_);
return v_r_1044_;
}
}
LEAN_EXPORT void l_Int32_shiftRight_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1045_ = stack[0].m_num;
uint32_t v_b_1046_ = stack[1].m_num;
uint32_t v_res_1047_;
v_res_1047_ = lean_int32_shift_right(v_a_1045_, v_b_1046_);
stack->m_num = v_res_1047_;
}
LEAN_EXPORT lean_object* l_Int32_shiftRight___boxed(lean_object* v_a_1048_, lean_object* v_b_1049_){
_start:
{
uint32_t v_a_boxed_1050_; uint32_t v_b_boxed_1051_; uint32_t v_res_1052_; lean_object* v_r_1053_; 
v_a_boxed_1050_ = lean_unbox_uint32(v_a_1048_);
lean_dec(v_a_1048_);
v_b_boxed_1051_ = lean_unbox_uint32(v_b_1049_);
lean_dec(v_b_1049_);
v_res_1052_ = lean_int32_shift_right(v_a_boxed_1050_, v_b_boxed_1051_);
v_r_1053_ = lean_box_uint32(v_res_1052_);
return v_r_1053_;
}
}
LEAN_EXPORT void l_Int32_complement_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1054_ = stack[0].m_num;
uint32_t v_res_1055_;
v_res_1055_ = lean_int32_complement(v_a_1054_);
stack->m_num = v_res_1055_;
}
LEAN_EXPORT lean_object* l_Int32_complement___boxed(lean_object* v_a_1056_){
_start:
{
uint32_t v_a_boxed_1057_; uint32_t v_res_1058_; lean_object* v_r_1059_; 
v_a_boxed_1057_ = lean_unbox_uint32(v_a_1056_);
lean_dec(v_a_1056_);
v_res_1058_ = lean_int32_complement(v_a_boxed_1057_);
v_r_1059_ = lean_box_uint32(v_res_1058_);
return v_r_1059_;
}
}
LEAN_EXPORT void l_Int32_abs_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1060_ = stack[0].m_num;
uint32_t v_res_1061_;
v_res_1061_ = lean_int32_abs(v_a_1060_);
stack->m_num = v_res_1061_;
}
LEAN_EXPORT lean_object* l_Int32_abs___boxed(lean_object* v_a_1062_){
_start:
{
uint32_t v_a_boxed_1063_; uint32_t v_res_1064_; lean_object* v_r_1065_; 
v_a_boxed_1063_ = lean_unbox_uint32(v_a_1062_);
lean_dec(v_a_1062_);
v_res_1064_ = lean_int32_abs(v_a_boxed_1063_);
v_r_1065_ = lean_box_uint32(v_res_1064_);
return v_r_1065_;
}
}
LEAN_EXPORT void l_Int32_decEq_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1066_ = stack[0].m_num;
uint32_t v_b_1067_ = stack[1].m_num;
uint8_t v_res_1068_;
v_res_1068_ = lean_int32_dec_eq(v_a_1066_, v_b_1067_);
stack->m_num = v_res_1068_;
}
LEAN_EXPORT lean_object* l_Int32_decEq___boxed(lean_object* v_a_1069_, lean_object* v_b_1070_){
_start:
{
uint32_t v_a_boxed_1071_; uint32_t v_b_boxed_1072_; uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_a_boxed_1071_ = lean_unbox_uint32(v_a_1069_);
lean_dec(v_a_1069_);
v_b_boxed_1072_ = lean_unbox_uint32(v_b_1070_);
lean_dec(v_b_1070_);
v_res_1073_ = lean_int32_dec_eq(v_a_boxed_1071_, v_b_boxed_1072_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
static uint32_t _init_l_instInhabitedInt32___closed__0(void){
_start:
{
lean_object* v___x_1075_; uint32_t v___x_1076_; 
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_int32_of_nat(v___x_1075_);
return v___x_1076_;
}
}
static uint32_t _init_l_instInhabitedInt32(void){
_start:
{
uint32_t v___x_1077_; 
v___x_1077_ = lean_uint32_once(&l_instInhabitedInt32___closed__0, &l_instInhabitedInt32___closed__0_once, _init_l_instInhabitedInt32___closed__0);
return v___x_1077_;
}
}
static lean_object* _init_l_instLTInt32(void){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_box(0);
return v___x_1090_;
}
}
static lean_object* _init_l_instLEInt32(void){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_box(0);
return v___x_1091_;
}
}
uint8_t l_instDecidableEqInt32(uint32_t v_a_1104_, uint32_t v_b_1105_){
_start:
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_int32_dec_eq(v_a_1104_, v_b_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT void l_instDecidableEqInt32_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1104_ = stack[0].m_num;
uint32_t v_b_1105_ = stack[1].m_num;
uint8_t v_res_1107_;
v_res_1107_ = l_instDecidableEqInt32(v_a_1104_, v_b_1105_);
stack->m_num = v_res_1107_;
}
LEAN_EXPORT lean_object* l_instDecidableEqInt32___boxed(lean_object* v_a_1108_, lean_object* v_b_1109_){
_start:
{
uint32_t v_a_boxed_1110_; uint32_t v_b_boxed_1111_; uint8_t v_res_1112_; lean_object* v_r_1113_; 
v_a_boxed_1110_ = lean_unbox_uint32(v_a_1108_);
lean_dec(v_a_1108_);
v_b_boxed_1111_ = lean_unbox_uint32(v_b_1109_);
lean_dec(v_b_1109_);
v_res_1112_ = l_instDecidableEqInt32(v_a_boxed_1110_, v_b_boxed_1111_);
v_r_1113_ = lean_box(v_res_1112_);
return v_r_1113_;
}
}
LEAN_EXPORT void l_Bool_toInt32_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_1114_ = stack[0].m_num;
uint32_t v_res_1115_;
v_res_1115_ = lean_bool_to_int32(v_b_1114_);
stack->m_num = v_res_1115_;
}
LEAN_EXPORT lean_object* l_Bool_toInt32___boxed(lean_object* v_b_1116_){
_start:
{
uint8_t v_b_boxed_1117_; uint32_t v_res_1118_; lean_object* v_r_1119_; 
v_b_boxed_1117_ = lean_unbox(v_b_1116_);
v_res_1118_ = lean_bool_to_int32(v_b_boxed_1117_);
v_r_1119_ = lean_box_uint32(v_res_1118_);
return v_r_1119_;
}
}
uint8_t l_Int32_decLt___aux__1(uint32_t v_a_1120_, uint32_t v_b_1121_){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1122_ = lean_unsigned_to_nat(32u);
v___x_1123_ = lean_uint32_to_nat(v_a_1120_);
v___x_1124_ = lean_uint32_to_nat(v_b_1121_);
v___x_1125_ = l_BitVec_slt(v___x_1122_, v___x_1123_, v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT void l_Int32_decLt___aux__1_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1120_ = stack[0].m_num;
uint32_t v_b_1121_ = stack[1].m_num;
uint8_t v_res_1126_;
v_res_1126_ = l_Int32_decLt___aux__1(v_a_1120_, v_b_1121_);
stack->m_num = v_res_1126_;
}
LEAN_EXPORT lean_object* l_Int32_decLt___aux__1___boxed(lean_object* v_a_1127_, lean_object* v_b_1128_){
_start:
{
uint32_t v_a_boxed_1129_; uint32_t v_b_boxed_1130_; uint8_t v_res_1131_; lean_object* v_r_1132_; 
v_a_boxed_1129_ = lean_unbox_uint32(v_a_1127_);
lean_dec(v_a_1127_);
v_b_boxed_1130_ = lean_unbox_uint32(v_b_1128_);
lean_dec(v_b_1128_);
v_res_1131_ = l_Int32_decLt___aux__1(v_a_boxed_1129_, v_b_boxed_1130_);
v_r_1132_ = lean_box(v_res_1131_);
return v_r_1132_;
}
}
LEAN_EXPORT void l_Int32_decLt_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1133_ = stack[0].m_num;
uint32_t v_b_1134_ = stack[1].m_num;
uint8_t v_res_1135_;
v_res_1135_ = lean_int32_dec_lt(v_a_1133_, v_b_1134_);
stack->m_num = v_res_1135_;
}
LEAN_EXPORT lean_object* l_Int32_decLt___boxed(lean_object* v_a_1136_, lean_object* v_b_1137_){
_start:
{
uint32_t v_a_boxed_1138_; uint32_t v_b_boxed_1139_; uint8_t v_res_1140_; lean_object* v_r_1141_; 
v_a_boxed_1138_ = lean_unbox_uint32(v_a_1136_);
lean_dec(v_a_1136_);
v_b_boxed_1139_ = lean_unbox_uint32(v_b_1137_);
lean_dec(v_b_1137_);
v_res_1140_ = lean_int32_dec_lt(v_a_boxed_1138_, v_b_boxed_1139_);
v_r_1141_ = lean_box(v_res_1140_);
return v_r_1141_;
}
}
uint8_t l_Int32_decLe___aux__1(uint32_t v_a_1142_, uint32_t v_b_1143_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1144_ = lean_unsigned_to_nat(32u);
v___x_1145_ = lean_uint32_to_nat(v_a_1142_);
v___x_1146_ = lean_uint32_to_nat(v_b_1143_);
v___x_1147_ = l_BitVec_sle(v___x_1144_, v___x_1145_, v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT void l_Int32_decLe___aux__1_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1142_ = stack[0].m_num;
uint32_t v_b_1143_ = stack[1].m_num;
uint8_t v_res_1148_;
v_res_1148_ = l_Int32_decLe___aux__1(v_a_1142_, v_b_1143_);
stack->m_num = v_res_1148_;
}
LEAN_EXPORT lean_object* l_Int32_decLe___aux__1___boxed(lean_object* v_a_1149_, lean_object* v_b_1150_){
_start:
{
uint32_t v_a_boxed_1151_; uint32_t v_b_boxed_1152_; uint8_t v_res_1153_; lean_object* v_r_1154_; 
v_a_boxed_1151_ = lean_unbox_uint32(v_a_1149_);
lean_dec(v_a_1149_);
v_b_boxed_1152_ = lean_unbox_uint32(v_b_1150_);
lean_dec(v_b_1150_);
v_res_1153_ = l_Int32_decLe___aux__1(v_a_boxed_1151_, v_b_boxed_1152_);
v_r_1154_ = lean_box(v_res_1153_);
return v_r_1154_;
}
}
LEAN_EXPORT void l_Int32_decLe_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1155_ = stack[0].m_num;
uint32_t v_b_1156_ = stack[1].m_num;
uint8_t v_res_1157_;
v_res_1157_ = lean_int32_dec_le(v_a_1155_, v_b_1156_);
stack->m_num = v_res_1157_;
}
LEAN_EXPORT lean_object* l_Int32_decLe___boxed(lean_object* v_a_1158_, lean_object* v_b_1159_){
_start:
{
uint32_t v_a_boxed_1160_; uint32_t v_b_boxed_1161_; uint8_t v_res_1162_; lean_object* v_r_1163_; 
v_a_boxed_1160_ = lean_unbox_uint32(v_a_1158_);
lean_dec(v_a_1158_);
v_b_boxed_1161_ = lean_unbox_uint32(v_b_1159_);
lean_dec(v_b_1159_);
v_res_1162_ = lean_int32_dec_le(v_a_boxed_1160_, v_b_boxed_1161_);
v_r_1163_ = lean_box(v_res_1162_);
return v_r_1163_;
}
}
uint32_t l_instMaxInt32___lam__0(uint32_t v_x_1164_, uint32_t v_y_1165_){
_start:
{
uint8_t v___x_1166_; 
v___x_1166_ = lean_int32_dec_le(v_x_1164_, v_y_1165_);
if (v___x_1166_ == 0)
{
return v_x_1164_;
}
else
{
return v_y_1165_;
}
}
}
LEAN_EXPORT void l_instMaxInt32___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_1164_ = stack[0].m_num;
uint32_t v_y_1165_ = stack[1].m_num;
uint32_t v_res_1167_;
v_res_1167_ = l_instMaxInt32___lam__0(v_x_1164_, v_y_1165_);
stack->m_num = v_res_1167_;
}
LEAN_EXPORT lean_object* l_instMaxInt32___lam__0___boxed(lean_object* v_x_1168_, lean_object* v_y_1169_){
_start:
{
uint32_t v_x_boxed_1170_; uint32_t v_y_boxed_1171_; uint32_t v_res_1172_; lean_object* v_r_1173_; 
v_x_boxed_1170_ = lean_unbox_uint32(v_x_1168_);
lean_dec(v_x_1168_);
v_y_boxed_1171_ = lean_unbox_uint32(v_y_1169_);
lean_dec(v_y_1169_);
v_res_1172_ = l_instMaxInt32___lam__0(v_x_boxed_1170_, v_y_boxed_1171_);
v_r_1173_ = lean_box_uint32(v_res_1172_);
return v_r_1173_;
}
}
uint32_t l_instMinInt32___lam__0(uint32_t v_x_1176_, uint32_t v_y_1177_){
_start:
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_int32_dec_le(v_x_1176_, v_y_1177_);
if (v___x_1178_ == 0)
{
return v_y_1177_;
}
else
{
return v_x_1176_;
}
}
}
LEAN_EXPORT void l_instMinInt32___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_1176_ = stack[0].m_num;
uint32_t v_y_1177_ = stack[1].m_num;
uint32_t v_res_1179_;
v_res_1179_ = l_instMinInt32___lam__0(v_x_1176_, v_y_1177_);
stack->m_num = v_res_1179_;
}
LEAN_EXPORT lean_object* l_instMinInt32___lam__0___boxed(lean_object* v_x_1180_, lean_object* v_y_1181_){
_start:
{
uint32_t v_x_boxed_1182_; uint32_t v_y_boxed_1183_; uint32_t v_res_1184_; lean_object* v_r_1185_; 
v_x_boxed_1182_ = lean_unbox_uint32(v_x_1180_);
lean_dec(v_x_1180_);
v_y_boxed_1183_ = lean_unbox_uint32(v_y_1181_);
lean_dec(v_y_1181_);
v_res_1184_ = l_instMinInt32___lam__0(v_x_boxed_1182_, v_y_boxed_1183_);
v_r_1185_ = lean_box_uint32(v_res_1184_);
return v_r_1185_;
}
}
static lean_object* _init_l_Int64_size___closed__0(void){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_cstr_to_nat("18446744073709551616");
return v___x_1188_;
}
}
static lean_object* _init_l_Int64_size(void){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_obj_once(&l_Int64_size___closed__0, &l_Int64_size___closed__0_once, _init_l_Int64_size___closed__0);
return v___x_1189_;
}
}
lean_object* l_Int64_toBitVec(uint64_t v_x_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_uint64_to_nat(v_x_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT void l_Int64_toBitVec_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_1190_ = stack[0].m_num;
lean_object* v_res_1192_;
v_res_1192_ = l_Int64_toBitVec(v_x_1190_);
stack->m_obj
 = v_res_1192_;
}
LEAN_EXPORT lean_object* l_Int64_toBitVec___boxed(lean_object* v_x_1193_){
_start:
{
uint64_t v_x_boxed_1194_; lean_object* v_res_1195_; 
v_x_boxed_1194_ = lean_unbox_uint64(v_x_1193_);
lean_dec_ref(v_x_1193_);
v_res_1195_ = l_Int64_toBitVec(v_x_boxed_1194_);
return v_res_1195_;
}
}
uint64_t l_UInt64_toInt64(uint64_t v_i_1196_){
_start:
{
return v_i_1196_;
}
}
LEAN_EXPORT void l_UInt64_toInt64_0interp(lean_interpreter_value* stack)
{
uint64_t v_i_1196_ = stack[0].m_num;
uint64_t v_res_1197_;
v_res_1197_ = l_UInt64_toInt64(v_i_1196_);
stack->m_num = v_res_1197_;
}
LEAN_EXPORT lean_object* l_UInt64_toInt64___boxed(lean_object* v_i_1198_){
_start:
{
uint64_t v_i_boxed_1199_; uint64_t v_res_1200_; lean_object* v_r_1201_; 
v_i_boxed_1199_ = lean_unbox_uint64(v_i_1198_);
lean_dec_ref(v_i_1198_);
v_res_1200_ = l_UInt64_toInt64(v_i_boxed_1199_);
v_r_1201_ = lean_box_uint64(v_res_1200_);
return v_r_1201_;
}
}
LEAN_EXPORT void l_Int64_ofInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1202_ = stack[0].m_obj;
uint64_t v_res_1203_;
v_res_1203_ = lean_int64_of_int(v_i_1202_);
stack->m_num = v_res_1203_;
}
LEAN_EXPORT lean_object* l_Int64_ofInt___boxed(lean_object* v_i_1204_){
_start:
{
uint64_t v_res_1205_; lean_object* v_r_1206_; 
v_res_1205_ = lean_int64_of_int(v_i_1204_);
lean_dec(v_i_1204_);
v_r_1206_ = lean_box_uint64(v_res_1205_);
return v_r_1206_;
}
}
LEAN_EXPORT void l_Int64_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1207_ = stack[0].m_obj;
uint64_t v_res_1208_;
v_res_1208_ = lean_int64_of_nat(v_n_1207_);
stack->m_num = v_res_1208_;
}
LEAN_EXPORT lean_object* l_Int64_ofNat___boxed(lean_object* v_n_1209_){
_start:
{
uint64_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = lean_int64_of_nat(v_n_1209_);
lean_dec(v_n_1209_);
v_r_1211_ = lean_box_uint64(v_res_1210_);
return v_r_1211_;
}
}
uint64_t l_Int_toInt64(lean_object* v_i_1212_){
_start:
{
uint64_t v___x_1213_; 
v___x_1213_ = lean_int64_of_int(v_i_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT void l_Int_toInt64_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1212_ = stack[0].m_obj;
uint64_t v_res_1214_;
v_res_1214_ = l_Int_toInt64(v_i_1212_);
stack->m_num = v_res_1214_;
}
LEAN_EXPORT lean_object* l_Int_toInt64___boxed(lean_object* v_i_1215_){
_start:
{
uint64_t v_res_1216_; lean_object* v_r_1217_; 
v_res_1216_ = l_Int_toInt64(v_i_1215_);
lean_dec(v_i_1215_);
v_r_1217_ = lean_box_uint64(v_res_1216_);
return v_r_1217_;
}
}
uint64_t l_Nat_toInt64(lean_object* v_n_1218_){
_start:
{
uint64_t v___x_1219_; 
v___x_1219_ = lean_int64_of_nat(v_n_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT void l_Nat_toInt64_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1218_ = stack[0].m_obj;
uint64_t v_res_1220_;
v_res_1220_ = l_Nat_toInt64(v_n_1218_);
stack->m_num = v_res_1220_;
}
LEAN_EXPORT lean_object* l_Nat_toInt64___boxed(lean_object* v_n_1221_){
_start:
{
uint64_t v_res_1222_; lean_object* v_r_1223_; 
v_res_1222_ = l_Nat_toInt64(v_n_1221_);
lean_dec(v_n_1221_);
v_r_1223_ = lean_box_uint64(v_res_1222_);
return v_r_1223_;
}
}
LEAN_EXPORT void l_Int64_toInt_0interp(lean_interpreter_value* stack)
{
uint64_t v_i_1224_ = stack[0].m_num;
lean_object* v_res_1225_;
v_res_1225_ = lean_int64_to_int_sint(v_i_1224_);
stack->m_obj
 = v_res_1225_;
}
LEAN_EXPORT lean_object* l_Int64_toInt___boxed(lean_object* v_i_1226_){
_start:
{
uint64_t v_i_boxed_1227_; lean_object* v_res_1228_; 
v_i_boxed_1227_ = lean_unbox_uint64(v_i_1226_);
lean_dec_ref(v_i_1226_);
v_res_1228_ = lean_int64_to_int_sint(v_i_boxed_1227_);
return v_res_1228_;
}
}
lean_object* l_Int64_toNatClampNeg(uint64_t v_i_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_int64_to_int_sint(v_i_1229_);
v___x_1231_ = l_Int_toNat(v___x_1230_);
lean_dec(v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT void l_Int64_toNatClampNeg_0interp(lean_interpreter_value* stack)
{
uint64_t v_i_1229_ = stack[0].m_num;
lean_object* v_res_1232_;
v_res_1232_ = l_Int64_toNatClampNeg(v_i_1229_);
stack->m_obj
 = v_res_1232_;
}
LEAN_EXPORT lean_object* l_Int64_toNatClampNeg___boxed(lean_object* v_i_1233_){
_start:
{
uint64_t v_i_boxed_1234_; lean_object* v_res_1235_; 
v_i_boxed_1234_ = lean_unbox_uint64(v_i_1233_);
lean_dec_ref(v_i_1233_);
v_res_1235_ = l_Int64_toNatClampNeg(v_i_boxed_1234_);
return v_res_1235_;
}
}
uint64_t l_Int64_ofBitVec(lean_object* v_b_1236_){
_start:
{
uint64_t v___x_1237_; 
v___x_1237_ = lean_uint64_of_nat_mk(v_b_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT void l_Int64_ofBitVec_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_1236_ = stack[0].m_obj;
uint64_t v_res_1238_;
v_res_1238_ = l_Int64_ofBitVec(v_b_1236_);
stack->m_num = v_res_1238_;
}
LEAN_EXPORT lean_object* l_Int64_ofBitVec___boxed(lean_object* v_b_1239_){
_start:
{
uint64_t v_res_1240_; lean_object* v_r_1241_; 
v_res_1240_ = l_Int64_ofBitVec(v_b_1239_);
v_r_1241_ = lean_box_uint64(v_res_1240_);
return v_r_1241_;
}
}
LEAN_EXPORT void l_Int64_toInt8_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1242_ = stack[0].m_num;
uint8_t v_res_1243_;
v_res_1243_ = lean_int64_to_int8(v_a_1242_);
stack->m_num = v_res_1243_;
}
LEAN_EXPORT lean_object* l_Int64_toInt8___boxed(lean_object* v_a_1244_){
_start:
{
uint64_t v_a_boxed_1245_; uint8_t v_res_1246_; lean_object* v_r_1247_; 
v_a_boxed_1245_ = lean_unbox_uint64(v_a_1244_);
lean_dec_ref(v_a_1244_);
v_res_1246_ = lean_int64_to_int8(v_a_boxed_1245_);
v_r_1247_ = lean_box(v_res_1246_);
return v_r_1247_;
}
}
LEAN_EXPORT void l_Int64_toInt16_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1248_ = stack[0].m_num;
uint16_t v_res_1249_;
v_res_1249_ = lean_int64_to_int16(v_a_1248_);
stack->m_num = v_res_1249_;
}
LEAN_EXPORT lean_object* l_Int64_toInt16___boxed(lean_object* v_a_1250_){
_start:
{
uint64_t v_a_boxed_1251_; uint16_t v_res_1252_; lean_object* v_r_1253_; 
v_a_boxed_1251_ = lean_unbox_uint64(v_a_1250_);
lean_dec_ref(v_a_1250_);
v_res_1252_ = lean_int64_to_int16(v_a_boxed_1251_);
v_r_1253_ = lean_box(v_res_1252_);
return v_r_1253_;
}
}
LEAN_EXPORT void l_Int64_toInt32_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1254_ = stack[0].m_num;
uint32_t v_res_1255_;
v_res_1255_ = lean_int64_to_int32(v_a_1254_);
stack->m_num = v_res_1255_;
}
LEAN_EXPORT lean_object* l_Int64_toInt32___boxed(lean_object* v_a_1256_){
_start:
{
uint64_t v_a_boxed_1257_; uint32_t v_res_1258_; lean_object* v_r_1259_; 
v_a_boxed_1257_ = lean_unbox_uint64(v_a_1256_);
lean_dec_ref(v_a_1256_);
v_res_1258_ = lean_int64_to_int32(v_a_boxed_1257_);
v_r_1259_ = lean_box_uint32(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT void l_Int8_toInt64_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_1260_ = stack[0].m_num;
uint64_t v_res_1261_;
v_res_1261_ = lean_int8_to_int64(v_a_1260_);
stack->m_num = v_res_1261_;
}
LEAN_EXPORT lean_object* l_Int8_toInt64___boxed(lean_object* v_a_1262_){
_start:
{
uint8_t v_a_boxed_1263_; uint64_t v_res_1264_; lean_object* v_r_1265_; 
v_a_boxed_1263_ = lean_unbox(v_a_1262_);
v_res_1264_ = lean_int8_to_int64(v_a_boxed_1263_);
v_r_1265_ = lean_box_uint64(v_res_1264_);
return v_r_1265_;
}
}
LEAN_EXPORT void l_Int16_toInt64_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_1266_ = stack[0].m_num;
uint64_t v_res_1267_;
v_res_1267_ = lean_int16_to_int64(v_a_1266_);
stack->m_num = v_res_1267_;
}
LEAN_EXPORT lean_object* l_Int16_toInt64___boxed(lean_object* v_a_1268_){
_start:
{
uint16_t v_a_boxed_1269_; uint64_t v_res_1270_; lean_object* v_r_1271_; 
v_a_boxed_1269_ = lean_unbox(v_a_1268_);
v_res_1270_ = lean_int16_to_int64(v_a_boxed_1269_);
v_r_1271_ = lean_box_uint64(v_res_1270_);
return v_r_1271_;
}
}
LEAN_EXPORT void l_Int32_toInt64_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1272_ = stack[0].m_num;
uint64_t v_res_1273_;
v_res_1273_ = lean_int32_to_int64(v_a_1272_);
stack->m_num = v_res_1273_;
}
LEAN_EXPORT lean_object* l_Int32_toInt64___boxed(lean_object* v_a_1274_){
_start:
{
uint32_t v_a_boxed_1275_; uint64_t v_res_1276_; lean_object* v_r_1277_; 
v_a_boxed_1275_ = lean_unbox_uint32(v_a_1274_);
lean_dec(v_a_1274_);
v_res_1276_ = lean_int32_to_int64(v_a_boxed_1275_);
v_r_1277_ = lean_box_uint64(v_res_1276_);
return v_r_1277_;
}
}
LEAN_EXPORT void l_Int64_neg_0interp(lean_interpreter_value* stack)
{
uint64_t v_i_1278_ = stack[0].m_num;
uint64_t v_res_1279_;
v_res_1279_ = lean_int64_neg(v_i_1278_);
stack->m_num = v_res_1279_;
}
LEAN_EXPORT lean_object* l_Int64_neg___boxed(lean_object* v_i_1280_){
_start:
{
uint64_t v_i_boxed_1281_; uint64_t v_res_1282_; lean_object* v_r_1283_; 
v_i_boxed_1281_ = lean_unbox_uint64(v_i_1280_);
lean_dec_ref(v_i_1280_);
v_res_1282_ = lean_int64_neg(v_i_boxed_1281_);
v_r_1283_ = lean_box_uint64(v_res_1282_);
return v_r_1283_;
}
}
lean_object* l_instToStringInt64___lam__0(uint64_t v_i_1284_){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_int64_to_int_sint(v_i_1284_);
v___x_1286_ = l_Int_repr(v___x_1285_);
lean_dec(v___x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT void l_instToStringInt64___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_i_1284_ = stack[0].m_num;
lean_object* v_res_1287_;
v_res_1287_ = l_instToStringInt64___lam__0(v_i_1284_);
stack->m_obj
 = v_res_1287_;
}
LEAN_EXPORT lean_object* l_instToStringInt64___lam__0___boxed(lean_object* v_i_1288_){
_start:
{
uint64_t v_i_boxed_1289_; lean_object* v_res_1290_; 
v_i_boxed_1289_ = lean_unbox_uint64(v_i_1288_);
lean_dec_ref(v_i_1288_);
v_res_1290_ = l_instToStringInt64___lam__0(v_i_boxed_1289_);
return v_res_1290_;
}
}
lean_object* l_instReprInt64___lam__0(uint64_t v_i_1293_, lean_object* v_prec_1294_){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1295_ = lean_int64_to_int_sint(v_i_1293_);
v___x_1296_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_1297_ = lean_int_dec_lt(v___x_1295_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = l_Int_repr(v___x_1295_);
lean_dec(v___x_1295_);
v___x_1299_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1300_ = l_Int_repr(v___x_1295_);
lean_dec(v___x_1295_);
v___x_1301_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
v___x_1302_ = l_Repr_addAppParen(v___x_1301_, v_prec_1294_);
return v___x_1302_;
}
}
}
LEAN_EXPORT void l_instReprInt64___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_i_1293_ = stack[0].m_num;
lean_object* v_prec_1294_ = stack[1].m_obj;
lean_object* v_res_1303_;
v_res_1303_ = l_instReprInt64___lam__0(v_i_1293_, v_prec_1294_);
stack->m_obj
 = v_res_1303_;
}
LEAN_EXPORT lean_object* l_instReprInt64___lam__0___boxed(lean_object* v_i_1304_, lean_object* v_prec_1305_){
_start:
{
uint64_t v_i_boxed_1306_; lean_object* v_res_1307_; 
v_i_boxed_1306_ = lean_unbox_uint64(v_i_1304_);
lean_dec_ref(v_i_1304_);
v_res_1307_ = l_instReprInt64___lam__0(v_i_boxed_1306_, v_prec_1305_);
lean_dec(v_prec_1305_);
return v_res_1307_;
}
}
static lean_object* _init_l_instReprAtomInt64(void){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = lean_box(0);
return v___x_1310_;
}
}
uint64_t l_instHashableInt64___lam__0(uint64_t v_i_1311_){
_start:
{
return v_i_1311_;
}
}
LEAN_EXPORT void l_instHashableInt64___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_i_1311_ = stack[0].m_num;
uint64_t v_res_1312_;
v_res_1312_ = l_instHashableInt64___lam__0(v_i_1311_);
stack->m_num = v_res_1312_;
}
LEAN_EXPORT lean_object* l_instHashableInt64___lam__0___boxed(lean_object* v_i_1313_){
_start:
{
uint64_t v_i_boxed_1314_; uint64_t v_res_1315_; lean_object* v_r_1316_; 
v_i_boxed_1314_ = lean_unbox_uint64(v_i_1313_);
lean_dec_ref(v_i_1313_);
v_res_1315_ = l_instHashableInt64___lam__0(v_i_boxed_1314_);
v_r_1316_ = lean_box_uint64(v_res_1315_);
return v_r_1316_;
}
}
uint64_t l_Int64_instOfNat(lean_object* v_n_1319_){
_start:
{
uint64_t v___x_1320_; 
v___x_1320_ = lean_int64_of_nat(v_n_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT void l_Int64_instOfNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1319_ = stack[0].m_obj;
uint64_t v_res_1321_;
v_res_1321_ = l_Int64_instOfNat(v_n_1319_);
stack->m_num = v_res_1321_;
}
LEAN_EXPORT lean_object* l_Int64_instOfNat___boxed(lean_object* v_n_1322_){
_start:
{
uint64_t v_res_1323_; lean_object* v_r_1324_; 
v_res_1323_ = l_Int64_instOfNat(v_n_1322_);
lean_dec(v_n_1322_);
v_r_1324_ = lean_box_uint64(v_res_1323_);
return v_r_1324_;
}
}
static uint64_t _init_l_Int64_maxValue___closed__0(void){
_start:
{
lean_object* v___x_1327_; uint64_t v___x_1328_; 
v___x_1327_ = lean_cstr_to_nat("9223372036854775807");
v___x_1328_ = lean_int64_of_nat(v___x_1327_);
return v___x_1328_;
}
}
static uint64_t _init_l_Int64_maxValue(void){
_start:
{
uint64_t v___x_1329_; 
v___x_1329_ = lean_uint64_once(&l_Int64_maxValue___closed__0, &l_Int64_maxValue___closed__0_once, _init_l_Int64_maxValue___closed__0);
return v___x_1329_;
}
}
static lean_object* _init_l_Int64_minValue___closed__0(void){
_start:
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_cstr_to_nat("9223372036854775808");
return v___x_1330_;
}
}
static uint64_t _init_l_Int64_minValue___closed__1(void){
_start:
{
lean_object* v___x_1331_; uint64_t v___x_1332_; 
v___x_1331_ = lean_obj_once(&l_Int64_minValue___closed__0, &l_Int64_minValue___closed__0_once, _init_l_Int64_minValue___closed__0);
v___x_1332_ = lean_int64_of_nat(v___x_1331_);
return v___x_1332_;
}
}
static uint64_t _init_l_Int64_minValue___closed__2(void){
_start:
{
uint64_t v___x_1333_; uint64_t v___x_1334_; 
v___x_1333_ = lean_uint64_once(&l_Int64_minValue___closed__1, &l_Int64_minValue___closed__1_once, _init_l_Int64_minValue___closed__1);
v___x_1334_ = lean_int64_neg(v___x_1333_);
return v___x_1334_;
}
}
static uint64_t _init_l_Int64_minValue(void){
_start:
{
uint64_t v___x_1335_; 
v___x_1335_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
return v___x_1335_;
}
}
uint64_t l_Int64_ofIntLE___redArg(lean_object* v_i_1336_){
_start:
{
uint64_t v___x_1337_; 
v___x_1337_ = lean_int64_of_int(v_i_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT void l_Int64_ofIntLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1336_ = stack[0].m_obj;
uint64_t v_res_1338_;
v_res_1338_ = l_Int64_ofIntLE___redArg(v_i_1336_);
stack->m_num = v_res_1338_;
}
LEAN_EXPORT lean_object* l_Int64_ofIntLE___redArg___boxed(lean_object* v_i_1339_){
_start:
{
uint64_t v_res_1340_; lean_object* v_r_1341_; 
v_res_1340_ = l_Int64_ofIntLE___redArg(v_i_1339_);
lean_dec(v_i_1339_);
v_r_1341_ = lean_box_uint64(v_res_1340_);
return v_r_1341_;
}
}
uint64_t l_Int64_ofIntLE(lean_object* v_i_1342_, lean_object* v___hl_1343_, lean_object* v___hr_1344_){
_start:
{
uint64_t v___x_1345_; 
v___x_1345_ = lean_int64_of_int(v_i_1342_);
return v___x_1345_;
}
}
LEAN_EXPORT void l_Int64_ofIntLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1342_ = stack[0].m_obj;
uint64_t v_res_1346_;
v_res_1346_ = l_Int64_ofIntLE(v_i_1342_, lean_box(0), lean_box(0));
stack->m_num = v_res_1346_;
}
LEAN_EXPORT lean_object* l_Int64_ofIntLE___boxed(lean_object* v_i_1347_, lean_object* v___hl_1348_, lean_object* v___hr_1349_){
_start:
{
uint64_t v_res_1350_; lean_object* v_r_1351_; 
v_res_1350_ = l_Int64_ofIntLE(v_i_1347_, v___hl_1348_, v___hr_1349_);
lean_dec(v_i_1347_);
v_r_1351_ = lean_box_uint64(v_res_1350_);
return v_r_1351_;
}
}
static lean_object* _init_l_Int64_ofIntClamp___closed__0(void){
_start:
{
uint64_t v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
v___x_1353_ = lean_int64_to_int_sint(v___x_1352_);
return v___x_1353_;
}
}
static lean_object* _init_l_Int64_ofIntClamp___closed__1(void){
_start:
{
uint64_t v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_uint64_once(&l_Int64_maxValue___closed__0, &l_Int64_maxValue___closed__0_once, _init_l_Int64_maxValue___closed__0);
v___x_1355_ = lean_int64_to_int_sint(v___x_1354_);
return v___x_1355_;
}
}
uint64_t l_Int64_ofIntClamp(lean_object* v_i_1356_){
_start:
{
uint64_t v___x_1357_; lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1357_ = lean_uint64_once(&l_Int64_minValue___closed__2, &l_Int64_minValue___closed__2_once, _init_l_Int64_minValue___closed__2);
v___x_1358_ = lean_obj_once(&l_Int64_ofIntClamp___closed__0, &l_Int64_ofIntClamp___closed__0_once, _init_l_Int64_ofIntClamp___closed__0);
v___x_1359_ = lean_int_dec_le(v___x_1358_, v_i_1356_);
if (v___x_1359_ == 0)
{
return v___x_1357_;
}
else
{
uint64_t v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v___x_1360_ = lean_uint64_once(&l_Int64_maxValue___closed__0, &l_Int64_maxValue___closed__0_once, _init_l_Int64_maxValue___closed__0);
v___x_1361_ = lean_obj_once(&l_Int64_ofIntClamp___closed__1, &l_Int64_ofIntClamp___closed__1_once, _init_l_Int64_ofIntClamp___closed__1);
v___x_1362_ = lean_int_dec_le(v_i_1356_, v___x_1361_);
if (v___x_1362_ == 0)
{
return v___x_1360_;
}
else
{
uint64_t v___x_1363_; 
v___x_1363_ = lean_int64_of_int(v_i_1356_);
return v___x_1363_;
}
}
}
}
LEAN_EXPORT void l_Int64_ofIntClamp_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1356_ = stack[0].m_obj;
uint64_t v_res_1364_;
v_res_1364_ = l_Int64_ofIntClamp(v_i_1356_);
stack->m_num = v_res_1364_;
}
LEAN_EXPORT lean_object* l_Int64_ofIntClamp___boxed(lean_object* v_i_1365_){
_start:
{
uint64_t v_res_1366_; lean_object* v_r_1367_; 
v_res_1366_ = l_Int64_ofIntClamp(v_i_1365_);
lean_dec(v_i_1365_);
v_r_1367_ = lean_box_uint64(v_res_1366_);
return v_r_1367_;
}
}
uint64_t l_Int64_ofIntTruncate(lean_object* v_i_1368_){
_start:
{
uint64_t v___x_1369_; 
v___x_1369_ = l_Int64_ofIntClamp(v_i_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT void l_Int64_ofIntTruncate_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1368_ = stack[0].m_obj;
uint64_t v_res_1370_;
v_res_1370_ = l_Int64_ofIntTruncate(v_i_1368_);
stack->m_num = v_res_1370_;
}
LEAN_EXPORT lean_object* l_Int64_ofIntTruncate___boxed(lean_object* v_i_1371_){
_start:
{
uint64_t v_res_1372_; lean_object* v_r_1373_; 
v_res_1372_ = l_Int64_ofIntTruncate(v_i_1371_);
lean_dec(v_i_1371_);
v_r_1373_ = lean_box_uint64(v_res_1372_);
return v_r_1373_;
}
}
LEAN_EXPORT void l_Int64_add_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1374_ = stack[0].m_num;
uint64_t v_b_1375_ = stack[1].m_num;
uint64_t v_res_1376_;
v_res_1376_ = lean_int64_add(v_a_1374_, v_b_1375_);
stack->m_num = v_res_1376_;
}
LEAN_EXPORT lean_object* l_Int64_add___boxed(lean_object* v_a_1377_, lean_object* v_b_1378_){
_start:
{
uint64_t v_a_boxed_1379_; uint64_t v_b_boxed_1380_; uint64_t v_res_1381_; lean_object* v_r_1382_; 
v_a_boxed_1379_ = lean_unbox_uint64(v_a_1377_);
lean_dec_ref(v_a_1377_);
v_b_boxed_1380_ = lean_unbox_uint64(v_b_1378_);
lean_dec_ref(v_b_1378_);
v_res_1381_ = lean_int64_add(v_a_boxed_1379_, v_b_boxed_1380_);
v_r_1382_ = lean_box_uint64(v_res_1381_);
return v_r_1382_;
}
}
LEAN_EXPORT void l_Int64_sub_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1383_ = stack[0].m_num;
uint64_t v_b_1384_ = stack[1].m_num;
uint64_t v_res_1385_;
v_res_1385_ = lean_int64_sub(v_a_1383_, v_b_1384_);
stack->m_num = v_res_1385_;
}
LEAN_EXPORT lean_object* l_Int64_sub___boxed(lean_object* v_a_1386_, lean_object* v_b_1387_){
_start:
{
uint64_t v_a_boxed_1388_; uint64_t v_b_boxed_1389_; uint64_t v_res_1390_; lean_object* v_r_1391_; 
v_a_boxed_1388_ = lean_unbox_uint64(v_a_1386_);
lean_dec_ref(v_a_1386_);
v_b_boxed_1389_ = lean_unbox_uint64(v_b_1387_);
lean_dec_ref(v_b_1387_);
v_res_1390_ = lean_int64_sub(v_a_boxed_1388_, v_b_boxed_1389_);
v_r_1391_ = lean_box_uint64(v_res_1390_);
return v_r_1391_;
}
}
LEAN_EXPORT void l_Int64_mul_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1392_ = stack[0].m_num;
uint64_t v_b_1393_ = stack[1].m_num;
uint64_t v_res_1394_;
v_res_1394_ = lean_int64_mul(v_a_1392_, v_b_1393_);
stack->m_num = v_res_1394_;
}
LEAN_EXPORT lean_object* l_Int64_mul___boxed(lean_object* v_a_1395_, lean_object* v_b_1396_){
_start:
{
uint64_t v_a_boxed_1397_; uint64_t v_b_boxed_1398_; uint64_t v_res_1399_; lean_object* v_r_1400_; 
v_a_boxed_1397_ = lean_unbox_uint64(v_a_1395_);
lean_dec_ref(v_a_1395_);
v_b_boxed_1398_ = lean_unbox_uint64(v_b_1396_);
lean_dec_ref(v_b_1396_);
v_res_1399_ = lean_int64_mul(v_a_boxed_1397_, v_b_boxed_1398_);
v_r_1400_ = lean_box_uint64(v_res_1399_);
return v_r_1400_;
}
}
LEAN_EXPORT void l_Int64_div_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1401_ = stack[0].m_num;
uint64_t v_b_1402_ = stack[1].m_num;
uint64_t v_res_1403_;
v_res_1403_ = lean_int64_div(v_a_1401_, v_b_1402_);
stack->m_num = v_res_1403_;
}
LEAN_EXPORT lean_object* l_Int64_div___boxed(lean_object* v_a_1404_, lean_object* v_b_1405_){
_start:
{
uint64_t v_a_boxed_1406_; uint64_t v_b_boxed_1407_; uint64_t v_res_1408_; lean_object* v_r_1409_; 
v_a_boxed_1406_ = lean_unbox_uint64(v_a_1404_);
lean_dec_ref(v_a_1404_);
v_b_boxed_1407_ = lean_unbox_uint64(v_b_1405_);
lean_dec_ref(v_b_1405_);
v_res_1408_ = lean_int64_div(v_a_boxed_1406_, v_b_boxed_1407_);
v_r_1409_ = lean_box_uint64(v_res_1408_);
return v_r_1409_;
}
}
static uint64_t _init_l_Int64_pow___closed__0(void){
_start:
{
lean_object* v___x_1410_; uint64_t v___x_1411_; 
v___x_1410_ = lean_unsigned_to_nat(1u);
v___x_1411_ = lean_int64_of_nat(v___x_1410_);
return v___x_1411_;
}
}
uint64_t l_Int64_pow(uint64_t v_x_1412_, lean_object* v_n_1413_){
_start:
{
lean_object* v_zero_1414_; uint8_t v_isZero_1415_; 
v_zero_1414_ = lean_unsigned_to_nat(0u);
v_isZero_1415_ = lean_nat_dec_eq(v_n_1413_, v_zero_1414_);
if (v_isZero_1415_ == 1)
{
uint64_t v___x_1416_; 
v___x_1416_ = lean_uint64_once(&l_Int64_pow___closed__0, &l_Int64_pow___closed__0_once, _init_l_Int64_pow___closed__0);
return v___x_1416_;
}
else
{
lean_object* v_one_1417_; lean_object* v_n_1418_; uint64_t v___x_1419_; uint64_t v___x_1420_; 
v_one_1417_ = lean_unsigned_to_nat(1u);
v_n_1418_ = lean_nat_sub(v_n_1413_, v_one_1417_);
v___x_1419_ = l_Int64_pow(v_x_1412_, v_n_1418_);
lean_dec(v_n_1418_);
v___x_1420_ = lean_int64_mul(v___x_1419_, v_x_1412_);
return v___x_1420_;
}
}
}
LEAN_EXPORT void l_Int64_pow_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_1412_ = stack[0].m_num;
lean_object* v_n_1413_ = stack[1].m_obj;
uint64_t v_res_1421_;
v_res_1421_ = l_Int64_pow(v_x_1412_, v_n_1413_);
stack->m_num = v_res_1421_;
}
LEAN_EXPORT lean_object* l_Int64_pow___boxed(lean_object* v_x_1422_, lean_object* v_n_1423_){
_start:
{
uint64_t v_x_boxed_1424_; uint64_t v_res_1425_; lean_object* v_r_1426_; 
v_x_boxed_1424_ = lean_unbox_uint64(v_x_1422_);
lean_dec_ref(v_x_1422_);
v_res_1425_ = l_Int64_pow(v_x_boxed_1424_, v_n_1423_);
lean_dec(v_n_1423_);
v_r_1426_ = lean_box_uint64(v_res_1425_);
return v_r_1426_;
}
}
LEAN_EXPORT void l_Int64_mod_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1427_ = stack[0].m_num;
uint64_t v_b_1428_ = stack[1].m_num;
uint64_t v_res_1429_;
v_res_1429_ = lean_int64_mod(v_a_1427_, v_b_1428_);
stack->m_num = v_res_1429_;
}
LEAN_EXPORT lean_object* l_Int64_mod___boxed(lean_object* v_a_1430_, lean_object* v_b_1431_){
_start:
{
uint64_t v_a_boxed_1432_; uint64_t v_b_boxed_1433_; uint64_t v_res_1434_; lean_object* v_r_1435_; 
v_a_boxed_1432_ = lean_unbox_uint64(v_a_1430_);
lean_dec_ref(v_a_1430_);
v_b_boxed_1433_ = lean_unbox_uint64(v_b_1431_);
lean_dec_ref(v_b_1431_);
v_res_1434_ = lean_int64_mod(v_a_boxed_1432_, v_b_boxed_1433_);
v_r_1435_ = lean_box_uint64(v_res_1434_);
return v_r_1435_;
}
}
LEAN_EXPORT void l_Int64_land_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1436_ = stack[0].m_num;
uint64_t v_b_1437_ = stack[1].m_num;
uint64_t v_res_1438_;
v_res_1438_ = lean_int64_land(v_a_1436_, v_b_1437_);
stack->m_num = v_res_1438_;
}
LEAN_EXPORT lean_object* l_Int64_land___boxed(lean_object* v_a_1439_, lean_object* v_b_1440_){
_start:
{
uint64_t v_a_boxed_1441_; uint64_t v_b_boxed_1442_; uint64_t v_res_1443_; lean_object* v_r_1444_; 
v_a_boxed_1441_ = lean_unbox_uint64(v_a_1439_);
lean_dec_ref(v_a_1439_);
v_b_boxed_1442_ = lean_unbox_uint64(v_b_1440_);
lean_dec_ref(v_b_1440_);
v_res_1443_ = lean_int64_land(v_a_boxed_1441_, v_b_boxed_1442_);
v_r_1444_ = lean_box_uint64(v_res_1443_);
return v_r_1444_;
}
}
LEAN_EXPORT void l_Int64_lor_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1445_ = stack[0].m_num;
uint64_t v_b_1446_ = stack[1].m_num;
uint64_t v_res_1447_;
v_res_1447_ = lean_int64_lor(v_a_1445_, v_b_1446_);
stack->m_num = v_res_1447_;
}
LEAN_EXPORT lean_object* l_Int64_lor___boxed(lean_object* v_a_1448_, lean_object* v_b_1449_){
_start:
{
uint64_t v_a_boxed_1450_; uint64_t v_b_boxed_1451_; uint64_t v_res_1452_; lean_object* v_r_1453_; 
v_a_boxed_1450_ = lean_unbox_uint64(v_a_1448_);
lean_dec_ref(v_a_1448_);
v_b_boxed_1451_ = lean_unbox_uint64(v_b_1449_);
lean_dec_ref(v_b_1449_);
v_res_1452_ = lean_int64_lor(v_a_boxed_1450_, v_b_boxed_1451_);
v_r_1453_ = lean_box_uint64(v_res_1452_);
return v_r_1453_;
}
}
LEAN_EXPORT void l_Int64_xor_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1454_ = stack[0].m_num;
uint64_t v_b_1455_ = stack[1].m_num;
uint64_t v_res_1456_;
v_res_1456_ = lean_int64_xor(v_a_1454_, v_b_1455_);
stack->m_num = v_res_1456_;
}
LEAN_EXPORT lean_object* l_Int64_xor___boxed(lean_object* v_a_1457_, lean_object* v_b_1458_){
_start:
{
uint64_t v_a_boxed_1459_; uint64_t v_b_boxed_1460_; uint64_t v_res_1461_; lean_object* v_r_1462_; 
v_a_boxed_1459_ = lean_unbox_uint64(v_a_1457_);
lean_dec_ref(v_a_1457_);
v_b_boxed_1460_ = lean_unbox_uint64(v_b_1458_);
lean_dec_ref(v_b_1458_);
v_res_1461_ = lean_int64_xor(v_a_boxed_1459_, v_b_boxed_1460_);
v_r_1462_ = lean_box_uint64(v_res_1461_);
return v_r_1462_;
}
}
LEAN_EXPORT void l_Int64_shiftLeft_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1463_ = stack[0].m_num;
uint64_t v_b_1464_ = stack[1].m_num;
uint64_t v_res_1465_;
v_res_1465_ = lean_int64_shift_left(v_a_1463_, v_b_1464_);
stack->m_num = v_res_1465_;
}
LEAN_EXPORT lean_object* l_Int64_shiftLeft___boxed(lean_object* v_a_1466_, lean_object* v_b_1467_){
_start:
{
uint64_t v_a_boxed_1468_; uint64_t v_b_boxed_1469_; uint64_t v_res_1470_; lean_object* v_r_1471_; 
v_a_boxed_1468_ = lean_unbox_uint64(v_a_1466_);
lean_dec_ref(v_a_1466_);
v_b_boxed_1469_ = lean_unbox_uint64(v_b_1467_);
lean_dec_ref(v_b_1467_);
v_res_1470_ = lean_int64_shift_left(v_a_boxed_1468_, v_b_boxed_1469_);
v_r_1471_ = lean_box_uint64(v_res_1470_);
return v_r_1471_;
}
}
LEAN_EXPORT void l_Int64_shiftRight_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1472_ = stack[0].m_num;
uint64_t v_b_1473_ = stack[1].m_num;
uint64_t v_res_1474_;
v_res_1474_ = lean_int64_shift_right(v_a_1472_, v_b_1473_);
stack->m_num = v_res_1474_;
}
LEAN_EXPORT lean_object* l_Int64_shiftRight___boxed(lean_object* v_a_1475_, lean_object* v_b_1476_){
_start:
{
uint64_t v_a_boxed_1477_; uint64_t v_b_boxed_1478_; uint64_t v_res_1479_; lean_object* v_r_1480_; 
v_a_boxed_1477_ = lean_unbox_uint64(v_a_1475_);
lean_dec_ref(v_a_1475_);
v_b_boxed_1478_ = lean_unbox_uint64(v_b_1476_);
lean_dec_ref(v_b_1476_);
v_res_1479_ = lean_int64_shift_right(v_a_boxed_1477_, v_b_boxed_1478_);
v_r_1480_ = lean_box_uint64(v_res_1479_);
return v_r_1480_;
}
}
LEAN_EXPORT void l_Int64_complement_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1481_ = stack[0].m_num;
uint64_t v_res_1482_;
v_res_1482_ = lean_int64_complement(v_a_1481_);
stack->m_num = v_res_1482_;
}
LEAN_EXPORT lean_object* l_Int64_complement___boxed(lean_object* v_a_1483_){
_start:
{
uint64_t v_a_boxed_1484_; uint64_t v_res_1485_; lean_object* v_r_1486_; 
v_a_boxed_1484_ = lean_unbox_uint64(v_a_1483_);
lean_dec_ref(v_a_1483_);
v_res_1485_ = lean_int64_complement(v_a_boxed_1484_);
v_r_1486_ = lean_box_uint64(v_res_1485_);
return v_r_1486_;
}
}
LEAN_EXPORT void l_Int64_abs_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1487_ = stack[0].m_num;
uint64_t v_res_1488_;
v_res_1488_ = lean_int64_abs(v_a_1487_);
stack->m_num = v_res_1488_;
}
LEAN_EXPORT lean_object* l_Int64_abs___boxed(lean_object* v_a_1489_){
_start:
{
uint64_t v_a_boxed_1490_; uint64_t v_res_1491_; lean_object* v_r_1492_; 
v_a_boxed_1490_ = lean_unbox_uint64(v_a_1489_);
lean_dec_ref(v_a_1489_);
v_res_1491_ = lean_int64_abs(v_a_boxed_1490_);
v_r_1492_ = lean_box_uint64(v_res_1491_);
return v_r_1492_;
}
}
LEAN_EXPORT void l_Int64_decEq_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1493_ = stack[0].m_num;
uint64_t v_b_1494_ = stack[1].m_num;
uint8_t v_res_1495_;
v_res_1495_ = lean_int64_dec_eq(v_a_1493_, v_b_1494_);
stack->m_num = v_res_1495_;
}
LEAN_EXPORT lean_object* l_Int64_decEq___boxed(lean_object* v_a_1496_, lean_object* v_b_1497_){
_start:
{
uint64_t v_a_boxed_1498_; uint64_t v_b_boxed_1499_; uint8_t v_res_1500_; lean_object* v_r_1501_; 
v_a_boxed_1498_ = lean_unbox_uint64(v_a_1496_);
lean_dec_ref(v_a_1496_);
v_b_boxed_1499_ = lean_unbox_uint64(v_b_1497_);
lean_dec_ref(v_b_1497_);
v_res_1500_ = lean_int64_dec_eq(v_a_boxed_1498_, v_b_boxed_1499_);
v_r_1501_ = lean_box(v_res_1500_);
return v_r_1501_;
}
}
static uint64_t _init_l_instInhabitedInt64___closed__0(void){
_start:
{
lean_object* v___x_1502_; uint64_t v___x_1503_; 
v___x_1502_ = lean_unsigned_to_nat(0u);
v___x_1503_ = lean_int64_of_nat(v___x_1502_);
return v___x_1503_;
}
}
static uint64_t _init_l_instInhabitedInt64(void){
_start:
{
uint64_t v___x_1504_; 
v___x_1504_ = lean_uint64_once(&l_instInhabitedInt64___closed__0, &l_instInhabitedInt64___closed__0_once, _init_l_instInhabitedInt64___closed__0);
return v___x_1504_;
}
}
static lean_object* _init_l_instLTInt64(void){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_box(0);
return v___x_1517_;
}
}
static lean_object* _init_l_instLEInt64(void){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_box(0);
return v___x_1518_;
}
}
uint8_t l_instDecidableEqInt64(uint64_t v_a_1531_, uint64_t v_b_1532_){
_start:
{
uint8_t v___x_1533_; 
v___x_1533_ = lean_int64_dec_eq(v_a_1531_, v_b_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT void l_instDecidableEqInt64_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1531_ = stack[0].m_num;
uint64_t v_b_1532_ = stack[1].m_num;
uint8_t v_res_1534_;
v_res_1534_ = l_instDecidableEqInt64(v_a_1531_, v_b_1532_);
stack->m_num = v_res_1534_;
}
LEAN_EXPORT lean_object* l_instDecidableEqInt64___boxed(lean_object* v_a_1535_, lean_object* v_b_1536_){
_start:
{
uint64_t v_a_boxed_1537_; uint64_t v_b_boxed_1538_; uint8_t v_res_1539_; lean_object* v_r_1540_; 
v_a_boxed_1537_ = lean_unbox_uint64(v_a_1535_);
lean_dec_ref(v_a_1535_);
v_b_boxed_1538_ = lean_unbox_uint64(v_b_1536_);
lean_dec_ref(v_b_1536_);
v_res_1539_ = l_instDecidableEqInt64(v_a_boxed_1537_, v_b_boxed_1538_);
v_r_1540_ = lean_box(v_res_1539_);
return v_r_1540_;
}
}
LEAN_EXPORT void l_Bool_toInt64_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_1541_ = stack[0].m_num;
uint64_t v_res_1542_;
v_res_1542_ = lean_bool_to_int64(v_b_1541_);
stack->m_num = v_res_1542_;
}
LEAN_EXPORT lean_object* l_Bool_toInt64___boxed(lean_object* v_b_1543_){
_start:
{
uint8_t v_b_boxed_1544_; uint64_t v_res_1545_; lean_object* v_r_1546_; 
v_b_boxed_1544_ = lean_unbox(v_b_1543_);
v_res_1545_ = lean_bool_to_int64(v_b_boxed_1544_);
v_r_1546_ = lean_box_uint64(v_res_1545_);
return v_r_1546_;
}
}
uint8_t l_Int64_decLt___aux__1(uint64_t v_a_1547_, uint64_t v_b_1548_){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1549_ = lean_unsigned_to_nat(64u);
v___x_1550_ = lean_uint64_to_nat(v_a_1547_);
v___x_1551_ = lean_uint64_to_nat(v_b_1548_);
v___x_1552_ = l_BitVec_slt(v___x_1549_, v___x_1550_, v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT void l_Int64_decLt___aux__1_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1547_ = stack[0].m_num;
uint64_t v_b_1548_ = stack[1].m_num;
uint8_t v_res_1553_;
v_res_1553_ = l_Int64_decLt___aux__1(v_a_1547_, v_b_1548_);
stack->m_num = v_res_1553_;
}
LEAN_EXPORT lean_object* l_Int64_decLt___aux__1___boxed(lean_object* v_a_1554_, lean_object* v_b_1555_){
_start:
{
uint64_t v_a_boxed_1556_; uint64_t v_b_boxed_1557_; uint8_t v_res_1558_; lean_object* v_r_1559_; 
v_a_boxed_1556_ = lean_unbox_uint64(v_a_1554_);
lean_dec_ref(v_a_1554_);
v_b_boxed_1557_ = lean_unbox_uint64(v_b_1555_);
lean_dec_ref(v_b_1555_);
v_res_1558_ = l_Int64_decLt___aux__1(v_a_boxed_1556_, v_b_boxed_1557_);
v_r_1559_ = lean_box(v_res_1558_);
return v_r_1559_;
}
}
LEAN_EXPORT void l_Int64_decLt_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1560_ = stack[0].m_num;
uint64_t v_b_1561_ = stack[1].m_num;
uint8_t v_res_1562_;
v_res_1562_ = lean_int64_dec_lt(v_a_1560_, v_b_1561_);
stack->m_num = v_res_1562_;
}
LEAN_EXPORT lean_object* l_Int64_decLt___boxed(lean_object* v_a_1563_, lean_object* v_b_1564_){
_start:
{
uint64_t v_a_boxed_1565_; uint64_t v_b_boxed_1566_; uint8_t v_res_1567_; lean_object* v_r_1568_; 
v_a_boxed_1565_ = lean_unbox_uint64(v_a_1563_);
lean_dec_ref(v_a_1563_);
v_b_boxed_1566_ = lean_unbox_uint64(v_b_1564_);
lean_dec_ref(v_b_1564_);
v_res_1567_ = lean_int64_dec_lt(v_a_boxed_1565_, v_b_boxed_1566_);
v_r_1568_ = lean_box(v_res_1567_);
return v_r_1568_;
}
}
uint8_t l_Int64_decLe___aux__1(uint64_t v_a_1569_, uint64_t v_b_1570_){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1571_ = lean_unsigned_to_nat(64u);
v___x_1572_ = lean_uint64_to_nat(v_a_1569_);
v___x_1573_ = lean_uint64_to_nat(v_b_1570_);
v___x_1574_ = l_BitVec_sle(v___x_1571_, v___x_1572_, v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT void l_Int64_decLe___aux__1_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1569_ = stack[0].m_num;
uint64_t v_b_1570_ = stack[1].m_num;
uint8_t v_res_1575_;
v_res_1575_ = l_Int64_decLe___aux__1(v_a_1569_, v_b_1570_);
stack->m_num = v_res_1575_;
}
LEAN_EXPORT lean_object* l_Int64_decLe___aux__1___boxed(lean_object* v_a_1576_, lean_object* v_b_1577_){
_start:
{
uint64_t v_a_boxed_1578_; uint64_t v_b_boxed_1579_; uint8_t v_res_1580_; lean_object* v_r_1581_; 
v_a_boxed_1578_ = lean_unbox_uint64(v_a_1576_);
lean_dec_ref(v_a_1576_);
v_b_boxed_1579_ = lean_unbox_uint64(v_b_1577_);
lean_dec_ref(v_b_1577_);
v_res_1580_ = l_Int64_decLe___aux__1(v_a_boxed_1578_, v_b_boxed_1579_);
v_r_1581_ = lean_box(v_res_1580_);
return v_r_1581_;
}
}
LEAN_EXPORT void l_Int64_decLe_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1582_ = stack[0].m_num;
uint64_t v_b_1583_ = stack[1].m_num;
uint8_t v_res_1584_;
v_res_1584_ = lean_int64_dec_le(v_a_1582_, v_b_1583_);
stack->m_num = v_res_1584_;
}
LEAN_EXPORT lean_object* l_Int64_decLe___boxed(lean_object* v_a_1585_, lean_object* v_b_1586_){
_start:
{
uint64_t v_a_boxed_1587_; uint64_t v_b_boxed_1588_; uint8_t v_res_1589_; lean_object* v_r_1590_; 
v_a_boxed_1587_ = lean_unbox_uint64(v_a_1585_);
lean_dec_ref(v_a_1585_);
v_b_boxed_1588_ = lean_unbox_uint64(v_b_1586_);
lean_dec_ref(v_b_1586_);
v_res_1589_ = lean_int64_dec_le(v_a_boxed_1587_, v_b_boxed_1588_);
v_r_1590_ = lean_box(v_res_1589_);
return v_r_1590_;
}
}
uint64_t l_instMaxInt64___lam__0(uint64_t v_x_1591_, uint64_t v_y_1592_){
_start:
{
uint8_t v___x_1593_; 
v___x_1593_ = lean_int64_dec_le(v_x_1591_, v_y_1592_);
if (v___x_1593_ == 0)
{
return v_x_1591_;
}
else
{
return v_y_1592_;
}
}
}
LEAN_EXPORT void l_instMaxInt64___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_1591_ = stack[0].m_num;
uint64_t v_y_1592_ = stack[1].m_num;
uint64_t v_res_1594_;
v_res_1594_ = l_instMaxInt64___lam__0(v_x_1591_, v_y_1592_);
stack->m_num = v_res_1594_;
}
LEAN_EXPORT lean_object* l_instMaxInt64___lam__0___boxed(lean_object* v_x_1595_, lean_object* v_y_1596_){
_start:
{
uint64_t v_x_boxed_1597_; uint64_t v_y_boxed_1598_; uint64_t v_res_1599_; lean_object* v_r_1600_; 
v_x_boxed_1597_ = lean_unbox_uint64(v_x_1595_);
lean_dec_ref(v_x_1595_);
v_y_boxed_1598_ = lean_unbox_uint64(v_y_1596_);
lean_dec_ref(v_y_1596_);
v_res_1599_ = l_instMaxInt64___lam__0(v_x_boxed_1597_, v_y_boxed_1598_);
v_r_1600_ = lean_box_uint64(v_res_1599_);
return v_r_1600_;
}
}
uint64_t l_instMinInt64___lam__0(uint64_t v_x_1603_, uint64_t v_y_1604_){
_start:
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_int64_dec_le(v_x_1603_, v_y_1604_);
if (v___x_1605_ == 0)
{
return v_y_1604_;
}
else
{
return v_x_1603_;
}
}
}
LEAN_EXPORT void l_instMinInt64___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_1603_ = stack[0].m_num;
uint64_t v_y_1604_ = stack[1].m_num;
uint64_t v_res_1606_;
v_res_1606_ = l_instMinInt64___lam__0(v_x_1603_, v_y_1604_);
stack->m_num = v_res_1606_;
}
LEAN_EXPORT lean_object* l_instMinInt64___lam__0___boxed(lean_object* v_x_1607_, lean_object* v_y_1608_){
_start:
{
uint64_t v_x_boxed_1609_; uint64_t v_y_boxed_1610_; uint64_t v_res_1611_; lean_object* v_r_1612_; 
v_x_boxed_1609_ = lean_unbox_uint64(v_x_1607_);
lean_dec_ref(v_x_1607_);
v_y_boxed_1610_ = lean_unbox_uint64(v_y_1608_);
lean_dec_ref(v_y_1608_);
v_res_1611_ = l_instMinInt64___lam__0(v_x_boxed_1609_, v_y_boxed_1610_);
v_r_1612_ = lean_box_uint64(v_res_1611_);
return v_r_1612_;
}
}
static lean_object* _init_l_ISize_size___closed__0(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = l_System_Platform_numBits;
v___x_1616_ = lean_unsigned_to_nat(2u);
v___x_1617_ = lean_nat_pow(v___x_1616_, v___x_1615_);
return v___x_1617_;
}
}
static lean_object* _init_l_ISize_size(void){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_obj_once(&l_ISize_size___closed__0, &l_ISize_size___closed__0_once, _init_l_ISize_size___closed__0);
return v___x_1618_;
}
}
lean_object* l_ISize_toBitVec(size_t v_x_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_usize_to_nat(v_x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT void l_ISize_toBitVec_0interp(lean_interpreter_value* stack)
{
size_t v_x_1619_ = stack[0].m_num;
lean_object* v_res_1621_;
v_res_1621_ = l_ISize_toBitVec(v_x_1619_);
stack->m_obj
 = v_res_1621_;
}
LEAN_EXPORT lean_object* l_ISize_toBitVec___boxed(lean_object* v_x_1622_){
_start:
{
size_t v_x_boxed_1623_; lean_object* v_res_1624_; 
v_x_boxed_1623_ = lean_unbox_usize(v_x_1622_);
lean_dec(v_x_1622_);
v_res_1624_ = l_ISize_toBitVec(v_x_boxed_1623_);
return v_res_1624_;
}
}
lean_object* l_ISize_toBitVec32___redArg(size_t v_a_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_usize_to_nat(v_a_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT void l_ISize_toBitVec32___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_a_1625_ = stack[0].m_num;
lean_object* v_res_1627_;
v_res_1627_ = l_ISize_toBitVec32___redArg(v_a_1625_);
stack->m_obj
 = v_res_1627_;
}
LEAN_EXPORT lean_object* l_ISize_toBitVec32___redArg___boxed(lean_object* v_a_1628_){
_start:
{
size_t v_a_boxed_1629_; lean_object* v_res_1630_; 
v_a_boxed_1629_ = lean_unbox_usize(v_a_1628_);
lean_dec(v_a_1628_);
v_res_1630_ = l_ISize_toBitVec32___redArg(v_a_boxed_1629_);
return v_res_1630_;
}
}
lean_object* l_ISize_toBitVec32(size_t v_a_1631_, lean_object* v_h_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = lean_usize_to_nat(v_a_1631_);
return v___x_1633_;
}
}
LEAN_EXPORT void l_ISize_toBitVec32_0interp(lean_interpreter_value* stack)
{
size_t v_a_1631_ = stack[0].m_num;
lean_object* v_res_1634_;
v_res_1634_ = l_ISize_toBitVec32(v_a_1631_, lean_box(0));
stack->m_obj
 = v_res_1634_;
}
LEAN_EXPORT lean_object* l_ISize_toBitVec32___boxed(lean_object* v_a_1635_, lean_object* v_h_1636_){
_start:
{
size_t v_a_boxed_1637_; lean_object* v_res_1638_; 
v_a_boxed_1637_ = lean_unbox_usize(v_a_1635_);
lean_dec(v_a_1635_);
v_res_1638_ = l_ISize_toBitVec32(v_a_boxed_1637_, v_h_1636_);
return v_res_1638_;
}
}
lean_object* l_ISize_toBitVec64___redArg(size_t v_a_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_usize_to_nat(v_a_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT void l_ISize_toBitVec64___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_a_1639_ = stack[0].m_num;
lean_object* v_res_1641_;
v_res_1641_ = l_ISize_toBitVec64___redArg(v_a_1639_);
stack->m_obj
 = v_res_1641_;
}
LEAN_EXPORT lean_object* l_ISize_toBitVec64___redArg___boxed(lean_object* v_a_1642_){
_start:
{
size_t v_a_boxed_1643_; lean_object* v_res_1644_; 
v_a_boxed_1643_ = lean_unbox_usize(v_a_1642_);
lean_dec(v_a_1642_);
v_res_1644_ = l_ISize_toBitVec64___redArg(v_a_boxed_1643_);
return v_res_1644_;
}
}
lean_object* l_ISize_toBitVec64(size_t v_a_1645_, lean_object* v_h_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_usize_to_nat(v_a_1645_);
return v___x_1647_;
}
}
LEAN_EXPORT void l_ISize_toBitVec64_0interp(lean_interpreter_value* stack)
{
size_t v_a_1645_ = stack[0].m_num;
lean_object* v_res_1648_;
v_res_1648_ = l_ISize_toBitVec64(v_a_1645_, lean_box(0));
stack->m_obj
 = v_res_1648_;
}
LEAN_EXPORT lean_object* l_ISize_toBitVec64___boxed(lean_object* v_a_1649_, lean_object* v_h_1650_){
_start:
{
size_t v_a_boxed_1651_; lean_object* v_res_1652_; 
v_a_boxed_1651_ = lean_unbox_usize(v_a_1649_);
lean_dec(v_a_1649_);
v_res_1652_ = l_ISize_toBitVec64(v_a_boxed_1651_, v_h_1650_);
return v_res_1652_;
}
}
size_t l_USize_toISize(size_t v_i_1653_){
_start:
{
return v_i_1653_;
}
}
LEAN_EXPORT void l_USize_toISize_0interp(lean_interpreter_value* stack)
{
size_t v_i_1653_ = stack[0].m_num;
size_t v_res_1654_;
v_res_1654_ = l_USize_toISize(v_i_1653_);
stack->m_num = v_res_1654_;
}
LEAN_EXPORT lean_object* l_USize_toISize___boxed(lean_object* v_i_1655_){
_start:
{
size_t v_i_boxed_1656_; size_t v_res_1657_; lean_object* v_r_1658_; 
v_i_boxed_1656_ = lean_unbox_usize(v_i_1655_);
lean_dec(v_i_1655_);
v_res_1657_ = l_USize_toISize(v_i_boxed_1656_);
v_r_1658_ = lean_box_usize(v_res_1657_);
return v_r_1658_;
}
}
LEAN_EXPORT void l_ISize_ofInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1659_ = stack[0].m_obj;
size_t v_res_1660_;
v_res_1660_ = lean_isize_of_int(v_i_1659_);
stack->m_num = v_res_1660_;
}
LEAN_EXPORT lean_object* l_ISize_ofInt___boxed(lean_object* v_i_1661_){
_start:
{
size_t v_res_1662_; lean_object* v_r_1663_; 
v_res_1662_ = lean_isize_of_int(v_i_1661_);
lean_dec(v_i_1661_);
v_r_1663_ = lean_box_usize(v_res_1662_);
return v_r_1663_;
}
}
LEAN_EXPORT void l_ISize_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1664_ = stack[0].m_obj;
size_t v_res_1665_;
v_res_1665_ = lean_isize_of_nat(v_n_1664_);
stack->m_num = v_res_1665_;
}
LEAN_EXPORT lean_object* l_ISize_ofNat___boxed(lean_object* v_n_1666_){
_start:
{
size_t v_res_1667_; lean_object* v_r_1668_; 
v_res_1667_ = lean_isize_of_nat(v_n_1666_);
lean_dec(v_n_1666_);
v_r_1668_ = lean_box_usize(v_res_1667_);
return v_r_1668_;
}
}
size_t l_Int_toISize(lean_object* v_i_1669_){
_start:
{
size_t v___x_1670_; 
v___x_1670_ = lean_isize_of_int(v_i_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT void l_Int_toISize_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1669_ = stack[0].m_obj;
size_t v_res_1671_;
v_res_1671_ = l_Int_toISize(v_i_1669_);
stack->m_num = v_res_1671_;
}
LEAN_EXPORT lean_object* l_Int_toISize___boxed(lean_object* v_i_1672_){
_start:
{
size_t v_res_1673_; lean_object* v_r_1674_; 
v_res_1673_ = l_Int_toISize(v_i_1672_);
lean_dec(v_i_1672_);
v_r_1674_ = lean_box_usize(v_res_1673_);
return v_r_1674_;
}
}
size_t l_Nat_toISize(lean_object* v_n_1675_){
_start:
{
size_t v___x_1676_; 
v___x_1676_ = lean_isize_of_nat(v_n_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT void l_Nat_toISize_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1675_ = stack[0].m_obj;
size_t v_res_1677_;
v_res_1677_ = l_Nat_toISize(v_n_1675_);
stack->m_num = v_res_1677_;
}
LEAN_EXPORT lean_object* l_Nat_toISize___boxed(lean_object* v_n_1678_){
_start:
{
size_t v_res_1679_; lean_object* v_r_1680_; 
v_res_1679_ = l_Nat_toISize(v_n_1678_);
lean_dec(v_n_1678_);
v_r_1680_ = lean_box_usize(v_res_1679_);
return v_r_1680_;
}
}
LEAN_EXPORT void l_ISize_toInt_0interp(lean_interpreter_value* stack)
{
size_t v_i_1681_ = stack[0].m_num;
lean_object* v_res_1682_;
v_res_1682_ = lean_isize_to_int(v_i_1681_);
stack->m_obj
 = v_res_1682_;
}
LEAN_EXPORT lean_object* l_ISize_toInt___boxed(lean_object* v_i_1683_){
_start:
{
size_t v_i_boxed_1684_; lean_object* v_res_1685_; 
v_i_boxed_1684_ = lean_unbox_usize(v_i_1683_);
lean_dec(v_i_1683_);
v_res_1685_ = lean_isize_to_int(v_i_boxed_1684_);
return v_res_1685_;
}
}
lean_object* l_ISize_toNatClampNeg(size_t v_i_1686_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_isize_to_int(v_i_1686_);
v___x_1688_ = l_Int_toNat(v___x_1687_);
lean_dec(v___x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT void l_ISize_toNatClampNeg_0interp(lean_interpreter_value* stack)
{
size_t v_i_1686_ = stack[0].m_num;
lean_object* v_res_1689_;
v_res_1689_ = l_ISize_toNatClampNeg(v_i_1686_);
stack->m_obj
 = v_res_1689_;
}
LEAN_EXPORT lean_object* l_ISize_toNatClampNeg___boxed(lean_object* v_i_1690_){
_start:
{
size_t v_i_boxed_1691_; lean_object* v_res_1692_; 
v_i_boxed_1691_ = lean_unbox_usize(v_i_1690_);
lean_dec(v_i_1690_);
v_res_1692_ = l_ISize_toNatClampNeg(v_i_boxed_1691_);
return v_res_1692_;
}
}
size_t l_ISize_ofBitVec(lean_object* v_b_1693_){
_start:
{
size_t v___x_1694_; 
v___x_1694_ = lean_usize_of_nat_mk(v_b_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT void l_ISize_ofBitVec_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_1693_ = stack[0].m_obj;
size_t v_res_1695_;
v_res_1695_ = l_ISize_ofBitVec(v_b_1693_);
stack->m_num = v_res_1695_;
}
LEAN_EXPORT lean_object* l_ISize_ofBitVec___boxed(lean_object* v_b_1696_){
_start:
{
size_t v_res_1697_; lean_object* v_r_1698_; 
v_res_1697_ = l_ISize_ofBitVec(v_b_1696_);
v_r_1698_ = lean_box_usize(v_res_1697_);
return v_r_1698_;
}
}
LEAN_EXPORT void l_ISize_toInt8_0interp(lean_interpreter_value* stack)
{
size_t v_a_1699_ = stack[0].m_num;
uint8_t v_res_1700_;
v_res_1700_ = lean_isize_to_int8(v_a_1699_);
stack->m_num = v_res_1700_;
}
LEAN_EXPORT lean_object* l_ISize_toInt8___boxed(lean_object* v_a_1701_){
_start:
{
size_t v_a_boxed_1702_; uint8_t v_res_1703_; lean_object* v_r_1704_; 
v_a_boxed_1702_ = lean_unbox_usize(v_a_1701_);
lean_dec(v_a_1701_);
v_res_1703_ = lean_isize_to_int8(v_a_boxed_1702_);
v_r_1704_ = lean_box(v_res_1703_);
return v_r_1704_;
}
}
LEAN_EXPORT void l_ISize_toInt16_0interp(lean_interpreter_value* stack)
{
size_t v_a_1705_ = stack[0].m_num;
uint16_t v_res_1706_;
v_res_1706_ = lean_isize_to_int16(v_a_1705_);
stack->m_num = v_res_1706_;
}
LEAN_EXPORT lean_object* l_ISize_toInt16___boxed(lean_object* v_a_1707_){
_start:
{
size_t v_a_boxed_1708_; uint16_t v_res_1709_; lean_object* v_r_1710_; 
v_a_boxed_1708_ = lean_unbox_usize(v_a_1707_);
lean_dec(v_a_1707_);
v_res_1709_ = lean_isize_to_int16(v_a_boxed_1708_);
v_r_1710_ = lean_box(v_res_1709_);
return v_r_1710_;
}
}
LEAN_EXPORT void l_ISize_toInt32_0interp(lean_interpreter_value* stack)
{
size_t v_a_1711_ = stack[0].m_num;
uint32_t v_res_1712_;
v_res_1712_ = lean_isize_to_int32(v_a_1711_);
stack->m_num = v_res_1712_;
}
LEAN_EXPORT lean_object* l_ISize_toInt32___boxed(lean_object* v_a_1713_){
_start:
{
size_t v_a_boxed_1714_; uint32_t v_res_1715_; lean_object* v_r_1716_; 
v_a_boxed_1714_ = lean_unbox_usize(v_a_1713_);
lean_dec(v_a_1713_);
v_res_1715_ = lean_isize_to_int32(v_a_boxed_1714_);
v_r_1716_ = lean_box_uint32(v_res_1715_);
return v_r_1716_;
}
}
LEAN_EXPORT void l_ISize_toInt64_0interp(lean_interpreter_value* stack)
{
size_t v_a_1717_ = stack[0].m_num;
uint64_t v_res_1718_;
v_res_1718_ = lean_isize_to_int64(v_a_1717_);
stack->m_num = v_res_1718_;
}
LEAN_EXPORT lean_object* l_ISize_toInt64___boxed(lean_object* v_a_1719_){
_start:
{
size_t v_a_boxed_1720_; uint64_t v_res_1721_; lean_object* v_r_1722_; 
v_a_boxed_1720_ = lean_unbox_usize(v_a_1719_);
lean_dec(v_a_1719_);
v_res_1721_ = lean_isize_to_int64(v_a_boxed_1720_);
v_r_1722_ = lean_box_uint64(v_res_1721_);
return v_r_1722_;
}
}
LEAN_EXPORT void l_Int8_toISize_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_1723_ = stack[0].m_num;
size_t v_res_1724_;
v_res_1724_ = lean_int8_to_isize(v_a_1723_);
stack->m_num = v_res_1724_;
}
LEAN_EXPORT lean_object* l_Int8_toISize___boxed(lean_object* v_a_1725_){
_start:
{
uint8_t v_a_boxed_1726_; size_t v_res_1727_; lean_object* v_r_1728_; 
v_a_boxed_1726_ = lean_unbox(v_a_1725_);
v_res_1727_ = lean_int8_to_isize(v_a_boxed_1726_);
v_r_1728_ = lean_box_usize(v_res_1727_);
return v_r_1728_;
}
}
LEAN_EXPORT void l_Int16_toISize_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_1729_ = stack[0].m_num;
size_t v_res_1730_;
v_res_1730_ = lean_int16_to_isize(v_a_1729_);
stack->m_num = v_res_1730_;
}
LEAN_EXPORT lean_object* l_Int16_toISize___boxed(lean_object* v_a_1731_){
_start:
{
uint16_t v_a_boxed_1732_; size_t v_res_1733_; lean_object* v_r_1734_; 
v_a_boxed_1732_ = lean_unbox(v_a_1731_);
v_res_1733_ = lean_int16_to_isize(v_a_boxed_1732_);
v_r_1734_ = lean_box_usize(v_res_1733_);
return v_r_1734_;
}
}
LEAN_EXPORT void l_Int32_toISize_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1735_ = stack[0].m_num;
size_t v_res_1736_;
v_res_1736_ = lean_int32_to_isize(v_a_1735_);
stack->m_num = v_res_1736_;
}
LEAN_EXPORT lean_object* l_Int32_toISize___boxed(lean_object* v_a_1737_){
_start:
{
uint32_t v_a_boxed_1738_; size_t v_res_1739_; lean_object* v_r_1740_; 
v_a_boxed_1738_ = lean_unbox_uint32(v_a_1737_);
lean_dec(v_a_1737_);
v_res_1739_ = lean_int32_to_isize(v_a_boxed_1738_);
v_r_1740_ = lean_box_usize(v_res_1739_);
return v_r_1740_;
}
}
LEAN_EXPORT void l_Int64_toISize_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1741_ = stack[0].m_num;
size_t v_res_1742_;
v_res_1742_ = lean_int64_to_isize(v_a_1741_);
stack->m_num = v_res_1742_;
}
LEAN_EXPORT lean_object* l_Int64_toISize___boxed(lean_object* v_a_1743_){
_start:
{
uint64_t v_a_boxed_1744_; size_t v_res_1745_; lean_object* v_r_1746_; 
v_a_boxed_1744_ = lean_unbox_uint64(v_a_1743_);
lean_dec_ref(v_a_1743_);
v_res_1745_ = lean_int64_to_isize(v_a_boxed_1744_);
v_r_1746_ = lean_box_usize(v_res_1745_);
return v_r_1746_;
}
}
LEAN_EXPORT void l_ISize_neg_0interp(lean_interpreter_value* stack)
{
size_t v_i_1747_ = stack[0].m_num;
size_t v_res_1748_;
v_res_1748_ = lean_isize_neg(v_i_1747_);
stack->m_num = v_res_1748_;
}
LEAN_EXPORT lean_object* l_ISize_neg___boxed(lean_object* v_i_1749_){
_start:
{
size_t v_i_boxed_1750_; size_t v_res_1751_; lean_object* v_r_1752_; 
v_i_boxed_1750_ = lean_unbox_usize(v_i_1749_);
lean_dec(v_i_1749_);
v_res_1751_ = lean_isize_neg(v_i_boxed_1750_);
v_r_1752_ = lean_box_usize(v_res_1751_);
return v_r_1752_;
}
}
lean_object* l_instToStringISize___lam__0(size_t v_i_1753_){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_isize_to_int(v_i_1753_);
v___x_1755_ = l_Int_repr(v___x_1754_);
lean_dec(v___x_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT void l_instToStringISize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_1753_ = stack[0].m_num;
lean_object* v_res_1756_;
v_res_1756_ = l_instToStringISize___lam__0(v_i_1753_);
stack->m_obj
 = v_res_1756_;
}
LEAN_EXPORT lean_object* l_instToStringISize___lam__0___boxed(lean_object* v_i_1757_){
_start:
{
size_t v_i_boxed_1758_; lean_object* v_res_1759_; 
v_i_boxed_1758_ = lean_unbox_usize(v_i_1757_);
lean_dec(v_i_1757_);
v_res_1759_ = l_instToStringISize___lam__0(v_i_boxed_1758_);
return v_res_1759_;
}
}
lean_object* l_instReprISize___lam__0(size_t v_i_1762_, lean_object* v_prec_1763_){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1764_ = lean_isize_to_int(v_i_1762_);
v___x_1765_ = lean_obj_once(&l_instReprInt8___lam__0___closed__0, &l_instReprInt8___lam__0___closed__0_once, _init_l_instReprInt8___lam__0___closed__0);
v___x_1766_ = lean_int_dec_lt(v___x_1764_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = l_Int_repr(v___x_1764_);
lean_dec(v___x_1764_);
v___x_1768_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = l_Int_repr(v___x_1764_);
lean_dec(v___x_1764_);
v___x_1770_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1769_);
v___x_1771_ = l_Repr_addAppParen(v___x_1770_, v_prec_1763_);
return v___x_1771_;
}
}
}
LEAN_EXPORT void l_instReprISize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_1762_ = stack[0].m_num;
lean_object* v_prec_1763_ = stack[1].m_obj;
lean_object* v_res_1772_;
v_res_1772_ = l_instReprISize___lam__0(v_i_1762_, v_prec_1763_);
stack->m_obj
 = v_res_1772_;
}
LEAN_EXPORT lean_object* l_instReprISize___lam__0___boxed(lean_object* v_i_1773_, lean_object* v_prec_1774_){
_start:
{
size_t v_i_boxed_1775_; lean_object* v_res_1776_; 
v_i_boxed_1775_ = lean_unbox_usize(v_i_1773_);
lean_dec(v_i_1773_);
v_res_1776_ = l_instReprISize___lam__0(v_i_boxed_1775_, v_prec_1774_);
lean_dec(v_prec_1774_);
return v_res_1776_;
}
}
static lean_object* _init_l_instReprAtomISize(void){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = lean_box(0);
return v___x_1779_;
}
}
size_t l_ISize_instOfNat(lean_object* v_n_1782_){
_start:
{
size_t v___x_1783_; 
v___x_1783_ = lean_isize_of_nat(v_n_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT void l_ISize_instOfNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_1782_ = stack[0].m_obj;
size_t v_res_1784_;
v_res_1784_ = l_ISize_instOfNat(v_n_1782_);
stack->m_num = v_res_1784_;
}
LEAN_EXPORT lean_object* l_ISize_instOfNat___boxed(lean_object* v_n_1785_){
_start:
{
size_t v_res_1786_; lean_object* v_r_1787_; 
v_res_1786_ = l_ISize_instOfNat(v_n_1785_);
lean_dec(v_n_1785_);
v_r_1787_ = lean_box_usize(v_res_1786_);
return v_r_1787_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__0(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_unsigned_to_nat(2u);
v___x_1791_ = lean_nat_to_int(v___x_1790_);
return v___x_1791_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__1(void){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = l_System_Platform_numBits;
v___x_1794_ = lean_nat_sub(v___x_1793_, v___x_1792_);
return v___x_1794_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__2(void){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = lean_obj_once(&l_ISize_maxValue___closed__1, &l_ISize_maxValue___closed__1_once, _init_l_ISize_maxValue___closed__1);
v___x_1796_ = lean_obj_once(&l_ISize_maxValue___closed__0, &l_ISize_maxValue___closed__0_once, _init_l_ISize_maxValue___closed__0);
v___x_1797_ = l_Int_pow(v___x_1796_, v___x_1795_);
return v___x_1797_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__3(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = lean_nat_to_int(v___x_1798_);
return v___x_1799_;
}
}
static lean_object* _init_l_ISize_maxValue___closed__4(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = lean_obj_once(&l_ISize_maxValue___closed__3, &l_ISize_maxValue___closed__3_once, _init_l_ISize_maxValue___closed__3);
v___x_1801_ = lean_obj_once(&l_ISize_maxValue___closed__2, &l_ISize_maxValue___closed__2_once, _init_l_ISize_maxValue___closed__2);
v___x_1802_ = lean_int_sub(v___x_1801_, v___x_1800_);
return v___x_1802_;
}
}
static size_t _init_l_ISize_maxValue___closed__5(void){
_start:
{
lean_object* v___x_1803_; size_t v___x_1804_; 
v___x_1803_ = lean_obj_once(&l_ISize_maxValue___closed__4, &l_ISize_maxValue___closed__4_once, _init_l_ISize_maxValue___closed__4);
v___x_1804_ = lean_isize_of_int(v___x_1803_);
return v___x_1804_;
}
}
static size_t _init_l_ISize_maxValue(void){
_start:
{
size_t v___x_1805_; 
v___x_1805_ = lean_usize_once(&l_ISize_maxValue___closed__5, &l_ISize_maxValue___closed__5_once, _init_l_ISize_maxValue___closed__5);
return v___x_1805_;
}
}
static lean_object* _init_l_ISize_minValue___closed__0(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = lean_obj_once(&l_ISize_maxValue___closed__2, &l_ISize_maxValue___closed__2_once, _init_l_ISize_maxValue___closed__2);
v___x_1807_ = lean_int_neg(v___x_1806_);
return v___x_1807_;
}
}
static size_t _init_l_ISize_minValue___closed__1(void){
_start:
{
lean_object* v___x_1808_; size_t v___x_1809_; 
v___x_1808_ = lean_obj_once(&l_ISize_minValue___closed__0, &l_ISize_minValue___closed__0_once, _init_l_ISize_minValue___closed__0);
v___x_1809_ = lean_isize_of_int(v___x_1808_);
return v___x_1809_;
}
}
static size_t _init_l_ISize_minValue(void){
_start:
{
size_t v___x_1810_; 
v___x_1810_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
return v___x_1810_;
}
}
size_t l_ISize_ofIntLE___redArg(lean_object* v_i_1811_){
_start:
{
size_t v___x_1812_; 
v___x_1812_ = lean_isize_of_int(v_i_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT void l_ISize_ofIntLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1811_ = stack[0].m_obj;
size_t v_res_1813_;
v_res_1813_ = l_ISize_ofIntLE___redArg(v_i_1811_);
stack->m_num = v_res_1813_;
}
LEAN_EXPORT lean_object* l_ISize_ofIntLE___redArg___boxed(lean_object* v_i_1814_){
_start:
{
size_t v_res_1815_; lean_object* v_r_1816_; 
v_res_1815_ = l_ISize_ofIntLE___redArg(v_i_1814_);
lean_dec(v_i_1814_);
v_r_1816_ = lean_box_usize(v_res_1815_);
return v_r_1816_;
}
}
size_t l_ISize_ofIntLE(lean_object* v_i_1817_, lean_object* v___hl_1818_, lean_object* v___hr_1819_){
_start:
{
size_t v___x_1820_; 
v___x_1820_ = lean_isize_of_int(v_i_1817_);
return v___x_1820_;
}
}
LEAN_EXPORT void l_ISize_ofIntLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1817_ = stack[0].m_obj;
size_t v_res_1821_;
v_res_1821_ = l_ISize_ofIntLE(v_i_1817_, lean_box(0), lean_box(0));
stack->m_num = v_res_1821_;
}
LEAN_EXPORT lean_object* l_ISize_ofIntLE___boxed(lean_object* v_i_1822_, lean_object* v___hl_1823_, lean_object* v___hr_1824_){
_start:
{
size_t v_res_1825_; lean_object* v_r_1826_; 
v_res_1825_ = l_ISize_ofIntLE(v_i_1822_, v___hl_1823_, v___hr_1824_);
lean_dec(v_i_1822_);
v_r_1826_ = lean_box_usize(v_res_1825_);
return v_r_1826_;
}
}
static lean_object* _init_l_ISize_ofIntClamp___closed__0(void){
_start:
{
size_t v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
v___x_1828_ = lean_isize_to_int(v___x_1827_);
return v___x_1828_;
}
}
static lean_object* _init_l_ISize_ofIntClamp___closed__1(void){
_start:
{
size_t v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_usize_once(&l_ISize_maxValue___closed__5, &l_ISize_maxValue___closed__5_once, _init_l_ISize_maxValue___closed__5);
v___x_1830_ = lean_isize_to_int(v___x_1829_);
return v___x_1830_;
}
}
size_t l_ISize_ofIntClamp(lean_object* v_i_1831_){
_start:
{
size_t v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1832_ = lean_usize_once(&l_ISize_minValue___closed__1, &l_ISize_minValue___closed__1_once, _init_l_ISize_minValue___closed__1);
v___x_1833_ = lean_obj_once(&l_ISize_ofIntClamp___closed__0, &l_ISize_ofIntClamp___closed__0_once, _init_l_ISize_ofIntClamp___closed__0);
v___x_1834_ = lean_int_dec_le(v___x_1833_, v_i_1831_);
if (v___x_1834_ == 0)
{
return v___x_1832_;
}
else
{
size_t v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1835_ = lean_usize_once(&l_ISize_maxValue___closed__5, &l_ISize_maxValue___closed__5_once, _init_l_ISize_maxValue___closed__5);
v___x_1836_ = lean_obj_once(&l_ISize_ofIntClamp___closed__1, &l_ISize_ofIntClamp___closed__1_once, _init_l_ISize_ofIntClamp___closed__1);
v___x_1837_ = lean_int_dec_le(v_i_1831_, v___x_1836_);
if (v___x_1837_ == 0)
{
return v___x_1835_;
}
else
{
size_t v___x_1838_; 
v___x_1838_ = lean_isize_of_int(v_i_1831_);
return v___x_1838_;
}
}
}
}
LEAN_EXPORT void l_ISize_ofIntClamp_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1831_ = stack[0].m_obj;
size_t v_res_1839_;
v_res_1839_ = l_ISize_ofIntClamp(v_i_1831_);
stack->m_num = v_res_1839_;
}
LEAN_EXPORT lean_object* l_ISize_ofIntClamp___boxed(lean_object* v_i_1840_){
_start:
{
size_t v_res_1841_; lean_object* v_r_1842_; 
v_res_1841_ = l_ISize_ofIntClamp(v_i_1840_);
lean_dec(v_i_1840_);
v_r_1842_ = lean_box_usize(v_res_1841_);
return v_r_1842_;
}
}
size_t l_ISize_ofIntTruncate(lean_object* v_i_1843_){
_start:
{
size_t v___x_1844_; 
v___x_1844_ = l_ISize_ofIntClamp(v_i_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT void l_ISize_ofIntTruncate_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_1843_ = stack[0].m_obj;
size_t v_res_1845_;
v_res_1845_ = l_ISize_ofIntTruncate(v_i_1843_);
stack->m_num = v_res_1845_;
}
LEAN_EXPORT lean_object* l_ISize_ofIntTruncate___boxed(lean_object* v_i_1846_){
_start:
{
size_t v_res_1847_; lean_object* v_r_1848_; 
v_res_1847_ = l_ISize_ofIntTruncate(v_i_1846_);
lean_dec(v_i_1846_);
v_r_1848_ = lean_box_usize(v_res_1847_);
return v_r_1848_;
}
}
LEAN_EXPORT void l_ISize_add_0interp(lean_interpreter_value* stack)
{
size_t v_a_1849_ = stack[0].m_num;
size_t v_b_1850_ = stack[1].m_num;
size_t v_res_1851_;
v_res_1851_ = lean_isize_add(v_a_1849_, v_b_1850_);
stack->m_num = v_res_1851_;
}
LEAN_EXPORT lean_object* l_ISize_add___boxed(lean_object* v_a_1852_, lean_object* v_b_1853_){
_start:
{
size_t v_a_boxed_1854_; size_t v_b_boxed_1855_; size_t v_res_1856_; lean_object* v_r_1857_; 
v_a_boxed_1854_ = lean_unbox_usize(v_a_1852_);
lean_dec(v_a_1852_);
v_b_boxed_1855_ = lean_unbox_usize(v_b_1853_);
lean_dec(v_b_1853_);
v_res_1856_ = lean_isize_add(v_a_boxed_1854_, v_b_boxed_1855_);
v_r_1857_ = lean_box_usize(v_res_1856_);
return v_r_1857_;
}
}
LEAN_EXPORT void l_ISize_sub_0interp(lean_interpreter_value* stack)
{
size_t v_a_1858_ = stack[0].m_num;
size_t v_b_1859_ = stack[1].m_num;
size_t v_res_1860_;
v_res_1860_ = lean_isize_sub(v_a_1858_, v_b_1859_);
stack->m_num = v_res_1860_;
}
LEAN_EXPORT lean_object* l_ISize_sub___boxed(lean_object* v_a_1861_, lean_object* v_b_1862_){
_start:
{
size_t v_a_boxed_1863_; size_t v_b_boxed_1864_; size_t v_res_1865_; lean_object* v_r_1866_; 
v_a_boxed_1863_ = lean_unbox_usize(v_a_1861_);
lean_dec(v_a_1861_);
v_b_boxed_1864_ = lean_unbox_usize(v_b_1862_);
lean_dec(v_b_1862_);
v_res_1865_ = lean_isize_sub(v_a_boxed_1863_, v_b_boxed_1864_);
v_r_1866_ = lean_box_usize(v_res_1865_);
return v_r_1866_;
}
}
LEAN_EXPORT void l_ISize_mul_0interp(lean_interpreter_value* stack)
{
size_t v_a_1867_ = stack[0].m_num;
size_t v_b_1868_ = stack[1].m_num;
size_t v_res_1869_;
v_res_1869_ = lean_isize_mul(v_a_1867_, v_b_1868_);
stack->m_num = v_res_1869_;
}
LEAN_EXPORT lean_object* l_ISize_mul___boxed(lean_object* v_a_1870_, lean_object* v_b_1871_){
_start:
{
size_t v_a_boxed_1872_; size_t v_b_boxed_1873_; size_t v_res_1874_; lean_object* v_r_1875_; 
v_a_boxed_1872_ = lean_unbox_usize(v_a_1870_);
lean_dec(v_a_1870_);
v_b_boxed_1873_ = lean_unbox_usize(v_b_1871_);
lean_dec(v_b_1871_);
v_res_1874_ = lean_isize_mul(v_a_boxed_1872_, v_b_boxed_1873_);
v_r_1875_ = lean_box_usize(v_res_1874_);
return v_r_1875_;
}
}
LEAN_EXPORT void l_ISize_div_0interp(lean_interpreter_value* stack)
{
size_t v_a_1876_ = stack[0].m_num;
size_t v_b_1877_ = stack[1].m_num;
size_t v_res_1878_;
v_res_1878_ = lean_isize_div(v_a_1876_, v_b_1877_);
stack->m_num = v_res_1878_;
}
LEAN_EXPORT lean_object* l_ISize_div___boxed(lean_object* v_a_1879_, lean_object* v_b_1880_){
_start:
{
size_t v_a_boxed_1881_; size_t v_b_boxed_1882_; size_t v_res_1883_; lean_object* v_r_1884_; 
v_a_boxed_1881_ = lean_unbox_usize(v_a_1879_);
lean_dec(v_a_1879_);
v_b_boxed_1882_ = lean_unbox_usize(v_b_1880_);
lean_dec(v_b_1880_);
v_res_1883_ = lean_isize_div(v_a_boxed_1881_, v_b_boxed_1882_);
v_r_1884_ = lean_box_usize(v_res_1883_);
return v_r_1884_;
}
}
static size_t _init_l_ISize_pow___closed__0(void){
_start:
{
lean_object* v___x_1885_; size_t v___x_1886_; 
v___x_1885_ = lean_unsigned_to_nat(1u);
v___x_1886_ = lean_isize_of_nat(v___x_1885_);
return v___x_1886_;
}
}
size_t l_ISize_pow(size_t v_x_1887_, lean_object* v_n_1888_){
_start:
{
lean_object* v_zero_1889_; uint8_t v_isZero_1890_; 
v_zero_1889_ = lean_unsigned_to_nat(0u);
v_isZero_1890_ = lean_nat_dec_eq(v_n_1888_, v_zero_1889_);
if (v_isZero_1890_ == 1)
{
size_t v___x_1891_; 
v___x_1891_ = lean_usize_once(&l_ISize_pow___closed__0, &l_ISize_pow___closed__0_once, _init_l_ISize_pow___closed__0);
return v___x_1891_;
}
else
{
lean_object* v_one_1892_; lean_object* v_n_1893_; size_t v___x_1894_; size_t v___x_1895_; 
v_one_1892_ = lean_unsigned_to_nat(1u);
v_n_1893_ = lean_nat_sub(v_n_1888_, v_one_1892_);
v___x_1894_ = l_ISize_pow(v_x_1887_, v_n_1893_);
lean_dec(v_n_1893_);
v___x_1895_ = lean_isize_mul(v___x_1894_, v_x_1887_);
return v___x_1895_;
}
}
}
LEAN_EXPORT void l_ISize_pow_0interp(lean_interpreter_value* stack)
{
size_t v_x_1887_ = stack[0].m_num;
lean_object* v_n_1888_ = stack[1].m_obj;
size_t v_res_1896_;
v_res_1896_ = l_ISize_pow(v_x_1887_, v_n_1888_);
stack->m_num = v_res_1896_;
}
LEAN_EXPORT lean_object* l_ISize_pow___boxed(lean_object* v_x_1897_, lean_object* v_n_1898_){
_start:
{
size_t v_x_boxed_1899_; size_t v_res_1900_; lean_object* v_r_1901_; 
v_x_boxed_1899_ = lean_unbox_usize(v_x_1897_);
lean_dec(v_x_1897_);
v_res_1900_ = l_ISize_pow(v_x_boxed_1899_, v_n_1898_);
lean_dec(v_n_1898_);
v_r_1901_ = lean_box_usize(v_res_1900_);
return v_r_1901_;
}
}
LEAN_EXPORT void l_ISize_mod_0interp(lean_interpreter_value* stack)
{
size_t v_a_1902_ = stack[0].m_num;
size_t v_b_1903_ = stack[1].m_num;
size_t v_res_1904_;
v_res_1904_ = lean_isize_mod(v_a_1902_, v_b_1903_);
stack->m_num = v_res_1904_;
}
LEAN_EXPORT lean_object* l_ISize_mod___boxed(lean_object* v_a_1905_, lean_object* v_b_1906_){
_start:
{
size_t v_a_boxed_1907_; size_t v_b_boxed_1908_; size_t v_res_1909_; lean_object* v_r_1910_; 
v_a_boxed_1907_ = lean_unbox_usize(v_a_1905_);
lean_dec(v_a_1905_);
v_b_boxed_1908_ = lean_unbox_usize(v_b_1906_);
lean_dec(v_b_1906_);
v_res_1909_ = lean_isize_mod(v_a_boxed_1907_, v_b_boxed_1908_);
v_r_1910_ = lean_box_usize(v_res_1909_);
return v_r_1910_;
}
}
LEAN_EXPORT void l_ISize_land_0interp(lean_interpreter_value* stack)
{
size_t v_a_1911_ = stack[0].m_num;
size_t v_b_1912_ = stack[1].m_num;
size_t v_res_1913_;
v_res_1913_ = lean_isize_land(v_a_1911_, v_b_1912_);
stack->m_num = v_res_1913_;
}
LEAN_EXPORT lean_object* l_ISize_land___boxed(lean_object* v_a_1914_, lean_object* v_b_1915_){
_start:
{
size_t v_a_boxed_1916_; size_t v_b_boxed_1917_; size_t v_res_1918_; lean_object* v_r_1919_; 
v_a_boxed_1916_ = lean_unbox_usize(v_a_1914_);
lean_dec(v_a_1914_);
v_b_boxed_1917_ = lean_unbox_usize(v_b_1915_);
lean_dec(v_b_1915_);
v_res_1918_ = lean_isize_land(v_a_boxed_1916_, v_b_boxed_1917_);
v_r_1919_ = lean_box_usize(v_res_1918_);
return v_r_1919_;
}
}
LEAN_EXPORT void l_ISize_lor_0interp(lean_interpreter_value* stack)
{
size_t v_a_1920_ = stack[0].m_num;
size_t v_b_1921_ = stack[1].m_num;
size_t v_res_1922_;
v_res_1922_ = lean_isize_lor(v_a_1920_, v_b_1921_);
stack->m_num = v_res_1922_;
}
LEAN_EXPORT lean_object* l_ISize_lor___boxed(lean_object* v_a_1923_, lean_object* v_b_1924_){
_start:
{
size_t v_a_boxed_1925_; size_t v_b_boxed_1926_; size_t v_res_1927_; lean_object* v_r_1928_; 
v_a_boxed_1925_ = lean_unbox_usize(v_a_1923_);
lean_dec(v_a_1923_);
v_b_boxed_1926_ = lean_unbox_usize(v_b_1924_);
lean_dec(v_b_1924_);
v_res_1927_ = lean_isize_lor(v_a_boxed_1925_, v_b_boxed_1926_);
v_r_1928_ = lean_box_usize(v_res_1927_);
return v_r_1928_;
}
}
LEAN_EXPORT void l_ISize_xor_0interp(lean_interpreter_value* stack)
{
size_t v_a_1929_ = stack[0].m_num;
size_t v_b_1930_ = stack[1].m_num;
size_t v_res_1931_;
v_res_1931_ = lean_isize_xor(v_a_1929_, v_b_1930_);
stack->m_num = v_res_1931_;
}
LEAN_EXPORT lean_object* l_ISize_xor___boxed(lean_object* v_a_1932_, lean_object* v_b_1933_){
_start:
{
size_t v_a_boxed_1934_; size_t v_b_boxed_1935_; size_t v_res_1936_; lean_object* v_r_1937_; 
v_a_boxed_1934_ = lean_unbox_usize(v_a_1932_);
lean_dec(v_a_1932_);
v_b_boxed_1935_ = lean_unbox_usize(v_b_1933_);
lean_dec(v_b_1933_);
v_res_1936_ = lean_isize_xor(v_a_boxed_1934_, v_b_boxed_1935_);
v_r_1937_ = lean_box_usize(v_res_1936_);
return v_r_1937_;
}
}
LEAN_EXPORT void l_ISize_shiftLeft_0interp(lean_interpreter_value* stack)
{
size_t v_a_1938_ = stack[0].m_num;
size_t v_b_1939_ = stack[1].m_num;
size_t v_res_1940_;
v_res_1940_ = lean_isize_shift_left(v_a_1938_, v_b_1939_);
stack->m_num = v_res_1940_;
}
LEAN_EXPORT lean_object* l_ISize_shiftLeft___boxed(lean_object* v_a_1941_, lean_object* v_b_1942_){
_start:
{
size_t v_a_boxed_1943_; size_t v_b_boxed_1944_; size_t v_res_1945_; lean_object* v_r_1946_; 
v_a_boxed_1943_ = lean_unbox_usize(v_a_1941_);
lean_dec(v_a_1941_);
v_b_boxed_1944_ = lean_unbox_usize(v_b_1942_);
lean_dec(v_b_1942_);
v_res_1945_ = lean_isize_shift_left(v_a_boxed_1943_, v_b_boxed_1944_);
v_r_1946_ = lean_box_usize(v_res_1945_);
return v_r_1946_;
}
}
LEAN_EXPORT void l_ISize_shiftRight_0interp(lean_interpreter_value* stack)
{
size_t v_a_1947_ = stack[0].m_num;
size_t v_b_1948_ = stack[1].m_num;
size_t v_res_1949_;
v_res_1949_ = lean_isize_shift_right(v_a_1947_, v_b_1948_);
stack->m_num = v_res_1949_;
}
LEAN_EXPORT lean_object* l_ISize_shiftRight___boxed(lean_object* v_a_1950_, lean_object* v_b_1951_){
_start:
{
size_t v_a_boxed_1952_; size_t v_b_boxed_1953_; size_t v_res_1954_; lean_object* v_r_1955_; 
v_a_boxed_1952_ = lean_unbox_usize(v_a_1950_);
lean_dec(v_a_1950_);
v_b_boxed_1953_ = lean_unbox_usize(v_b_1951_);
lean_dec(v_b_1951_);
v_res_1954_ = lean_isize_shift_right(v_a_boxed_1952_, v_b_boxed_1953_);
v_r_1955_ = lean_box_usize(v_res_1954_);
return v_r_1955_;
}
}
LEAN_EXPORT void l_ISize_complement_0interp(lean_interpreter_value* stack)
{
size_t v_a_1956_ = stack[0].m_num;
size_t v_res_1957_;
v_res_1957_ = lean_isize_complement(v_a_1956_);
stack->m_num = v_res_1957_;
}
LEAN_EXPORT lean_object* l_ISize_complement___boxed(lean_object* v_a_1958_){
_start:
{
size_t v_a_boxed_1959_; size_t v_res_1960_; lean_object* v_r_1961_; 
v_a_boxed_1959_ = lean_unbox_usize(v_a_1958_);
lean_dec(v_a_1958_);
v_res_1960_ = lean_isize_complement(v_a_boxed_1959_);
v_r_1961_ = lean_box_usize(v_res_1960_);
return v_r_1961_;
}
}
LEAN_EXPORT void l_ISize_abs_0interp(lean_interpreter_value* stack)
{
size_t v_a_1962_ = stack[0].m_num;
size_t v_res_1963_;
v_res_1963_ = lean_isize_abs(v_a_1962_);
stack->m_num = v_res_1963_;
}
LEAN_EXPORT lean_object* l_ISize_abs___boxed(lean_object* v_a_1964_){
_start:
{
size_t v_a_boxed_1965_; size_t v_res_1966_; lean_object* v_r_1967_; 
v_a_boxed_1965_ = lean_unbox_usize(v_a_1964_);
lean_dec(v_a_1964_);
v_res_1966_ = lean_isize_abs(v_a_boxed_1965_);
v_r_1967_ = lean_box_usize(v_res_1966_);
return v_r_1967_;
}
}
LEAN_EXPORT void l_ISize_decEq_0interp(lean_interpreter_value* stack)
{
size_t v_a_1968_ = stack[0].m_num;
size_t v_b_1969_ = stack[1].m_num;
uint8_t v_res_1970_;
v_res_1970_ = lean_isize_dec_eq(v_a_1968_, v_b_1969_);
stack->m_num = v_res_1970_;
}
LEAN_EXPORT lean_object* l_ISize_decEq___boxed(lean_object* v_a_1971_, lean_object* v_b_1972_){
_start:
{
size_t v_a_boxed_1973_; size_t v_b_boxed_1974_; uint8_t v_res_1975_; lean_object* v_r_1976_; 
v_a_boxed_1973_ = lean_unbox_usize(v_a_1971_);
lean_dec(v_a_1971_);
v_b_boxed_1974_ = lean_unbox_usize(v_b_1972_);
lean_dec(v_b_1972_);
v_res_1975_ = lean_isize_dec_eq(v_a_boxed_1973_, v_b_boxed_1974_);
v_r_1976_ = lean_box(v_res_1975_);
return v_r_1976_;
}
}
static size_t _init_l_instInhabitedISize___closed__0(void){
_start:
{
lean_object* v___x_1977_; size_t v___x_1978_; 
v___x_1977_ = lean_unsigned_to_nat(0u);
v___x_1978_ = lean_isize_of_nat(v___x_1977_);
return v___x_1978_;
}
}
static size_t _init_l_instInhabitedISize(void){
_start:
{
size_t v___x_1979_; 
v___x_1979_ = lean_usize_once(&l_instInhabitedISize___closed__0, &l_instInhabitedISize___closed__0_once, _init_l_instInhabitedISize___closed__0);
return v___x_1979_;
}
}
static lean_object* _init_l_instLTISize(void){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_box(0);
return v___x_1992_;
}
}
static lean_object* _init_l_instLEISize(void){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_box(0);
return v___x_1993_;
}
}
uint8_t l_instDecidableEqISize(size_t v_a_2006_, size_t v_b_2007_){
_start:
{
uint8_t v___x_2008_; 
v___x_2008_ = lean_isize_dec_eq(v_a_2006_, v_b_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT void l_instDecidableEqISize_0interp(lean_interpreter_value* stack)
{
size_t v_a_2006_ = stack[0].m_num;
size_t v_b_2007_ = stack[1].m_num;
uint8_t v_res_2009_;
v_res_2009_ = l_instDecidableEqISize(v_a_2006_, v_b_2007_);
stack->m_num = v_res_2009_;
}
LEAN_EXPORT lean_object* l_instDecidableEqISize___boxed(lean_object* v_a_2010_, lean_object* v_b_2011_){
_start:
{
size_t v_a_boxed_2012_; size_t v_b_boxed_2013_; uint8_t v_res_2014_; lean_object* v_r_2015_; 
v_a_boxed_2012_ = lean_unbox_usize(v_a_2010_);
lean_dec(v_a_2010_);
v_b_boxed_2013_ = lean_unbox_usize(v_b_2011_);
lean_dec(v_b_2011_);
v_res_2014_ = l_instDecidableEqISize(v_a_boxed_2012_, v_b_boxed_2013_);
v_r_2015_ = lean_box(v_res_2014_);
return v_r_2015_;
}
}
LEAN_EXPORT void l_Bool_toISize_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_2016_ = stack[0].m_num;
size_t v_res_2017_;
v_res_2017_ = lean_bool_to_isize(v_b_2016_);
stack->m_num = v_res_2017_;
}
LEAN_EXPORT lean_object* l_Bool_toISize___boxed(lean_object* v_b_2018_){
_start:
{
uint8_t v_b_boxed_2019_; size_t v_res_2020_; lean_object* v_r_2021_; 
v_b_boxed_2019_ = lean_unbox(v_b_2018_);
v_res_2020_ = lean_bool_to_isize(v_b_boxed_2019_);
v_r_2021_ = lean_box_usize(v_res_2020_);
return v_r_2021_;
}
}
uint8_t l_ISize_decLt___aux__1(size_t v_a_2022_, size_t v_b_2023_){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2024_ = l_System_Platform_numBits;
v___x_2025_ = lean_usize_to_nat(v_a_2022_);
v___x_2026_ = lean_usize_to_nat(v_b_2023_);
v___x_2027_ = l_BitVec_slt(v___x_2024_, v___x_2025_, v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT void l_ISize_decLt___aux__1_0interp(lean_interpreter_value* stack)
{
size_t v_a_2022_ = stack[0].m_num;
size_t v_b_2023_ = stack[1].m_num;
uint8_t v_res_2028_;
v_res_2028_ = l_ISize_decLt___aux__1(v_a_2022_, v_b_2023_);
stack->m_num = v_res_2028_;
}
LEAN_EXPORT lean_object* l_ISize_decLt___aux__1___boxed(lean_object* v_a_2029_, lean_object* v_b_2030_){
_start:
{
size_t v_a_boxed_2031_; size_t v_b_boxed_2032_; uint8_t v_res_2033_; lean_object* v_r_2034_; 
v_a_boxed_2031_ = lean_unbox_usize(v_a_2029_);
lean_dec(v_a_2029_);
v_b_boxed_2032_ = lean_unbox_usize(v_b_2030_);
lean_dec(v_b_2030_);
v_res_2033_ = l_ISize_decLt___aux__1(v_a_boxed_2031_, v_b_boxed_2032_);
v_r_2034_ = lean_box(v_res_2033_);
return v_r_2034_;
}
}
LEAN_EXPORT void l_ISize_decLt_0interp(lean_interpreter_value* stack)
{
size_t v_a_2035_ = stack[0].m_num;
size_t v_b_2036_ = stack[1].m_num;
uint8_t v_res_2037_;
v_res_2037_ = lean_isize_dec_lt(v_a_2035_, v_b_2036_);
stack->m_num = v_res_2037_;
}
LEAN_EXPORT lean_object* l_ISize_decLt___boxed(lean_object* v_a_2038_, lean_object* v_b_2039_){
_start:
{
size_t v_a_boxed_2040_; size_t v_b_boxed_2041_; uint8_t v_res_2042_; lean_object* v_r_2043_; 
v_a_boxed_2040_ = lean_unbox_usize(v_a_2038_);
lean_dec(v_a_2038_);
v_b_boxed_2041_ = lean_unbox_usize(v_b_2039_);
lean_dec(v_b_2039_);
v_res_2042_ = lean_isize_dec_lt(v_a_boxed_2040_, v_b_boxed_2041_);
v_r_2043_ = lean_box(v_res_2042_);
return v_r_2043_;
}
}
uint8_t l_ISize_decLe___aux__1(size_t v_a_2044_, size_t v_b_2045_){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2046_ = l_System_Platform_numBits;
v___x_2047_ = lean_usize_to_nat(v_a_2044_);
v___x_2048_ = lean_usize_to_nat(v_b_2045_);
v___x_2049_ = l_BitVec_sle(v___x_2046_, v___x_2047_, v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT void l_ISize_decLe___aux__1_0interp(lean_interpreter_value* stack)
{
size_t v_a_2044_ = stack[0].m_num;
size_t v_b_2045_ = stack[1].m_num;
uint8_t v_res_2050_;
v_res_2050_ = l_ISize_decLe___aux__1(v_a_2044_, v_b_2045_);
stack->m_num = v_res_2050_;
}
LEAN_EXPORT lean_object* l_ISize_decLe___aux__1___boxed(lean_object* v_a_2051_, lean_object* v_b_2052_){
_start:
{
size_t v_a_boxed_2053_; size_t v_b_boxed_2054_; uint8_t v_res_2055_; lean_object* v_r_2056_; 
v_a_boxed_2053_ = lean_unbox_usize(v_a_2051_);
lean_dec(v_a_2051_);
v_b_boxed_2054_ = lean_unbox_usize(v_b_2052_);
lean_dec(v_b_2052_);
v_res_2055_ = l_ISize_decLe___aux__1(v_a_boxed_2053_, v_b_boxed_2054_);
v_r_2056_ = lean_box(v_res_2055_);
return v_r_2056_;
}
}
LEAN_EXPORT void l_ISize_decLe_0interp(lean_interpreter_value* stack)
{
size_t v_a_2057_ = stack[0].m_num;
size_t v_b_2058_ = stack[1].m_num;
uint8_t v_res_2059_;
v_res_2059_ = lean_isize_dec_le(v_a_2057_, v_b_2058_);
stack->m_num = v_res_2059_;
}
LEAN_EXPORT lean_object* l_ISize_decLe___boxed(lean_object* v_a_2060_, lean_object* v_b_2061_){
_start:
{
size_t v_a_boxed_2062_; size_t v_b_boxed_2063_; uint8_t v_res_2064_; lean_object* v_r_2065_; 
v_a_boxed_2062_ = lean_unbox_usize(v_a_2060_);
lean_dec(v_a_2060_);
v_b_boxed_2063_ = lean_unbox_usize(v_b_2061_);
lean_dec(v_b_2061_);
v_res_2064_ = lean_isize_dec_le(v_a_boxed_2062_, v_b_boxed_2063_);
v_r_2065_ = lean_box(v_res_2064_);
return v_r_2065_;
}
}
size_t l_instMaxISize___lam__0(size_t v_x_2066_, size_t v_y_2067_){
_start:
{
uint8_t v___x_2068_; 
v___x_2068_ = lean_isize_dec_le(v_x_2066_, v_y_2067_);
if (v___x_2068_ == 0)
{
return v_x_2066_;
}
else
{
return v_y_2067_;
}
}
}
LEAN_EXPORT void l_instMaxISize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_x_2066_ = stack[0].m_num;
size_t v_y_2067_ = stack[1].m_num;
size_t v_res_2069_;
v_res_2069_ = l_instMaxISize___lam__0(v_x_2066_, v_y_2067_);
stack->m_num = v_res_2069_;
}
LEAN_EXPORT lean_object* l_instMaxISize___lam__0___boxed(lean_object* v_x_2070_, lean_object* v_y_2071_){
_start:
{
size_t v_x_boxed_2072_; size_t v_y_boxed_2073_; size_t v_res_2074_; lean_object* v_r_2075_; 
v_x_boxed_2072_ = lean_unbox_usize(v_x_2070_);
lean_dec(v_x_2070_);
v_y_boxed_2073_ = lean_unbox_usize(v_y_2071_);
lean_dec(v_y_2071_);
v_res_2074_ = l_instMaxISize___lam__0(v_x_boxed_2072_, v_y_boxed_2073_);
v_r_2075_ = lean_box_usize(v_res_2074_);
return v_r_2075_;
}
}
size_t l_instMinISize___lam__0(size_t v_x_2078_, size_t v_y_2079_){
_start:
{
uint8_t v___x_2080_; 
v___x_2080_ = lean_isize_dec_le(v_x_2078_, v_y_2079_);
if (v___x_2080_ == 0)
{
return v_y_2079_;
}
else
{
return v_x_2078_;
}
}
}
LEAN_EXPORT void l_instMinISize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_x_2078_ = stack[0].m_num;
size_t v_y_2079_ = stack[1].m_num;
size_t v_res_2081_;
v_res_2081_ = l_instMinISize___lam__0(v_x_2078_, v_y_2079_);
stack->m_num = v_res_2081_;
}
LEAN_EXPORT lean_object* l_instMinISize___lam__0___boxed(lean_object* v_x_2082_, lean_object* v_y_2083_){
_start:
{
size_t v_x_boxed_2084_; size_t v_y_boxed_2085_; size_t v_res_2086_; lean_object* v_r_2087_; 
v_x_boxed_2084_ = lean_unbox_usize(v_x_2082_);
lean_dec(v_x_2082_);
v_y_boxed_2085_ = lean_unbox_usize(v_y_2083_);
lean_dec(v_y_2083_);
v_res_2086_ = l_instMinISize___lam__0(v_x_boxed_2084_, v_y_boxed_2085_);
v_r_2087_ = lean_box_usize(v_res_2086_);
return v_r_2087_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Extra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
