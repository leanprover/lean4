// Lean compiler output
// Module: Init.Data.UInt.Basic
// Imports: public import Init.Data.BitVec.Basic
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
uint32_t lean_uint32_of_nat_mk(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
uint8_t lean_uint8_of_nat_mk(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_uint8_dec_lt(uint8_t, uint8_t);
extern lean_object* l_System_Platform_numBits;
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_of_nat_mk(lean_object*);
uint64_t lean_uint64_of_nat_mk(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_uint16_to_nat(uint16_t);
uint16_t lean_uint16_of_nat_mk(lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_UInt8_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_ofFin___boxed(lean_object*);
static lean_once_cell_t l_UInt8_ofInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt8_ofInt___closed__0;
static lean_once_cell_t l_UInt8_ofInt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt8_ofInt___closed__1;
LEAN_EXPORT uint8_t l_UInt8_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_ofInt___boxed(lean_object*);
uint8_t lean_uint8_add(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_add___boxed(lean_object*, lean_object*);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_sub___boxed(lean_object*, lean_object*);
uint8_t lean_uint8_mul(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_mul___boxed(lean_object*, lean_object*);
uint8_t lean_uint8_div(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt8_pow(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_pow___boxed(lean_object*, lean_object*);
uint8_t lean_uint8_mod(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_mod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt8_modn_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt8_modn_spec__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt8_modn(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_modn___boxed(lean_object*, lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_land___boxed(lean_object*, lean_object*);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_lor___boxed(lean_object*, lean_object*);
uint8_t lean_uint8_xor(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_xor___boxed(lean_object*, lean_object*);
uint8_t lean_uint8_shift_left(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_shiftLeft___boxed(lean_object*, lean_object*);
uint8_t lean_uint8_shift_right(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_shiftRight___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instAddUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAddUInt8___closed__0 = (const lean_object*)&l_instAddUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instAddUInt8 = (const lean_object*)&l_instAddUInt8___closed__0_value;
static const lean_closure_object l_instSubUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSubUInt8___closed__0 = (const lean_object*)&l_instSubUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instSubUInt8 = (const lean_object*)&l_instSubUInt8___closed__0_value;
static const lean_closure_object l_instMulUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMulUInt8___closed__0 = (const lean_object*)&l_instMulUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instMulUInt8 = (const lean_object*)&l_instMulUInt8___closed__0_value;
static const lean_closure_object l_instPowUInt8Nat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instPowUInt8Nat___closed__0 = (const lean_object*)&l_instPowUInt8Nat___closed__0_value;
LEAN_EXPORT const lean_object* l_instPowUInt8Nat = (const lean_object*)&l_instPowUInt8Nat___closed__0_value;
static const lean_closure_object l_instModUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_mod___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instModUInt8___closed__0 = (const lean_object*)&l_instModUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instModUInt8 = (const lean_object*)&l_instModUInt8___closed__0_value;
static const lean_closure_object l_instHModUInt8Nat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_modn___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHModUInt8Nat___closed__0 = (const lean_object*)&l_instHModUInt8Nat___closed__0_value;
LEAN_EXPORT const lean_object* l_instHModUInt8Nat = (const lean_object*)&l_instHModUInt8Nat___closed__0_value;
static const lean_closure_object l_instDivUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instDivUInt8___closed__0 = (const lean_object*)&l_instDivUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instDivUInt8 = (const lean_object*)&l_instDivUInt8___closed__0_value;
uint8_t lean_uint8_complement(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_complement___boxed(lean_object*);
uint8_t lean_uint8_neg(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_neg___boxed(lean_object*);
static const lean_closure_object l_instComplementUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_complement___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instComplementUInt8___closed__0 = (const lean_object*)&l_instComplementUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instComplementUInt8 = (const lean_object*)&l_instComplementUInt8___closed__0_value;
static const lean_closure_object l_instNegUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instNegUInt8___closed__0 = (const lean_object*)&l_instNegUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instNegUInt8 = (const lean_object*)&l_instNegUInt8___closed__0_value;
static const lean_closure_object l_instAndOpUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_land___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAndOpUInt8___closed__0 = (const lean_object*)&l_instAndOpUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instAndOpUInt8 = (const lean_object*)&l_instAndOpUInt8___closed__0_value;
static const lean_closure_object l_instOrOpUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_lor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrOpUInt8___closed__0 = (const lean_object*)&l_instOrOpUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrOpUInt8 = (const lean_object*)&l_instOrOpUInt8___closed__0_value;
static const lean_closure_object l_instXorOpUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_xor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instXorOpUInt8___closed__0 = (const lean_object*)&l_instXorOpUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instXorOpUInt8 = (const lean_object*)&l_instXorOpUInt8___closed__0_value;
static const lean_closure_object l_instShiftLeftUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftLeftUInt8___closed__0 = (const lean_object*)&l_instShiftLeftUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftLeftUInt8 = (const lean_object*)&l_instShiftLeftUInt8___closed__0_value;
static const lean_closure_object l_instShiftRightUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftRightUInt8___closed__0 = (const lean_object*)&l_instShiftRightUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftRightUInt8 = (const lean_object*)&l_instShiftRightUInt8___closed__0_value;
uint8_t lean_bool_to_uint8(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toUInt8___boxed(lean_object*);
LEAN_EXPORT uint8_t l_instMaxUInt8___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instMaxUInt8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMaxUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMaxUInt8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMaxUInt8___closed__0 = (const lean_object*)&l_instMaxUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instMaxUInt8 = (const lean_object*)&l_instMaxUInt8___closed__0_value;
LEAN_EXPORT uint8_t l_instMinUInt8___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_instMinUInt8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMinUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMinUInt8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMinUInt8___closed__0 = (const lean_object*)&l_instMinUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instMinUInt8 = (const lean_object*)&l_instMinUInt8___closed__0_value;
LEAN_EXPORT uint8_t l_UInt8_toAsciiLower(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_toAsciiLower___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt8_toAsciiUpper(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_toAsciiUpper___boxed(lean_object*);
LEAN_EXPORT uint16_t l_UInt16_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_ofFin___boxed(lean_object*);
static lean_once_cell_t l_UInt16_ofInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt16_ofInt___closed__0;
LEAN_EXPORT uint16_t l_UInt16_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_ofInt___boxed(lean_object*);
uint16_t lean_uint16_add(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_add___boxed(lean_object*, lean_object*);
uint16_t lean_uint16_sub(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_sub___boxed(lean_object*, lean_object*);
uint16_t lean_uint16_mul(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_mul___boxed(lean_object*, lean_object*);
uint16_t lean_uint16_div(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_UInt16_pow(uint16_t, lean_object*);
LEAN_EXPORT lean_object* l_UInt16_pow___boxed(lean_object*, lean_object*);
uint16_t lean_uint16_mod(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_mod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt16_modn_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt16_modn_spec__0___boxed(lean_object*);
LEAN_EXPORT uint16_t l_UInt16_modn(uint16_t, lean_object*);
LEAN_EXPORT lean_object* l_UInt16_modn___boxed(lean_object*, lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_land___boxed(lean_object*, lean_object*);
uint16_t lean_uint16_lor(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_lor___boxed(lean_object*, lean_object*);
uint16_t lean_uint16_xor(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_xor___boxed(lean_object*, lean_object*);
uint16_t lean_uint16_shift_left(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_shiftLeft___boxed(lean_object*, lean_object*);
uint16_t lean_uint16_shift_right(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_shiftRight___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instAddUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAddUInt16___closed__0 = (const lean_object*)&l_instAddUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instAddUInt16 = (const lean_object*)&l_instAddUInt16___closed__0_value;
static const lean_closure_object l_instSubUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSubUInt16___closed__0 = (const lean_object*)&l_instSubUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instSubUInt16 = (const lean_object*)&l_instSubUInt16___closed__0_value;
static const lean_closure_object l_instMulUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMulUInt16___closed__0 = (const lean_object*)&l_instMulUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instMulUInt16 = (const lean_object*)&l_instMulUInt16___closed__0_value;
static const lean_closure_object l_instPowUInt16Nat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instPowUInt16Nat___closed__0 = (const lean_object*)&l_instPowUInt16Nat___closed__0_value;
LEAN_EXPORT const lean_object* l_instPowUInt16Nat = (const lean_object*)&l_instPowUInt16Nat___closed__0_value;
static const lean_closure_object l_instModUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_mod___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instModUInt16___closed__0 = (const lean_object*)&l_instModUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instModUInt16 = (const lean_object*)&l_instModUInt16___closed__0_value;
static const lean_closure_object l_instHModUInt16Nat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_modn___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHModUInt16Nat___closed__0 = (const lean_object*)&l_instHModUInt16Nat___closed__0_value;
LEAN_EXPORT const lean_object* l_instHModUInt16Nat = (const lean_object*)&l_instHModUInt16Nat___closed__0_value;
static const lean_closure_object l_instDivUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instDivUInt16___closed__0 = (const lean_object*)&l_instDivUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instDivUInt16 = (const lean_object*)&l_instDivUInt16___closed__0_value;
LEAN_EXPORT lean_object* l_instLTUInt16;
LEAN_EXPORT lean_object* l_instLEUInt16;
uint16_t lean_uint16_complement(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_complement___boxed(lean_object*);
uint16_t lean_uint16_neg(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_neg___boxed(lean_object*);
static const lean_closure_object l_instComplementUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_complement___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instComplementUInt16___closed__0 = (const lean_object*)&l_instComplementUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instComplementUInt16 = (const lean_object*)&l_instComplementUInt16___closed__0_value;
static const lean_closure_object l_instNegUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instNegUInt16___closed__0 = (const lean_object*)&l_instNegUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instNegUInt16 = (const lean_object*)&l_instNegUInt16___closed__0_value;
static const lean_closure_object l_instAndOpUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_land___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAndOpUInt16___closed__0 = (const lean_object*)&l_instAndOpUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instAndOpUInt16 = (const lean_object*)&l_instAndOpUInt16___closed__0_value;
static const lean_closure_object l_instOrOpUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_lor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrOpUInt16___closed__0 = (const lean_object*)&l_instOrOpUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrOpUInt16 = (const lean_object*)&l_instOrOpUInt16___closed__0_value;
static const lean_closure_object l_instXorOpUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_xor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instXorOpUInt16___closed__0 = (const lean_object*)&l_instXorOpUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instXorOpUInt16 = (const lean_object*)&l_instXorOpUInt16___closed__0_value;
static const lean_closure_object l_instShiftLeftUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftLeftUInt16___closed__0 = (const lean_object*)&l_instShiftLeftUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftLeftUInt16 = (const lean_object*)&l_instShiftLeftUInt16___closed__0_value;
static const lean_closure_object l_instShiftRightUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftRightUInt16___closed__0 = (const lean_object*)&l_instShiftRightUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftRightUInt16 = (const lean_object*)&l_instShiftRightUInt16___closed__0_value;
uint16_t lean_bool_to_uint16(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toUInt16___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt16_decLt___aux__1(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_decLt___aux__1___boxed(lean_object*, lean_object*);
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt16_decLe___aux__1(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_decLe___aux__1___boxed(lean_object*, lean_object*);
uint8_t lean_uint16_dec_le(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_instMaxUInt16___lam__0(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_instMaxUInt16___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMaxUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMaxUInt16___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMaxUInt16___closed__0 = (const lean_object*)&l_instMaxUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instMaxUInt16 = (const lean_object*)&l_instMaxUInt16___closed__0_value;
LEAN_EXPORT uint16_t l_instMinUInt16___lam__0(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_instMinUInt16___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMinUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMinUInt16___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMinUInt16___closed__0 = (const lean_object*)&l_instMinUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instMinUInt16 = (const lean_object*)&l_instMinUInt16___closed__0_value;
LEAN_EXPORT uint32_t l_UInt32_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_UInt32_ofFin___boxed(lean_object*);
static lean_once_cell_t l_UInt32_ofInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt32_ofInt___closed__0;
LEAN_EXPORT uint32_t l_UInt32_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_UInt32_ofInt___boxed(lean_object*);
uint32_t lean_uint32_mul(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_mul___boxed(lean_object*, lean_object*);
uint32_t lean_uint32_div(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_UInt32_pow(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_UInt32_pow___boxed(lean_object*, lean_object*);
uint32_t lean_uint32_mod(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_mod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt32_modn_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt32_modn_spec__0___boxed(lean_object*);
LEAN_EXPORT uint32_t l_UInt32_modn(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_UInt32_modn___boxed(lean_object*, lean_object*);
uint32_t lean_uint32_land(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_land___boxed(lean_object*, lean_object*);
uint32_t lean_uint32_lor(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_lor___boxed(lean_object*, lean_object*);
uint32_t lean_uint32_xor(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_xor___boxed(lean_object*, lean_object*);
uint32_t lean_uint32_shift_left(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_shiftLeft___boxed(lean_object*, lean_object*);
uint32_t lean_uint32_shift_right(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_shiftRight___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMulUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMulUInt32___closed__0 = (const lean_object*)&l_instMulUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instMulUInt32 = (const lean_object*)&l_instMulUInt32___closed__0_value;
static const lean_closure_object l_instPowUInt32Nat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instPowUInt32Nat___closed__0 = (const lean_object*)&l_instPowUInt32Nat___closed__0_value;
LEAN_EXPORT const lean_object* l_instPowUInt32Nat = (const lean_object*)&l_instPowUInt32Nat___closed__0_value;
static const lean_closure_object l_instModUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_mod___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instModUInt32___closed__0 = (const lean_object*)&l_instModUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instModUInt32 = (const lean_object*)&l_instModUInt32___closed__0_value;
static const lean_closure_object l_instHModUInt32Nat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_modn___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHModUInt32Nat___closed__0 = (const lean_object*)&l_instHModUInt32Nat___closed__0_value;
LEAN_EXPORT const lean_object* l_instHModUInt32Nat = (const lean_object*)&l_instHModUInt32Nat___closed__0_value;
static const lean_closure_object l_instDivUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instDivUInt32___closed__0 = (const lean_object*)&l_instDivUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instDivUInt32 = (const lean_object*)&l_instDivUInt32___closed__0_value;
uint32_t lean_uint32_complement(uint32_t);
LEAN_EXPORT lean_object* l_UInt32_complement___boxed(lean_object*);
uint32_t lean_uint32_neg(uint32_t);
LEAN_EXPORT lean_object* l_UInt32_neg___boxed(lean_object*);
static const lean_closure_object l_instComplementUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_complement___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instComplementUInt32___closed__0 = (const lean_object*)&l_instComplementUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instComplementUInt32 = (const lean_object*)&l_instComplementUInt32___closed__0_value;
static const lean_closure_object l_instNegUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instNegUInt32___closed__0 = (const lean_object*)&l_instNegUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instNegUInt32 = (const lean_object*)&l_instNegUInt32___closed__0_value;
static const lean_closure_object l_instAndOpUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_land___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAndOpUInt32___closed__0 = (const lean_object*)&l_instAndOpUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instAndOpUInt32 = (const lean_object*)&l_instAndOpUInt32___closed__0_value;
static const lean_closure_object l_instOrOpUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_lor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrOpUInt32___closed__0 = (const lean_object*)&l_instOrOpUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrOpUInt32 = (const lean_object*)&l_instOrOpUInt32___closed__0_value;
static const lean_closure_object l_instXorOpUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_xor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instXorOpUInt32___closed__0 = (const lean_object*)&l_instXorOpUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instXorOpUInt32 = (const lean_object*)&l_instXorOpUInt32___closed__0_value;
static const lean_closure_object l_instShiftLeftUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftLeftUInt32___closed__0 = (const lean_object*)&l_instShiftLeftUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftLeftUInt32 = (const lean_object*)&l_instShiftLeftUInt32___closed__0_value;
static const lean_closure_object l_instShiftRightUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftRightUInt32___closed__0 = (const lean_object*)&l_instShiftRightUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftRightUInt32 = (const lean_object*)&l_instShiftRightUInt32___closed__0_value;
uint32_t lean_bool_to_uint32(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toUInt32___boxed(lean_object*);
LEAN_EXPORT uint64_t l_UInt64_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_UInt64_ofFin___boxed(lean_object*);
static lean_once_cell_t l_UInt64_ofInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt64_ofInt___closed__0;
LEAN_EXPORT uint64_t l_UInt64_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_UInt64_ofInt___boxed(lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_add___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_sub(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_sub___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_mul(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_mul___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_div(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_UInt64_pow(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_pow___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_mod(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_mod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt64_modn_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt64_modn_spec__0___boxed(lean_object*);
LEAN_EXPORT uint64_t l_UInt64_modn(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_UInt64_modn___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_land(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_land___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_lor___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_xor___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_shiftLeft___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_shiftRight___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instAddUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAddUInt64___closed__0 = (const lean_object*)&l_instAddUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instAddUInt64 = (const lean_object*)&l_instAddUInt64___closed__0_value;
static const lean_closure_object l_instSubUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSubUInt64___closed__0 = (const lean_object*)&l_instSubUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instSubUInt64 = (const lean_object*)&l_instSubUInt64___closed__0_value;
static const lean_closure_object l_instMulUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMulUInt64___closed__0 = (const lean_object*)&l_instMulUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instMulUInt64 = (const lean_object*)&l_instMulUInt64___closed__0_value;
static const lean_closure_object l_instPowUInt64Nat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instPowUInt64Nat___closed__0 = (const lean_object*)&l_instPowUInt64Nat___closed__0_value;
LEAN_EXPORT const lean_object* l_instPowUInt64Nat = (const lean_object*)&l_instPowUInt64Nat___closed__0_value;
static const lean_closure_object l_instModUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_mod___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instModUInt64___closed__0 = (const lean_object*)&l_instModUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instModUInt64 = (const lean_object*)&l_instModUInt64___closed__0_value;
static const lean_closure_object l_instHModUInt64Nat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_modn___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHModUInt64Nat___closed__0 = (const lean_object*)&l_instHModUInt64Nat___closed__0_value;
LEAN_EXPORT const lean_object* l_instHModUInt64Nat = (const lean_object*)&l_instHModUInt64Nat___closed__0_value;
static const lean_closure_object l_instDivUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instDivUInt64___closed__0 = (const lean_object*)&l_instDivUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instDivUInt64 = (const lean_object*)&l_instDivUInt64___closed__0_value;
LEAN_EXPORT lean_object* l_instLTUInt64;
LEAN_EXPORT lean_object* l_instLEUInt64;
uint64_t lean_uint64_complement(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_complement___boxed(lean_object*);
uint64_t lean_uint64_neg(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_neg___boxed(lean_object*);
static const lean_closure_object l_instComplementUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_complement___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instComplementUInt64___closed__0 = (const lean_object*)&l_instComplementUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instComplementUInt64 = (const lean_object*)&l_instComplementUInt64___closed__0_value;
static const lean_closure_object l_instNegUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instNegUInt64___closed__0 = (const lean_object*)&l_instNegUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instNegUInt64 = (const lean_object*)&l_instNegUInt64___closed__0_value;
static const lean_closure_object l_instAndOpUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_land___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAndOpUInt64___closed__0 = (const lean_object*)&l_instAndOpUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instAndOpUInt64 = (const lean_object*)&l_instAndOpUInt64___closed__0_value;
static const lean_closure_object l_instOrOpUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_lor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrOpUInt64___closed__0 = (const lean_object*)&l_instOrOpUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrOpUInt64 = (const lean_object*)&l_instOrOpUInt64___closed__0_value;
static const lean_closure_object l_instXorOpUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_xor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instXorOpUInt64___closed__0 = (const lean_object*)&l_instXorOpUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instXorOpUInt64 = (const lean_object*)&l_instXorOpUInt64___closed__0_value;
static const lean_closure_object l_instShiftLeftUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftLeftUInt64___closed__0 = (const lean_object*)&l_instShiftLeftUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftLeftUInt64 = (const lean_object*)&l_instShiftLeftUInt64___closed__0_value;
static const lean_closure_object l_instShiftRightUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftRightUInt64___closed__0 = (const lean_object*)&l_instShiftRightUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftRightUInt64 = (const lean_object*)&l_instShiftRightUInt64___closed__0_value;
uint64_t lean_bool_to_uint64(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toUInt64___boxed(lean_object*);
LEAN_EXPORT uint8_t l_UInt64_decLt___aux__1(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_decLt___aux__1___boxed(lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt64_decLe___aux__1(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_decLe___aux__1___boxed(lean_object*, lean_object*);
uint8_t lean_uint64_dec_le(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_decLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instMaxUInt64___lam__0(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_instMaxUInt64___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMaxUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMaxUInt64___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMaxUInt64___closed__0 = (const lean_object*)&l_instMaxUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instMaxUInt64 = (const lean_object*)&l_instMaxUInt64___closed__0_value;
LEAN_EXPORT uint64_t l_instMinUInt64___lam__0(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_instMinUInt64___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMinUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMinUInt64___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMinUInt64___closed__0 = (const lean_object*)&l_instMinUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instMinUInt64 = (const lean_object*)&l_instMinUInt64___closed__0_value;
LEAN_EXPORT size_t l_USize_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_USize_ofFin___boxed(lean_object*);
static lean_once_cell_t l_USize_ofInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_USize_ofInt___closed__0;
LEAN_EXPORT size_t l_USize_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_USize_ofInt___boxed(lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_mul___boxed(lean_object*, lean_object*);
size_t lean_usize_div(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_USize_pow(size_t, lean_object*);
LEAN_EXPORT lean_object* l_USize_pow___boxed(lean_object*, lean_object*);
size_t lean_usize_mod(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_mod___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00USize_modn_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00USize_modn_spec__0___boxed(lean_object*);
LEAN_EXPORT size_t l_USize_modn(size_t, lean_object*);
LEAN_EXPORT lean_object* l_USize_modn___boxed(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_land___boxed(lean_object*, lean_object*);
size_t lean_usize_lor(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_lor___boxed(lean_object*, lean_object*);
size_t lean_usize_xor(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_xor___boxed(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_shiftLeft___boxed(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_shiftRight___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_USize_ofNat32___boxed(lean_object*, lean_object*);
size_t lean_uint8_to_usize(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_toUSize___boxed(lean_object*);
uint8_t lean_usize_to_uint8(size_t);
LEAN_EXPORT lean_object* l_USize_toUInt8___boxed(lean_object*);
size_t lean_uint16_to_usize(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_toUSize___boxed(lean_object*);
uint16_t lean_usize_to_uint16(size_t);
LEAN_EXPORT lean_object* l_USize_toUInt16___boxed(lean_object*);
size_t lean_uint32_to_usize(uint32_t);
LEAN_EXPORT lean_object* l_UInt32_toUSize___boxed(lean_object*);
uint32_t lean_usize_to_uint32(size_t);
LEAN_EXPORT lean_object* l_USize_toUInt32___boxed(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_toUSize___boxed(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
LEAN_EXPORT lean_object* l_USize_toUInt64___boxed(lean_object*);
LEAN_EXPORT lean_object* l_USize_toBitVec32___redArg(size_t);
LEAN_EXPORT lean_object* l_USize_toBitVec32___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_USize_toBitVec32(size_t, lean_object*);
LEAN_EXPORT lean_object* l_USize_toBitVec32___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_USize_toBitVec64___redArg(size_t);
LEAN_EXPORT lean_object* l_USize_toBitVec64___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_USize_toBitVec64(size_t, lean_object*);
LEAN_EXPORT lean_object* l_USize_toBitVec64___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMulUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMulUSize___closed__0 = (const lean_object*)&l_instMulUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instMulUSize = (const lean_object*)&l_instMulUSize___closed__0_value;
static const lean_closure_object l_instPowUSizeNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instPowUSizeNat___closed__0 = (const lean_object*)&l_instPowUSizeNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instPowUSizeNat = (const lean_object*)&l_instPowUSizeNat___closed__0_value;
static const lean_closure_object l_instModUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_mod___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instModUSize___closed__0 = (const lean_object*)&l_instModUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instModUSize = (const lean_object*)&l_instModUSize___closed__0_value;
static const lean_closure_object l_instHModUSizeNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_modn___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHModUSizeNat___closed__0 = (const lean_object*)&l_instHModUSizeNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instHModUSizeNat = (const lean_object*)&l_instHModUSizeNat___closed__0_value;
static const lean_closure_object l_instDivUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instDivUSize___closed__0 = (const lean_object*)&l_instDivUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instDivUSize = (const lean_object*)&l_instDivUSize___closed__0_value;
size_t lean_usize_complement(size_t);
LEAN_EXPORT lean_object* l_USize_complement___boxed(lean_object*);
size_t lean_usize_neg(size_t);
LEAN_EXPORT lean_object* l_USize_neg___boxed(lean_object*);
static const lean_closure_object l_instComplementUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_complement___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instComplementUSize___closed__0 = (const lean_object*)&l_instComplementUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instComplementUSize = (const lean_object*)&l_instComplementUSize___closed__0_value;
static const lean_closure_object l_instNegUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instNegUSize___closed__0 = (const lean_object*)&l_instNegUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instNegUSize = (const lean_object*)&l_instNegUSize___closed__0_value;
static const lean_closure_object l_instAndOpUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_land___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instAndOpUSize___closed__0 = (const lean_object*)&l_instAndOpUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instAndOpUSize = (const lean_object*)&l_instAndOpUSize___closed__0_value;
static const lean_closure_object l_instOrOpUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_lor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOrOpUSize___closed__0 = (const lean_object*)&l_instOrOpUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instOrOpUSize = (const lean_object*)&l_instOrOpUSize___closed__0_value;
static const lean_closure_object l_instXorOpUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_xor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instXorOpUSize___closed__0 = (const lean_object*)&l_instXorOpUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instXorOpUSize = (const lean_object*)&l_instXorOpUSize___closed__0_value;
static const lean_closure_object l_instShiftLeftUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftLeftUSize___closed__0 = (const lean_object*)&l_instShiftLeftUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftLeftUSize = (const lean_object*)&l_instShiftLeftUSize___closed__0_value;
static const lean_closure_object l_instShiftRightUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instShiftRightUSize___closed__0 = (const lean_object*)&l_instShiftRightUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instShiftRightUSize = (const lean_object*)&l_instShiftRightUSize___closed__0_value;
size_t lean_bool_to_usize(uint8_t);
LEAN_EXPORT lean_object* l_Bool_toUSize___boxed(lean_object*);
LEAN_EXPORT size_t l_instMaxUSize___lam__0(size_t, size_t);
LEAN_EXPORT lean_object* l_instMaxUSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMaxUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMaxUSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMaxUSize___closed__0 = (const lean_object*)&l_instMaxUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instMaxUSize = (const lean_object*)&l_instMaxUSize___closed__0_value;
LEAN_EXPORT size_t l_instMinUSize___lam__0(size_t, size_t);
LEAN_EXPORT lean_object* l_instMinUSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instMinUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMinUSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMinUSize___closed__0 = (const lean_object*)&l_instMinUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instMinUSize = (const lean_object*)&l_instMinUSize___closed__0_value;
LEAN_EXPORT uint8_t l_UInt8_ofFin(lean_object* v_a_1_){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = lean_uint8_of_nat_mk(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_UInt8_ofFin___boxed(lean_object* v_a_3_){
_start:
{
uint8_t v_res_4_; lean_object* v_r_5_; 
v_res_4_ = l_UInt8_ofFin(v_a_3_);
v_r_5_ = lean_box(v_res_4_);
return v_r_5_;
}
}
static lean_object* _init_l_UInt8_ofInt___closed__0(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_unsigned_to_nat(2u);
v___x_7_ = lean_nat_to_int(v___x_6_);
return v___x_7_;
}
}
static lean_object* _init_l_UInt8_ofInt___closed__1(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_unsigned_to_nat(8u);
v___x_9_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_10_ = l_Int_pow(v___x_9_, v___x_8_);
return v___x_10_;
}
}
LEAN_EXPORT uint8_t l_UInt8_ofInt(lean_object* v_x_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_12_ = lean_obj_once(&l_UInt8_ofInt___closed__1, &l_UInt8_ofInt___closed__1_once, _init_l_UInt8_ofInt___closed__1);
v___x_13_ = lean_int_emod(v_x_11_, v___x_12_);
v___x_14_ = l_Int_toNat(v___x_13_);
lean_dec(v___x_13_);
v___x_15_ = lean_uint8_of_nat(v___x_14_);
lean_dec(v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_UInt8_ofInt___boxed(lean_object* v_x_16_){
_start:
{
uint8_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_UInt8_ofInt(v_x_16_);
lean_dec(v_x_16_);
v_r_18_ = lean_box(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT lean_object* l_UInt8_add___boxed(lean_object* v_a_21_, lean_object* v_b_22_){
_start:
{
uint8_t v_a_boxed_23_; uint8_t v_b_boxed_24_; uint8_t v_res_25_; lean_object* v_r_26_; 
v_a_boxed_23_ = lean_unbox(v_a_21_);
v_b_boxed_24_ = lean_unbox(v_b_22_);
v_res_25_ = lean_uint8_add(v_a_boxed_23_, v_b_boxed_24_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT lean_object* l_UInt8_sub___boxed(lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
uint8_t v_a_boxed_31_; uint8_t v_b_boxed_32_; uint8_t v_res_33_; lean_object* v_r_34_; 
v_a_boxed_31_ = lean_unbox(v_a_29_);
v_b_boxed_32_ = lean_unbox(v_b_30_);
v_res_33_ = lean_uint8_sub(v_a_boxed_31_, v_b_boxed_32_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT lean_object* l_UInt8_mul___boxed(lean_object* v_a_37_, lean_object* v_b_38_){
_start:
{
uint8_t v_a_boxed_39_; uint8_t v_b_boxed_40_; uint8_t v_res_41_; lean_object* v_r_42_; 
v_a_boxed_39_ = lean_unbox(v_a_37_);
v_b_boxed_40_ = lean_unbox(v_b_38_);
v_res_41_ = lean_uint8_mul(v_a_boxed_39_, v_b_boxed_40_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT lean_object* l_UInt8_div___boxed(lean_object* v_a_45_, lean_object* v_b_46_){
_start:
{
uint8_t v_a_boxed_47_; uint8_t v_b_boxed_48_; uint8_t v_res_49_; lean_object* v_r_50_; 
v_a_boxed_47_ = lean_unbox(v_a_45_);
v_b_boxed_48_ = lean_unbox(v_b_46_);
v_res_49_ = lean_uint8_div(v_a_boxed_47_, v_b_boxed_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT uint8_t l_UInt8_pow(uint8_t v_x_51_, lean_object* v_n_52_){
_start:
{
lean_object* v_zero_53_; uint8_t v_isZero_54_; 
v_zero_53_ = lean_unsigned_to_nat(0u);
v_isZero_54_ = lean_nat_dec_eq(v_n_52_, v_zero_53_);
if (v_isZero_54_ == 1)
{
uint8_t v___x_55_; 
v___x_55_ = 1;
return v___x_55_;
}
else
{
lean_object* v_one_56_; lean_object* v_n_57_; uint8_t v___x_58_; uint8_t v___x_59_; 
v_one_56_ = lean_unsigned_to_nat(1u);
v_n_57_ = lean_nat_sub(v_n_52_, v_one_56_);
v___x_58_ = l_UInt8_pow(v_x_51_, v_n_57_);
lean_dec(v_n_57_);
v___x_59_ = lean_uint8_mul(v___x_58_, v_x_51_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_pow___boxed(lean_object* v_x_60_, lean_object* v_n_61_){
_start:
{
uint8_t v_x_boxed_62_; uint8_t v_res_63_; lean_object* v_r_64_; 
v_x_boxed_62_ = lean_unbox(v_x_60_);
v_res_63_ = l_UInt8_pow(v_x_boxed_62_, v_n_61_);
lean_dec(v_n_61_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
LEAN_EXPORT lean_object* l_UInt8_mod___boxed(lean_object* v_a_67_, lean_object* v_b_68_){
_start:
{
uint8_t v_a_boxed_69_; uint8_t v_b_boxed_70_; uint8_t v_res_71_; lean_object* v_r_72_; 
v_a_boxed_69_ = lean_unbox(v_a_67_);
v_b_boxed_70_ = lean_unbox(v_b_68_);
v_res_71_ = lean_uint8_mod(v_a_boxed_69_, v_b_boxed_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt8_modn_spec__0(lean_object* v_a_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(8u);
v___x_75_ = l_BitVec_ofNat(v___x_74_, v_a_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt8_modn_spec__0___boxed(lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Nat_cast___at___00UInt8_modn_spec__0(v_a_76_);
lean_dec(v_a_76_);
return v_res_77_;
}
}
LEAN_EXPORT uint8_t l_UInt8_modn(uint8_t v_a_78_, lean_object* v_n_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_80_ = lean_uint8_to_nat(v_a_78_);
v___x_81_ = lean_nat_mod(v___x_80_, v_n_79_);
lean_dec(v___x_80_);
v___x_82_ = l_Nat_cast___at___00UInt8_modn_spec__0(v___x_81_);
lean_dec(v___x_81_);
v___x_83_ = lean_uint8_of_nat_mk(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_UInt8_modn___boxed(lean_object* v_a_84_, lean_object* v_n_85_){
_start:
{
uint8_t v_a_boxed_86_; uint8_t v_res_87_; lean_object* v_r_88_; 
v_a_boxed_86_ = lean_unbox(v_a_84_);
v_res_87_ = l_UInt8_modn(v_a_boxed_86_, v_n_85_);
lean_dec(v_n_85_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l_UInt8_land___boxed(lean_object* v_a_91_, lean_object* v_b_92_){
_start:
{
uint8_t v_a_boxed_93_; uint8_t v_b_boxed_94_; uint8_t v_res_95_; lean_object* v_r_96_; 
v_a_boxed_93_ = lean_unbox(v_a_91_);
v_b_boxed_94_ = lean_unbox(v_b_92_);
v_res_95_ = lean_uint8_land(v_a_boxed_93_, v_b_boxed_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT lean_object* l_UInt8_lor___boxed(lean_object* v_a_99_, lean_object* v_b_100_){
_start:
{
uint8_t v_a_boxed_101_; uint8_t v_b_boxed_102_; uint8_t v_res_103_; lean_object* v_r_104_; 
v_a_boxed_101_ = lean_unbox(v_a_99_);
v_b_boxed_102_ = lean_unbox(v_b_100_);
v_res_103_ = lean_uint8_lor(v_a_boxed_101_, v_b_boxed_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT lean_object* l_UInt8_xor___boxed(lean_object* v_a_107_, lean_object* v_b_108_){
_start:
{
uint8_t v_a_boxed_109_; uint8_t v_b_boxed_110_; uint8_t v_res_111_; lean_object* v_r_112_; 
v_a_boxed_109_ = lean_unbox(v_a_107_);
v_b_boxed_110_ = lean_unbox(v_b_108_);
v_res_111_ = lean_uint8_xor(v_a_boxed_109_, v_b_boxed_110_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT lean_object* l_UInt8_shiftLeft___boxed(lean_object* v_a_115_, lean_object* v_b_116_){
_start:
{
uint8_t v_a_boxed_117_; uint8_t v_b_boxed_118_; uint8_t v_res_119_; lean_object* v_r_120_; 
v_a_boxed_117_ = lean_unbox(v_a_115_);
v_b_boxed_118_ = lean_unbox(v_b_116_);
v_res_119_ = lean_uint8_shift_left(v_a_boxed_117_, v_b_boxed_118_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT lean_object* l_UInt8_shiftRight___boxed(lean_object* v_a_123_, lean_object* v_b_124_){
_start:
{
uint8_t v_a_boxed_125_; uint8_t v_b_boxed_126_; uint8_t v_res_127_; lean_object* v_r_128_; 
v_a_boxed_125_ = lean_unbox(v_a_123_);
v_b_boxed_126_ = lean_unbox(v_b_124_);
v_res_127_ = lean_uint8_shift_right(v_a_boxed_125_, v_b_boxed_126_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT lean_object* l_UInt8_complement___boxed(lean_object* v_a_144_){
_start:
{
uint8_t v_a_boxed_145_; uint8_t v_res_146_; lean_object* v_r_147_; 
v_a_boxed_145_ = lean_unbox(v_a_144_);
v_res_146_ = lean_uint8_complement(v_a_boxed_145_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_UInt8_neg___boxed(lean_object* v_a_149_){
_start:
{
uint8_t v_a_boxed_150_; uint8_t v_res_151_; lean_object* v_r_152_; 
v_a_boxed_150_ = lean_unbox(v_a_149_);
v_res_151_ = lean_uint8_neg(v_a_boxed_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT lean_object* l_Bool_toUInt8___boxed(lean_object* v_b_168_){
_start:
{
uint8_t v_b_boxed_169_; uint8_t v_res_170_; lean_object* v_r_171_; 
v_b_boxed_169_ = lean_unbox(v_b_168_);
v_res_170_ = lean_bool_to_uint8(v_b_boxed_169_);
v_r_171_ = lean_box(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT uint8_t l_instMaxUInt8___lam__0(uint8_t v_x_172_, uint8_t v_y_173_){
_start:
{
uint8_t v___x_174_; 
v___x_174_ = lean_uint8_dec_le(v_x_172_, v_y_173_);
if (v___x_174_ == 0)
{
return v_x_172_;
}
else
{
return v_y_173_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxUInt8___lam__0___boxed(lean_object* v_x_175_, lean_object* v_y_176_){
_start:
{
uint8_t v_x_boxed_177_; uint8_t v_y_boxed_178_; uint8_t v_res_179_; lean_object* v_r_180_; 
v_x_boxed_177_ = lean_unbox(v_x_175_);
v_y_boxed_178_ = lean_unbox(v_y_176_);
v_res_179_ = l_instMaxUInt8___lam__0(v_x_boxed_177_, v_y_boxed_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT uint8_t l_instMinUInt8___lam__0(uint8_t v_x_183_, uint8_t v_y_184_){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = lean_uint8_dec_le(v_x_183_, v_y_184_);
if (v___x_185_ == 0)
{
return v_y_184_;
}
else
{
return v_x_183_;
}
}
}
LEAN_EXPORT lean_object* l_instMinUInt8___lam__0___boxed(lean_object* v_x_186_, lean_object* v_y_187_){
_start:
{
uint8_t v_x_boxed_188_; uint8_t v_y_boxed_189_; uint8_t v_res_190_; lean_object* v_r_191_; 
v_x_boxed_188_ = lean_unbox(v_x_186_);
v_y_boxed_189_ = lean_unbox(v_y_187_);
v_res_190_ = l_instMinUInt8___lam__0(v_x_boxed_188_, v_y_boxed_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint8_t l_UInt8_toAsciiLower(uint8_t v_b_194_){
_start:
{
uint8_t v___x_195_; uint8_t v___x_196_; uint8_t v___x_197_; uint8_t v___x_198_; uint8_t v___x_199_; uint8_t v___x_200_; uint8_t v___x_201_; uint8_t v___x_202_; 
v___x_195_ = 65;
v___x_196_ = lean_uint8_sub(v_b_194_, v___x_195_);
v___x_197_ = 26;
v___x_198_ = lean_uint8_dec_lt(v___x_196_, v___x_197_);
v___x_199_ = lean_bool_to_uint8(v___x_198_);
v___x_200_ = 5;
v___x_201_ = lean_uint8_shift_left(v___x_199_, v___x_200_);
v___x_202_ = lean_uint8_add(v_b_194_, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toAsciiLower___boxed(lean_object* v_b_203_){
_start:
{
uint8_t v_b_boxed_204_; uint8_t v_res_205_; lean_object* v_r_206_; 
v_b_boxed_204_ = lean_unbox(v_b_203_);
v_res_205_ = l_UInt8_toAsciiLower(v_b_boxed_204_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT uint8_t l_UInt8_toAsciiUpper(uint8_t v_b_207_){
_start:
{
uint8_t v___x_208_; uint8_t v___x_209_; uint8_t v___x_210_; uint8_t v___x_211_; uint8_t v___x_212_; uint8_t v___x_213_; uint8_t v___x_214_; uint8_t v___x_215_; 
v___x_208_ = 97;
v___x_209_ = lean_uint8_sub(v_b_207_, v___x_208_);
v___x_210_ = 26;
v___x_211_ = lean_uint8_dec_lt(v___x_209_, v___x_210_);
v___x_212_ = lean_bool_to_uint8(v___x_211_);
v___x_213_ = 5;
v___x_214_ = lean_uint8_shift_left(v___x_212_, v___x_213_);
v___x_215_ = lean_uint8_sub(v_b_207_, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toAsciiUpper___boxed(lean_object* v_b_216_){
_start:
{
uint8_t v_b_boxed_217_; uint8_t v_res_218_; lean_object* v_r_219_; 
v_b_boxed_217_ = lean_unbox(v_b_216_);
v_res_218_ = l_UInt8_toAsciiUpper(v_b_boxed_217_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
LEAN_EXPORT uint16_t l_UInt16_ofFin(lean_object* v_a_220_){
_start:
{
uint16_t v___x_221_; 
v___x_221_ = lean_uint16_of_nat_mk(v_a_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofFin___boxed(lean_object* v_a_222_){
_start:
{
uint16_t v_res_223_; lean_object* v_r_224_; 
v_res_223_ = l_UInt16_ofFin(v_a_222_);
v_r_224_ = lean_box(v_res_223_);
return v_r_224_;
}
}
static lean_object* _init_l_UInt16_ofInt___closed__0(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_unsigned_to_nat(16u);
v___x_226_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_227_ = l_Int_pow(v___x_226_, v___x_225_);
return v___x_227_;
}
}
LEAN_EXPORT uint16_t l_UInt16_ofInt(lean_object* v_x_228_){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint16_t v___x_232_; 
v___x_229_ = lean_obj_once(&l_UInt16_ofInt___closed__0, &l_UInt16_ofInt___closed__0_once, _init_l_UInt16_ofInt___closed__0);
v___x_230_ = lean_int_emod(v_x_228_, v___x_229_);
v___x_231_ = l_Int_toNat(v___x_230_);
lean_dec(v___x_230_);
v___x_232_ = lean_uint16_of_nat(v___x_231_);
lean_dec(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofInt___boxed(lean_object* v_x_233_){
_start:
{
uint16_t v_res_234_; lean_object* v_r_235_; 
v_res_234_ = l_UInt16_ofInt(v_x_233_);
lean_dec(v_x_233_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT lean_object* l_UInt16_add___boxed(lean_object* v_a_238_, lean_object* v_b_239_){
_start:
{
uint16_t v_a_boxed_240_; uint16_t v_b_boxed_241_; uint16_t v_res_242_; lean_object* v_r_243_; 
v_a_boxed_240_ = lean_unbox(v_a_238_);
v_b_boxed_241_ = lean_unbox(v_b_239_);
v_res_242_ = lean_uint16_add(v_a_boxed_240_, v_b_boxed_241_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT lean_object* l_UInt16_sub___boxed(lean_object* v_a_246_, lean_object* v_b_247_){
_start:
{
uint16_t v_a_boxed_248_; uint16_t v_b_boxed_249_; uint16_t v_res_250_; lean_object* v_r_251_; 
v_a_boxed_248_ = lean_unbox(v_a_246_);
v_b_boxed_249_ = lean_unbox(v_b_247_);
v_res_250_ = lean_uint16_sub(v_a_boxed_248_, v_b_boxed_249_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT lean_object* l_UInt16_mul___boxed(lean_object* v_a_254_, lean_object* v_b_255_){
_start:
{
uint16_t v_a_boxed_256_; uint16_t v_b_boxed_257_; uint16_t v_res_258_; lean_object* v_r_259_; 
v_a_boxed_256_ = lean_unbox(v_a_254_);
v_b_boxed_257_ = lean_unbox(v_b_255_);
v_res_258_ = lean_uint16_mul(v_a_boxed_256_, v_b_boxed_257_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_UInt16_div___boxed(lean_object* v_a_262_, lean_object* v_b_263_){
_start:
{
uint16_t v_a_boxed_264_; uint16_t v_b_boxed_265_; uint16_t v_res_266_; lean_object* v_r_267_; 
v_a_boxed_264_ = lean_unbox(v_a_262_);
v_b_boxed_265_ = lean_unbox(v_b_263_);
v_res_266_ = lean_uint16_div(v_a_boxed_264_, v_b_boxed_265_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT uint16_t l_UInt16_pow(uint16_t v_x_268_, lean_object* v_n_269_){
_start:
{
lean_object* v_zero_270_; uint8_t v_isZero_271_; 
v_zero_270_ = lean_unsigned_to_nat(0u);
v_isZero_271_ = lean_nat_dec_eq(v_n_269_, v_zero_270_);
if (v_isZero_271_ == 1)
{
uint16_t v___x_272_; 
v___x_272_ = 1;
return v___x_272_;
}
else
{
lean_object* v_one_273_; lean_object* v_n_274_; uint16_t v___x_275_; uint16_t v___x_276_; 
v_one_273_ = lean_unsigned_to_nat(1u);
v_n_274_ = lean_nat_sub(v_n_269_, v_one_273_);
v___x_275_ = l_UInt16_pow(v_x_268_, v_n_274_);
lean_dec(v_n_274_);
v___x_276_ = lean_uint16_mul(v___x_275_, v_x_268_);
return v___x_276_;
}
}
}
LEAN_EXPORT lean_object* l_UInt16_pow___boxed(lean_object* v_x_277_, lean_object* v_n_278_){
_start:
{
uint16_t v_x_boxed_279_; uint16_t v_res_280_; lean_object* v_r_281_; 
v_x_boxed_279_ = lean_unbox(v_x_277_);
v_res_280_ = l_UInt16_pow(v_x_boxed_279_, v_n_278_);
lean_dec(v_n_278_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT lean_object* l_UInt16_mod___boxed(lean_object* v_a_284_, lean_object* v_b_285_){
_start:
{
uint16_t v_a_boxed_286_; uint16_t v_b_boxed_287_; uint16_t v_res_288_; lean_object* v_r_289_; 
v_a_boxed_286_ = lean_unbox(v_a_284_);
v_b_boxed_287_ = lean_unbox(v_b_285_);
v_res_288_ = lean_uint16_mod(v_a_boxed_286_, v_b_boxed_287_);
v_r_289_ = lean_box(v_res_288_);
return v_r_289_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt16_modn_spec__0(lean_object* v_a_290_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(16u);
v___x_292_ = l_BitVec_ofNat(v___x_291_, v_a_290_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt16_modn_spec__0___boxed(lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Nat_cast___at___00UInt16_modn_spec__0(v_a_293_);
lean_dec(v_a_293_);
return v_res_294_;
}
}
LEAN_EXPORT uint16_t l_UInt16_modn(uint16_t v_a_295_, lean_object* v_n_296_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint16_t v___x_300_; 
v___x_297_ = lean_uint16_to_nat(v_a_295_);
v___x_298_ = lean_nat_mod(v___x_297_, v_n_296_);
lean_dec(v___x_297_);
v___x_299_ = l_Nat_cast___at___00UInt16_modn_spec__0(v___x_298_);
lean_dec(v___x_298_);
v___x_300_ = lean_uint16_of_nat_mk(v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_UInt16_modn___boxed(lean_object* v_a_301_, lean_object* v_n_302_){
_start:
{
uint16_t v_a_boxed_303_; uint16_t v_res_304_; lean_object* v_r_305_; 
v_a_boxed_303_ = lean_unbox(v_a_301_);
v_res_304_ = l_UInt16_modn(v_a_boxed_303_, v_n_302_);
lean_dec(v_n_302_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT lean_object* l_UInt16_land___boxed(lean_object* v_a_308_, lean_object* v_b_309_){
_start:
{
uint16_t v_a_boxed_310_; uint16_t v_b_boxed_311_; uint16_t v_res_312_; lean_object* v_r_313_; 
v_a_boxed_310_ = lean_unbox(v_a_308_);
v_b_boxed_311_ = lean_unbox(v_b_309_);
v_res_312_ = lean_uint16_land(v_a_boxed_310_, v_b_boxed_311_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT lean_object* l_UInt16_lor___boxed(lean_object* v_a_316_, lean_object* v_b_317_){
_start:
{
uint16_t v_a_boxed_318_; uint16_t v_b_boxed_319_; uint16_t v_res_320_; lean_object* v_r_321_; 
v_a_boxed_318_ = lean_unbox(v_a_316_);
v_b_boxed_319_ = lean_unbox(v_b_317_);
v_res_320_ = lean_uint16_lor(v_a_boxed_318_, v_b_boxed_319_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT lean_object* l_UInt16_xor___boxed(lean_object* v_a_324_, lean_object* v_b_325_){
_start:
{
uint16_t v_a_boxed_326_; uint16_t v_b_boxed_327_; uint16_t v_res_328_; lean_object* v_r_329_; 
v_a_boxed_326_ = lean_unbox(v_a_324_);
v_b_boxed_327_ = lean_unbox(v_b_325_);
v_res_328_ = lean_uint16_xor(v_a_boxed_326_, v_b_boxed_327_);
v_r_329_ = lean_box(v_res_328_);
return v_r_329_;
}
}
LEAN_EXPORT lean_object* l_UInt16_shiftLeft___boxed(lean_object* v_a_332_, lean_object* v_b_333_){
_start:
{
uint16_t v_a_boxed_334_; uint16_t v_b_boxed_335_; uint16_t v_res_336_; lean_object* v_r_337_; 
v_a_boxed_334_ = lean_unbox(v_a_332_);
v_b_boxed_335_ = lean_unbox(v_b_333_);
v_res_336_ = lean_uint16_shift_left(v_a_boxed_334_, v_b_boxed_335_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT lean_object* l_UInt16_shiftRight___boxed(lean_object* v_a_340_, lean_object* v_b_341_){
_start:
{
uint16_t v_a_boxed_342_; uint16_t v_b_boxed_343_; uint16_t v_res_344_; lean_object* v_r_345_; 
v_a_boxed_342_ = lean_unbox(v_a_340_);
v_b_boxed_343_ = lean_unbox(v_b_341_);
v_res_344_ = lean_uint16_shift_right(v_a_boxed_342_, v_b_boxed_343_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
static lean_object* _init_l_instLTUInt16(void){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = lean_box(0);
return v___x_360_;
}
}
static lean_object* _init_l_instLEUInt16(void){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_box(0);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_UInt16_complement___boxed(lean_object* v_a_363_){
_start:
{
uint16_t v_a_boxed_364_; uint16_t v_res_365_; lean_object* v_r_366_; 
v_a_boxed_364_ = lean_unbox(v_a_363_);
v_res_365_ = lean_uint16_complement(v_a_boxed_364_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
LEAN_EXPORT lean_object* l_UInt16_neg___boxed(lean_object* v_a_368_){
_start:
{
uint16_t v_a_boxed_369_; uint16_t v_res_370_; lean_object* v_r_371_; 
v_a_boxed_369_ = lean_unbox(v_a_368_);
v_res_370_ = lean_uint16_neg(v_a_boxed_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT lean_object* l_Bool_toUInt16___boxed(lean_object* v_b_387_){
_start:
{
uint8_t v_b_boxed_388_; uint16_t v_res_389_; lean_object* v_r_390_; 
v_b_boxed_388_ = lean_unbox(v_b_387_);
v_res_389_ = lean_bool_to_uint16(v_b_boxed_388_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_UInt16_decLt___aux__1(uint16_t v_a_391_, uint16_t v_b_392_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_393_ = lean_uint16_to_nat(v_a_391_);
v___x_394_ = lean_uint16_to_nat(v_b_392_);
v___x_395_ = lean_nat_dec_lt(v___x_393_, v___x_394_);
lean_dec(v___x_394_);
lean_dec(v___x_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_UInt16_decLt___aux__1___boxed(lean_object* v_a_396_, lean_object* v_b_397_){
_start:
{
uint16_t v_a_boxed_398_; uint16_t v_b_boxed_399_; uint8_t v_res_400_; lean_object* v_r_401_; 
v_a_boxed_398_ = lean_unbox(v_a_396_);
v_b_boxed_399_ = lean_unbox(v_b_397_);
v_res_400_ = l_UInt16_decLt___aux__1(v_a_boxed_398_, v_b_boxed_399_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT lean_object* l_UInt16_decLt___boxed(lean_object* v_a_404_, lean_object* v_b_405_){
_start:
{
uint16_t v_a_boxed_406_; uint16_t v_b_boxed_407_; uint8_t v_res_408_; lean_object* v_r_409_; 
v_a_boxed_406_ = lean_unbox(v_a_404_);
v_b_boxed_407_ = lean_unbox(v_b_405_);
v_res_408_ = lean_uint16_dec_lt(v_a_boxed_406_, v_b_boxed_407_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT uint8_t l_UInt16_decLe___aux__1(uint16_t v_a_410_, uint16_t v_b_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_412_ = lean_uint16_to_nat(v_a_410_);
v___x_413_ = lean_uint16_to_nat(v_b_411_);
v___x_414_ = lean_nat_dec_le(v___x_412_, v___x_413_);
lean_dec(v___x_413_);
lean_dec(v___x_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_UInt16_decLe___aux__1___boxed(lean_object* v_a_415_, lean_object* v_b_416_){
_start:
{
uint16_t v_a_boxed_417_; uint16_t v_b_boxed_418_; uint8_t v_res_419_; lean_object* v_r_420_; 
v_a_boxed_417_ = lean_unbox(v_a_415_);
v_b_boxed_418_ = lean_unbox(v_b_416_);
v_res_419_ = l_UInt16_decLe___aux__1(v_a_boxed_417_, v_b_boxed_418_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
LEAN_EXPORT lean_object* l_UInt16_decLe___boxed(lean_object* v_a_423_, lean_object* v_b_424_){
_start:
{
uint16_t v_a_boxed_425_; uint16_t v_b_boxed_426_; uint8_t v_res_427_; lean_object* v_r_428_; 
v_a_boxed_425_ = lean_unbox(v_a_423_);
v_b_boxed_426_ = lean_unbox(v_b_424_);
v_res_427_ = lean_uint16_dec_le(v_a_boxed_425_, v_b_boxed_426_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT uint16_t l_instMaxUInt16___lam__0(uint16_t v_x_429_, uint16_t v_y_430_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = lean_uint16_dec_le(v_x_429_, v_y_430_);
if (v___x_431_ == 0)
{
return v_x_429_;
}
else
{
return v_y_430_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxUInt16___lam__0___boxed(lean_object* v_x_432_, lean_object* v_y_433_){
_start:
{
uint16_t v_x_boxed_434_; uint16_t v_y_boxed_435_; uint16_t v_res_436_; lean_object* v_r_437_; 
v_x_boxed_434_ = lean_unbox(v_x_432_);
v_y_boxed_435_ = lean_unbox(v_y_433_);
v_res_436_ = l_instMaxUInt16___lam__0(v_x_boxed_434_, v_y_boxed_435_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT uint16_t l_instMinUInt16___lam__0(uint16_t v_x_440_, uint16_t v_y_441_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = lean_uint16_dec_le(v_x_440_, v_y_441_);
if (v___x_442_ == 0)
{
return v_y_441_;
}
else
{
return v_x_440_;
}
}
}
LEAN_EXPORT lean_object* l_instMinUInt16___lam__0___boxed(lean_object* v_x_443_, lean_object* v_y_444_){
_start:
{
uint16_t v_x_boxed_445_; uint16_t v_y_boxed_446_; uint16_t v_res_447_; lean_object* v_r_448_; 
v_x_boxed_445_ = lean_unbox(v_x_443_);
v_y_boxed_446_ = lean_unbox(v_y_444_);
v_res_447_ = l_instMinUInt16___lam__0(v_x_boxed_445_, v_y_boxed_446_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofFin(lean_object* v_a_451_){
_start:
{
uint32_t v___x_452_; 
v___x_452_ = lean_uint32_of_nat_mk(v_a_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofFin___boxed(lean_object* v_a_453_){
_start:
{
uint32_t v_res_454_; lean_object* v_r_455_; 
v_res_454_ = l_UInt32_ofFin(v_a_453_);
v_r_455_ = lean_box_uint32(v_res_454_);
return v_r_455_;
}
}
static lean_object* _init_l_UInt32_ofInt___closed__0(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_unsigned_to_nat(32u);
v___x_457_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_458_ = l_Int_pow(v___x_457_, v___x_456_);
return v___x_458_;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofInt(lean_object* v_x_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint32_t v___x_463_; 
v___x_460_ = lean_obj_once(&l_UInt32_ofInt___closed__0, &l_UInt32_ofInt___closed__0_once, _init_l_UInt32_ofInt___closed__0);
v___x_461_ = lean_int_emod(v_x_459_, v___x_460_);
v___x_462_ = l_Int_toNat(v___x_461_);
lean_dec(v___x_461_);
v___x_463_ = lean_uint32_of_nat(v___x_462_);
lean_dec(v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofInt___boxed(lean_object* v_x_464_){
_start:
{
uint32_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_UInt32_ofInt(v_x_464_);
lean_dec(v_x_464_);
v_r_466_ = lean_box_uint32(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT lean_object* l_UInt32_mul___boxed(lean_object* v_a_469_, lean_object* v_b_470_){
_start:
{
uint32_t v_a_boxed_471_; uint32_t v_b_boxed_472_; uint32_t v_res_473_; lean_object* v_r_474_; 
v_a_boxed_471_ = lean_unbox_uint32(v_a_469_);
lean_dec(v_a_469_);
v_b_boxed_472_ = lean_unbox_uint32(v_b_470_);
lean_dec(v_b_470_);
v_res_473_ = lean_uint32_mul(v_a_boxed_471_, v_b_boxed_472_);
v_r_474_ = lean_box_uint32(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT lean_object* l_UInt32_div___boxed(lean_object* v_a_477_, lean_object* v_b_478_){
_start:
{
uint32_t v_a_boxed_479_; uint32_t v_b_boxed_480_; uint32_t v_res_481_; lean_object* v_r_482_; 
v_a_boxed_479_ = lean_unbox_uint32(v_a_477_);
lean_dec(v_a_477_);
v_b_boxed_480_ = lean_unbox_uint32(v_b_478_);
lean_dec(v_b_478_);
v_res_481_ = lean_uint32_div(v_a_boxed_479_, v_b_boxed_480_);
v_r_482_ = lean_box_uint32(v_res_481_);
return v_r_482_;
}
}
LEAN_EXPORT uint32_t l_UInt32_pow(uint32_t v_x_483_, lean_object* v_n_484_){
_start:
{
lean_object* v_zero_485_; uint8_t v_isZero_486_; 
v_zero_485_ = lean_unsigned_to_nat(0u);
v_isZero_486_ = lean_nat_dec_eq(v_n_484_, v_zero_485_);
if (v_isZero_486_ == 1)
{
uint32_t v___x_487_; 
v___x_487_ = 1;
return v___x_487_;
}
else
{
lean_object* v_one_488_; lean_object* v_n_489_; uint32_t v___x_490_; uint32_t v___x_491_; 
v_one_488_ = lean_unsigned_to_nat(1u);
v_n_489_ = lean_nat_sub(v_n_484_, v_one_488_);
v___x_490_ = l_UInt32_pow(v_x_483_, v_n_489_);
lean_dec(v_n_489_);
v___x_491_ = lean_uint32_mul(v___x_490_, v_x_483_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_UInt32_pow___boxed(lean_object* v_x_492_, lean_object* v_n_493_){
_start:
{
uint32_t v_x_boxed_494_; uint32_t v_res_495_; lean_object* v_r_496_; 
v_x_boxed_494_ = lean_unbox_uint32(v_x_492_);
lean_dec(v_x_492_);
v_res_495_ = l_UInt32_pow(v_x_boxed_494_, v_n_493_);
lean_dec(v_n_493_);
v_r_496_ = lean_box_uint32(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT lean_object* l_UInt32_mod___boxed(lean_object* v_a_499_, lean_object* v_b_500_){
_start:
{
uint32_t v_a_boxed_501_; uint32_t v_b_boxed_502_; uint32_t v_res_503_; lean_object* v_r_504_; 
v_a_boxed_501_ = lean_unbox_uint32(v_a_499_);
lean_dec(v_a_499_);
v_b_boxed_502_ = lean_unbox_uint32(v_b_500_);
lean_dec(v_b_500_);
v_res_503_ = lean_uint32_mod(v_a_boxed_501_, v_b_boxed_502_);
v_r_504_ = lean_box_uint32(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt32_modn_spec__0(lean_object* v_a_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(32u);
v___x_507_ = l_BitVec_ofNat(v___x_506_, v_a_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt32_modn_spec__0___boxed(lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Nat_cast___at___00UInt32_modn_spec__0(v_a_508_);
lean_dec(v_a_508_);
return v_res_509_;
}
}
LEAN_EXPORT uint32_t l_UInt32_modn(uint32_t v_a_510_, lean_object* v_n_511_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; uint32_t v___x_515_; 
v___x_512_ = lean_uint32_to_nat(v_a_510_);
v___x_513_ = lean_nat_mod(v___x_512_, v_n_511_);
lean_dec(v___x_512_);
v___x_514_ = l_Nat_cast___at___00UInt32_modn_spec__0(v___x_513_);
lean_dec(v___x_513_);
v___x_515_ = lean_uint32_of_nat_mk(v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_UInt32_modn___boxed(lean_object* v_a_516_, lean_object* v_n_517_){
_start:
{
uint32_t v_a_boxed_518_; uint32_t v_res_519_; lean_object* v_r_520_; 
v_a_boxed_518_ = lean_unbox_uint32(v_a_516_);
lean_dec(v_a_516_);
v_res_519_ = l_UInt32_modn(v_a_boxed_518_, v_n_517_);
lean_dec(v_n_517_);
v_r_520_ = lean_box_uint32(v_res_519_);
return v_r_520_;
}
}
LEAN_EXPORT lean_object* l_UInt32_land___boxed(lean_object* v_a_523_, lean_object* v_b_524_){
_start:
{
uint32_t v_a_boxed_525_; uint32_t v_b_boxed_526_; uint32_t v_res_527_; lean_object* v_r_528_; 
v_a_boxed_525_ = lean_unbox_uint32(v_a_523_);
lean_dec(v_a_523_);
v_b_boxed_526_ = lean_unbox_uint32(v_b_524_);
lean_dec(v_b_524_);
v_res_527_ = lean_uint32_land(v_a_boxed_525_, v_b_boxed_526_);
v_r_528_ = lean_box_uint32(v_res_527_);
return v_r_528_;
}
}
LEAN_EXPORT lean_object* l_UInt32_lor___boxed(lean_object* v_a_531_, lean_object* v_b_532_){
_start:
{
uint32_t v_a_boxed_533_; uint32_t v_b_boxed_534_; uint32_t v_res_535_; lean_object* v_r_536_; 
v_a_boxed_533_ = lean_unbox_uint32(v_a_531_);
lean_dec(v_a_531_);
v_b_boxed_534_ = lean_unbox_uint32(v_b_532_);
lean_dec(v_b_532_);
v_res_535_ = lean_uint32_lor(v_a_boxed_533_, v_b_boxed_534_);
v_r_536_ = lean_box_uint32(v_res_535_);
return v_r_536_;
}
}
LEAN_EXPORT lean_object* l_UInt32_xor___boxed(lean_object* v_a_539_, lean_object* v_b_540_){
_start:
{
uint32_t v_a_boxed_541_; uint32_t v_b_boxed_542_; uint32_t v_res_543_; lean_object* v_r_544_; 
v_a_boxed_541_ = lean_unbox_uint32(v_a_539_);
lean_dec(v_a_539_);
v_b_boxed_542_ = lean_unbox_uint32(v_b_540_);
lean_dec(v_b_540_);
v_res_543_ = lean_uint32_xor(v_a_boxed_541_, v_b_boxed_542_);
v_r_544_ = lean_box_uint32(v_res_543_);
return v_r_544_;
}
}
LEAN_EXPORT lean_object* l_UInt32_shiftLeft___boxed(lean_object* v_a_547_, lean_object* v_b_548_){
_start:
{
uint32_t v_a_boxed_549_; uint32_t v_b_boxed_550_; uint32_t v_res_551_; lean_object* v_r_552_; 
v_a_boxed_549_ = lean_unbox_uint32(v_a_547_);
lean_dec(v_a_547_);
v_b_boxed_550_ = lean_unbox_uint32(v_b_548_);
lean_dec(v_b_548_);
v_res_551_ = lean_uint32_shift_left(v_a_boxed_549_, v_b_boxed_550_);
v_r_552_ = lean_box_uint32(v_res_551_);
return v_r_552_;
}
}
LEAN_EXPORT lean_object* l_UInt32_shiftRight___boxed(lean_object* v_a_555_, lean_object* v_b_556_){
_start:
{
uint32_t v_a_boxed_557_; uint32_t v_b_boxed_558_; uint32_t v_res_559_; lean_object* v_r_560_; 
v_a_boxed_557_ = lean_unbox_uint32(v_a_555_);
lean_dec(v_a_555_);
v_b_boxed_558_ = lean_unbox_uint32(v_b_556_);
lean_dec(v_b_556_);
v_res_559_ = lean_uint32_shift_right(v_a_boxed_557_, v_b_boxed_558_);
v_r_560_ = lean_box_uint32(v_res_559_);
return v_r_560_;
}
}
LEAN_EXPORT lean_object* l_UInt32_complement___boxed(lean_object* v_a_572_){
_start:
{
uint32_t v_a_boxed_573_; uint32_t v_res_574_; lean_object* v_r_575_; 
v_a_boxed_573_ = lean_unbox_uint32(v_a_572_);
lean_dec(v_a_572_);
v_res_574_ = lean_uint32_complement(v_a_boxed_573_);
v_r_575_ = lean_box_uint32(v_res_574_);
return v_r_575_;
}
}
LEAN_EXPORT lean_object* l_UInt32_neg___boxed(lean_object* v_a_577_){
_start:
{
uint32_t v_a_boxed_578_; uint32_t v_res_579_; lean_object* v_r_580_; 
v_a_boxed_578_ = lean_unbox_uint32(v_a_577_);
lean_dec(v_a_577_);
v_res_579_ = lean_uint32_neg(v_a_boxed_578_);
v_r_580_ = lean_box_uint32(v_res_579_);
return v_r_580_;
}
}
LEAN_EXPORT lean_object* l_Bool_toUInt32___boxed(lean_object* v_b_596_){
_start:
{
uint8_t v_b_boxed_597_; uint32_t v_res_598_; lean_object* v_r_599_; 
v_b_boxed_597_ = lean_unbox(v_b_596_);
v_res_598_ = lean_bool_to_uint32(v_b_boxed_597_);
v_r_599_ = lean_box_uint32(v_res_598_);
return v_r_599_;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofFin(lean_object* v_a_600_){
_start:
{
uint64_t v___x_601_; 
v___x_601_ = lean_uint64_of_nat_mk(v_a_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofFin___boxed(lean_object* v_a_602_){
_start:
{
uint64_t v_res_603_; lean_object* v_r_604_; 
v_res_603_ = l_UInt64_ofFin(v_a_602_);
v_r_604_ = lean_box_uint64(v_res_603_);
return v_r_604_;
}
}
static lean_object* _init_l_UInt64_ofInt___closed__0(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_unsigned_to_nat(64u);
v___x_606_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_607_ = l_Int_pow(v___x_606_, v___x_605_);
return v___x_607_;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofInt(lean_object* v_x_608_){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint64_t v___x_612_; 
v___x_609_ = lean_obj_once(&l_UInt64_ofInt___closed__0, &l_UInt64_ofInt___closed__0_once, _init_l_UInt64_ofInt___closed__0);
v___x_610_ = lean_int_emod(v_x_608_, v___x_609_);
v___x_611_ = l_Int_toNat(v___x_610_);
lean_dec(v___x_610_);
v___x_612_ = lean_uint64_of_nat(v___x_611_);
lean_dec(v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofInt___boxed(lean_object* v_x_613_){
_start:
{
uint64_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = l_UInt64_ofInt(v_x_613_);
lean_dec(v_x_613_);
v_r_615_ = lean_box_uint64(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT lean_object* l_UInt64_add___boxed(lean_object* v_a_618_, lean_object* v_b_619_){
_start:
{
uint64_t v_a_boxed_620_; uint64_t v_b_boxed_621_; uint64_t v_res_622_; lean_object* v_r_623_; 
v_a_boxed_620_ = lean_unbox_uint64(v_a_618_);
lean_dec_ref(v_a_618_);
v_b_boxed_621_ = lean_unbox_uint64(v_b_619_);
lean_dec_ref(v_b_619_);
v_res_622_ = lean_uint64_add(v_a_boxed_620_, v_b_boxed_621_);
v_r_623_ = lean_box_uint64(v_res_622_);
return v_r_623_;
}
}
LEAN_EXPORT lean_object* l_UInt64_sub___boxed(lean_object* v_a_626_, lean_object* v_b_627_){
_start:
{
uint64_t v_a_boxed_628_; uint64_t v_b_boxed_629_; uint64_t v_res_630_; lean_object* v_r_631_; 
v_a_boxed_628_ = lean_unbox_uint64(v_a_626_);
lean_dec_ref(v_a_626_);
v_b_boxed_629_ = lean_unbox_uint64(v_b_627_);
lean_dec_ref(v_b_627_);
v_res_630_ = lean_uint64_sub(v_a_boxed_628_, v_b_boxed_629_);
v_r_631_ = lean_box_uint64(v_res_630_);
return v_r_631_;
}
}
LEAN_EXPORT lean_object* l_UInt64_mul___boxed(lean_object* v_a_634_, lean_object* v_b_635_){
_start:
{
uint64_t v_a_boxed_636_; uint64_t v_b_boxed_637_; uint64_t v_res_638_; lean_object* v_r_639_; 
v_a_boxed_636_ = lean_unbox_uint64(v_a_634_);
lean_dec_ref(v_a_634_);
v_b_boxed_637_ = lean_unbox_uint64(v_b_635_);
lean_dec_ref(v_b_635_);
v_res_638_ = lean_uint64_mul(v_a_boxed_636_, v_b_boxed_637_);
v_r_639_ = lean_box_uint64(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT lean_object* l_UInt64_div___boxed(lean_object* v_a_642_, lean_object* v_b_643_){
_start:
{
uint64_t v_a_boxed_644_; uint64_t v_b_boxed_645_; uint64_t v_res_646_; lean_object* v_r_647_; 
v_a_boxed_644_ = lean_unbox_uint64(v_a_642_);
lean_dec_ref(v_a_642_);
v_b_boxed_645_ = lean_unbox_uint64(v_b_643_);
lean_dec_ref(v_b_643_);
v_res_646_ = lean_uint64_div(v_a_boxed_644_, v_b_boxed_645_);
v_r_647_ = lean_box_uint64(v_res_646_);
return v_r_647_;
}
}
LEAN_EXPORT uint64_t l_UInt64_pow(uint64_t v_x_648_, lean_object* v_n_649_){
_start:
{
lean_object* v_zero_650_; uint8_t v_isZero_651_; 
v_zero_650_ = lean_unsigned_to_nat(0u);
v_isZero_651_ = lean_nat_dec_eq(v_n_649_, v_zero_650_);
if (v_isZero_651_ == 1)
{
uint64_t v___x_652_; 
v___x_652_ = 1ULL;
return v___x_652_;
}
else
{
lean_object* v_one_653_; lean_object* v_n_654_; uint64_t v___x_655_; uint64_t v___x_656_; 
v_one_653_ = lean_unsigned_to_nat(1u);
v_n_654_ = lean_nat_sub(v_n_649_, v_one_653_);
v___x_655_ = l_UInt64_pow(v_x_648_, v_n_654_);
lean_dec(v_n_654_);
v___x_656_ = lean_uint64_mul(v___x_655_, v_x_648_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_pow___boxed(lean_object* v_x_657_, lean_object* v_n_658_){
_start:
{
uint64_t v_x_boxed_659_; uint64_t v_res_660_; lean_object* v_r_661_; 
v_x_boxed_659_ = lean_unbox_uint64(v_x_657_);
lean_dec_ref(v_x_657_);
v_res_660_ = l_UInt64_pow(v_x_boxed_659_, v_n_658_);
lean_dec(v_n_658_);
v_r_661_ = lean_box_uint64(v_res_660_);
return v_r_661_;
}
}
LEAN_EXPORT lean_object* l_UInt64_mod___boxed(lean_object* v_a_664_, lean_object* v_b_665_){
_start:
{
uint64_t v_a_boxed_666_; uint64_t v_b_boxed_667_; uint64_t v_res_668_; lean_object* v_r_669_; 
v_a_boxed_666_ = lean_unbox_uint64(v_a_664_);
lean_dec_ref(v_a_664_);
v_b_boxed_667_ = lean_unbox_uint64(v_b_665_);
lean_dec_ref(v_b_665_);
v_res_668_ = lean_uint64_mod(v_a_boxed_666_, v_b_boxed_667_);
v_r_669_ = lean_box_uint64(v_res_668_);
return v_r_669_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt64_modn_spec__0(lean_object* v_a_670_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_unsigned_to_nat(64u);
v___x_672_ = l_BitVec_ofNat(v___x_671_, v_a_670_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt64_modn_spec__0___boxed(lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Nat_cast___at___00UInt64_modn_spec__0(v_a_673_);
lean_dec(v_a_673_);
return v_res_674_;
}
}
LEAN_EXPORT uint64_t l_UInt64_modn(uint64_t v_a_675_, lean_object* v_n_676_){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint64_t v___x_680_; 
v___x_677_ = lean_uint64_to_nat(v_a_675_);
v___x_678_ = lean_nat_mod(v___x_677_, v_n_676_);
lean_dec(v___x_677_);
v___x_679_ = l_Nat_cast___at___00UInt64_modn_spec__0(v___x_678_);
lean_dec(v___x_678_);
v___x_680_ = lean_uint64_of_nat_mk(v___x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_UInt64_modn___boxed(lean_object* v_a_681_, lean_object* v_n_682_){
_start:
{
uint64_t v_a_boxed_683_; uint64_t v_res_684_; lean_object* v_r_685_; 
v_a_boxed_683_ = lean_unbox_uint64(v_a_681_);
lean_dec_ref(v_a_681_);
v_res_684_ = l_UInt64_modn(v_a_boxed_683_, v_n_682_);
lean_dec(v_n_682_);
v_r_685_ = lean_box_uint64(v_res_684_);
return v_r_685_;
}
}
LEAN_EXPORT lean_object* l_UInt64_land___boxed(lean_object* v_a_688_, lean_object* v_b_689_){
_start:
{
uint64_t v_a_boxed_690_; uint64_t v_b_boxed_691_; uint64_t v_res_692_; lean_object* v_r_693_; 
v_a_boxed_690_ = lean_unbox_uint64(v_a_688_);
lean_dec_ref(v_a_688_);
v_b_boxed_691_ = lean_unbox_uint64(v_b_689_);
lean_dec_ref(v_b_689_);
v_res_692_ = lean_uint64_land(v_a_boxed_690_, v_b_boxed_691_);
v_r_693_ = lean_box_uint64(v_res_692_);
return v_r_693_;
}
}
LEAN_EXPORT lean_object* l_UInt64_lor___boxed(lean_object* v_a_696_, lean_object* v_b_697_){
_start:
{
uint64_t v_a_boxed_698_; uint64_t v_b_boxed_699_; uint64_t v_res_700_; lean_object* v_r_701_; 
v_a_boxed_698_ = lean_unbox_uint64(v_a_696_);
lean_dec_ref(v_a_696_);
v_b_boxed_699_ = lean_unbox_uint64(v_b_697_);
lean_dec_ref(v_b_697_);
v_res_700_ = lean_uint64_lor(v_a_boxed_698_, v_b_boxed_699_);
v_r_701_ = lean_box_uint64(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT lean_object* l_UInt64_xor___boxed(lean_object* v_a_704_, lean_object* v_b_705_){
_start:
{
uint64_t v_a_boxed_706_; uint64_t v_b_boxed_707_; uint64_t v_res_708_; lean_object* v_r_709_; 
v_a_boxed_706_ = lean_unbox_uint64(v_a_704_);
lean_dec_ref(v_a_704_);
v_b_boxed_707_ = lean_unbox_uint64(v_b_705_);
lean_dec_ref(v_b_705_);
v_res_708_ = lean_uint64_xor(v_a_boxed_706_, v_b_boxed_707_);
v_r_709_ = lean_box_uint64(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l_UInt64_shiftLeft___boxed(lean_object* v_a_712_, lean_object* v_b_713_){
_start:
{
uint64_t v_a_boxed_714_; uint64_t v_b_boxed_715_; uint64_t v_res_716_; lean_object* v_r_717_; 
v_a_boxed_714_ = lean_unbox_uint64(v_a_712_);
lean_dec_ref(v_a_712_);
v_b_boxed_715_ = lean_unbox_uint64(v_b_713_);
lean_dec_ref(v_b_713_);
v_res_716_ = lean_uint64_shift_left(v_a_boxed_714_, v_b_boxed_715_);
v_r_717_ = lean_box_uint64(v_res_716_);
return v_r_717_;
}
}
LEAN_EXPORT lean_object* l_UInt64_shiftRight___boxed(lean_object* v_a_720_, lean_object* v_b_721_){
_start:
{
uint64_t v_a_boxed_722_; uint64_t v_b_boxed_723_; uint64_t v_res_724_; lean_object* v_r_725_; 
v_a_boxed_722_ = lean_unbox_uint64(v_a_720_);
lean_dec_ref(v_a_720_);
v_b_boxed_723_ = lean_unbox_uint64(v_b_721_);
lean_dec_ref(v_b_721_);
v_res_724_ = lean_uint64_shift_right(v_a_boxed_722_, v_b_boxed_723_);
v_r_725_ = lean_box_uint64(v_res_724_);
return v_r_725_;
}
}
static lean_object* _init_l_instLTUInt64(void){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = lean_box(0);
return v___x_740_;
}
}
static lean_object* _init_l_instLEUInt64(void){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = lean_box(0);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_UInt64_complement___boxed(lean_object* v_a_743_){
_start:
{
uint64_t v_a_boxed_744_; uint64_t v_res_745_; lean_object* v_r_746_; 
v_a_boxed_744_ = lean_unbox_uint64(v_a_743_);
lean_dec_ref(v_a_743_);
v_res_745_ = lean_uint64_complement(v_a_boxed_744_);
v_r_746_ = lean_box_uint64(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT lean_object* l_UInt64_neg___boxed(lean_object* v_a_748_){
_start:
{
uint64_t v_a_boxed_749_; uint64_t v_res_750_; lean_object* v_r_751_; 
v_a_boxed_749_ = lean_unbox_uint64(v_a_748_);
lean_dec_ref(v_a_748_);
v_res_750_ = lean_uint64_neg(v_a_boxed_749_);
v_r_751_ = lean_box_uint64(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT lean_object* l_Bool_toUInt64___boxed(lean_object* v_b_767_){
_start:
{
uint8_t v_b_boxed_768_; uint64_t v_res_769_; lean_object* v_r_770_; 
v_b_boxed_768_ = lean_unbox(v_b_767_);
v_res_769_ = lean_bool_to_uint64(v_b_boxed_768_);
v_r_770_ = lean_box_uint64(v_res_769_);
return v_r_770_;
}
}
LEAN_EXPORT uint8_t l_UInt64_decLt___aux__1(uint64_t v_a_771_, uint64_t v_b_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_773_ = lean_uint64_to_nat(v_a_771_);
v___x_774_ = lean_uint64_to_nat(v_b_772_);
v___x_775_ = lean_nat_dec_lt(v___x_773_, v___x_774_);
lean_dec(v___x_774_);
lean_dec(v___x_773_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_UInt64_decLt___aux__1___boxed(lean_object* v_a_776_, lean_object* v_b_777_){
_start:
{
uint64_t v_a_boxed_778_; uint64_t v_b_boxed_779_; uint8_t v_res_780_; lean_object* v_r_781_; 
v_a_boxed_778_ = lean_unbox_uint64(v_a_776_);
lean_dec_ref(v_a_776_);
v_b_boxed_779_ = lean_unbox_uint64(v_b_777_);
lean_dec_ref(v_b_777_);
v_res_780_ = l_UInt64_decLt___aux__1(v_a_boxed_778_, v_b_boxed_779_);
v_r_781_ = lean_box(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT lean_object* l_UInt64_decLt___boxed(lean_object* v_a_784_, lean_object* v_b_785_){
_start:
{
uint64_t v_a_boxed_786_; uint64_t v_b_boxed_787_; uint8_t v_res_788_; lean_object* v_r_789_; 
v_a_boxed_786_ = lean_unbox_uint64(v_a_784_);
lean_dec_ref(v_a_784_);
v_b_boxed_787_ = lean_unbox_uint64(v_b_785_);
lean_dec_ref(v_b_785_);
v_res_788_ = lean_uint64_dec_lt(v_a_boxed_786_, v_b_boxed_787_);
v_r_789_ = lean_box(v_res_788_);
return v_r_789_;
}
}
LEAN_EXPORT uint8_t l_UInt64_decLe___aux__1(uint64_t v_a_790_, uint64_t v_b_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_792_ = lean_uint64_to_nat(v_a_790_);
v___x_793_ = lean_uint64_to_nat(v_b_791_);
v___x_794_ = lean_nat_dec_le(v___x_792_, v___x_793_);
lean_dec(v___x_793_);
lean_dec(v___x_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_UInt64_decLe___aux__1___boxed(lean_object* v_a_795_, lean_object* v_b_796_){
_start:
{
uint64_t v_a_boxed_797_; uint64_t v_b_boxed_798_; uint8_t v_res_799_; lean_object* v_r_800_; 
v_a_boxed_797_ = lean_unbox_uint64(v_a_795_);
lean_dec_ref(v_a_795_);
v_b_boxed_798_ = lean_unbox_uint64(v_b_796_);
lean_dec_ref(v_b_796_);
v_res_799_ = l_UInt64_decLe___aux__1(v_a_boxed_797_, v_b_boxed_798_);
v_r_800_ = lean_box(v_res_799_);
return v_r_800_;
}
}
LEAN_EXPORT lean_object* l_UInt64_decLe___boxed(lean_object* v_a_803_, lean_object* v_b_804_){
_start:
{
uint64_t v_a_boxed_805_; uint64_t v_b_boxed_806_; uint8_t v_res_807_; lean_object* v_r_808_; 
v_a_boxed_805_ = lean_unbox_uint64(v_a_803_);
lean_dec_ref(v_a_803_);
v_b_boxed_806_ = lean_unbox_uint64(v_b_804_);
lean_dec_ref(v_b_804_);
v_res_807_ = lean_uint64_dec_le(v_a_boxed_805_, v_b_boxed_806_);
v_r_808_ = lean_box(v_res_807_);
return v_r_808_;
}
}
LEAN_EXPORT uint64_t l_instMaxUInt64___lam__0(uint64_t v_x_809_, uint64_t v_y_810_){
_start:
{
uint8_t v___x_811_; 
v___x_811_ = lean_uint64_dec_le(v_x_809_, v_y_810_);
if (v___x_811_ == 0)
{
return v_x_809_;
}
else
{
return v_y_810_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxUInt64___lam__0___boxed(lean_object* v_x_812_, lean_object* v_y_813_){
_start:
{
uint64_t v_x_boxed_814_; uint64_t v_y_boxed_815_; uint64_t v_res_816_; lean_object* v_r_817_; 
v_x_boxed_814_ = lean_unbox_uint64(v_x_812_);
lean_dec_ref(v_x_812_);
v_y_boxed_815_ = lean_unbox_uint64(v_y_813_);
lean_dec_ref(v_y_813_);
v_res_816_ = l_instMaxUInt64___lam__0(v_x_boxed_814_, v_y_boxed_815_);
v_r_817_ = lean_box_uint64(v_res_816_);
return v_r_817_;
}
}
LEAN_EXPORT uint64_t l_instMinUInt64___lam__0(uint64_t v_x_820_, uint64_t v_y_821_){
_start:
{
uint8_t v___x_822_; 
v___x_822_ = lean_uint64_dec_le(v_x_820_, v_y_821_);
if (v___x_822_ == 0)
{
return v_y_821_;
}
else
{
return v_x_820_;
}
}
}
LEAN_EXPORT lean_object* l_instMinUInt64___lam__0___boxed(lean_object* v_x_823_, lean_object* v_y_824_){
_start:
{
uint64_t v_x_boxed_825_; uint64_t v_y_boxed_826_; uint64_t v_res_827_; lean_object* v_r_828_; 
v_x_boxed_825_ = lean_unbox_uint64(v_x_823_);
lean_dec_ref(v_x_823_);
v_y_boxed_826_ = lean_unbox_uint64(v_y_824_);
lean_dec_ref(v_y_824_);
v_res_827_ = l_instMinUInt64___lam__0(v_x_boxed_825_, v_y_boxed_826_);
v_r_828_ = lean_box_uint64(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT size_t l_USize_ofFin(lean_object* v_a_831_){
_start:
{
size_t v___x_832_; 
v___x_832_ = lean_usize_of_nat_mk(v_a_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_USize_ofFin___boxed(lean_object* v_a_833_){
_start:
{
size_t v_res_834_; lean_object* v_r_835_; 
v_res_834_ = l_USize_ofFin(v_a_833_);
v_r_835_ = lean_box_usize(v_res_834_);
return v_r_835_;
}
}
static lean_object* _init_l_USize_ofInt___closed__0(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = l_System_Platform_numBits;
v___x_837_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_838_ = l_Int_pow(v___x_837_, v___x_836_);
return v___x_838_;
}
}
LEAN_EXPORT size_t l_USize_ofInt(lean_object* v_x_839_){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; size_t v___x_843_; 
v___x_840_ = lean_obj_once(&l_USize_ofInt___closed__0, &l_USize_ofInt___closed__0_once, _init_l_USize_ofInt___closed__0);
v___x_841_ = lean_int_emod(v_x_839_, v___x_840_);
v___x_842_ = l_Int_toNat(v___x_841_);
lean_dec(v___x_841_);
v___x_843_ = lean_usize_of_nat(v___x_842_);
lean_dec(v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_USize_ofInt___boxed(lean_object* v_x_844_){
_start:
{
size_t v_res_845_; lean_object* v_r_846_; 
v_res_845_ = l_USize_ofInt(v_x_844_);
lean_dec(v_x_844_);
v_r_846_ = lean_box_usize(v_res_845_);
return v_r_846_;
}
}
LEAN_EXPORT lean_object* l_USize_mul___boxed(lean_object* v_a_849_, lean_object* v_b_850_){
_start:
{
size_t v_a_boxed_851_; size_t v_b_boxed_852_; size_t v_res_853_; lean_object* v_r_854_; 
v_a_boxed_851_ = lean_unbox_usize(v_a_849_);
lean_dec(v_a_849_);
v_b_boxed_852_ = lean_unbox_usize(v_b_850_);
lean_dec(v_b_850_);
v_res_853_ = lean_usize_mul(v_a_boxed_851_, v_b_boxed_852_);
v_r_854_ = lean_box_usize(v_res_853_);
return v_r_854_;
}
}
LEAN_EXPORT lean_object* l_USize_div___boxed(lean_object* v_a_857_, lean_object* v_b_858_){
_start:
{
size_t v_a_boxed_859_; size_t v_b_boxed_860_; size_t v_res_861_; lean_object* v_r_862_; 
v_a_boxed_859_ = lean_unbox_usize(v_a_857_);
lean_dec(v_a_857_);
v_b_boxed_860_ = lean_unbox_usize(v_b_858_);
lean_dec(v_b_858_);
v_res_861_ = lean_usize_div(v_a_boxed_859_, v_b_boxed_860_);
v_r_862_ = lean_box_usize(v_res_861_);
return v_r_862_;
}
}
LEAN_EXPORT size_t l_USize_pow(size_t v_x_863_, lean_object* v_n_864_){
_start:
{
lean_object* v_zero_865_; uint8_t v_isZero_866_; 
v_zero_865_ = lean_unsigned_to_nat(0u);
v_isZero_866_ = lean_nat_dec_eq(v_n_864_, v_zero_865_);
if (v_isZero_866_ == 1)
{
size_t v___x_867_; 
v___x_867_ = ((size_t)1ULL);
return v___x_867_;
}
else
{
lean_object* v_one_868_; lean_object* v_n_869_; size_t v___x_870_; size_t v___x_871_; 
v_one_868_ = lean_unsigned_to_nat(1u);
v_n_869_ = lean_nat_sub(v_n_864_, v_one_868_);
v___x_870_ = l_USize_pow(v_x_863_, v_n_869_);
lean_dec(v_n_869_);
v___x_871_ = lean_usize_mul(v___x_870_, v_x_863_);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_USize_pow___boxed(lean_object* v_x_872_, lean_object* v_n_873_){
_start:
{
size_t v_x_boxed_874_; size_t v_res_875_; lean_object* v_r_876_; 
v_x_boxed_874_ = lean_unbox_usize(v_x_872_);
lean_dec(v_x_872_);
v_res_875_ = l_USize_pow(v_x_boxed_874_, v_n_873_);
lean_dec(v_n_873_);
v_r_876_ = lean_box_usize(v_res_875_);
return v_r_876_;
}
}
LEAN_EXPORT lean_object* l_USize_mod___boxed(lean_object* v_a_879_, lean_object* v_b_880_){
_start:
{
size_t v_a_boxed_881_; size_t v_b_boxed_882_; size_t v_res_883_; lean_object* v_r_884_; 
v_a_boxed_881_ = lean_unbox_usize(v_a_879_);
lean_dec(v_a_879_);
v_b_boxed_882_ = lean_unbox_usize(v_b_880_);
lean_dec(v_b_880_);
v_res_883_ = lean_usize_mod(v_a_boxed_881_, v_b_boxed_882_);
v_r_884_ = lean_box_usize(v_res_883_);
return v_r_884_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00USize_modn_spec__0(lean_object* v_a_885_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = l_System_Platform_numBits;
v___x_887_ = l_BitVec_ofNat(v___x_886_, v_a_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00USize_modn_spec__0___boxed(lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Nat_cast___at___00USize_modn_spec__0(v_a_888_);
lean_dec(v_a_888_);
return v_res_889_;
}
}
LEAN_EXPORT size_t l_USize_modn(size_t v_a_890_, lean_object* v_n_891_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; size_t v___x_895_; 
v___x_892_ = lean_usize_to_nat(v_a_890_);
v___x_893_ = lean_nat_mod(v___x_892_, v_n_891_);
lean_dec(v___x_892_);
v___x_894_ = l_Nat_cast___at___00USize_modn_spec__0(v___x_893_);
lean_dec(v___x_893_);
v___x_895_ = lean_usize_of_nat_mk(v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_USize_modn___boxed(lean_object* v_a_896_, lean_object* v_n_897_){
_start:
{
size_t v_a_boxed_898_; size_t v_res_899_; lean_object* v_r_900_; 
v_a_boxed_898_ = lean_unbox_usize(v_a_896_);
lean_dec(v_a_896_);
v_res_899_ = l_USize_modn(v_a_boxed_898_, v_n_897_);
lean_dec(v_n_897_);
v_r_900_ = lean_box_usize(v_res_899_);
return v_r_900_;
}
}
LEAN_EXPORT lean_object* l_USize_land___boxed(lean_object* v_a_903_, lean_object* v_b_904_){
_start:
{
size_t v_a_boxed_905_; size_t v_b_boxed_906_; size_t v_res_907_; lean_object* v_r_908_; 
v_a_boxed_905_ = lean_unbox_usize(v_a_903_);
lean_dec(v_a_903_);
v_b_boxed_906_ = lean_unbox_usize(v_b_904_);
lean_dec(v_b_904_);
v_res_907_ = lean_usize_land(v_a_boxed_905_, v_b_boxed_906_);
v_r_908_ = lean_box_usize(v_res_907_);
return v_r_908_;
}
}
LEAN_EXPORT lean_object* l_USize_lor___boxed(lean_object* v_a_911_, lean_object* v_b_912_){
_start:
{
size_t v_a_boxed_913_; size_t v_b_boxed_914_; size_t v_res_915_; lean_object* v_r_916_; 
v_a_boxed_913_ = lean_unbox_usize(v_a_911_);
lean_dec(v_a_911_);
v_b_boxed_914_ = lean_unbox_usize(v_b_912_);
lean_dec(v_b_912_);
v_res_915_ = lean_usize_lor(v_a_boxed_913_, v_b_boxed_914_);
v_r_916_ = lean_box_usize(v_res_915_);
return v_r_916_;
}
}
LEAN_EXPORT lean_object* l_USize_xor___boxed(lean_object* v_a_919_, lean_object* v_b_920_){
_start:
{
size_t v_a_boxed_921_; size_t v_b_boxed_922_; size_t v_res_923_; lean_object* v_r_924_; 
v_a_boxed_921_ = lean_unbox_usize(v_a_919_);
lean_dec(v_a_919_);
v_b_boxed_922_ = lean_unbox_usize(v_b_920_);
lean_dec(v_b_920_);
v_res_923_ = lean_usize_xor(v_a_boxed_921_, v_b_boxed_922_);
v_r_924_ = lean_box_usize(v_res_923_);
return v_r_924_;
}
}
LEAN_EXPORT lean_object* l_USize_shiftLeft___boxed(lean_object* v_a_927_, lean_object* v_b_928_){
_start:
{
size_t v_a_boxed_929_; size_t v_b_boxed_930_; size_t v_res_931_; lean_object* v_r_932_; 
v_a_boxed_929_ = lean_unbox_usize(v_a_927_);
lean_dec(v_a_927_);
v_b_boxed_930_ = lean_unbox_usize(v_b_928_);
lean_dec(v_b_928_);
v_res_931_ = lean_usize_shift_left(v_a_boxed_929_, v_b_boxed_930_);
v_r_932_ = lean_box_usize(v_res_931_);
return v_r_932_;
}
}
LEAN_EXPORT lean_object* l_USize_shiftRight___boxed(lean_object* v_a_935_, lean_object* v_b_936_){
_start:
{
size_t v_a_boxed_937_; size_t v_b_boxed_938_; size_t v_res_939_; lean_object* v_r_940_; 
v_a_boxed_937_ = lean_unbox_usize(v_a_935_);
lean_dec(v_a_935_);
v_b_boxed_938_ = lean_unbox_usize(v_b_936_);
lean_dec(v_b_936_);
v_res_939_ = lean_usize_shift_right(v_a_boxed_937_, v_b_boxed_938_);
v_r_940_ = lean_box_usize(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT lean_object* l_USize_ofNat32___boxed(lean_object* v_n_943_, lean_object* v_h_944_){
_start:
{
size_t v_res_945_; lean_object* v_r_946_; 
v_res_945_ = lean_usize_of_nat(v_n_943_);
lean_dec(v_n_943_);
v_r_946_ = lean_box_usize(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUSize___boxed(lean_object* v_a_948_){
_start:
{
uint8_t v_a_boxed_949_; size_t v_res_950_; lean_object* v_r_951_; 
v_a_boxed_949_ = lean_unbox(v_a_948_);
v_res_950_ = lean_uint8_to_usize(v_a_boxed_949_);
v_r_951_ = lean_box_usize(v_res_950_);
return v_r_951_;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt8___boxed(lean_object* v_a_953_){
_start:
{
size_t v_a_boxed_954_; uint8_t v_res_955_; lean_object* v_r_956_; 
v_a_boxed_954_ = lean_unbox_usize(v_a_953_);
lean_dec(v_a_953_);
v_res_955_ = lean_usize_to_uint8(v_a_boxed_954_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUSize___boxed(lean_object* v_a_958_){
_start:
{
uint16_t v_a_boxed_959_; size_t v_res_960_; lean_object* v_r_961_; 
v_a_boxed_959_ = lean_unbox(v_a_958_);
v_res_960_ = lean_uint16_to_usize(v_a_boxed_959_);
v_r_961_ = lean_box_usize(v_res_960_);
return v_r_961_;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt16___boxed(lean_object* v_a_963_){
_start:
{
size_t v_a_boxed_964_; uint16_t v_res_965_; lean_object* v_r_966_; 
v_a_boxed_964_ = lean_unbox_usize(v_a_963_);
lean_dec(v_a_963_);
v_res_965_ = lean_usize_to_uint16(v_a_boxed_964_);
v_r_966_ = lean_box(v_res_965_);
return v_r_966_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUSize___boxed(lean_object* v_a_968_){
_start:
{
uint32_t v_a_boxed_969_; size_t v_res_970_; lean_object* v_r_971_; 
v_a_boxed_969_ = lean_unbox_uint32(v_a_968_);
lean_dec(v_a_968_);
v_res_970_ = lean_uint32_to_usize(v_a_boxed_969_);
v_r_971_ = lean_box_usize(v_res_970_);
return v_r_971_;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt32___boxed(lean_object* v_a_973_){
_start:
{
size_t v_a_boxed_974_; uint32_t v_res_975_; lean_object* v_r_976_; 
v_a_boxed_974_ = lean_unbox_usize(v_a_973_);
lean_dec(v_a_973_);
v_res_975_ = lean_usize_to_uint32(v_a_boxed_974_);
v_r_976_ = lean_box_uint32(v_res_975_);
return v_r_976_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUSize___boxed(lean_object* v_a_978_){
_start:
{
uint64_t v_a_boxed_979_; size_t v_res_980_; lean_object* v_r_981_; 
v_a_boxed_979_ = lean_unbox_uint64(v_a_978_);
lean_dec_ref(v_a_978_);
v_res_980_ = lean_uint64_to_usize(v_a_boxed_979_);
v_r_981_ = lean_box_usize(v_res_980_);
return v_r_981_;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt64___boxed(lean_object* v_a_983_){
_start:
{
size_t v_a_boxed_984_; uint64_t v_res_985_; lean_object* v_r_986_; 
v_a_boxed_984_ = lean_unbox_usize(v_a_983_);
lean_dec(v_a_983_);
v_res_985_ = lean_usize_to_uint64(v_a_boxed_984_);
v_r_986_ = lean_box_uint64(v_res_985_);
return v_r_986_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec32___redArg(size_t v_a_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = lean_usize_to_nat(v_a_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec32___redArg___boxed(lean_object* v_a_989_){
_start:
{
size_t v_a_boxed_990_; lean_object* v_res_991_; 
v_a_boxed_990_ = lean_unbox_usize(v_a_989_);
lean_dec(v_a_989_);
v_res_991_ = l_USize_toBitVec32___redArg(v_a_boxed_990_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec32(size_t v_a_992_, lean_object* v_h_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = lean_usize_to_nat(v_a_992_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec32___boxed(lean_object* v_a_995_, lean_object* v_h_996_){
_start:
{
size_t v_a_boxed_997_; lean_object* v_res_998_; 
v_a_boxed_997_ = lean_unbox_usize(v_a_995_);
lean_dec(v_a_995_);
v_res_998_ = l_USize_toBitVec32(v_a_boxed_997_, v_h_996_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec64___redArg(size_t v_a_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_usize_to_nat(v_a_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec64___redArg___boxed(lean_object* v_a_1001_){
_start:
{
size_t v_a_boxed_1002_; lean_object* v_res_1003_; 
v_a_boxed_1002_ = lean_unbox_usize(v_a_1001_);
lean_dec(v_a_1001_);
v_res_1003_ = l_USize_toBitVec64___redArg(v_a_boxed_1002_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec64(size_t v_a_1004_, lean_object* v_h_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_usize_to_nat(v_a_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec64___boxed(lean_object* v_a_1007_, lean_object* v_h_1008_){
_start:
{
size_t v_a_boxed_1009_; lean_object* v_res_1010_; 
v_a_boxed_1009_ = lean_unbox_usize(v_a_1007_);
lean_dec(v_a_1007_);
v_res_1010_ = l_USize_toBitVec64(v_a_boxed_1009_, v_h_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_USize_complement___boxed(lean_object* v_a_1022_){
_start:
{
size_t v_a_boxed_1023_; size_t v_res_1024_; lean_object* v_r_1025_; 
v_a_boxed_1023_ = lean_unbox_usize(v_a_1022_);
lean_dec(v_a_1022_);
v_res_1024_ = lean_usize_complement(v_a_boxed_1023_);
v_r_1025_ = lean_box_usize(v_res_1024_);
return v_r_1025_;
}
}
LEAN_EXPORT lean_object* l_USize_neg___boxed(lean_object* v_a_1027_){
_start:
{
size_t v_a_boxed_1028_; size_t v_res_1029_; lean_object* v_r_1030_; 
v_a_boxed_1028_ = lean_unbox_usize(v_a_1027_);
lean_dec(v_a_1027_);
v_res_1029_ = lean_usize_neg(v_a_boxed_1028_);
v_r_1030_ = lean_box_usize(v_res_1029_);
return v_r_1030_;
}
}
LEAN_EXPORT lean_object* l_Bool_toUSize___boxed(lean_object* v_b_1046_){
_start:
{
uint8_t v_b_boxed_1047_; size_t v_res_1048_; lean_object* v_r_1049_; 
v_b_boxed_1047_ = lean_unbox(v_b_1046_);
v_res_1048_ = lean_bool_to_usize(v_b_boxed_1047_);
v_r_1049_ = lean_box_usize(v_res_1048_);
return v_r_1049_;
}
}
LEAN_EXPORT size_t l_instMaxUSize___lam__0(size_t v_x_1050_, size_t v_y_1051_){
_start:
{
uint8_t v___x_1052_; 
v___x_1052_ = lean_usize_dec_le(v_x_1050_, v_y_1051_);
if (v___x_1052_ == 0)
{
return v_x_1050_;
}
else
{
return v_y_1051_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxUSize___lam__0___boxed(lean_object* v_x_1053_, lean_object* v_y_1054_){
_start:
{
size_t v_x_boxed_1055_; size_t v_y_boxed_1056_; size_t v_res_1057_; lean_object* v_r_1058_; 
v_x_boxed_1055_ = lean_unbox_usize(v_x_1053_);
lean_dec(v_x_1053_);
v_y_boxed_1056_ = lean_unbox_usize(v_y_1054_);
lean_dec(v_y_1054_);
v_res_1057_ = l_instMaxUSize___lam__0(v_x_boxed_1055_, v_y_boxed_1056_);
v_r_1058_ = lean_box_usize(v_res_1057_);
return v_r_1058_;
}
}
LEAN_EXPORT size_t l_instMinUSize___lam__0(size_t v_x_1061_, size_t v_y_1062_){
_start:
{
uint8_t v___x_1063_; 
v___x_1063_ = lean_usize_dec_le(v_x_1061_, v_y_1062_);
if (v___x_1063_ == 0)
{
return v_y_1062_;
}
else
{
return v_x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_instMinUSize___lam__0___boxed(lean_object* v_x_1064_, lean_object* v_y_1065_){
_start:
{
size_t v_x_boxed_1066_; size_t v_y_boxed_1067_; size_t v_res_1068_; lean_object* v_r_1069_; 
v_x_boxed_1066_ = lean_unbox_usize(v_x_1064_);
lean_dec(v_x_1064_);
v_y_boxed_1067_ = lean_unbox_usize(v_y_1065_);
lean_dec(v_y_1065_);
v_res_1068_ = l_instMinUSize___lam__0(v_x_boxed_1066_, v_y_boxed_1067_);
v_r_1069_ = lean_box_usize(v_res_1068_);
return v_r_1069_;
}
}
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instLTUInt16 = _init_l_instLTUInt16();
lean_mark_persistent(l_instLTUInt16);
l_instLEUInt16 = _init_l_instLEUInt16();
lean_mark_persistent(l_instLEUInt16);
l_instLTUInt64 = _init_l_instLTUInt64();
lean_mark_persistent(l_instLTUInt64);
l_instLEUInt64 = _init_l_instLEUInt64();
lean_mark_persistent(l_instLEUInt64);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_UInt_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_UInt_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
