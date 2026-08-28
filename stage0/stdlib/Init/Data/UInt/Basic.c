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
lean_object* lean_uint64_to_nat(uint64_t);
uint64_t lean_uint64_of_nat_mk(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_uint16_to_nat(uint16_t);
uint16_t lean_uint16_of_nat_mk(lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
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
uint8_t lean_uint16_dec_lt(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_decLt___boxed(lean_object*, lean_object*);
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
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_decLt___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_UInt16_decLt___boxed(lean_object* v_a_393_, lean_object* v_b_394_){
_start:
{
uint16_t v_a_boxed_395_; uint16_t v_b_boxed_396_; uint8_t v_res_397_; lean_object* v_r_398_; 
v_a_boxed_395_ = lean_unbox(v_a_393_);
v_b_boxed_396_ = lean_unbox(v_b_394_);
v_res_397_ = lean_uint16_dec_lt(v_a_boxed_395_, v_b_boxed_396_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT lean_object* l_UInt16_decLe___boxed(lean_object* v_a_401_, lean_object* v_b_402_){
_start:
{
uint16_t v_a_boxed_403_; uint16_t v_b_boxed_404_; uint8_t v_res_405_; lean_object* v_r_406_; 
v_a_boxed_403_ = lean_unbox(v_a_401_);
v_b_boxed_404_ = lean_unbox(v_b_402_);
v_res_405_ = lean_uint16_dec_le(v_a_boxed_403_, v_b_boxed_404_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT uint16_t l_instMaxUInt16___lam__0(uint16_t v_x_407_, uint16_t v_y_408_){
_start:
{
uint8_t v___x_409_; 
v___x_409_ = lean_uint16_dec_le(v_x_407_, v_y_408_);
if (v___x_409_ == 0)
{
return v_x_407_;
}
else
{
return v_y_408_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxUInt16___lam__0___boxed(lean_object* v_x_410_, lean_object* v_y_411_){
_start:
{
uint16_t v_x_boxed_412_; uint16_t v_y_boxed_413_; uint16_t v_res_414_; lean_object* v_r_415_; 
v_x_boxed_412_ = lean_unbox(v_x_410_);
v_y_boxed_413_ = lean_unbox(v_y_411_);
v_res_414_ = l_instMaxUInt16___lam__0(v_x_boxed_412_, v_y_boxed_413_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT uint16_t l_instMinUInt16___lam__0(uint16_t v_x_418_, uint16_t v_y_419_){
_start:
{
uint8_t v___x_420_; 
v___x_420_ = lean_uint16_dec_le(v_x_418_, v_y_419_);
if (v___x_420_ == 0)
{
return v_y_419_;
}
else
{
return v_x_418_;
}
}
}
LEAN_EXPORT lean_object* l_instMinUInt16___lam__0___boxed(lean_object* v_x_421_, lean_object* v_y_422_){
_start:
{
uint16_t v_x_boxed_423_; uint16_t v_y_boxed_424_; uint16_t v_res_425_; lean_object* v_r_426_; 
v_x_boxed_423_ = lean_unbox(v_x_421_);
v_y_boxed_424_ = lean_unbox(v_y_422_);
v_res_425_ = l_instMinUInt16___lam__0(v_x_boxed_423_, v_y_boxed_424_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofFin(lean_object* v_a_429_){
_start:
{
uint32_t v___x_430_; 
v___x_430_ = lean_uint32_of_nat_mk(v_a_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofFin___boxed(lean_object* v_a_431_){
_start:
{
uint32_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_UInt32_ofFin(v_a_431_);
v_r_433_ = lean_box_uint32(v_res_432_);
return v_r_433_;
}
}
static lean_object* _init_l_UInt32_ofInt___closed__0(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_unsigned_to_nat(32u);
v___x_435_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_436_ = l_Int_pow(v___x_435_, v___x_434_);
return v___x_436_;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofInt(lean_object* v_x_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint32_t v___x_441_; 
v___x_438_ = lean_obj_once(&l_UInt32_ofInt___closed__0, &l_UInt32_ofInt___closed__0_once, _init_l_UInt32_ofInt___closed__0);
v___x_439_ = lean_int_emod(v_x_437_, v___x_438_);
v___x_440_ = l_Int_toNat(v___x_439_);
lean_dec(v___x_439_);
v___x_441_ = lean_uint32_of_nat(v___x_440_);
lean_dec(v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofInt___boxed(lean_object* v_x_442_){
_start:
{
uint32_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_UInt32_ofInt(v_x_442_);
lean_dec(v_x_442_);
v_r_444_ = lean_box_uint32(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l_UInt32_mul___boxed(lean_object* v_a_447_, lean_object* v_b_448_){
_start:
{
uint32_t v_a_boxed_449_; uint32_t v_b_boxed_450_; uint32_t v_res_451_; lean_object* v_r_452_; 
v_a_boxed_449_ = lean_unbox_uint32(v_a_447_);
lean_dec(v_a_447_);
v_b_boxed_450_ = lean_unbox_uint32(v_b_448_);
lean_dec(v_b_448_);
v_res_451_ = lean_uint32_mul(v_a_boxed_449_, v_b_boxed_450_);
v_r_452_ = lean_box_uint32(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT lean_object* l_UInt32_div___boxed(lean_object* v_a_455_, lean_object* v_b_456_){
_start:
{
uint32_t v_a_boxed_457_; uint32_t v_b_boxed_458_; uint32_t v_res_459_; lean_object* v_r_460_; 
v_a_boxed_457_ = lean_unbox_uint32(v_a_455_);
lean_dec(v_a_455_);
v_b_boxed_458_ = lean_unbox_uint32(v_b_456_);
lean_dec(v_b_456_);
v_res_459_ = lean_uint32_div(v_a_boxed_457_, v_b_boxed_458_);
v_r_460_ = lean_box_uint32(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT uint32_t l_UInt32_pow(uint32_t v_x_461_, lean_object* v_n_462_){
_start:
{
lean_object* v_zero_463_; uint8_t v_isZero_464_; 
v_zero_463_ = lean_unsigned_to_nat(0u);
v_isZero_464_ = lean_nat_dec_eq(v_n_462_, v_zero_463_);
if (v_isZero_464_ == 1)
{
uint32_t v___x_465_; 
v___x_465_ = 1;
return v___x_465_;
}
else
{
lean_object* v_one_466_; lean_object* v_n_467_; uint32_t v___x_468_; uint32_t v___x_469_; 
v_one_466_ = lean_unsigned_to_nat(1u);
v_n_467_ = lean_nat_sub(v_n_462_, v_one_466_);
v___x_468_ = l_UInt32_pow(v_x_461_, v_n_467_);
lean_dec(v_n_467_);
v___x_469_ = lean_uint32_mul(v___x_468_, v_x_461_);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_UInt32_pow___boxed(lean_object* v_x_470_, lean_object* v_n_471_){
_start:
{
uint32_t v_x_boxed_472_; uint32_t v_res_473_; lean_object* v_r_474_; 
v_x_boxed_472_ = lean_unbox_uint32(v_x_470_);
lean_dec(v_x_470_);
v_res_473_ = l_UInt32_pow(v_x_boxed_472_, v_n_471_);
lean_dec(v_n_471_);
v_r_474_ = lean_box_uint32(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT lean_object* l_UInt32_mod___boxed(lean_object* v_a_477_, lean_object* v_b_478_){
_start:
{
uint32_t v_a_boxed_479_; uint32_t v_b_boxed_480_; uint32_t v_res_481_; lean_object* v_r_482_; 
v_a_boxed_479_ = lean_unbox_uint32(v_a_477_);
lean_dec(v_a_477_);
v_b_boxed_480_ = lean_unbox_uint32(v_b_478_);
lean_dec(v_b_478_);
v_res_481_ = lean_uint32_mod(v_a_boxed_479_, v_b_boxed_480_);
v_r_482_ = lean_box_uint32(v_res_481_);
return v_r_482_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt32_modn_spec__0(lean_object* v_a_483_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(32u);
v___x_485_ = l_BitVec_ofNat(v___x_484_, v_a_483_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt32_modn_spec__0___boxed(lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Nat_cast___at___00UInt32_modn_spec__0(v_a_486_);
lean_dec(v_a_486_);
return v_res_487_;
}
}
LEAN_EXPORT uint32_t l_UInt32_modn(uint32_t v_a_488_, lean_object* v_n_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint32_t v___x_493_; 
v___x_490_ = lean_uint32_to_nat(v_a_488_);
v___x_491_ = lean_nat_mod(v___x_490_, v_n_489_);
lean_dec(v___x_490_);
v___x_492_ = l_Nat_cast___at___00UInt32_modn_spec__0(v___x_491_);
lean_dec(v___x_491_);
v___x_493_ = lean_uint32_of_nat_mk(v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_UInt32_modn___boxed(lean_object* v_a_494_, lean_object* v_n_495_){
_start:
{
uint32_t v_a_boxed_496_; uint32_t v_res_497_; lean_object* v_r_498_; 
v_a_boxed_496_ = lean_unbox_uint32(v_a_494_);
lean_dec(v_a_494_);
v_res_497_ = l_UInt32_modn(v_a_boxed_496_, v_n_495_);
lean_dec(v_n_495_);
v_r_498_ = lean_box_uint32(v_res_497_);
return v_r_498_;
}
}
LEAN_EXPORT lean_object* l_UInt32_land___boxed(lean_object* v_a_501_, lean_object* v_b_502_){
_start:
{
uint32_t v_a_boxed_503_; uint32_t v_b_boxed_504_; uint32_t v_res_505_; lean_object* v_r_506_; 
v_a_boxed_503_ = lean_unbox_uint32(v_a_501_);
lean_dec(v_a_501_);
v_b_boxed_504_ = lean_unbox_uint32(v_b_502_);
lean_dec(v_b_502_);
v_res_505_ = lean_uint32_land(v_a_boxed_503_, v_b_boxed_504_);
v_r_506_ = lean_box_uint32(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT lean_object* l_UInt32_lor___boxed(lean_object* v_a_509_, lean_object* v_b_510_){
_start:
{
uint32_t v_a_boxed_511_; uint32_t v_b_boxed_512_; uint32_t v_res_513_; lean_object* v_r_514_; 
v_a_boxed_511_ = lean_unbox_uint32(v_a_509_);
lean_dec(v_a_509_);
v_b_boxed_512_ = lean_unbox_uint32(v_b_510_);
lean_dec(v_b_510_);
v_res_513_ = lean_uint32_lor(v_a_boxed_511_, v_b_boxed_512_);
v_r_514_ = lean_box_uint32(v_res_513_);
return v_r_514_;
}
}
LEAN_EXPORT lean_object* l_UInt32_xor___boxed(lean_object* v_a_517_, lean_object* v_b_518_){
_start:
{
uint32_t v_a_boxed_519_; uint32_t v_b_boxed_520_; uint32_t v_res_521_; lean_object* v_r_522_; 
v_a_boxed_519_ = lean_unbox_uint32(v_a_517_);
lean_dec(v_a_517_);
v_b_boxed_520_ = lean_unbox_uint32(v_b_518_);
lean_dec(v_b_518_);
v_res_521_ = lean_uint32_xor(v_a_boxed_519_, v_b_boxed_520_);
v_r_522_ = lean_box_uint32(v_res_521_);
return v_r_522_;
}
}
LEAN_EXPORT lean_object* l_UInt32_shiftLeft___boxed(lean_object* v_a_525_, lean_object* v_b_526_){
_start:
{
uint32_t v_a_boxed_527_; uint32_t v_b_boxed_528_; uint32_t v_res_529_; lean_object* v_r_530_; 
v_a_boxed_527_ = lean_unbox_uint32(v_a_525_);
lean_dec(v_a_525_);
v_b_boxed_528_ = lean_unbox_uint32(v_b_526_);
lean_dec(v_b_526_);
v_res_529_ = lean_uint32_shift_left(v_a_boxed_527_, v_b_boxed_528_);
v_r_530_ = lean_box_uint32(v_res_529_);
return v_r_530_;
}
}
LEAN_EXPORT lean_object* l_UInt32_shiftRight___boxed(lean_object* v_a_533_, lean_object* v_b_534_){
_start:
{
uint32_t v_a_boxed_535_; uint32_t v_b_boxed_536_; uint32_t v_res_537_; lean_object* v_r_538_; 
v_a_boxed_535_ = lean_unbox_uint32(v_a_533_);
lean_dec(v_a_533_);
v_b_boxed_536_ = lean_unbox_uint32(v_b_534_);
lean_dec(v_b_534_);
v_res_537_ = lean_uint32_shift_right(v_a_boxed_535_, v_b_boxed_536_);
v_r_538_ = lean_box_uint32(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT lean_object* l_UInt32_complement___boxed(lean_object* v_a_550_){
_start:
{
uint32_t v_a_boxed_551_; uint32_t v_res_552_; lean_object* v_r_553_; 
v_a_boxed_551_ = lean_unbox_uint32(v_a_550_);
lean_dec(v_a_550_);
v_res_552_ = lean_uint32_complement(v_a_boxed_551_);
v_r_553_ = lean_box_uint32(v_res_552_);
return v_r_553_;
}
}
LEAN_EXPORT lean_object* l_UInt32_neg___boxed(lean_object* v_a_555_){
_start:
{
uint32_t v_a_boxed_556_; uint32_t v_res_557_; lean_object* v_r_558_; 
v_a_boxed_556_ = lean_unbox_uint32(v_a_555_);
lean_dec(v_a_555_);
v_res_557_ = lean_uint32_neg(v_a_boxed_556_);
v_r_558_ = lean_box_uint32(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT lean_object* l_Bool_toUInt32___boxed(lean_object* v_b_574_){
_start:
{
uint8_t v_b_boxed_575_; uint32_t v_res_576_; lean_object* v_r_577_; 
v_b_boxed_575_ = lean_unbox(v_b_574_);
v_res_576_ = lean_bool_to_uint32(v_b_boxed_575_);
v_r_577_ = lean_box_uint32(v_res_576_);
return v_r_577_;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofFin(lean_object* v_a_578_){
_start:
{
uint64_t v___x_579_; 
v___x_579_ = lean_uint64_of_nat_mk(v_a_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofFin___boxed(lean_object* v_a_580_){
_start:
{
uint64_t v_res_581_; lean_object* v_r_582_; 
v_res_581_ = l_UInt64_ofFin(v_a_580_);
v_r_582_ = lean_box_uint64(v_res_581_);
return v_r_582_;
}
}
static lean_object* _init_l_UInt64_ofInt___closed__0(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_unsigned_to_nat(64u);
v___x_584_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_585_ = l_Int_pow(v___x_584_, v___x_583_);
return v___x_585_;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofInt(lean_object* v_x_586_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint64_t v___x_590_; 
v___x_587_ = lean_obj_once(&l_UInt64_ofInt___closed__0, &l_UInt64_ofInt___closed__0_once, _init_l_UInt64_ofInt___closed__0);
v___x_588_ = lean_int_emod(v_x_586_, v___x_587_);
v___x_589_ = l_Int_toNat(v___x_588_);
lean_dec(v___x_588_);
v___x_590_ = lean_uint64_of_nat(v___x_589_);
lean_dec(v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofInt___boxed(lean_object* v_x_591_){
_start:
{
uint64_t v_res_592_; lean_object* v_r_593_; 
v_res_592_ = l_UInt64_ofInt(v_x_591_);
lean_dec(v_x_591_);
v_r_593_ = lean_box_uint64(v_res_592_);
return v_r_593_;
}
}
LEAN_EXPORT lean_object* l_UInt64_add___boxed(lean_object* v_a_596_, lean_object* v_b_597_){
_start:
{
uint64_t v_a_boxed_598_; uint64_t v_b_boxed_599_; uint64_t v_res_600_; lean_object* v_r_601_; 
v_a_boxed_598_ = lean_unbox_uint64(v_a_596_);
lean_dec_ref(v_a_596_);
v_b_boxed_599_ = lean_unbox_uint64(v_b_597_);
lean_dec_ref(v_b_597_);
v_res_600_ = lean_uint64_add(v_a_boxed_598_, v_b_boxed_599_);
v_r_601_ = lean_box_uint64(v_res_600_);
return v_r_601_;
}
}
LEAN_EXPORT lean_object* l_UInt64_sub___boxed(lean_object* v_a_604_, lean_object* v_b_605_){
_start:
{
uint64_t v_a_boxed_606_; uint64_t v_b_boxed_607_; uint64_t v_res_608_; lean_object* v_r_609_; 
v_a_boxed_606_ = lean_unbox_uint64(v_a_604_);
lean_dec_ref(v_a_604_);
v_b_boxed_607_ = lean_unbox_uint64(v_b_605_);
lean_dec_ref(v_b_605_);
v_res_608_ = lean_uint64_sub(v_a_boxed_606_, v_b_boxed_607_);
v_r_609_ = lean_box_uint64(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT lean_object* l_UInt64_mul___boxed(lean_object* v_a_612_, lean_object* v_b_613_){
_start:
{
uint64_t v_a_boxed_614_; uint64_t v_b_boxed_615_; uint64_t v_res_616_; lean_object* v_r_617_; 
v_a_boxed_614_ = lean_unbox_uint64(v_a_612_);
lean_dec_ref(v_a_612_);
v_b_boxed_615_ = lean_unbox_uint64(v_b_613_);
lean_dec_ref(v_b_613_);
v_res_616_ = lean_uint64_mul(v_a_boxed_614_, v_b_boxed_615_);
v_r_617_ = lean_box_uint64(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT lean_object* l_UInt64_div___boxed(lean_object* v_a_620_, lean_object* v_b_621_){
_start:
{
uint64_t v_a_boxed_622_; uint64_t v_b_boxed_623_; uint64_t v_res_624_; lean_object* v_r_625_; 
v_a_boxed_622_ = lean_unbox_uint64(v_a_620_);
lean_dec_ref(v_a_620_);
v_b_boxed_623_ = lean_unbox_uint64(v_b_621_);
lean_dec_ref(v_b_621_);
v_res_624_ = lean_uint64_div(v_a_boxed_622_, v_b_boxed_623_);
v_r_625_ = lean_box_uint64(v_res_624_);
return v_r_625_;
}
}
LEAN_EXPORT uint64_t l_UInt64_pow(uint64_t v_x_626_, lean_object* v_n_627_){
_start:
{
lean_object* v_zero_628_; uint8_t v_isZero_629_; 
v_zero_628_ = lean_unsigned_to_nat(0u);
v_isZero_629_ = lean_nat_dec_eq(v_n_627_, v_zero_628_);
if (v_isZero_629_ == 1)
{
uint64_t v___x_630_; 
v___x_630_ = 1ULL;
return v___x_630_;
}
else
{
lean_object* v_one_631_; lean_object* v_n_632_; uint64_t v___x_633_; uint64_t v___x_634_; 
v_one_631_ = lean_unsigned_to_nat(1u);
v_n_632_ = lean_nat_sub(v_n_627_, v_one_631_);
v___x_633_ = l_UInt64_pow(v_x_626_, v_n_632_);
lean_dec(v_n_632_);
v___x_634_ = lean_uint64_mul(v___x_633_, v_x_626_);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_pow___boxed(lean_object* v_x_635_, lean_object* v_n_636_){
_start:
{
uint64_t v_x_boxed_637_; uint64_t v_res_638_; lean_object* v_r_639_; 
v_x_boxed_637_ = lean_unbox_uint64(v_x_635_);
lean_dec_ref(v_x_635_);
v_res_638_ = l_UInt64_pow(v_x_boxed_637_, v_n_636_);
lean_dec(v_n_636_);
v_r_639_ = lean_box_uint64(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT lean_object* l_UInt64_mod___boxed(lean_object* v_a_642_, lean_object* v_b_643_){
_start:
{
uint64_t v_a_boxed_644_; uint64_t v_b_boxed_645_; uint64_t v_res_646_; lean_object* v_r_647_; 
v_a_boxed_644_ = lean_unbox_uint64(v_a_642_);
lean_dec_ref(v_a_642_);
v_b_boxed_645_ = lean_unbox_uint64(v_b_643_);
lean_dec_ref(v_b_643_);
v_res_646_ = lean_uint64_mod(v_a_boxed_644_, v_b_boxed_645_);
v_r_647_ = lean_box_uint64(v_res_646_);
return v_r_647_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt64_modn_spec__0(lean_object* v_a_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(64u);
v___x_650_ = l_BitVec_ofNat(v___x_649_, v_a_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt64_modn_spec__0___boxed(lean_object* v_a_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Nat_cast___at___00UInt64_modn_spec__0(v_a_651_);
lean_dec(v_a_651_);
return v_res_652_;
}
}
LEAN_EXPORT uint64_t l_UInt64_modn(uint64_t v_a_653_, lean_object* v_n_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint64_t v___x_658_; 
v___x_655_ = lean_uint64_to_nat(v_a_653_);
v___x_656_ = lean_nat_mod(v___x_655_, v_n_654_);
lean_dec(v___x_655_);
v___x_657_ = l_Nat_cast___at___00UInt64_modn_spec__0(v___x_656_);
lean_dec(v___x_656_);
v___x_658_ = lean_uint64_of_nat_mk(v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_UInt64_modn___boxed(lean_object* v_a_659_, lean_object* v_n_660_){
_start:
{
uint64_t v_a_boxed_661_; uint64_t v_res_662_; lean_object* v_r_663_; 
v_a_boxed_661_ = lean_unbox_uint64(v_a_659_);
lean_dec_ref(v_a_659_);
v_res_662_ = l_UInt64_modn(v_a_boxed_661_, v_n_660_);
lean_dec(v_n_660_);
v_r_663_ = lean_box_uint64(v_res_662_);
return v_r_663_;
}
}
LEAN_EXPORT lean_object* l_UInt64_land___boxed(lean_object* v_a_666_, lean_object* v_b_667_){
_start:
{
uint64_t v_a_boxed_668_; uint64_t v_b_boxed_669_; uint64_t v_res_670_; lean_object* v_r_671_; 
v_a_boxed_668_ = lean_unbox_uint64(v_a_666_);
lean_dec_ref(v_a_666_);
v_b_boxed_669_ = lean_unbox_uint64(v_b_667_);
lean_dec_ref(v_b_667_);
v_res_670_ = lean_uint64_land(v_a_boxed_668_, v_b_boxed_669_);
v_r_671_ = lean_box_uint64(v_res_670_);
return v_r_671_;
}
}
LEAN_EXPORT lean_object* l_UInt64_lor___boxed(lean_object* v_a_674_, lean_object* v_b_675_){
_start:
{
uint64_t v_a_boxed_676_; uint64_t v_b_boxed_677_; uint64_t v_res_678_; lean_object* v_r_679_; 
v_a_boxed_676_ = lean_unbox_uint64(v_a_674_);
lean_dec_ref(v_a_674_);
v_b_boxed_677_ = lean_unbox_uint64(v_b_675_);
lean_dec_ref(v_b_675_);
v_res_678_ = lean_uint64_lor(v_a_boxed_676_, v_b_boxed_677_);
v_r_679_ = lean_box_uint64(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT lean_object* l_UInt64_xor___boxed(lean_object* v_a_682_, lean_object* v_b_683_){
_start:
{
uint64_t v_a_boxed_684_; uint64_t v_b_boxed_685_; uint64_t v_res_686_; lean_object* v_r_687_; 
v_a_boxed_684_ = lean_unbox_uint64(v_a_682_);
lean_dec_ref(v_a_682_);
v_b_boxed_685_ = lean_unbox_uint64(v_b_683_);
lean_dec_ref(v_b_683_);
v_res_686_ = lean_uint64_xor(v_a_boxed_684_, v_b_boxed_685_);
v_r_687_ = lean_box_uint64(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT lean_object* l_UInt64_shiftLeft___boxed(lean_object* v_a_690_, lean_object* v_b_691_){
_start:
{
uint64_t v_a_boxed_692_; uint64_t v_b_boxed_693_; uint64_t v_res_694_; lean_object* v_r_695_; 
v_a_boxed_692_ = lean_unbox_uint64(v_a_690_);
lean_dec_ref(v_a_690_);
v_b_boxed_693_ = lean_unbox_uint64(v_b_691_);
lean_dec_ref(v_b_691_);
v_res_694_ = lean_uint64_shift_left(v_a_boxed_692_, v_b_boxed_693_);
v_r_695_ = lean_box_uint64(v_res_694_);
return v_r_695_;
}
}
LEAN_EXPORT lean_object* l_UInt64_shiftRight___boxed(lean_object* v_a_698_, lean_object* v_b_699_){
_start:
{
uint64_t v_a_boxed_700_; uint64_t v_b_boxed_701_; uint64_t v_res_702_; lean_object* v_r_703_; 
v_a_boxed_700_ = lean_unbox_uint64(v_a_698_);
lean_dec_ref(v_a_698_);
v_b_boxed_701_ = lean_unbox_uint64(v_b_699_);
lean_dec_ref(v_b_699_);
v_res_702_ = lean_uint64_shift_right(v_a_boxed_700_, v_b_boxed_701_);
v_r_703_ = lean_box_uint64(v_res_702_);
return v_r_703_;
}
}
static lean_object* _init_l_instLTUInt64(void){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_box(0);
return v___x_718_;
}
}
static lean_object* _init_l_instLEUInt64(void){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_box(0);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_UInt64_complement___boxed(lean_object* v_a_721_){
_start:
{
uint64_t v_a_boxed_722_; uint64_t v_res_723_; lean_object* v_r_724_; 
v_a_boxed_722_ = lean_unbox_uint64(v_a_721_);
lean_dec_ref(v_a_721_);
v_res_723_ = lean_uint64_complement(v_a_boxed_722_);
v_r_724_ = lean_box_uint64(v_res_723_);
return v_r_724_;
}
}
LEAN_EXPORT lean_object* l_UInt64_neg___boxed(lean_object* v_a_726_){
_start:
{
uint64_t v_a_boxed_727_; uint64_t v_res_728_; lean_object* v_r_729_; 
v_a_boxed_727_ = lean_unbox_uint64(v_a_726_);
lean_dec_ref(v_a_726_);
v_res_728_ = lean_uint64_neg(v_a_boxed_727_);
v_r_729_ = lean_box_uint64(v_res_728_);
return v_r_729_;
}
}
LEAN_EXPORT lean_object* l_Bool_toUInt64___boxed(lean_object* v_b_745_){
_start:
{
uint8_t v_b_boxed_746_; uint64_t v_res_747_; lean_object* v_r_748_; 
v_b_boxed_746_ = lean_unbox(v_b_745_);
v_res_747_ = lean_bool_to_uint64(v_b_boxed_746_);
v_r_748_ = lean_box_uint64(v_res_747_);
return v_r_748_;
}
}
LEAN_EXPORT lean_object* l_UInt64_decLt___boxed(lean_object* v_a_751_, lean_object* v_b_752_){
_start:
{
uint64_t v_a_boxed_753_; uint64_t v_b_boxed_754_; uint8_t v_res_755_; lean_object* v_r_756_; 
v_a_boxed_753_ = lean_unbox_uint64(v_a_751_);
lean_dec_ref(v_a_751_);
v_b_boxed_754_ = lean_unbox_uint64(v_b_752_);
lean_dec_ref(v_b_752_);
v_res_755_ = lean_uint64_dec_lt(v_a_boxed_753_, v_b_boxed_754_);
v_r_756_ = lean_box(v_res_755_);
return v_r_756_;
}
}
LEAN_EXPORT lean_object* l_UInt64_decLe___boxed(lean_object* v_a_759_, lean_object* v_b_760_){
_start:
{
uint64_t v_a_boxed_761_; uint64_t v_b_boxed_762_; uint8_t v_res_763_; lean_object* v_r_764_; 
v_a_boxed_761_ = lean_unbox_uint64(v_a_759_);
lean_dec_ref(v_a_759_);
v_b_boxed_762_ = lean_unbox_uint64(v_b_760_);
lean_dec_ref(v_b_760_);
v_res_763_ = lean_uint64_dec_le(v_a_boxed_761_, v_b_boxed_762_);
v_r_764_ = lean_box(v_res_763_);
return v_r_764_;
}
}
LEAN_EXPORT uint64_t l_instMaxUInt64___lam__0(uint64_t v_x_765_, uint64_t v_y_766_){
_start:
{
uint8_t v___x_767_; 
v___x_767_ = lean_uint64_dec_le(v_x_765_, v_y_766_);
if (v___x_767_ == 0)
{
return v_x_765_;
}
else
{
return v_y_766_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxUInt64___lam__0___boxed(lean_object* v_x_768_, lean_object* v_y_769_){
_start:
{
uint64_t v_x_boxed_770_; uint64_t v_y_boxed_771_; uint64_t v_res_772_; lean_object* v_r_773_; 
v_x_boxed_770_ = lean_unbox_uint64(v_x_768_);
lean_dec_ref(v_x_768_);
v_y_boxed_771_ = lean_unbox_uint64(v_y_769_);
lean_dec_ref(v_y_769_);
v_res_772_ = l_instMaxUInt64___lam__0(v_x_boxed_770_, v_y_boxed_771_);
v_r_773_ = lean_box_uint64(v_res_772_);
return v_r_773_;
}
}
LEAN_EXPORT uint64_t l_instMinUInt64___lam__0(uint64_t v_x_776_, uint64_t v_y_777_){
_start:
{
uint8_t v___x_778_; 
v___x_778_ = lean_uint64_dec_le(v_x_776_, v_y_777_);
if (v___x_778_ == 0)
{
return v_y_777_;
}
else
{
return v_x_776_;
}
}
}
LEAN_EXPORT lean_object* l_instMinUInt64___lam__0___boxed(lean_object* v_x_779_, lean_object* v_y_780_){
_start:
{
uint64_t v_x_boxed_781_; uint64_t v_y_boxed_782_; uint64_t v_res_783_; lean_object* v_r_784_; 
v_x_boxed_781_ = lean_unbox_uint64(v_x_779_);
lean_dec_ref(v_x_779_);
v_y_boxed_782_ = lean_unbox_uint64(v_y_780_);
lean_dec_ref(v_y_780_);
v_res_783_ = l_instMinUInt64___lam__0(v_x_boxed_781_, v_y_boxed_782_);
v_r_784_ = lean_box_uint64(v_res_783_);
return v_r_784_;
}
}
LEAN_EXPORT size_t l_USize_ofFin(lean_object* v_a_787_){
_start:
{
size_t v___x_788_; 
v___x_788_ = lean_usize_of_nat_mk(v_a_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_USize_ofFin___boxed(lean_object* v_a_789_){
_start:
{
size_t v_res_790_; lean_object* v_r_791_; 
v_res_790_ = l_USize_ofFin(v_a_789_);
v_r_791_ = lean_box_usize(v_res_790_);
return v_r_791_;
}
}
static lean_object* _init_l_USize_ofInt___closed__0(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_792_ = l_System_Platform_numBits;
v___x_793_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_794_ = l_Int_pow(v___x_793_, v___x_792_);
return v___x_794_;
}
}
LEAN_EXPORT size_t l_USize_ofInt(lean_object* v_x_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; size_t v___x_799_; 
v___x_796_ = lean_obj_once(&l_USize_ofInt___closed__0, &l_USize_ofInt___closed__0_once, _init_l_USize_ofInt___closed__0);
v___x_797_ = lean_int_emod(v_x_795_, v___x_796_);
v___x_798_ = l_Int_toNat(v___x_797_);
lean_dec(v___x_797_);
v___x_799_ = lean_usize_of_nat(v___x_798_);
lean_dec(v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_USize_ofInt___boxed(lean_object* v_x_800_){
_start:
{
size_t v_res_801_; lean_object* v_r_802_; 
v_res_801_ = l_USize_ofInt(v_x_800_);
lean_dec(v_x_800_);
v_r_802_ = lean_box_usize(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT lean_object* l_USize_mul___boxed(lean_object* v_a_805_, lean_object* v_b_806_){
_start:
{
size_t v_a_boxed_807_; size_t v_b_boxed_808_; size_t v_res_809_; lean_object* v_r_810_; 
v_a_boxed_807_ = lean_unbox_usize(v_a_805_);
lean_dec(v_a_805_);
v_b_boxed_808_ = lean_unbox_usize(v_b_806_);
lean_dec(v_b_806_);
v_res_809_ = lean_usize_mul(v_a_boxed_807_, v_b_boxed_808_);
v_r_810_ = lean_box_usize(v_res_809_);
return v_r_810_;
}
}
LEAN_EXPORT lean_object* l_USize_div___boxed(lean_object* v_a_813_, lean_object* v_b_814_){
_start:
{
size_t v_a_boxed_815_; size_t v_b_boxed_816_; size_t v_res_817_; lean_object* v_r_818_; 
v_a_boxed_815_ = lean_unbox_usize(v_a_813_);
lean_dec(v_a_813_);
v_b_boxed_816_ = lean_unbox_usize(v_b_814_);
lean_dec(v_b_814_);
v_res_817_ = lean_usize_div(v_a_boxed_815_, v_b_boxed_816_);
v_r_818_ = lean_box_usize(v_res_817_);
return v_r_818_;
}
}
LEAN_EXPORT size_t l_USize_pow(size_t v_x_819_, lean_object* v_n_820_){
_start:
{
lean_object* v_zero_821_; uint8_t v_isZero_822_; 
v_zero_821_ = lean_unsigned_to_nat(0u);
v_isZero_822_ = lean_nat_dec_eq(v_n_820_, v_zero_821_);
if (v_isZero_822_ == 1)
{
size_t v___x_823_; 
v___x_823_ = ((size_t)1ULL);
return v___x_823_;
}
else
{
lean_object* v_one_824_; lean_object* v_n_825_; size_t v___x_826_; size_t v___x_827_; 
v_one_824_ = lean_unsigned_to_nat(1u);
v_n_825_ = lean_nat_sub(v_n_820_, v_one_824_);
v___x_826_ = l_USize_pow(v_x_819_, v_n_825_);
lean_dec(v_n_825_);
v___x_827_ = lean_usize_mul(v___x_826_, v_x_819_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_USize_pow___boxed(lean_object* v_x_828_, lean_object* v_n_829_){
_start:
{
size_t v_x_boxed_830_; size_t v_res_831_; lean_object* v_r_832_; 
v_x_boxed_830_ = lean_unbox_usize(v_x_828_);
lean_dec(v_x_828_);
v_res_831_ = l_USize_pow(v_x_boxed_830_, v_n_829_);
lean_dec(v_n_829_);
v_r_832_ = lean_box_usize(v_res_831_);
return v_r_832_;
}
}
LEAN_EXPORT lean_object* l_USize_mod___boxed(lean_object* v_a_835_, lean_object* v_b_836_){
_start:
{
size_t v_a_boxed_837_; size_t v_b_boxed_838_; size_t v_res_839_; lean_object* v_r_840_; 
v_a_boxed_837_ = lean_unbox_usize(v_a_835_);
lean_dec(v_a_835_);
v_b_boxed_838_ = lean_unbox_usize(v_b_836_);
lean_dec(v_b_836_);
v_res_839_ = lean_usize_mod(v_a_boxed_837_, v_b_boxed_838_);
v_r_840_ = lean_box_usize(v_res_839_);
return v_r_840_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00USize_modn_spec__0(lean_object* v_a_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = l_System_Platform_numBits;
v___x_843_ = l_BitVec_ofNat(v___x_842_, v_a_841_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00USize_modn_spec__0___boxed(lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Nat_cast___at___00USize_modn_spec__0(v_a_844_);
lean_dec(v_a_844_);
return v_res_845_;
}
}
LEAN_EXPORT size_t l_USize_modn(size_t v_a_846_, lean_object* v_n_847_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; size_t v___x_851_; 
v___x_848_ = lean_usize_to_nat(v_a_846_);
v___x_849_ = lean_nat_mod(v___x_848_, v_n_847_);
lean_dec(v___x_848_);
v___x_850_ = l_Nat_cast___at___00USize_modn_spec__0(v___x_849_);
lean_dec(v___x_849_);
v___x_851_ = lean_usize_of_nat_mk(v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_USize_modn___boxed(lean_object* v_a_852_, lean_object* v_n_853_){
_start:
{
size_t v_a_boxed_854_; size_t v_res_855_; lean_object* v_r_856_; 
v_a_boxed_854_ = lean_unbox_usize(v_a_852_);
lean_dec(v_a_852_);
v_res_855_ = l_USize_modn(v_a_boxed_854_, v_n_853_);
lean_dec(v_n_853_);
v_r_856_ = lean_box_usize(v_res_855_);
return v_r_856_;
}
}
LEAN_EXPORT lean_object* l_USize_land___boxed(lean_object* v_a_859_, lean_object* v_b_860_){
_start:
{
size_t v_a_boxed_861_; size_t v_b_boxed_862_; size_t v_res_863_; lean_object* v_r_864_; 
v_a_boxed_861_ = lean_unbox_usize(v_a_859_);
lean_dec(v_a_859_);
v_b_boxed_862_ = lean_unbox_usize(v_b_860_);
lean_dec(v_b_860_);
v_res_863_ = lean_usize_land(v_a_boxed_861_, v_b_boxed_862_);
v_r_864_ = lean_box_usize(v_res_863_);
return v_r_864_;
}
}
LEAN_EXPORT lean_object* l_USize_lor___boxed(lean_object* v_a_867_, lean_object* v_b_868_){
_start:
{
size_t v_a_boxed_869_; size_t v_b_boxed_870_; size_t v_res_871_; lean_object* v_r_872_; 
v_a_boxed_869_ = lean_unbox_usize(v_a_867_);
lean_dec(v_a_867_);
v_b_boxed_870_ = lean_unbox_usize(v_b_868_);
lean_dec(v_b_868_);
v_res_871_ = lean_usize_lor(v_a_boxed_869_, v_b_boxed_870_);
v_r_872_ = lean_box_usize(v_res_871_);
return v_r_872_;
}
}
LEAN_EXPORT lean_object* l_USize_xor___boxed(lean_object* v_a_875_, lean_object* v_b_876_){
_start:
{
size_t v_a_boxed_877_; size_t v_b_boxed_878_; size_t v_res_879_; lean_object* v_r_880_; 
v_a_boxed_877_ = lean_unbox_usize(v_a_875_);
lean_dec(v_a_875_);
v_b_boxed_878_ = lean_unbox_usize(v_b_876_);
lean_dec(v_b_876_);
v_res_879_ = lean_usize_xor(v_a_boxed_877_, v_b_boxed_878_);
v_r_880_ = lean_box_usize(v_res_879_);
return v_r_880_;
}
}
LEAN_EXPORT lean_object* l_USize_shiftLeft___boxed(lean_object* v_a_883_, lean_object* v_b_884_){
_start:
{
size_t v_a_boxed_885_; size_t v_b_boxed_886_; size_t v_res_887_; lean_object* v_r_888_; 
v_a_boxed_885_ = lean_unbox_usize(v_a_883_);
lean_dec(v_a_883_);
v_b_boxed_886_ = lean_unbox_usize(v_b_884_);
lean_dec(v_b_884_);
v_res_887_ = lean_usize_shift_left(v_a_boxed_885_, v_b_boxed_886_);
v_r_888_ = lean_box_usize(v_res_887_);
return v_r_888_;
}
}
LEAN_EXPORT lean_object* l_USize_shiftRight___boxed(lean_object* v_a_891_, lean_object* v_b_892_){
_start:
{
size_t v_a_boxed_893_; size_t v_b_boxed_894_; size_t v_res_895_; lean_object* v_r_896_; 
v_a_boxed_893_ = lean_unbox_usize(v_a_891_);
lean_dec(v_a_891_);
v_b_boxed_894_ = lean_unbox_usize(v_b_892_);
lean_dec(v_b_892_);
v_res_895_ = lean_usize_shift_right(v_a_boxed_893_, v_b_boxed_894_);
v_r_896_ = lean_box_usize(v_res_895_);
return v_r_896_;
}
}
LEAN_EXPORT lean_object* l_USize_ofNat32___boxed(lean_object* v_n_899_, lean_object* v_h_900_){
_start:
{
size_t v_res_901_; lean_object* v_r_902_; 
v_res_901_ = lean_usize_of_nat(v_n_899_);
lean_dec(v_n_899_);
v_r_902_ = lean_box_usize(v_res_901_);
return v_r_902_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUSize___boxed(lean_object* v_a_904_){
_start:
{
uint8_t v_a_boxed_905_; size_t v_res_906_; lean_object* v_r_907_; 
v_a_boxed_905_ = lean_unbox(v_a_904_);
v_res_906_ = lean_uint8_to_usize(v_a_boxed_905_);
v_r_907_ = lean_box_usize(v_res_906_);
return v_r_907_;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt8___boxed(lean_object* v_a_909_){
_start:
{
size_t v_a_boxed_910_; uint8_t v_res_911_; lean_object* v_r_912_; 
v_a_boxed_910_ = lean_unbox_usize(v_a_909_);
lean_dec(v_a_909_);
v_res_911_ = lean_usize_to_uint8(v_a_boxed_910_);
v_r_912_ = lean_box(v_res_911_);
return v_r_912_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUSize___boxed(lean_object* v_a_914_){
_start:
{
uint16_t v_a_boxed_915_; size_t v_res_916_; lean_object* v_r_917_; 
v_a_boxed_915_ = lean_unbox(v_a_914_);
v_res_916_ = lean_uint16_to_usize(v_a_boxed_915_);
v_r_917_ = lean_box_usize(v_res_916_);
return v_r_917_;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt16___boxed(lean_object* v_a_919_){
_start:
{
size_t v_a_boxed_920_; uint16_t v_res_921_; lean_object* v_r_922_; 
v_a_boxed_920_ = lean_unbox_usize(v_a_919_);
lean_dec(v_a_919_);
v_res_921_ = lean_usize_to_uint16(v_a_boxed_920_);
v_r_922_ = lean_box(v_res_921_);
return v_r_922_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUSize___boxed(lean_object* v_a_924_){
_start:
{
uint32_t v_a_boxed_925_; size_t v_res_926_; lean_object* v_r_927_; 
v_a_boxed_925_ = lean_unbox_uint32(v_a_924_);
lean_dec(v_a_924_);
v_res_926_ = lean_uint32_to_usize(v_a_boxed_925_);
v_r_927_ = lean_box_usize(v_res_926_);
return v_r_927_;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt32___boxed(lean_object* v_a_929_){
_start:
{
size_t v_a_boxed_930_; uint32_t v_res_931_; lean_object* v_r_932_; 
v_a_boxed_930_ = lean_unbox_usize(v_a_929_);
lean_dec(v_a_929_);
v_res_931_ = lean_usize_to_uint32(v_a_boxed_930_);
v_r_932_ = lean_box_uint32(v_res_931_);
return v_r_932_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUSize___boxed(lean_object* v_a_934_){
_start:
{
uint64_t v_a_boxed_935_; size_t v_res_936_; lean_object* v_r_937_; 
v_a_boxed_935_ = lean_unbox_uint64(v_a_934_);
lean_dec_ref(v_a_934_);
v_res_936_ = lean_uint64_to_usize(v_a_boxed_935_);
v_r_937_ = lean_box_usize(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt64___boxed(lean_object* v_a_939_){
_start:
{
size_t v_a_boxed_940_; uint64_t v_res_941_; lean_object* v_r_942_; 
v_a_boxed_940_ = lean_unbox_usize(v_a_939_);
lean_dec(v_a_939_);
v_res_941_ = lean_usize_to_uint64(v_a_boxed_940_);
v_r_942_ = lean_box_uint64(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec32___redArg(size_t v_a_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = lean_usize_to_nat(v_a_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec32___redArg___boxed(lean_object* v_a_945_){
_start:
{
size_t v_a_boxed_946_; lean_object* v_res_947_; 
v_a_boxed_946_ = lean_unbox_usize(v_a_945_);
lean_dec(v_a_945_);
v_res_947_ = l_USize_toBitVec32___redArg(v_a_boxed_946_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec32(size_t v_a_948_, lean_object* v_h_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = lean_usize_to_nat(v_a_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec32___boxed(lean_object* v_a_951_, lean_object* v_h_952_){
_start:
{
size_t v_a_boxed_953_; lean_object* v_res_954_; 
v_a_boxed_953_ = lean_unbox_usize(v_a_951_);
lean_dec(v_a_951_);
v_res_954_ = l_USize_toBitVec32(v_a_boxed_953_, v_h_952_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec64___redArg(size_t v_a_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = lean_usize_to_nat(v_a_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec64___redArg___boxed(lean_object* v_a_957_){
_start:
{
size_t v_a_boxed_958_; lean_object* v_res_959_; 
v_a_boxed_958_ = lean_unbox_usize(v_a_957_);
lean_dec(v_a_957_);
v_res_959_ = l_USize_toBitVec64___redArg(v_a_boxed_958_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec64(size_t v_a_960_, lean_object* v_h_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_usize_to_nat(v_a_960_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_USize_toBitVec64___boxed(lean_object* v_a_963_, lean_object* v_h_964_){
_start:
{
size_t v_a_boxed_965_; lean_object* v_res_966_; 
v_a_boxed_965_ = lean_unbox_usize(v_a_963_);
lean_dec(v_a_963_);
v_res_966_ = l_USize_toBitVec64(v_a_boxed_965_, v_h_964_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_USize_complement___boxed(lean_object* v_a_978_){
_start:
{
size_t v_a_boxed_979_; size_t v_res_980_; lean_object* v_r_981_; 
v_a_boxed_979_ = lean_unbox_usize(v_a_978_);
lean_dec(v_a_978_);
v_res_980_ = lean_usize_complement(v_a_boxed_979_);
v_r_981_ = lean_box_usize(v_res_980_);
return v_r_981_;
}
}
LEAN_EXPORT lean_object* l_USize_neg___boxed(lean_object* v_a_983_){
_start:
{
size_t v_a_boxed_984_; size_t v_res_985_; lean_object* v_r_986_; 
v_a_boxed_984_ = lean_unbox_usize(v_a_983_);
lean_dec(v_a_983_);
v_res_985_ = lean_usize_neg(v_a_boxed_984_);
v_r_986_ = lean_box_usize(v_res_985_);
return v_r_986_;
}
}
LEAN_EXPORT lean_object* l_Bool_toUSize___boxed(lean_object* v_b_1002_){
_start:
{
uint8_t v_b_boxed_1003_; size_t v_res_1004_; lean_object* v_r_1005_; 
v_b_boxed_1003_ = lean_unbox(v_b_1002_);
v_res_1004_ = lean_bool_to_usize(v_b_boxed_1003_);
v_r_1005_ = lean_box_usize(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT size_t l_instMaxUSize___lam__0(size_t v_x_1006_, size_t v_y_1007_){
_start:
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_usize_dec_le(v_x_1006_, v_y_1007_);
if (v___x_1008_ == 0)
{
return v_x_1006_;
}
else
{
return v_y_1007_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxUSize___lam__0___boxed(lean_object* v_x_1009_, lean_object* v_y_1010_){
_start:
{
size_t v_x_boxed_1011_; size_t v_y_boxed_1012_; size_t v_res_1013_; lean_object* v_r_1014_; 
v_x_boxed_1011_ = lean_unbox_usize(v_x_1009_);
lean_dec(v_x_1009_);
v_y_boxed_1012_ = lean_unbox_usize(v_y_1010_);
lean_dec(v_y_1010_);
v_res_1013_ = l_instMaxUSize___lam__0(v_x_boxed_1011_, v_y_boxed_1012_);
v_r_1014_ = lean_box_usize(v_res_1013_);
return v_r_1014_;
}
}
LEAN_EXPORT size_t l_instMinUSize___lam__0(size_t v_x_1017_, size_t v_y_1018_){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_usize_dec_le(v_x_1017_, v_y_1018_);
if (v___x_1019_ == 0)
{
return v_y_1018_;
}
else
{
return v_x_1017_;
}
}
}
LEAN_EXPORT lean_object* l_instMinUSize___lam__0___boxed(lean_object* v_x_1020_, lean_object* v_y_1021_){
_start:
{
size_t v_x_boxed_1022_; size_t v_y_boxed_1023_; size_t v_res_1024_; lean_object* v_r_1025_; 
v_x_boxed_1022_ = lean_unbox_usize(v_x_1020_);
lean_dec(v_x_1020_);
v_y_boxed_1023_ = lean_unbox_usize(v_y_1021_);
lean_dec(v_y_1021_);
v_res_1024_ = l_instMinUSize___lam__0(v_x_boxed_1022_, v_y_boxed_1023_);
v_r_1025_ = lean_box_usize(v_res_1024_);
return v_r_1025_;
}
}
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
