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
uint8_t l_UInt8_ofFin(lean_object* v_a_1_){
_start:
{
uint8_t v___x_2_; 
v___x_2_ = lean_uint8_of_nat_mk(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT void l_UInt8_ofFin_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
uint8_t v_res_3_;
v_res_3_ = l_UInt8_ofFin(v_a_1_);
stack->m_num = v_res_3_;
}
LEAN_EXPORT lean_object* l_UInt8_ofFin___boxed(lean_object* v_a_4_){
_start:
{
uint8_t v_res_5_; lean_object* v_r_6_; 
v_res_5_ = l_UInt8_ofFin(v_a_4_);
v_r_6_ = lean_box(v_res_5_);
return v_r_6_;
}
}
static lean_object* _init_l_UInt8_ofInt___closed__0(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_unsigned_to_nat(2u);
v___x_8_ = lean_nat_to_int(v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_UInt8_ofInt___closed__1(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = lean_unsigned_to_nat(8u);
v___x_10_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_11_ = l_Int_pow(v___x_10_, v___x_9_);
return v___x_11_;
}
}
uint8_t l_UInt8_ofInt(lean_object* v_x_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_13_ = lean_obj_once(&l_UInt8_ofInt___closed__1, &l_UInt8_ofInt___closed__1_once, _init_l_UInt8_ofInt___closed__1);
v___x_14_ = lean_int_emod(v_x_12_, v___x_13_);
v___x_15_ = l_Int_toNat(v___x_14_);
lean_dec(v___x_14_);
v___x_16_ = lean_uint8_of_nat(v___x_15_);
lean_dec(v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT void l_UInt8_ofInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_12_ = stack[0].m_obj;
uint8_t v_res_17_;
v_res_17_ = l_UInt8_ofInt(v_x_12_);
stack->m_num = v_res_17_;
}
LEAN_EXPORT lean_object* l_UInt8_ofInt___boxed(lean_object* v_x_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_UInt8_ofInt(v_x_18_);
lean_dec(v_x_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT void l_UInt8_add_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_21_ = stack[0].m_num;
uint8_t v_b_22_ = stack[1].m_num;
uint8_t v_res_23_;
v_res_23_ = lean_uint8_add(v_a_21_, v_b_22_);
stack->m_num = v_res_23_;
}
LEAN_EXPORT lean_object* l_UInt8_add___boxed(lean_object* v_a_24_, lean_object* v_b_25_){
_start:
{
uint8_t v_a_boxed_26_; uint8_t v_b_boxed_27_; uint8_t v_res_28_; lean_object* v_r_29_; 
v_a_boxed_26_ = lean_unbox(v_a_24_);
v_b_boxed_27_ = lean_unbox(v_b_25_);
v_res_28_ = lean_uint8_add(v_a_boxed_26_, v_b_boxed_27_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT void l_UInt8_sub_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_30_ = stack[0].m_num;
uint8_t v_b_31_ = stack[1].m_num;
uint8_t v_res_32_;
v_res_32_ = lean_uint8_sub(v_a_30_, v_b_31_);
stack->m_num = v_res_32_;
}
LEAN_EXPORT lean_object* l_UInt8_sub___boxed(lean_object* v_a_33_, lean_object* v_b_34_){
_start:
{
uint8_t v_a_boxed_35_; uint8_t v_b_boxed_36_; uint8_t v_res_37_; lean_object* v_r_38_; 
v_a_boxed_35_ = lean_unbox(v_a_33_);
v_b_boxed_36_ = lean_unbox(v_b_34_);
v_res_37_ = lean_uint8_sub(v_a_boxed_35_, v_b_boxed_36_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT void l_UInt8_mul_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_39_ = stack[0].m_num;
uint8_t v_b_40_ = stack[1].m_num;
uint8_t v_res_41_;
v_res_41_ = lean_uint8_mul(v_a_39_, v_b_40_);
stack->m_num = v_res_41_;
}
LEAN_EXPORT lean_object* l_UInt8_mul___boxed(lean_object* v_a_42_, lean_object* v_b_43_){
_start:
{
uint8_t v_a_boxed_44_; uint8_t v_b_boxed_45_; uint8_t v_res_46_; lean_object* v_r_47_; 
v_a_boxed_44_ = lean_unbox(v_a_42_);
v_b_boxed_45_ = lean_unbox(v_b_43_);
v_res_46_ = lean_uint8_mul(v_a_boxed_44_, v_b_boxed_45_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT void l_UInt8_div_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_48_ = stack[0].m_num;
uint8_t v_b_49_ = stack[1].m_num;
uint8_t v_res_50_;
v_res_50_ = lean_uint8_div(v_a_48_, v_b_49_);
stack->m_num = v_res_50_;
}
LEAN_EXPORT lean_object* l_UInt8_div___boxed(lean_object* v_a_51_, lean_object* v_b_52_){
_start:
{
uint8_t v_a_boxed_53_; uint8_t v_b_boxed_54_; uint8_t v_res_55_; lean_object* v_r_56_; 
v_a_boxed_53_ = lean_unbox(v_a_51_);
v_b_boxed_54_ = lean_unbox(v_b_52_);
v_res_55_ = lean_uint8_div(v_a_boxed_53_, v_b_boxed_54_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
uint8_t l_UInt8_pow(uint8_t v_x_57_, lean_object* v_n_58_){
_start:
{
lean_object* v_zero_59_; uint8_t v_isZero_60_; 
v_zero_59_ = lean_unsigned_to_nat(0u);
v_isZero_60_ = lean_nat_dec_eq(v_n_58_, v_zero_59_);
if (v_isZero_60_ == 1)
{
uint8_t v___x_61_; 
v___x_61_ = 1;
return v___x_61_;
}
else
{
lean_object* v_one_62_; lean_object* v_n_63_; uint8_t v___x_64_; uint8_t v___x_65_; 
v_one_62_ = lean_unsigned_to_nat(1u);
v_n_63_ = lean_nat_sub(v_n_58_, v_one_62_);
v___x_64_ = l_UInt8_pow(v_x_57_, v_n_63_);
lean_dec(v_n_63_);
v___x_65_ = lean_uint8_mul(v___x_64_, v_x_57_);
return v___x_65_;
}
}
}
LEAN_EXPORT void l_UInt8_pow_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_57_ = stack[0].m_num;
lean_object* v_n_58_ = stack[1].m_obj;
uint8_t v_res_66_;
v_res_66_ = l_UInt8_pow(v_x_57_, v_n_58_);
stack->m_num = v_res_66_;
}
LEAN_EXPORT lean_object* l_UInt8_pow___boxed(lean_object* v_x_67_, lean_object* v_n_68_){
_start:
{
uint8_t v_x_boxed_69_; uint8_t v_res_70_; lean_object* v_r_71_; 
v_x_boxed_69_ = lean_unbox(v_x_67_);
v_res_70_ = l_UInt8_pow(v_x_boxed_69_, v_n_68_);
lean_dec(v_n_68_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT void l_UInt8_mod_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_72_ = stack[0].m_num;
uint8_t v_b_73_ = stack[1].m_num;
uint8_t v_res_74_;
v_res_74_ = lean_uint8_mod(v_a_72_, v_b_73_);
stack->m_num = v_res_74_;
}
LEAN_EXPORT lean_object* l_UInt8_mod___boxed(lean_object* v_a_75_, lean_object* v_b_76_){
_start:
{
uint8_t v_a_boxed_77_; uint8_t v_b_boxed_78_; uint8_t v_res_79_; lean_object* v_r_80_; 
v_a_boxed_77_ = lean_unbox(v_a_75_);
v_b_boxed_78_ = lean_unbox(v_b_76_);
v_res_79_ = lean_uint8_mod(v_a_boxed_77_, v_b_boxed_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt8_modn_spec__0(lean_object* v_a_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(8u);
v___x_83_ = l_BitVec_ofNat(v___x_82_, v_a_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt8_modn_spec__0___boxed(lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Nat_cast___at___00UInt8_modn_spec__0(v_a_84_);
lean_dec(v_a_84_);
return v_res_85_;
}
}
uint8_t l_UInt8_modn(uint8_t v_a_86_, lean_object* v_n_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_88_ = lean_uint8_to_nat(v_a_86_);
v___x_89_ = lean_nat_mod(v___x_88_, v_n_87_);
lean_dec(v___x_88_);
v___x_90_ = l_Nat_cast___at___00UInt8_modn_spec__0(v___x_89_);
lean_dec(v___x_89_);
v___x_91_ = lean_uint8_of_nat_mk(v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT void l_UInt8_modn_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_86_ = stack[0].m_num;
lean_object* v_n_87_ = stack[1].m_obj;
uint8_t v_res_92_;
v_res_92_ = l_UInt8_modn(v_a_86_, v_n_87_);
stack->m_num = v_res_92_;
}
LEAN_EXPORT lean_object* l_UInt8_modn___boxed(lean_object* v_a_93_, lean_object* v_n_94_){
_start:
{
uint8_t v_a_boxed_95_; uint8_t v_res_96_; lean_object* v_r_97_; 
v_a_boxed_95_ = lean_unbox(v_a_93_);
v_res_96_ = l_UInt8_modn(v_a_boxed_95_, v_n_94_);
lean_dec(v_n_94_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT void l_UInt8_land_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_98_ = stack[0].m_num;
uint8_t v_b_99_ = stack[1].m_num;
uint8_t v_res_100_;
v_res_100_ = lean_uint8_land(v_a_98_, v_b_99_);
stack->m_num = v_res_100_;
}
LEAN_EXPORT lean_object* l_UInt8_land___boxed(lean_object* v_a_101_, lean_object* v_b_102_){
_start:
{
uint8_t v_a_boxed_103_; uint8_t v_b_boxed_104_; uint8_t v_res_105_; lean_object* v_r_106_; 
v_a_boxed_103_ = lean_unbox(v_a_101_);
v_b_boxed_104_ = lean_unbox(v_b_102_);
v_res_105_ = lean_uint8_land(v_a_boxed_103_, v_b_boxed_104_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT void l_UInt8_lor_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_107_ = stack[0].m_num;
uint8_t v_b_108_ = stack[1].m_num;
uint8_t v_res_109_;
v_res_109_ = lean_uint8_lor(v_a_107_, v_b_108_);
stack->m_num = v_res_109_;
}
LEAN_EXPORT lean_object* l_UInt8_lor___boxed(lean_object* v_a_110_, lean_object* v_b_111_){
_start:
{
uint8_t v_a_boxed_112_; uint8_t v_b_boxed_113_; uint8_t v_res_114_; lean_object* v_r_115_; 
v_a_boxed_112_ = lean_unbox(v_a_110_);
v_b_boxed_113_ = lean_unbox(v_b_111_);
v_res_114_ = lean_uint8_lor(v_a_boxed_112_, v_b_boxed_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT void l_UInt8_xor_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_116_ = stack[0].m_num;
uint8_t v_b_117_ = stack[1].m_num;
uint8_t v_res_118_;
v_res_118_ = lean_uint8_xor(v_a_116_, v_b_117_);
stack->m_num = v_res_118_;
}
LEAN_EXPORT lean_object* l_UInt8_xor___boxed(lean_object* v_a_119_, lean_object* v_b_120_){
_start:
{
uint8_t v_a_boxed_121_; uint8_t v_b_boxed_122_; uint8_t v_res_123_; lean_object* v_r_124_; 
v_a_boxed_121_ = lean_unbox(v_a_119_);
v_b_boxed_122_ = lean_unbox(v_b_120_);
v_res_123_ = lean_uint8_xor(v_a_boxed_121_, v_b_boxed_122_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT void l_UInt8_shiftLeft_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_125_ = stack[0].m_num;
uint8_t v_b_126_ = stack[1].m_num;
uint8_t v_res_127_;
v_res_127_ = lean_uint8_shift_left(v_a_125_, v_b_126_);
stack->m_num = v_res_127_;
}
LEAN_EXPORT lean_object* l_UInt8_shiftLeft___boxed(lean_object* v_a_128_, lean_object* v_b_129_){
_start:
{
uint8_t v_a_boxed_130_; uint8_t v_b_boxed_131_; uint8_t v_res_132_; lean_object* v_r_133_; 
v_a_boxed_130_ = lean_unbox(v_a_128_);
v_b_boxed_131_ = lean_unbox(v_b_129_);
v_res_132_ = lean_uint8_shift_left(v_a_boxed_130_, v_b_boxed_131_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT void l_UInt8_shiftRight_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_134_ = stack[0].m_num;
uint8_t v_b_135_ = stack[1].m_num;
uint8_t v_res_136_;
v_res_136_ = lean_uint8_shift_right(v_a_134_, v_b_135_);
stack->m_num = v_res_136_;
}
LEAN_EXPORT lean_object* l_UInt8_shiftRight___boxed(lean_object* v_a_137_, lean_object* v_b_138_){
_start:
{
uint8_t v_a_boxed_139_; uint8_t v_b_boxed_140_; uint8_t v_res_141_; lean_object* v_r_142_; 
v_a_boxed_139_ = lean_unbox(v_a_137_);
v_b_boxed_140_ = lean_unbox(v_b_138_);
v_res_141_ = lean_uint8_shift_right(v_a_boxed_139_, v_b_boxed_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT void l_UInt8_complement_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_157_ = stack[0].m_num;
uint8_t v_res_158_;
v_res_158_ = lean_uint8_complement(v_a_157_);
stack->m_num = v_res_158_;
}
LEAN_EXPORT lean_object* l_UInt8_complement___boxed(lean_object* v_a_159_){
_start:
{
uint8_t v_a_boxed_160_; uint8_t v_res_161_; lean_object* v_r_162_; 
v_a_boxed_160_ = lean_unbox(v_a_159_);
v_res_161_ = lean_uint8_complement(v_a_boxed_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT void l_UInt8_neg_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_163_ = stack[0].m_num;
uint8_t v_res_164_;
v_res_164_ = lean_uint8_neg(v_a_163_);
stack->m_num = v_res_164_;
}
LEAN_EXPORT lean_object* l_UInt8_neg___boxed(lean_object* v_a_165_){
_start:
{
uint8_t v_a_boxed_166_; uint8_t v_res_167_; lean_object* v_r_168_; 
v_a_boxed_166_ = lean_unbox(v_a_165_);
v_res_167_ = lean_uint8_neg(v_a_boxed_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT void l_Bool_toUInt8_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_183_ = stack[0].m_num;
uint8_t v_res_184_;
v_res_184_ = lean_bool_to_uint8(v_b_183_);
stack->m_num = v_res_184_;
}
LEAN_EXPORT lean_object* l_Bool_toUInt8___boxed(lean_object* v_b_185_){
_start:
{
uint8_t v_b_boxed_186_; uint8_t v_res_187_; lean_object* v_r_188_; 
v_b_boxed_186_ = lean_unbox(v_b_185_);
v_res_187_ = lean_bool_to_uint8(v_b_boxed_186_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
uint8_t l_instMaxUInt8___lam__0(uint8_t v_x_189_, uint8_t v_y_190_){
_start:
{
uint8_t v___x_191_; 
v___x_191_ = lean_uint8_dec_le(v_x_189_, v_y_190_);
if (v___x_191_ == 0)
{
return v_x_189_;
}
else
{
return v_y_190_;
}
}
}
LEAN_EXPORT void l_instMaxUInt8___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_189_ = stack[0].m_num;
uint8_t v_y_190_ = stack[1].m_num;
uint8_t v_res_192_;
v_res_192_ = l_instMaxUInt8___lam__0(v_x_189_, v_y_190_);
stack->m_num = v_res_192_;
}
LEAN_EXPORT lean_object* l_instMaxUInt8___lam__0___boxed(lean_object* v_x_193_, lean_object* v_y_194_){
_start:
{
uint8_t v_x_boxed_195_; uint8_t v_y_boxed_196_; uint8_t v_res_197_; lean_object* v_r_198_; 
v_x_boxed_195_ = lean_unbox(v_x_193_);
v_y_boxed_196_ = lean_unbox(v_y_194_);
v_res_197_ = l_instMaxUInt8___lam__0(v_x_boxed_195_, v_y_boxed_196_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
uint8_t l_instMinUInt8___lam__0(uint8_t v_x_201_, uint8_t v_y_202_){
_start:
{
uint8_t v___x_203_; 
v___x_203_ = lean_uint8_dec_le(v_x_201_, v_y_202_);
if (v___x_203_ == 0)
{
return v_y_202_;
}
else
{
return v_x_201_;
}
}
}
LEAN_EXPORT void l_instMinUInt8___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_201_ = stack[0].m_num;
uint8_t v_y_202_ = stack[1].m_num;
uint8_t v_res_204_;
v_res_204_ = l_instMinUInt8___lam__0(v_x_201_, v_y_202_);
stack->m_num = v_res_204_;
}
LEAN_EXPORT lean_object* l_instMinUInt8___lam__0___boxed(lean_object* v_x_205_, lean_object* v_y_206_){
_start:
{
uint8_t v_x_boxed_207_; uint8_t v_y_boxed_208_; uint8_t v_res_209_; lean_object* v_r_210_; 
v_x_boxed_207_ = lean_unbox(v_x_205_);
v_y_boxed_208_ = lean_unbox(v_y_206_);
v_res_209_ = l_instMinUInt8___lam__0(v_x_boxed_207_, v_y_boxed_208_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
uint8_t l_UInt8_toAsciiLower(uint8_t v_b_213_){
_start:
{
uint8_t v___x_214_; uint8_t v___x_215_; uint8_t v___x_216_; uint8_t v___x_217_; uint8_t v___x_218_; uint8_t v___x_219_; uint8_t v___x_220_; uint8_t v___x_221_; 
v___x_214_ = 65;
v___x_215_ = lean_uint8_sub(v_b_213_, v___x_214_);
v___x_216_ = 26;
v___x_217_ = lean_uint8_dec_lt(v___x_215_, v___x_216_);
v___x_218_ = lean_bool_to_uint8(v___x_217_);
v___x_219_ = 5;
v___x_220_ = lean_uint8_shift_left(v___x_218_, v___x_219_);
v___x_221_ = lean_uint8_add(v_b_213_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT void l_UInt8_toAsciiLower_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_213_ = stack[0].m_num;
uint8_t v_res_222_;
v_res_222_ = l_UInt8_toAsciiLower(v_b_213_);
stack->m_num = v_res_222_;
}
LEAN_EXPORT lean_object* l_UInt8_toAsciiLower___boxed(lean_object* v_b_223_){
_start:
{
uint8_t v_b_boxed_224_; uint8_t v_res_225_; lean_object* v_r_226_; 
v_b_boxed_224_ = lean_unbox(v_b_223_);
v_res_225_ = l_UInt8_toAsciiLower(v_b_boxed_224_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
uint8_t l_UInt8_toAsciiUpper(uint8_t v_b_227_){
_start:
{
uint8_t v___x_228_; uint8_t v___x_229_; uint8_t v___x_230_; uint8_t v___x_231_; uint8_t v___x_232_; uint8_t v___x_233_; uint8_t v___x_234_; uint8_t v___x_235_; 
v___x_228_ = 97;
v___x_229_ = lean_uint8_sub(v_b_227_, v___x_228_);
v___x_230_ = 26;
v___x_231_ = lean_uint8_dec_lt(v___x_229_, v___x_230_);
v___x_232_ = lean_bool_to_uint8(v___x_231_);
v___x_233_ = 5;
v___x_234_ = lean_uint8_shift_left(v___x_232_, v___x_233_);
v___x_235_ = lean_uint8_sub(v_b_227_, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT void l_UInt8_toAsciiUpper_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_227_ = stack[0].m_num;
uint8_t v_res_236_;
v_res_236_ = l_UInt8_toAsciiUpper(v_b_227_);
stack->m_num = v_res_236_;
}
LEAN_EXPORT lean_object* l_UInt8_toAsciiUpper___boxed(lean_object* v_b_237_){
_start:
{
uint8_t v_b_boxed_238_; uint8_t v_res_239_; lean_object* v_r_240_; 
v_b_boxed_238_ = lean_unbox(v_b_237_);
v_res_239_ = l_UInt8_toAsciiUpper(v_b_boxed_238_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
uint16_t l_UInt16_ofFin(lean_object* v_a_241_){
_start:
{
uint16_t v___x_242_; 
v___x_242_ = lean_uint16_of_nat_mk(v_a_241_);
return v___x_242_;
}
}
LEAN_EXPORT void l_UInt16_ofFin_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_241_ = stack[0].m_obj;
uint16_t v_res_243_;
v_res_243_ = l_UInt16_ofFin(v_a_241_);
stack->m_num = v_res_243_;
}
LEAN_EXPORT lean_object* l_UInt16_ofFin___boxed(lean_object* v_a_244_){
_start:
{
uint16_t v_res_245_; lean_object* v_r_246_; 
v_res_245_ = l_UInt16_ofFin(v_a_244_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
static lean_object* _init_l_UInt16_ofInt___closed__0(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_unsigned_to_nat(16u);
v___x_248_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_249_ = l_Int_pow(v___x_248_, v___x_247_);
return v___x_249_;
}
}
uint16_t l_UInt16_ofInt(lean_object* v_x_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint16_t v___x_254_; 
v___x_251_ = lean_obj_once(&l_UInt16_ofInt___closed__0, &l_UInt16_ofInt___closed__0_once, _init_l_UInt16_ofInt___closed__0);
v___x_252_ = lean_int_emod(v_x_250_, v___x_251_);
v___x_253_ = l_Int_toNat(v___x_252_);
lean_dec(v___x_252_);
v___x_254_ = lean_uint16_of_nat(v___x_253_);
lean_dec(v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT void l_UInt16_ofInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_250_ = stack[0].m_obj;
uint16_t v_res_255_;
v_res_255_ = l_UInt16_ofInt(v_x_250_);
stack->m_num = v_res_255_;
}
LEAN_EXPORT lean_object* l_UInt16_ofInt___boxed(lean_object* v_x_256_){
_start:
{
uint16_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_UInt16_ofInt(v_x_256_);
lean_dec(v_x_256_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT void l_UInt16_add_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_259_ = stack[0].m_num;
uint16_t v_b_260_ = stack[1].m_num;
uint16_t v_res_261_;
v_res_261_ = lean_uint16_add(v_a_259_, v_b_260_);
stack->m_num = v_res_261_;
}
LEAN_EXPORT lean_object* l_UInt16_add___boxed(lean_object* v_a_262_, lean_object* v_b_263_){
_start:
{
uint16_t v_a_boxed_264_; uint16_t v_b_boxed_265_; uint16_t v_res_266_; lean_object* v_r_267_; 
v_a_boxed_264_ = lean_unbox(v_a_262_);
v_b_boxed_265_ = lean_unbox(v_b_263_);
v_res_266_ = lean_uint16_add(v_a_boxed_264_, v_b_boxed_265_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT void l_UInt16_sub_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_268_ = stack[0].m_num;
uint16_t v_b_269_ = stack[1].m_num;
uint16_t v_res_270_;
v_res_270_ = lean_uint16_sub(v_a_268_, v_b_269_);
stack->m_num = v_res_270_;
}
LEAN_EXPORT lean_object* l_UInt16_sub___boxed(lean_object* v_a_271_, lean_object* v_b_272_){
_start:
{
uint16_t v_a_boxed_273_; uint16_t v_b_boxed_274_; uint16_t v_res_275_; lean_object* v_r_276_; 
v_a_boxed_273_ = lean_unbox(v_a_271_);
v_b_boxed_274_ = lean_unbox(v_b_272_);
v_res_275_ = lean_uint16_sub(v_a_boxed_273_, v_b_boxed_274_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT void l_UInt16_mul_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_277_ = stack[0].m_num;
uint16_t v_b_278_ = stack[1].m_num;
uint16_t v_res_279_;
v_res_279_ = lean_uint16_mul(v_a_277_, v_b_278_);
stack->m_num = v_res_279_;
}
LEAN_EXPORT lean_object* l_UInt16_mul___boxed(lean_object* v_a_280_, lean_object* v_b_281_){
_start:
{
uint16_t v_a_boxed_282_; uint16_t v_b_boxed_283_; uint16_t v_res_284_; lean_object* v_r_285_; 
v_a_boxed_282_ = lean_unbox(v_a_280_);
v_b_boxed_283_ = lean_unbox(v_b_281_);
v_res_284_ = lean_uint16_mul(v_a_boxed_282_, v_b_boxed_283_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
LEAN_EXPORT void l_UInt16_div_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_286_ = stack[0].m_num;
uint16_t v_b_287_ = stack[1].m_num;
uint16_t v_res_288_;
v_res_288_ = lean_uint16_div(v_a_286_, v_b_287_);
stack->m_num = v_res_288_;
}
LEAN_EXPORT lean_object* l_UInt16_div___boxed(lean_object* v_a_289_, lean_object* v_b_290_){
_start:
{
uint16_t v_a_boxed_291_; uint16_t v_b_boxed_292_; uint16_t v_res_293_; lean_object* v_r_294_; 
v_a_boxed_291_ = lean_unbox(v_a_289_);
v_b_boxed_292_ = lean_unbox(v_b_290_);
v_res_293_ = lean_uint16_div(v_a_boxed_291_, v_b_boxed_292_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
uint16_t l_UInt16_pow(uint16_t v_x_295_, lean_object* v_n_296_){
_start:
{
lean_object* v_zero_297_; uint8_t v_isZero_298_; 
v_zero_297_ = lean_unsigned_to_nat(0u);
v_isZero_298_ = lean_nat_dec_eq(v_n_296_, v_zero_297_);
if (v_isZero_298_ == 1)
{
uint16_t v___x_299_; 
v___x_299_ = 1;
return v___x_299_;
}
else
{
lean_object* v_one_300_; lean_object* v_n_301_; uint16_t v___x_302_; uint16_t v___x_303_; 
v_one_300_ = lean_unsigned_to_nat(1u);
v_n_301_ = lean_nat_sub(v_n_296_, v_one_300_);
v___x_302_ = l_UInt16_pow(v_x_295_, v_n_301_);
lean_dec(v_n_301_);
v___x_303_ = lean_uint16_mul(v___x_302_, v_x_295_);
return v___x_303_;
}
}
}
LEAN_EXPORT void l_UInt16_pow_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_295_ = stack[0].m_num;
lean_object* v_n_296_ = stack[1].m_obj;
uint16_t v_res_304_;
v_res_304_ = l_UInt16_pow(v_x_295_, v_n_296_);
stack->m_num = v_res_304_;
}
LEAN_EXPORT lean_object* l_UInt16_pow___boxed(lean_object* v_x_305_, lean_object* v_n_306_){
_start:
{
uint16_t v_x_boxed_307_; uint16_t v_res_308_; lean_object* v_r_309_; 
v_x_boxed_307_ = lean_unbox(v_x_305_);
v_res_308_ = l_UInt16_pow(v_x_boxed_307_, v_n_306_);
lean_dec(v_n_306_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT void l_UInt16_mod_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_310_ = stack[0].m_num;
uint16_t v_b_311_ = stack[1].m_num;
uint16_t v_res_312_;
v_res_312_ = lean_uint16_mod(v_a_310_, v_b_311_);
stack->m_num = v_res_312_;
}
LEAN_EXPORT lean_object* l_UInt16_mod___boxed(lean_object* v_a_313_, lean_object* v_b_314_){
_start:
{
uint16_t v_a_boxed_315_; uint16_t v_b_boxed_316_; uint16_t v_res_317_; lean_object* v_r_318_; 
v_a_boxed_315_ = lean_unbox(v_a_313_);
v_b_boxed_316_ = lean_unbox(v_b_314_);
v_res_317_ = lean_uint16_mod(v_a_boxed_315_, v_b_boxed_316_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt16_modn_spec__0(lean_object* v_a_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(16u);
v___x_321_ = l_BitVec_ofNat(v___x_320_, v_a_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt16_modn_spec__0___boxed(lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Nat_cast___at___00UInt16_modn_spec__0(v_a_322_);
lean_dec(v_a_322_);
return v_res_323_;
}
}
uint16_t l_UInt16_modn(uint16_t v_a_324_, lean_object* v_n_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint16_t v___x_329_; 
v___x_326_ = lean_uint16_to_nat(v_a_324_);
v___x_327_ = lean_nat_mod(v___x_326_, v_n_325_);
lean_dec(v___x_326_);
v___x_328_ = l_Nat_cast___at___00UInt16_modn_spec__0(v___x_327_);
lean_dec(v___x_327_);
v___x_329_ = lean_uint16_of_nat_mk(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT void l_UInt16_modn_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_324_ = stack[0].m_num;
lean_object* v_n_325_ = stack[1].m_obj;
uint16_t v_res_330_;
v_res_330_ = l_UInt16_modn(v_a_324_, v_n_325_);
stack->m_num = v_res_330_;
}
LEAN_EXPORT lean_object* l_UInt16_modn___boxed(lean_object* v_a_331_, lean_object* v_n_332_){
_start:
{
uint16_t v_a_boxed_333_; uint16_t v_res_334_; lean_object* v_r_335_; 
v_a_boxed_333_ = lean_unbox(v_a_331_);
v_res_334_ = l_UInt16_modn(v_a_boxed_333_, v_n_332_);
lean_dec(v_n_332_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT void l_UInt16_land_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_336_ = stack[0].m_num;
uint16_t v_b_337_ = stack[1].m_num;
uint16_t v_res_338_;
v_res_338_ = lean_uint16_land(v_a_336_, v_b_337_);
stack->m_num = v_res_338_;
}
LEAN_EXPORT lean_object* l_UInt16_land___boxed(lean_object* v_a_339_, lean_object* v_b_340_){
_start:
{
uint16_t v_a_boxed_341_; uint16_t v_b_boxed_342_; uint16_t v_res_343_; lean_object* v_r_344_; 
v_a_boxed_341_ = lean_unbox(v_a_339_);
v_b_boxed_342_ = lean_unbox(v_b_340_);
v_res_343_ = lean_uint16_land(v_a_boxed_341_, v_b_boxed_342_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT void l_UInt16_lor_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_345_ = stack[0].m_num;
uint16_t v_b_346_ = stack[1].m_num;
uint16_t v_res_347_;
v_res_347_ = lean_uint16_lor(v_a_345_, v_b_346_);
stack->m_num = v_res_347_;
}
LEAN_EXPORT lean_object* l_UInt16_lor___boxed(lean_object* v_a_348_, lean_object* v_b_349_){
_start:
{
uint16_t v_a_boxed_350_; uint16_t v_b_boxed_351_; uint16_t v_res_352_; lean_object* v_r_353_; 
v_a_boxed_350_ = lean_unbox(v_a_348_);
v_b_boxed_351_ = lean_unbox(v_b_349_);
v_res_352_ = lean_uint16_lor(v_a_boxed_350_, v_b_boxed_351_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT void l_UInt16_xor_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_354_ = stack[0].m_num;
uint16_t v_b_355_ = stack[1].m_num;
uint16_t v_res_356_;
v_res_356_ = lean_uint16_xor(v_a_354_, v_b_355_);
stack->m_num = v_res_356_;
}
LEAN_EXPORT lean_object* l_UInt16_xor___boxed(lean_object* v_a_357_, lean_object* v_b_358_){
_start:
{
uint16_t v_a_boxed_359_; uint16_t v_b_boxed_360_; uint16_t v_res_361_; lean_object* v_r_362_; 
v_a_boxed_359_ = lean_unbox(v_a_357_);
v_b_boxed_360_ = lean_unbox(v_b_358_);
v_res_361_ = lean_uint16_xor(v_a_boxed_359_, v_b_boxed_360_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT void l_UInt16_shiftLeft_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_363_ = stack[0].m_num;
uint16_t v_b_364_ = stack[1].m_num;
uint16_t v_res_365_;
v_res_365_ = lean_uint16_shift_left(v_a_363_, v_b_364_);
stack->m_num = v_res_365_;
}
LEAN_EXPORT lean_object* l_UInt16_shiftLeft___boxed(lean_object* v_a_366_, lean_object* v_b_367_){
_start:
{
uint16_t v_a_boxed_368_; uint16_t v_b_boxed_369_; uint16_t v_res_370_; lean_object* v_r_371_; 
v_a_boxed_368_ = lean_unbox(v_a_366_);
v_b_boxed_369_ = lean_unbox(v_b_367_);
v_res_370_ = lean_uint16_shift_left(v_a_boxed_368_, v_b_boxed_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT void l_UInt16_shiftRight_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_372_ = stack[0].m_num;
uint16_t v_b_373_ = stack[1].m_num;
uint16_t v_res_374_;
v_res_374_ = lean_uint16_shift_right(v_a_372_, v_b_373_);
stack->m_num = v_res_374_;
}
LEAN_EXPORT lean_object* l_UInt16_shiftRight___boxed(lean_object* v_a_375_, lean_object* v_b_376_){
_start:
{
uint16_t v_a_boxed_377_; uint16_t v_b_boxed_378_; uint16_t v_res_379_; lean_object* v_r_380_; 
v_a_boxed_377_ = lean_unbox(v_a_375_);
v_b_boxed_378_ = lean_unbox(v_b_376_);
v_res_379_ = lean_uint16_shift_right(v_a_boxed_377_, v_b_boxed_378_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
static lean_object* _init_l_instLTUInt16(void){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_box(0);
return v___x_395_;
}
}
static lean_object* _init_l_instLEUInt16(void){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = lean_box(0);
return v___x_396_;
}
}
LEAN_EXPORT void l_UInt16_complement_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_397_ = stack[0].m_num;
uint16_t v_res_398_;
v_res_398_ = lean_uint16_complement(v_a_397_);
stack->m_num = v_res_398_;
}
LEAN_EXPORT lean_object* l_UInt16_complement___boxed(lean_object* v_a_399_){
_start:
{
uint16_t v_a_boxed_400_; uint16_t v_res_401_; lean_object* v_r_402_; 
v_a_boxed_400_ = lean_unbox(v_a_399_);
v_res_401_ = lean_uint16_complement(v_a_boxed_400_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT void l_UInt16_neg_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_403_ = stack[0].m_num;
uint16_t v_res_404_;
v_res_404_ = lean_uint16_neg(v_a_403_);
stack->m_num = v_res_404_;
}
LEAN_EXPORT lean_object* l_UInt16_neg___boxed(lean_object* v_a_405_){
_start:
{
uint16_t v_a_boxed_406_; uint16_t v_res_407_; lean_object* v_r_408_; 
v_a_boxed_406_ = lean_unbox(v_a_405_);
v_res_407_ = lean_uint16_neg(v_a_boxed_406_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT void l_Bool_toUInt16_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_423_ = stack[0].m_num;
uint16_t v_res_424_;
v_res_424_ = lean_bool_to_uint16(v_b_423_);
stack->m_num = v_res_424_;
}
LEAN_EXPORT lean_object* l_Bool_toUInt16___boxed(lean_object* v_b_425_){
_start:
{
uint8_t v_b_boxed_426_; uint16_t v_res_427_; lean_object* v_r_428_; 
v_b_boxed_426_ = lean_unbox(v_b_425_);
v_res_427_ = lean_bool_to_uint16(v_b_boxed_426_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT void l_UInt16_decLt_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_429_ = stack[0].m_num;
uint16_t v_b_430_ = stack[1].m_num;
uint8_t v_res_431_;
v_res_431_ = lean_uint16_dec_lt(v_a_429_, v_b_430_);
stack->m_num = v_res_431_;
}
LEAN_EXPORT lean_object* l_UInt16_decLt___boxed(lean_object* v_a_432_, lean_object* v_b_433_){
_start:
{
uint16_t v_a_boxed_434_; uint16_t v_b_boxed_435_; uint8_t v_res_436_; lean_object* v_r_437_; 
v_a_boxed_434_ = lean_unbox(v_a_432_);
v_b_boxed_435_ = lean_unbox(v_b_433_);
v_res_436_ = lean_uint16_dec_lt(v_a_boxed_434_, v_b_boxed_435_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT void l_UInt16_decLe_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_438_ = stack[0].m_num;
uint16_t v_b_439_ = stack[1].m_num;
uint8_t v_res_440_;
v_res_440_ = lean_uint16_dec_le(v_a_438_, v_b_439_);
stack->m_num = v_res_440_;
}
LEAN_EXPORT lean_object* l_UInt16_decLe___boxed(lean_object* v_a_441_, lean_object* v_b_442_){
_start:
{
uint16_t v_a_boxed_443_; uint16_t v_b_boxed_444_; uint8_t v_res_445_; lean_object* v_r_446_; 
v_a_boxed_443_ = lean_unbox(v_a_441_);
v_b_boxed_444_ = lean_unbox(v_b_442_);
v_res_445_ = lean_uint16_dec_le(v_a_boxed_443_, v_b_boxed_444_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
uint16_t l_instMaxUInt16___lam__0(uint16_t v_x_447_, uint16_t v_y_448_){
_start:
{
uint8_t v___x_449_; 
v___x_449_ = lean_uint16_dec_le(v_x_447_, v_y_448_);
if (v___x_449_ == 0)
{
return v_x_447_;
}
else
{
return v_y_448_;
}
}
}
LEAN_EXPORT void l_instMaxUInt16___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_447_ = stack[0].m_num;
uint16_t v_y_448_ = stack[1].m_num;
uint16_t v_res_450_;
v_res_450_ = l_instMaxUInt16___lam__0(v_x_447_, v_y_448_);
stack->m_num = v_res_450_;
}
LEAN_EXPORT lean_object* l_instMaxUInt16___lam__0___boxed(lean_object* v_x_451_, lean_object* v_y_452_){
_start:
{
uint16_t v_x_boxed_453_; uint16_t v_y_boxed_454_; uint16_t v_res_455_; lean_object* v_r_456_; 
v_x_boxed_453_ = lean_unbox(v_x_451_);
v_y_boxed_454_ = lean_unbox(v_y_452_);
v_res_455_ = l_instMaxUInt16___lam__0(v_x_boxed_453_, v_y_boxed_454_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
uint16_t l_instMinUInt16___lam__0(uint16_t v_x_459_, uint16_t v_y_460_){
_start:
{
uint8_t v___x_461_; 
v___x_461_ = lean_uint16_dec_le(v_x_459_, v_y_460_);
if (v___x_461_ == 0)
{
return v_y_460_;
}
else
{
return v_x_459_;
}
}
}
LEAN_EXPORT void l_instMinUInt16___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_x_459_ = stack[0].m_num;
uint16_t v_y_460_ = stack[1].m_num;
uint16_t v_res_462_;
v_res_462_ = l_instMinUInt16___lam__0(v_x_459_, v_y_460_);
stack->m_num = v_res_462_;
}
LEAN_EXPORT lean_object* l_instMinUInt16___lam__0___boxed(lean_object* v_x_463_, lean_object* v_y_464_){
_start:
{
uint16_t v_x_boxed_465_; uint16_t v_y_boxed_466_; uint16_t v_res_467_; lean_object* v_r_468_; 
v_x_boxed_465_ = lean_unbox(v_x_463_);
v_y_boxed_466_ = lean_unbox(v_y_464_);
v_res_467_ = l_instMinUInt16___lam__0(v_x_boxed_465_, v_y_boxed_466_);
v_r_468_ = lean_box(v_res_467_);
return v_r_468_;
}
}
uint32_t l_UInt32_ofFin(lean_object* v_a_471_){
_start:
{
uint32_t v___x_472_; 
v___x_472_ = lean_uint32_of_nat_mk(v_a_471_);
return v___x_472_;
}
}
LEAN_EXPORT void l_UInt32_ofFin_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_471_ = stack[0].m_obj;
uint32_t v_res_473_;
v_res_473_ = l_UInt32_ofFin(v_a_471_);
stack->m_num = v_res_473_;
}
LEAN_EXPORT lean_object* l_UInt32_ofFin___boxed(lean_object* v_a_474_){
_start:
{
uint32_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_UInt32_ofFin(v_a_474_);
v_r_476_ = lean_box_uint32(v_res_475_);
return v_r_476_;
}
}
static lean_object* _init_l_UInt32_ofInt___closed__0(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_unsigned_to_nat(32u);
v___x_478_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_479_ = l_Int_pow(v___x_478_, v___x_477_);
return v___x_479_;
}
}
uint32_t l_UInt32_ofInt(lean_object* v_x_480_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint32_t v___x_484_; 
v___x_481_ = lean_obj_once(&l_UInt32_ofInt___closed__0, &l_UInt32_ofInt___closed__0_once, _init_l_UInt32_ofInt___closed__0);
v___x_482_ = lean_int_emod(v_x_480_, v___x_481_);
v___x_483_ = l_Int_toNat(v___x_482_);
lean_dec(v___x_482_);
v___x_484_ = lean_uint32_of_nat(v___x_483_);
lean_dec(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT void l_UInt32_ofInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_480_ = stack[0].m_obj;
uint32_t v_res_485_;
v_res_485_ = l_UInt32_ofInt(v_x_480_);
stack->m_num = v_res_485_;
}
LEAN_EXPORT lean_object* l_UInt32_ofInt___boxed(lean_object* v_x_486_){
_start:
{
uint32_t v_res_487_; lean_object* v_r_488_; 
v_res_487_ = l_UInt32_ofInt(v_x_486_);
lean_dec(v_x_486_);
v_r_488_ = lean_box_uint32(v_res_487_);
return v_r_488_;
}
}
LEAN_EXPORT void l_UInt32_mul_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_489_ = stack[0].m_num;
uint32_t v_b_490_ = stack[1].m_num;
uint32_t v_res_491_;
v_res_491_ = lean_uint32_mul(v_a_489_, v_b_490_);
stack->m_num = v_res_491_;
}
LEAN_EXPORT lean_object* l_UInt32_mul___boxed(lean_object* v_a_492_, lean_object* v_b_493_){
_start:
{
uint32_t v_a_boxed_494_; uint32_t v_b_boxed_495_; uint32_t v_res_496_; lean_object* v_r_497_; 
v_a_boxed_494_ = lean_unbox_uint32(v_a_492_);
lean_dec(v_a_492_);
v_b_boxed_495_ = lean_unbox_uint32(v_b_493_);
lean_dec(v_b_493_);
v_res_496_ = lean_uint32_mul(v_a_boxed_494_, v_b_boxed_495_);
v_r_497_ = lean_box_uint32(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT void l_UInt32_div_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_498_ = stack[0].m_num;
uint32_t v_b_499_ = stack[1].m_num;
uint32_t v_res_500_;
v_res_500_ = lean_uint32_div(v_a_498_, v_b_499_);
stack->m_num = v_res_500_;
}
LEAN_EXPORT lean_object* l_UInt32_div___boxed(lean_object* v_a_501_, lean_object* v_b_502_){
_start:
{
uint32_t v_a_boxed_503_; uint32_t v_b_boxed_504_; uint32_t v_res_505_; lean_object* v_r_506_; 
v_a_boxed_503_ = lean_unbox_uint32(v_a_501_);
lean_dec(v_a_501_);
v_b_boxed_504_ = lean_unbox_uint32(v_b_502_);
lean_dec(v_b_502_);
v_res_505_ = lean_uint32_div(v_a_boxed_503_, v_b_boxed_504_);
v_r_506_ = lean_box_uint32(v_res_505_);
return v_r_506_;
}
}
uint32_t l_UInt32_pow(uint32_t v_x_507_, lean_object* v_n_508_){
_start:
{
lean_object* v_zero_509_; uint8_t v_isZero_510_; 
v_zero_509_ = lean_unsigned_to_nat(0u);
v_isZero_510_ = lean_nat_dec_eq(v_n_508_, v_zero_509_);
if (v_isZero_510_ == 1)
{
uint32_t v___x_511_; 
v___x_511_ = 1;
return v___x_511_;
}
else
{
lean_object* v_one_512_; lean_object* v_n_513_; uint32_t v___x_514_; uint32_t v___x_515_; 
v_one_512_ = lean_unsigned_to_nat(1u);
v_n_513_ = lean_nat_sub(v_n_508_, v_one_512_);
v___x_514_ = l_UInt32_pow(v_x_507_, v_n_513_);
lean_dec(v_n_513_);
v___x_515_ = lean_uint32_mul(v___x_514_, v_x_507_);
return v___x_515_;
}
}
}
LEAN_EXPORT void l_UInt32_pow_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_507_ = stack[0].m_num;
lean_object* v_n_508_ = stack[1].m_obj;
uint32_t v_res_516_;
v_res_516_ = l_UInt32_pow(v_x_507_, v_n_508_);
stack->m_num = v_res_516_;
}
LEAN_EXPORT lean_object* l_UInt32_pow___boxed(lean_object* v_x_517_, lean_object* v_n_518_){
_start:
{
uint32_t v_x_boxed_519_; uint32_t v_res_520_; lean_object* v_r_521_; 
v_x_boxed_519_ = lean_unbox_uint32(v_x_517_);
lean_dec(v_x_517_);
v_res_520_ = l_UInt32_pow(v_x_boxed_519_, v_n_518_);
lean_dec(v_n_518_);
v_r_521_ = lean_box_uint32(v_res_520_);
return v_r_521_;
}
}
LEAN_EXPORT void l_UInt32_mod_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_522_ = stack[0].m_num;
uint32_t v_b_523_ = stack[1].m_num;
uint32_t v_res_524_;
v_res_524_ = lean_uint32_mod(v_a_522_, v_b_523_);
stack->m_num = v_res_524_;
}
LEAN_EXPORT lean_object* l_UInt32_mod___boxed(lean_object* v_a_525_, lean_object* v_b_526_){
_start:
{
uint32_t v_a_boxed_527_; uint32_t v_b_boxed_528_; uint32_t v_res_529_; lean_object* v_r_530_; 
v_a_boxed_527_ = lean_unbox_uint32(v_a_525_);
lean_dec(v_a_525_);
v_b_boxed_528_ = lean_unbox_uint32(v_b_526_);
lean_dec(v_b_526_);
v_res_529_ = lean_uint32_mod(v_a_boxed_527_, v_b_boxed_528_);
v_r_530_ = lean_box_uint32(v_res_529_);
return v_r_530_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt32_modn_spec__0(lean_object* v_a_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_unsigned_to_nat(32u);
v___x_533_ = l_BitVec_ofNat(v___x_532_, v_a_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt32_modn_spec__0___boxed(lean_object* v_a_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Nat_cast___at___00UInt32_modn_spec__0(v_a_534_);
lean_dec(v_a_534_);
return v_res_535_;
}
}
uint32_t l_UInt32_modn(uint32_t v_a_536_, lean_object* v_n_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint32_t v___x_541_; 
v___x_538_ = lean_uint32_to_nat(v_a_536_);
v___x_539_ = lean_nat_mod(v___x_538_, v_n_537_);
lean_dec(v___x_538_);
v___x_540_ = l_Nat_cast___at___00UInt32_modn_spec__0(v___x_539_);
lean_dec(v___x_539_);
v___x_541_ = lean_uint32_of_nat_mk(v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT void l_UInt32_modn_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_536_ = stack[0].m_num;
lean_object* v_n_537_ = stack[1].m_obj;
uint32_t v_res_542_;
v_res_542_ = l_UInt32_modn(v_a_536_, v_n_537_);
stack->m_num = v_res_542_;
}
LEAN_EXPORT lean_object* l_UInt32_modn___boxed(lean_object* v_a_543_, lean_object* v_n_544_){
_start:
{
uint32_t v_a_boxed_545_; uint32_t v_res_546_; lean_object* v_r_547_; 
v_a_boxed_545_ = lean_unbox_uint32(v_a_543_);
lean_dec(v_a_543_);
v_res_546_ = l_UInt32_modn(v_a_boxed_545_, v_n_544_);
lean_dec(v_n_544_);
v_r_547_ = lean_box_uint32(v_res_546_);
return v_r_547_;
}
}
LEAN_EXPORT void l_UInt32_land_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_548_ = stack[0].m_num;
uint32_t v_b_549_ = stack[1].m_num;
uint32_t v_res_550_;
v_res_550_ = lean_uint32_land(v_a_548_, v_b_549_);
stack->m_num = v_res_550_;
}
LEAN_EXPORT lean_object* l_UInt32_land___boxed(lean_object* v_a_551_, lean_object* v_b_552_){
_start:
{
uint32_t v_a_boxed_553_; uint32_t v_b_boxed_554_; uint32_t v_res_555_; lean_object* v_r_556_; 
v_a_boxed_553_ = lean_unbox_uint32(v_a_551_);
lean_dec(v_a_551_);
v_b_boxed_554_ = lean_unbox_uint32(v_b_552_);
lean_dec(v_b_552_);
v_res_555_ = lean_uint32_land(v_a_boxed_553_, v_b_boxed_554_);
v_r_556_ = lean_box_uint32(v_res_555_);
return v_r_556_;
}
}
LEAN_EXPORT void l_UInt32_lor_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_557_ = stack[0].m_num;
uint32_t v_b_558_ = stack[1].m_num;
uint32_t v_res_559_;
v_res_559_ = lean_uint32_lor(v_a_557_, v_b_558_);
stack->m_num = v_res_559_;
}
LEAN_EXPORT lean_object* l_UInt32_lor___boxed(lean_object* v_a_560_, lean_object* v_b_561_){
_start:
{
uint32_t v_a_boxed_562_; uint32_t v_b_boxed_563_; uint32_t v_res_564_; lean_object* v_r_565_; 
v_a_boxed_562_ = lean_unbox_uint32(v_a_560_);
lean_dec(v_a_560_);
v_b_boxed_563_ = lean_unbox_uint32(v_b_561_);
lean_dec(v_b_561_);
v_res_564_ = lean_uint32_lor(v_a_boxed_562_, v_b_boxed_563_);
v_r_565_ = lean_box_uint32(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT void l_UInt32_xor_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_566_ = stack[0].m_num;
uint32_t v_b_567_ = stack[1].m_num;
uint32_t v_res_568_;
v_res_568_ = lean_uint32_xor(v_a_566_, v_b_567_);
stack->m_num = v_res_568_;
}
LEAN_EXPORT lean_object* l_UInt32_xor___boxed(lean_object* v_a_569_, lean_object* v_b_570_){
_start:
{
uint32_t v_a_boxed_571_; uint32_t v_b_boxed_572_; uint32_t v_res_573_; lean_object* v_r_574_; 
v_a_boxed_571_ = lean_unbox_uint32(v_a_569_);
lean_dec(v_a_569_);
v_b_boxed_572_ = lean_unbox_uint32(v_b_570_);
lean_dec(v_b_570_);
v_res_573_ = lean_uint32_xor(v_a_boxed_571_, v_b_boxed_572_);
v_r_574_ = lean_box_uint32(v_res_573_);
return v_r_574_;
}
}
LEAN_EXPORT void l_UInt32_shiftLeft_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_575_ = stack[0].m_num;
uint32_t v_b_576_ = stack[1].m_num;
uint32_t v_res_577_;
v_res_577_ = lean_uint32_shift_left(v_a_575_, v_b_576_);
stack->m_num = v_res_577_;
}
LEAN_EXPORT lean_object* l_UInt32_shiftLeft___boxed(lean_object* v_a_578_, lean_object* v_b_579_){
_start:
{
uint32_t v_a_boxed_580_; uint32_t v_b_boxed_581_; uint32_t v_res_582_; lean_object* v_r_583_; 
v_a_boxed_580_ = lean_unbox_uint32(v_a_578_);
lean_dec(v_a_578_);
v_b_boxed_581_ = lean_unbox_uint32(v_b_579_);
lean_dec(v_b_579_);
v_res_582_ = lean_uint32_shift_left(v_a_boxed_580_, v_b_boxed_581_);
v_r_583_ = lean_box_uint32(v_res_582_);
return v_r_583_;
}
}
LEAN_EXPORT void l_UInt32_shiftRight_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_584_ = stack[0].m_num;
uint32_t v_b_585_ = stack[1].m_num;
uint32_t v_res_586_;
v_res_586_ = lean_uint32_shift_right(v_a_584_, v_b_585_);
stack->m_num = v_res_586_;
}
LEAN_EXPORT lean_object* l_UInt32_shiftRight___boxed(lean_object* v_a_587_, lean_object* v_b_588_){
_start:
{
uint32_t v_a_boxed_589_; uint32_t v_b_boxed_590_; uint32_t v_res_591_; lean_object* v_r_592_; 
v_a_boxed_589_ = lean_unbox_uint32(v_a_587_);
lean_dec(v_a_587_);
v_b_boxed_590_ = lean_unbox_uint32(v_b_588_);
lean_dec(v_b_588_);
v_res_591_ = lean_uint32_shift_right(v_a_boxed_589_, v_b_boxed_590_);
v_r_592_ = lean_box_uint32(v_res_591_);
return v_r_592_;
}
}
LEAN_EXPORT void l_UInt32_complement_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_603_ = stack[0].m_num;
uint32_t v_res_604_;
v_res_604_ = lean_uint32_complement(v_a_603_);
stack->m_num = v_res_604_;
}
LEAN_EXPORT lean_object* l_UInt32_complement___boxed(lean_object* v_a_605_){
_start:
{
uint32_t v_a_boxed_606_; uint32_t v_res_607_; lean_object* v_r_608_; 
v_a_boxed_606_ = lean_unbox_uint32(v_a_605_);
lean_dec(v_a_605_);
v_res_607_ = lean_uint32_complement(v_a_boxed_606_);
v_r_608_ = lean_box_uint32(v_res_607_);
return v_r_608_;
}
}
LEAN_EXPORT void l_UInt32_neg_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_609_ = stack[0].m_num;
uint32_t v_res_610_;
v_res_610_ = lean_uint32_neg(v_a_609_);
stack->m_num = v_res_610_;
}
LEAN_EXPORT lean_object* l_UInt32_neg___boxed(lean_object* v_a_611_){
_start:
{
uint32_t v_a_boxed_612_; uint32_t v_res_613_; lean_object* v_r_614_; 
v_a_boxed_612_ = lean_unbox_uint32(v_a_611_);
lean_dec(v_a_611_);
v_res_613_ = lean_uint32_neg(v_a_boxed_612_);
v_r_614_ = lean_box_uint32(v_res_613_);
return v_r_614_;
}
}
LEAN_EXPORT void l_Bool_toUInt32_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_629_ = stack[0].m_num;
uint32_t v_res_630_;
v_res_630_ = lean_bool_to_uint32(v_b_629_);
stack->m_num = v_res_630_;
}
LEAN_EXPORT lean_object* l_Bool_toUInt32___boxed(lean_object* v_b_631_){
_start:
{
uint8_t v_b_boxed_632_; uint32_t v_res_633_; lean_object* v_r_634_; 
v_b_boxed_632_ = lean_unbox(v_b_631_);
v_res_633_ = lean_bool_to_uint32(v_b_boxed_632_);
v_r_634_ = lean_box_uint32(v_res_633_);
return v_r_634_;
}
}
uint64_t l_UInt64_ofFin(lean_object* v_a_635_){
_start:
{
uint64_t v___x_636_; 
v___x_636_ = lean_uint64_of_nat_mk(v_a_635_);
return v___x_636_;
}
}
LEAN_EXPORT void l_UInt64_ofFin_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_635_ = stack[0].m_obj;
uint64_t v_res_637_;
v_res_637_ = l_UInt64_ofFin(v_a_635_);
stack->m_num = v_res_637_;
}
LEAN_EXPORT lean_object* l_UInt64_ofFin___boxed(lean_object* v_a_638_){
_start:
{
uint64_t v_res_639_; lean_object* v_r_640_; 
v_res_639_ = l_UInt64_ofFin(v_a_638_);
v_r_640_ = lean_box_uint64(v_res_639_);
return v_r_640_;
}
}
static lean_object* _init_l_UInt64_ofInt___closed__0(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_unsigned_to_nat(64u);
v___x_642_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_643_ = l_Int_pow(v___x_642_, v___x_641_);
return v___x_643_;
}
}
uint64_t l_UInt64_ofInt(lean_object* v_x_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint64_t v___x_648_; 
v___x_645_ = lean_obj_once(&l_UInt64_ofInt___closed__0, &l_UInt64_ofInt___closed__0_once, _init_l_UInt64_ofInt___closed__0);
v___x_646_ = lean_int_emod(v_x_644_, v___x_645_);
v___x_647_ = l_Int_toNat(v___x_646_);
lean_dec(v___x_646_);
v___x_648_ = lean_uint64_of_nat(v___x_647_);
lean_dec(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT void l_UInt64_ofInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_644_ = stack[0].m_obj;
uint64_t v_res_649_;
v_res_649_ = l_UInt64_ofInt(v_x_644_);
stack->m_num = v_res_649_;
}
LEAN_EXPORT lean_object* l_UInt64_ofInt___boxed(lean_object* v_x_650_){
_start:
{
uint64_t v_res_651_; lean_object* v_r_652_; 
v_res_651_ = l_UInt64_ofInt(v_x_650_);
lean_dec(v_x_650_);
v_r_652_ = lean_box_uint64(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT void l_UInt64_add_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_653_ = stack[0].m_num;
uint64_t v_b_654_ = stack[1].m_num;
uint64_t v_res_655_;
v_res_655_ = lean_uint64_add(v_a_653_, v_b_654_);
stack->m_num = v_res_655_;
}
LEAN_EXPORT lean_object* l_UInt64_add___boxed(lean_object* v_a_656_, lean_object* v_b_657_){
_start:
{
uint64_t v_a_boxed_658_; uint64_t v_b_boxed_659_; uint64_t v_res_660_; lean_object* v_r_661_; 
v_a_boxed_658_ = lean_unbox_uint64(v_a_656_);
lean_dec_ref(v_a_656_);
v_b_boxed_659_ = lean_unbox_uint64(v_b_657_);
lean_dec_ref(v_b_657_);
v_res_660_ = lean_uint64_add(v_a_boxed_658_, v_b_boxed_659_);
v_r_661_ = lean_box_uint64(v_res_660_);
return v_r_661_;
}
}
LEAN_EXPORT void l_UInt64_sub_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_662_ = stack[0].m_num;
uint64_t v_b_663_ = stack[1].m_num;
uint64_t v_res_664_;
v_res_664_ = lean_uint64_sub(v_a_662_, v_b_663_);
stack->m_num = v_res_664_;
}
LEAN_EXPORT lean_object* l_UInt64_sub___boxed(lean_object* v_a_665_, lean_object* v_b_666_){
_start:
{
uint64_t v_a_boxed_667_; uint64_t v_b_boxed_668_; uint64_t v_res_669_; lean_object* v_r_670_; 
v_a_boxed_667_ = lean_unbox_uint64(v_a_665_);
lean_dec_ref(v_a_665_);
v_b_boxed_668_ = lean_unbox_uint64(v_b_666_);
lean_dec_ref(v_b_666_);
v_res_669_ = lean_uint64_sub(v_a_boxed_667_, v_b_boxed_668_);
v_r_670_ = lean_box_uint64(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT void l_UInt64_mul_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_671_ = stack[0].m_num;
uint64_t v_b_672_ = stack[1].m_num;
uint64_t v_res_673_;
v_res_673_ = lean_uint64_mul(v_a_671_, v_b_672_);
stack->m_num = v_res_673_;
}
LEAN_EXPORT lean_object* l_UInt64_mul___boxed(lean_object* v_a_674_, lean_object* v_b_675_){
_start:
{
uint64_t v_a_boxed_676_; uint64_t v_b_boxed_677_; uint64_t v_res_678_; lean_object* v_r_679_; 
v_a_boxed_676_ = lean_unbox_uint64(v_a_674_);
lean_dec_ref(v_a_674_);
v_b_boxed_677_ = lean_unbox_uint64(v_b_675_);
lean_dec_ref(v_b_675_);
v_res_678_ = lean_uint64_mul(v_a_boxed_676_, v_b_boxed_677_);
v_r_679_ = lean_box_uint64(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT void l_UInt64_div_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_680_ = stack[0].m_num;
uint64_t v_b_681_ = stack[1].m_num;
uint64_t v_res_682_;
v_res_682_ = lean_uint64_div(v_a_680_, v_b_681_);
stack->m_num = v_res_682_;
}
LEAN_EXPORT lean_object* l_UInt64_div___boxed(lean_object* v_a_683_, lean_object* v_b_684_){
_start:
{
uint64_t v_a_boxed_685_; uint64_t v_b_boxed_686_; uint64_t v_res_687_; lean_object* v_r_688_; 
v_a_boxed_685_ = lean_unbox_uint64(v_a_683_);
lean_dec_ref(v_a_683_);
v_b_boxed_686_ = lean_unbox_uint64(v_b_684_);
lean_dec_ref(v_b_684_);
v_res_687_ = lean_uint64_div(v_a_boxed_685_, v_b_boxed_686_);
v_r_688_ = lean_box_uint64(v_res_687_);
return v_r_688_;
}
}
uint64_t l_UInt64_pow(uint64_t v_x_689_, lean_object* v_n_690_){
_start:
{
lean_object* v_zero_691_; uint8_t v_isZero_692_; 
v_zero_691_ = lean_unsigned_to_nat(0u);
v_isZero_692_ = lean_nat_dec_eq(v_n_690_, v_zero_691_);
if (v_isZero_692_ == 1)
{
uint64_t v___x_693_; 
v___x_693_ = 1ULL;
return v___x_693_;
}
else
{
lean_object* v_one_694_; lean_object* v_n_695_; uint64_t v___x_696_; uint64_t v___x_697_; 
v_one_694_ = lean_unsigned_to_nat(1u);
v_n_695_ = lean_nat_sub(v_n_690_, v_one_694_);
v___x_696_ = l_UInt64_pow(v_x_689_, v_n_695_);
lean_dec(v_n_695_);
v___x_697_ = lean_uint64_mul(v___x_696_, v_x_689_);
return v___x_697_;
}
}
}
LEAN_EXPORT void l_UInt64_pow_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_689_ = stack[0].m_num;
lean_object* v_n_690_ = stack[1].m_obj;
uint64_t v_res_698_;
v_res_698_ = l_UInt64_pow(v_x_689_, v_n_690_);
stack->m_num = v_res_698_;
}
LEAN_EXPORT lean_object* l_UInt64_pow___boxed(lean_object* v_x_699_, lean_object* v_n_700_){
_start:
{
uint64_t v_x_boxed_701_; uint64_t v_res_702_; lean_object* v_r_703_; 
v_x_boxed_701_ = lean_unbox_uint64(v_x_699_);
lean_dec_ref(v_x_699_);
v_res_702_ = l_UInt64_pow(v_x_boxed_701_, v_n_700_);
lean_dec(v_n_700_);
v_r_703_ = lean_box_uint64(v_res_702_);
return v_r_703_;
}
}
LEAN_EXPORT void l_UInt64_mod_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_704_ = stack[0].m_num;
uint64_t v_b_705_ = stack[1].m_num;
uint64_t v_res_706_;
v_res_706_ = lean_uint64_mod(v_a_704_, v_b_705_);
stack->m_num = v_res_706_;
}
LEAN_EXPORT lean_object* l_UInt64_mod___boxed(lean_object* v_a_707_, lean_object* v_b_708_){
_start:
{
uint64_t v_a_boxed_709_; uint64_t v_b_boxed_710_; uint64_t v_res_711_; lean_object* v_r_712_; 
v_a_boxed_709_ = lean_unbox_uint64(v_a_707_);
lean_dec_ref(v_a_707_);
v_b_boxed_710_ = lean_unbox_uint64(v_b_708_);
lean_dec_ref(v_b_708_);
v_res_711_ = lean_uint64_mod(v_a_boxed_709_, v_b_boxed_710_);
v_r_712_ = lean_box_uint64(v_res_711_);
return v_r_712_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt64_modn_spec__0(lean_object* v_a_713_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(64u);
v___x_715_ = l_BitVec_ofNat(v___x_714_, v_a_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt64_modn_spec__0___boxed(lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Nat_cast___at___00UInt64_modn_spec__0(v_a_716_);
lean_dec(v_a_716_);
return v_res_717_;
}
}
uint64_t l_UInt64_modn(uint64_t v_a_718_, lean_object* v_n_719_){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint64_t v___x_723_; 
v___x_720_ = lean_uint64_to_nat(v_a_718_);
v___x_721_ = lean_nat_mod(v___x_720_, v_n_719_);
lean_dec(v___x_720_);
v___x_722_ = l_Nat_cast___at___00UInt64_modn_spec__0(v___x_721_);
lean_dec(v___x_721_);
v___x_723_ = lean_uint64_of_nat_mk(v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT void l_UInt64_modn_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_718_ = stack[0].m_num;
lean_object* v_n_719_ = stack[1].m_obj;
uint64_t v_res_724_;
v_res_724_ = l_UInt64_modn(v_a_718_, v_n_719_);
stack->m_num = v_res_724_;
}
LEAN_EXPORT lean_object* l_UInt64_modn___boxed(lean_object* v_a_725_, lean_object* v_n_726_){
_start:
{
uint64_t v_a_boxed_727_; uint64_t v_res_728_; lean_object* v_r_729_; 
v_a_boxed_727_ = lean_unbox_uint64(v_a_725_);
lean_dec_ref(v_a_725_);
v_res_728_ = l_UInt64_modn(v_a_boxed_727_, v_n_726_);
lean_dec(v_n_726_);
v_r_729_ = lean_box_uint64(v_res_728_);
return v_r_729_;
}
}
LEAN_EXPORT void l_UInt64_land_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_730_ = stack[0].m_num;
uint64_t v_b_731_ = stack[1].m_num;
uint64_t v_res_732_;
v_res_732_ = lean_uint64_land(v_a_730_, v_b_731_);
stack->m_num = v_res_732_;
}
LEAN_EXPORT lean_object* l_UInt64_land___boxed(lean_object* v_a_733_, lean_object* v_b_734_){
_start:
{
uint64_t v_a_boxed_735_; uint64_t v_b_boxed_736_; uint64_t v_res_737_; lean_object* v_r_738_; 
v_a_boxed_735_ = lean_unbox_uint64(v_a_733_);
lean_dec_ref(v_a_733_);
v_b_boxed_736_ = lean_unbox_uint64(v_b_734_);
lean_dec_ref(v_b_734_);
v_res_737_ = lean_uint64_land(v_a_boxed_735_, v_b_boxed_736_);
v_r_738_ = lean_box_uint64(v_res_737_);
return v_r_738_;
}
}
LEAN_EXPORT void l_UInt64_lor_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_739_ = stack[0].m_num;
uint64_t v_b_740_ = stack[1].m_num;
uint64_t v_res_741_;
v_res_741_ = lean_uint64_lor(v_a_739_, v_b_740_);
stack->m_num = v_res_741_;
}
LEAN_EXPORT lean_object* l_UInt64_lor___boxed(lean_object* v_a_742_, lean_object* v_b_743_){
_start:
{
uint64_t v_a_boxed_744_; uint64_t v_b_boxed_745_; uint64_t v_res_746_; lean_object* v_r_747_; 
v_a_boxed_744_ = lean_unbox_uint64(v_a_742_);
lean_dec_ref(v_a_742_);
v_b_boxed_745_ = lean_unbox_uint64(v_b_743_);
lean_dec_ref(v_b_743_);
v_res_746_ = lean_uint64_lor(v_a_boxed_744_, v_b_boxed_745_);
v_r_747_ = lean_box_uint64(v_res_746_);
return v_r_747_;
}
}
LEAN_EXPORT void l_UInt64_xor_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_748_ = stack[0].m_num;
uint64_t v_b_749_ = stack[1].m_num;
uint64_t v_res_750_;
v_res_750_ = lean_uint64_xor(v_a_748_, v_b_749_);
stack->m_num = v_res_750_;
}
LEAN_EXPORT lean_object* l_UInt64_xor___boxed(lean_object* v_a_751_, lean_object* v_b_752_){
_start:
{
uint64_t v_a_boxed_753_; uint64_t v_b_boxed_754_; uint64_t v_res_755_; lean_object* v_r_756_; 
v_a_boxed_753_ = lean_unbox_uint64(v_a_751_);
lean_dec_ref(v_a_751_);
v_b_boxed_754_ = lean_unbox_uint64(v_b_752_);
lean_dec_ref(v_b_752_);
v_res_755_ = lean_uint64_xor(v_a_boxed_753_, v_b_boxed_754_);
v_r_756_ = lean_box_uint64(v_res_755_);
return v_r_756_;
}
}
LEAN_EXPORT void l_UInt64_shiftLeft_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_757_ = stack[0].m_num;
uint64_t v_b_758_ = stack[1].m_num;
uint64_t v_res_759_;
v_res_759_ = lean_uint64_shift_left(v_a_757_, v_b_758_);
stack->m_num = v_res_759_;
}
LEAN_EXPORT lean_object* l_UInt64_shiftLeft___boxed(lean_object* v_a_760_, lean_object* v_b_761_){
_start:
{
uint64_t v_a_boxed_762_; uint64_t v_b_boxed_763_; uint64_t v_res_764_; lean_object* v_r_765_; 
v_a_boxed_762_ = lean_unbox_uint64(v_a_760_);
lean_dec_ref(v_a_760_);
v_b_boxed_763_ = lean_unbox_uint64(v_b_761_);
lean_dec_ref(v_b_761_);
v_res_764_ = lean_uint64_shift_left(v_a_boxed_762_, v_b_boxed_763_);
v_r_765_ = lean_box_uint64(v_res_764_);
return v_r_765_;
}
}
LEAN_EXPORT void l_UInt64_shiftRight_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_766_ = stack[0].m_num;
uint64_t v_b_767_ = stack[1].m_num;
uint64_t v_res_768_;
v_res_768_ = lean_uint64_shift_right(v_a_766_, v_b_767_);
stack->m_num = v_res_768_;
}
LEAN_EXPORT lean_object* l_UInt64_shiftRight___boxed(lean_object* v_a_769_, lean_object* v_b_770_){
_start:
{
uint64_t v_a_boxed_771_; uint64_t v_b_boxed_772_; uint64_t v_res_773_; lean_object* v_r_774_; 
v_a_boxed_771_ = lean_unbox_uint64(v_a_769_);
lean_dec_ref(v_a_769_);
v_b_boxed_772_ = lean_unbox_uint64(v_b_770_);
lean_dec_ref(v_b_770_);
v_res_773_ = lean_uint64_shift_right(v_a_boxed_771_, v_b_boxed_772_);
v_r_774_ = lean_box_uint64(v_res_773_);
return v_r_774_;
}
}
static lean_object* _init_l_instLTUInt64(void){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = lean_box(0);
return v___x_789_;
}
}
static lean_object* _init_l_instLEUInt64(void){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = lean_box(0);
return v___x_790_;
}
}
LEAN_EXPORT void l_UInt64_complement_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_791_ = stack[0].m_num;
uint64_t v_res_792_;
v_res_792_ = lean_uint64_complement(v_a_791_);
stack->m_num = v_res_792_;
}
LEAN_EXPORT lean_object* l_UInt64_complement___boxed(lean_object* v_a_793_){
_start:
{
uint64_t v_a_boxed_794_; uint64_t v_res_795_; lean_object* v_r_796_; 
v_a_boxed_794_ = lean_unbox_uint64(v_a_793_);
lean_dec_ref(v_a_793_);
v_res_795_ = lean_uint64_complement(v_a_boxed_794_);
v_r_796_ = lean_box_uint64(v_res_795_);
return v_r_796_;
}
}
LEAN_EXPORT void l_UInt64_neg_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_797_ = stack[0].m_num;
uint64_t v_res_798_;
v_res_798_ = lean_uint64_neg(v_a_797_);
stack->m_num = v_res_798_;
}
LEAN_EXPORT lean_object* l_UInt64_neg___boxed(lean_object* v_a_799_){
_start:
{
uint64_t v_a_boxed_800_; uint64_t v_res_801_; lean_object* v_r_802_; 
v_a_boxed_800_ = lean_unbox_uint64(v_a_799_);
lean_dec_ref(v_a_799_);
v_res_801_ = lean_uint64_neg(v_a_boxed_800_);
v_r_802_ = lean_box_uint64(v_res_801_);
return v_r_802_;
}
}
LEAN_EXPORT void l_Bool_toUInt64_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_817_ = stack[0].m_num;
uint64_t v_res_818_;
v_res_818_ = lean_bool_to_uint64(v_b_817_);
stack->m_num = v_res_818_;
}
LEAN_EXPORT lean_object* l_Bool_toUInt64___boxed(lean_object* v_b_819_){
_start:
{
uint8_t v_b_boxed_820_; uint64_t v_res_821_; lean_object* v_r_822_; 
v_b_boxed_820_ = lean_unbox(v_b_819_);
v_res_821_ = lean_bool_to_uint64(v_b_boxed_820_);
v_r_822_ = lean_box_uint64(v_res_821_);
return v_r_822_;
}
}
LEAN_EXPORT void l_UInt64_decLt_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_823_ = stack[0].m_num;
uint64_t v_b_824_ = stack[1].m_num;
uint8_t v_res_825_;
v_res_825_ = lean_uint64_dec_lt(v_a_823_, v_b_824_);
stack->m_num = v_res_825_;
}
LEAN_EXPORT lean_object* l_UInt64_decLt___boxed(lean_object* v_a_826_, lean_object* v_b_827_){
_start:
{
uint64_t v_a_boxed_828_; uint64_t v_b_boxed_829_; uint8_t v_res_830_; lean_object* v_r_831_; 
v_a_boxed_828_ = lean_unbox_uint64(v_a_826_);
lean_dec_ref(v_a_826_);
v_b_boxed_829_ = lean_unbox_uint64(v_b_827_);
lean_dec_ref(v_b_827_);
v_res_830_ = lean_uint64_dec_lt(v_a_boxed_828_, v_b_boxed_829_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT void l_UInt64_decLe_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_832_ = stack[0].m_num;
uint64_t v_b_833_ = stack[1].m_num;
uint8_t v_res_834_;
v_res_834_ = lean_uint64_dec_le(v_a_832_, v_b_833_);
stack->m_num = v_res_834_;
}
LEAN_EXPORT lean_object* l_UInt64_decLe___boxed(lean_object* v_a_835_, lean_object* v_b_836_){
_start:
{
uint64_t v_a_boxed_837_; uint64_t v_b_boxed_838_; uint8_t v_res_839_; lean_object* v_r_840_; 
v_a_boxed_837_ = lean_unbox_uint64(v_a_835_);
lean_dec_ref(v_a_835_);
v_b_boxed_838_ = lean_unbox_uint64(v_b_836_);
lean_dec_ref(v_b_836_);
v_res_839_ = lean_uint64_dec_le(v_a_boxed_837_, v_b_boxed_838_);
v_r_840_ = lean_box(v_res_839_);
return v_r_840_;
}
}
uint64_t l_instMaxUInt64___lam__0(uint64_t v_x_841_, uint64_t v_y_842_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = lean_uint64_dec_le(v_x_841_, v_y_842_);
if (v___x_843_ == 0)
{
return v_x_841_;
}
else
{
return v_y_842_;
}
}
}
LEAN_EXPORT void l_instMaxUInt64___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_841_ = stack[0].m_num;
uint64_t v_y_842_ = stack[1].m_num;
uint64_t v_res_844_;
v_res_844_ = l_instMaxUInt64___lam__0(v_x_841_, v_y_842_);
stack->m_num = v_res_844_;
}
LEAN_EXPORT lean_object* l_instMaxUInt64___lam__0___boxed(lean_object* v_x_845_, lean_object* v_y_846_){
_start:
{
uint64_t v_x_boxed_847_; uint64_t v_y_boxed_848_; uint64_t v_res_849_; lean_object* v_r_850_; 
v_x_boxed_847_ = lean_unbox_uint64(v_x_845_);
lean_dec_ref(v_x_845_);
v_y_boxed_848_ = lean_unbox_uint64(v_y_846_);
lean_dec_ref(v_y_846_);
v_res_849_ = l_instMaxUInt64___lam__0(v_x_boxed_847_, v_y_boxed_848_);
v_r_850_ = lean_box_uint64(v_res_849_);
return v_r_850_;
}
}
uint64_t l_instMinUInt64___lam__0(uint64_t v_x_853_, uint64_t v_y_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = lean_uint64_dec_le(v_x_853_, v_y_854_);
if (v___x_855_ == 0)
{
return v_y_854_;
}
else
{
return v_x_853_;
}
}
}
LEAN_EXPORT void l_instMinUInt64___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_x_853_ = stack[0].m_num;
uint64_t v_y_854_ = stack[1].m_num;
uint64_t v_res_856_;
v_res_856_ = l_instMinUInt64___lam__0(v_x_853_, v_y_854_);
stack->m_num = v_res_856_;
}
LEAN_EXPORT lean_object* l_instMinUInt64___lam__0___boxed(lean_object* v_x_857_, lean_object* v_y_858_){
_start:
{
uint64_t v_x_boxed_859_; uint64_t v_y_boxed_860_; uint64_t v_res_861_; lean_object* v_r_862_; 
v_x_boxed_859_ = lean_unbox_uint64(v_x_857_);
lean_dec_ref(v_x_857_);
v_y_boxed_860_ = lean_unbox_uint64(v_y_858_);
lean_dec_ref(v_y_858_);
v_res_861_ = l_instMinUInt64___lam__0(v_x_boxed_859_, v_y_boxed_860_);
v_r_862_ = lean_box_uint64(v_res_861_);
return v_r_862_;
}
}
size_t l_USize_ofFin(lean_object* v_a_865_){
_start:
{
size_t v___x_866_; 
v___x_866_ = lean_usize_of_nat_mk(v_a_865_);
return v___x_866_;
}
}
LEAN_EXPORT void l_USize_ofFin_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_865_ = stack[0].m_obj;
size_t v_res_867_;
v_res_867_ = l_USize_ofFin(v_a_865_);
stack->m_num = v_res_867_;
}
LEAN_EXPORT lean_object* l_USize_ofFin___boxed(lean_object* v_a_868_){
_start:
{
size_t v_res_869_; lean_object* v_r_870_; 
v_res_869_ = l_USize_ofFin(v_a_868_);
v_r_870_ = lean_box_usize(v_res_869_);
return v_r_870_;
}
}
static lean_object* _init_l_USize_ofInt___closed__0(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_871_ = l_System_Platform_numBits;
v___x_872_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_873_ = l_Int_pow(v___x_872_, v___x_871_);
return v___x_873_;
}
}
size_t l_USize_ofInt(lean_object* v_x_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; size_t v___x_878_; 
v___x_875_ = lean_obj_once(&l_USize_ofInt___closed__0, &l_USize_ofInt___closed__0_once, _init_l_USize_ofInt___closed__0);
v___x_876_ = lean_int_emod(v_x_874_, v___x_875_);
v___x_877_ = l_Int_toNat(v___x_876_);
lean_dec(v___x_876_);
v___x_878_ = lean_usize_of_nat(v___x_877_);
lean_dec(v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT void l_USize_ofInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_874_ = stack[0].m_obj;
size_t v_res_879_;
v_res_879_ = l_USize_ofInt(v_x_874_);
stack->m_num = v_res_879_;
}
LEAN_EXPORT lean_object* l_USize_ofInt___boxed(lean_object* v_x_880_){
_start:
{
size_t v_res_881_; lean_object* v_r_882_; 
v_res_881_ = l_USize_ofInt(v_x_880_);
lean_dec(v_x_880_);
v_r_882_ = lean_box_usize(v_res_881_);
return v_r_882_;
}
}
LEAN_EXPORT void l_USize_mul_0interp(lean_interpreter_value* stack)
{
size_t v_a_883_ = stack[0].m_num;
size_t v_b_884_ = stack[1].m_num;
size_t v_res_885_;
v_res_885_ = lean_usize_mul(v_a_883_, v_b_884_);
stack->m_num = v_res_885_;
}
LEAN_EXPORT lean_object* l_USize_mul___boxed(lean_object* v_a_886_, lean_object* v_b_887_){
_start:
{
size_t v_a_boxed_888_; size_t v_b_boxed_889_; size_t v_res_890_; lean_object* v_r_891_; 
v_a_boxed_888_ = lean_unbox_usize(v_a_886_);
lean_dec(v_a_886_);
v_b_boxed_889_ = lean_unbox_usize(v_b_887_);
lean_dec(v_b_887_);
v_res_890_ = lean_usize_mul(v_a_boxed_888_, v_b_boxed_889_);
v_r_891_ = lean_box_usize(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT void l_USize_div_0interp(lean_interpreter_value* stack)
{
size_t v_a_892_ = stack[0].m_num;
size_t v_b_893_ = stack[1].m_num;
size_t v_res_894_;
v_res_894_ = lean_usize_div(v_a_892_, v_b_893_);
stack->m_num = v_res_894_;
}
LEAN_EXPORT lean_object* l_USize_div___boxed(lean_object* v_a_895_, lean_object* v_b_896_){
_start:
{
size_t v_a_boxed_897_; size_t v_b_boxed_898_; size_t v_res_899_; lean_object* v_r_900_; 
v_a_boxed_897_ = lean_unbox_usize(v_a_895_);
lean_dec(v_a_895_);
v_b_boxed_898_ = lean_unbox_usize(v_b_896_);
lean_dec(v_b_896_);
v_res_899_ = lean_usize_div(v_a_boxed_897_, v_b_boxed_898_);
v_r_900_ = lean_box_usize(v_res_899_);
return v_r_900_;
}
}
size_t l_USize_pow(size_t v_x_901_, lean_object* v_n_902_){
_start:
{
lean_object* v_zero_903_; uint8_t v_isZero_904_; 
v_zero_903_ = lean_unsigned_to_nat(0u);
v_isZero_904_ = lean_nat_dec_eq(v_n_902_, v_zero_903_);
if (v_isZero_904_ == 1)
{
size_t v___x_905_; 
v___x_905_ = ((size_t)1ULL);
return v___x_905_;
}
else
{
lean_object* v_one_906_; lean_object* v_n_907_; size_t v___x_908_; size_t v___x_909_; 
v_one_906_ = lean_unsigned_to_nat(1u);
v_n_907_ = lean_nat_sub(v_n_902_, v_one_906_);
v___x_908_ = l_USize_pow(v_x_901_, v_n_907_);
lean_dec(v_n_907_);
v___x_909_ = lean_usize_mul(v___x_908_, v_x_901_);
return v___x_909_;
}
}
}
LEAN_EXPORT void l_USize_pow_0interp(lean_interpreter_value* stack)
{
size_t v_x_901_ = stack[0].m_num;
lean_object* v_n_902_ = stack[1].m_obj;
size_t v_res_910_;
v_res_910_ = l_USize_pow(v_x_901_, v_n_902_);
stack->m_num = v_res_910_;
}
LEAN_EXPORT lean_object* l_USize_pow___boxed(lean_object* v_x_911_, lean_object* v_n_912_){
_start:
{
size_t v_x_boxed_913_; size_t v_res_914_; lean_object* v_r_915_; 
v_x_boxed_913_ = lean_unbox_usize(v_x_911_);
lean_dec(v_x_911_);
v_res_914_ = l_USize_pow(v_x_boxed_913_, v_n_912_);
lean_dec(v_n_912_);
v_r_915_ = lean_box_usize(v_res_914_);
return v_r_915_;
}
}
LEAN_EXPORT void l_USize_mod_0interp(lean_interpreter_value* stack)
{
size_t v_a_916_ = stack[0].m_num;
size_t v_b_917_ = stack[1].m_num;
size_t v_res_918_;
v_res_918_ = lean_usize_mod(v_a_916_, v_b_917_);
stack->m_num = v_res_918_;
}
LEAN_EXPORT lean_object* l_USize_mod___boxed(lean_object* v_a_919_, lean_object* v_b_920_){
_start:
{
size_t v_a_boxed_921_; size_t v_b_boxed_922_; size_t v_res_923_; lean_object* v_r_924_; 
v_a_boxed_921_ = lean_unbox_usize(v_a_919_);
lean_dec(v_a_919_);
v_b_boxed_922_ = lean_unbox_usize(v_b_920_);
lean_dec(v_b_920_);
v_res_923_ = lean_usize_mod(v_a_boxed_921_, v_b_boxed_922_);
v_r_924_ = lean_box_usize(v_res_923_);
return v_r_924_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00USize_modn_spec__0(lean_object* v_a_925_){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = l_System_Platform_numBits;
v___x_927_ = l_BitVec_ofNat(v___x_926_, v_a_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00USize_modn_spec__0___boxed(lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Nat_cast___at___00USize_modn_spec__0(v_a_928_);
lean_dec(v_a_928_);
return v_res_929_;
}
}
size_t l_USize_modn(size_t v_a_930_, lean_object* v_n_931_){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; size_t v___x_935_; 
v___x_932_ = lean_usize_to_nat(v_a_930_);
v___x_933_ = lean_nat_mod(v___x_932_, v_n_931_);
lean_dec(v___x_932_);
v___x_934_ = l_Nat_cast___at___00USize_modn_spec__0(v___x_933_);
lean_dec(v___x_933_);
v___x_935_ = lean_usize_of_nat_mk(v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT void l_USize_modn_0interp(lean_interpreter_value* stack)
{
size_t v_a_930_ = stack[0].m_num;
lean_object* v_n_931_ = stack[1].m_obj;
size_t v_res_936_;
v_res_936_ = l_USize_modn(v_a_930_, v_n_931_);
stack->m_num = v_res_936_;
}
LEAN_EXPORT lean_object* l_USize_modn___boxed(lean_object* v_a_937_, lean_object* v_n_938_){
_start:
{
size_t v_a_boxed_939_; size_t v_res_940_; lean_object* v_r_941_; 
v_a_boxed_939_ = lean_unbox_usize(v_a_937_);
lean_dec(v_a_937_);
v_res_940_ = l_USize_modn(v_a_boxed_939_, v_n_938_);
lean_dec(v_n_938_);
v_r_941_ = lean_box_usize(v_res_940_);
return v_r_941_;
}
}
LEAN_EXPORT void l_USize_land_0interp(lean_interpreter_value* stack)
{
size_t v_a_942_ = stack[0].m_num;
size_t v_b_943_ = stack[1].m_num;
size_t v_res_944_;
v_res_944_ = lean_usize_land(v_a_942_, v_b_943_);
stack->m_num = v_res_944_;
}
LEAN_EXPORT lean_object* l_USize_land___boxed(lean_object* v_a_945_, lean_object* v_b_946_){
_start:
{
size_t v_a_boxed_947_; size_t v_b_boxed_948_; size_t v_res_949_; lean_object* v_r_950_; 
v_a_boxed_947_ = lean_unbox_usize(v_a_945_);
lean_dec(v_a_945_);
v_b_boxed_948_ = lean_unbox_usize(v_b_946_);
lean_dec(v_b_946_);
v_res_949_ = lean_usize_land(v_a_boxed_947_, v_b_boxed_948_);
v_r_950_ = lean_box_usize(v_res_949_);
return v_r_950_;
}
}
LEAN_EXPORT void l_USize_lor_0interp(lean_interpreter_value* stack)
{
size_t v_a_951_ = stack[0].m_num;
size_t v_b_952_ = stack[1].m_num;
size_t v_res_953_;
v_res_953_ = lean_usize_lor(v_a_951_, v_b_952_);
stack->m_num = v_res_953_;
}
LEAN_EXPORT lean_object* l_USize_lor___boxed(lean_object* v_a_954_, lean_object* v_b_955_){
_start:
{
size_t v_a_boxed_956_; size_t v_b_boxed_957_; size_t v_res_958_; lean_object* v_r_959_; 
v_a_boxed_956_ = lean_unbox_usize(v_a_954_);
lean_dec(v_a_954_);
v_b_boxed_957_ = lean_unbox_usize(v_b_955_);
lean_dec(v_b_955_);
v_res_958_ = lean_usize_lor(v_a_boxed_956_, v_b_boxed_957_);
v_r_959_ = lean_box_usize(v_res_958_);
return v_r_959_;
}
}
LEAN_EXPORT void l_USize_xor_0interp(lean_interpreter_value* stack)
{
size_t v_a_960_ = stack[0].m_num;
size_t v_b_961_ = stack[1].m_num;
size_t v_res_962_;
v_res_962_ = lean_usize_xor(v_a_960_, v_b_961_);
stack->m_num = v_res_962_;
}
LEAN_EXPORT lean_object* l_USize_xor___boxed(lean_object* v_a_963_, lean_object* v_b_964_){
_start:
{
size_t v_a_boxed_965_; size_t v_b_boxed_966_; size_t v_res_967_; lean_object* v_r_968_; 
v_a_boxed_965_ = lean_unbox_usize(v_a_963_);
lean_dec(v_a_963_);
v_b_boxed_966_ = lean_unbox_usize(v_b_964_);
lean_dec(v_b_964_);
v_res_967_ = lean_usize_xor(v_a_boxed_965_, v_b_boxed_966_);
v_r_968_ = lean_box_usize(v_res_967_);
return v_r_968_;
}
}
LEAN_EXPORT void l_USize_shiftLeft_0interp(lean_interpreter_value* stack)
{
size_t v_a_969_ = stack[0].m_num;
size_t v_b_970_ = stack[1].m_num;
size_t v_res_971_;
v_res_971_ = lean_usize_shift_left(v_a_969_, v_b_970_);
stack->m_num = v_res_971_;
}
LEAN_EXPORT lean_object* l_USize_shiftLeft___boxed(lean_object* v_a_972_, lean_object* v_b_973_){
_start:
{
size_t v_a_boxed_974_; size_t v_b_boxed_975_; size_t v_res_976_; lean_object* v_r_977_; 
v_a_boxed_974_ = lean_unbox_usize(v_a_972_);
lean_dec(v_a_972_);
v_b_boxed_975_ = lean_unbox_usize(v_b_973_);
lean_dec(v_b_973_);
v_res_976_ = lean_usize_shift_left(v_a_boxed_974_, v_b_boxed_975_);
v_r_977_ = lean_box_usize(v_res_976_);
return v_r_977_;
}
}
LEAN_EXPORT void l_USize_shiftRight_0interp(lean_interpreter_value* stack)
{
size_t v_a_978_ = stack[0].m_num;
size_t v_b_979_ = stack[1].m_num;
size_t v_res_980_;
v_res_980_ = lean_usize_shift_right(v_a_978_, v_b_979_);
stack->m_num = v_res_980_;
}
LEAN_EXPORT lean_object* l_USize_shiftRight___boxed(lean_object* v_a_981_, lean_object* v_b_982_){
_start:
{
size_t v_a_boxed_983_; size_t v_b_boxed_984_; size_t v_res_985_; lean_object* v_r_986_; 
v_a_boxed_983_ = lean_unbox_usize(v_a_981_);
lean_dec(v_a_981_);
v_b_boxed_984_ = lean_unbox_usize(v_b_982_);
lean_dec(v_b_982_);
v_res_985_ = lean_usize_shift_right(v_a_boxed_983_, v_b_boxed_984_);
v_r_986_ = lean_box_usize(v_res_985_);
return v_r_986_;
}
}
LEAN_EXPORT void l_USize_ofNat32_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_987_ = stack[0].m_obj;
size_t v_res_989_;
v_res_989_ = lean_usize_of_nat(v_n_987_);
stack->m_num = v_res_989_;
}
LEAN_EXPORT lean_object* l_USize_ofNat32___boxed(lean_object* v_n_990_, lean_object* v_h_991_){
_start:
{
size_t v_res_992_; lean_object* v_r_993_; 
v_res_992_ = lean_usize_of_nat(v_n_990_);
lean_dec(v_n_990_);
v_r_993_ = lean_box_usize(v_res_992_);
return v_r_993_;
}
}
LEAN_EXPORT void l_UInt8_toUSize_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_994_ = stack[0].m_num;
size_t v_res_995_;
v_res_995_ = lean_uint8_to_usize(v_a_994_);
stack->m_num = v_res_995_;
}
LEAN_EXPORT lean_object* l_UInt8_toUSize___boxed(lean_object* v_a_996_){
_start:
{
uint8_t v_a_boxed_997_; size_t v_res_998_; lean_object* v_r_999_; 
v_a_boxed_997_ = lean_unbox(v_a_996_);
v_res_998_ = lean_uint8_to_usize(v_a_boxed_997_);
v_r_999_ = lean_box_usize(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT void l_USize_toUInt8_0interp(lean_interpreter_value* stack)
{
size_t v_a_1000_ = stack[0].m_num;
uint8_t v_res_1001_;
v_res_1001_ = lean_usize_to_uint8(v_a_1000_);
stack->m_num = v_res_1001_;
}
LEAN_EXPORT lean_object* l_USize_toUInt8___boxed(lean_object* v_a_1002_){
_start:
{
size_t v_a_boxed_1003_; uint8_t v_res_1004_; lean_object* v_r_1005_; 
v_a_boxed_1003_ = lean_unbox_usize(v_a_1002_);
lean_dec(v_a_1002_);
v_res_1004_ = lean_usize_to_uint8(v_a_boxed_1003_);
v_r_1005_ = lean_box(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT void l_UInt16_toUSize_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_1006_ = stack[0].m_num;
size_t v_res_1007_;
v_res_1007_ = lean_uint16_to_usize(v_a_1006_);
stack->m_num = v_res_1007_;
}
LEAN_EXPORT lean_object* l_UInt16_toUSize___boxed(lean_object* v_a_1008_){
_start:
{
uint16_t v_a_boxed_1009_; size_t v_res_1010_; lean_object* v_r_1011_; 
v_a_boxed_1009_ = lean_unbox(v_a_1008_);
v_res_1010_ = lean_uint16_to_usize(v_a_boxed_1009_);
v_r_1011_ = lean_box_usize(v_res_1010_);
return v_r_1011_;
}
}
LEAN_EXPORT void l_USize_toUInt16_0interp(lean_interpreter_value* stack)
{
size_t v_a_1012_ = stack[0].m_num;
uint16_t v_res_1013_;
v_res_1013_ = lean_usize_to_uint16(v_a_1012_);
stack->m_num = v_res_1013_;
}
LEAN_EXPORT lean_object* l_USize_toUInt16___boxed(lean_object* v_a_1014_){
_start:
{
size_t v_a_boxed_1015_; uint16_t v_res_1016_; lean_object* v_r_1017_; 
v_a_boxed_1015_ = lean_unbox_usize(v_a_1014_);
lean_dec(v_a_1014_);
v_res_1016_ = lean_usize_to_uint16(v_a_boxed_1015_);
v_r_1017_ = lean_box(v_res_1016_);
return v_r_1017_;
}
}
LEAN_EXPORT void l_UInt32_toUSize_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1018_ = stack[0].m_num;
size_t v_res_1019_;
v_res_1019_ = lean_uint32_to_usize(v_a_1018_);
stack->m_num = v_res_1019_;
}
LEAN_EXPORT lean_object* l_UInt32_toUSize___boxed(lean_object* v_a_1020_){
_start:
{
uint32_t v_a_boxed_1021_; size_t v_res_1022_; lean_object* v_r_1023_; 
v_a_boxed_1021_ = lean_unbox_uint32(v_a_1020_);
lean_dec(v_a_1020_);
v_res_1022_ = lean_uint32_to_usize(v_a_boxed_1021_);
v_r_1023_ = lean_box_usize(v_res_1022_);
return v_r_1023_;
}
}
LEAN_EXPORT void l_USize_toUInt32_0interp(lean_interpreter_value* stack)
{
size_t v_a_1024_ = stack[0].m_num;
uint32_t v_res_1025_;
v_res_1025_ = lean_usize_to_uint32(v_a_1024_);
stack->m_num = v_res_1025_;
}
LEAN_EXPORT lean_object* l_USize_toUInt32___boxed(lean_object* v_a_1026_){
_start:
{
size_t v_a_boxed_1027_; uint32_t v_res_1028_; lean_object* v_r_1029_; 
v_a_boxed_1027_ = lean_unbox_usize(v_a_1026_);
lean_dec(v_a_1026_);
v_res_1028_ = lean_usize_to_uint32(v_a_boxed_1027_);
v_r_1029_ = lean_box_uint32(v_res_1028_);
return v_r_1029_;
}
}
LEAN_EXPORT void l_UInt64_toUSize_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_1030_ = stack[0].m_num;
size_t v_res_1031_;
v_res_1031_ = lean_uint64_to_usize(v_a_1030_);
stack->m_num = v_res_1031_;
}
LEAN_EXPORT lean_object* l_UInt64_toUSize___boxed(lean_object* v_a_1032_){
_start:
{
uint64_t v_a_boxed_1033_; size_t v_res_1034_; lean_object* v_r_1035_; 
v_a_boxed_1033_ = lean_unbox_uint64(v_a_1032_);
lean_dec_ref(v_a_1032_);
v_res_1034_ = lean_uint64_to_usize(v_a_boxed_1033_);
v_r_1035_ = lean_box_usize(v_res_1034_);
return v_r_1035_;
}
}
LEAN_EXPORT void l_USize_toUInt64_0interp(lean_interpreter_value* stack)
{
size_t v_a_1036_ = stack[0].m_num;
uint64_t v_res_1037_;
v_res_1037_ = lean_usize_to_uint64(v_a_1036_);
stack->m_num = v_res_1037_;
}
LEAN_EXPORT lean_object* l_USize_toUInt64___boxed(lean_object* v_a_1038_){
_start:
{
size_t v_a_boxed_1039_; uint64_t v_res_1040_; lean_object* v_r_1041_; 
v_a_boxed_1039_ = lean_unbox_usize(v_a_1038_);
lean_dec(v_a_1038_);
v_res_1040_ = lean_usize_to_uint64(v_a_boxed_1039_);
v_r_1041_ = lean_box_uint64(v_res_1040_);
return v_r_1041_;
}
}
lean_object* l_USize_toBitVec32___redArg(size_t v_a_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_usize_to_nat(v_a_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT void l_USize_toBitVec32___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_a_1042_ = stack[0].m_num;
lean_object* v_res_1044_;
v_res_1044_ = l_USize_toBitVec32___redArg(v_a_1042_);
stack->m_obj
 = v_res_1044_;
}
LEAN_EXPORT lean_object* l_USize_toBitVec32___redArg___boxed(lean_object* v_a_1045_){
_start:
{
size_t v_a_boxed_1046_; lean_object* v_res_1047_; 
v_a_boxed_1046_ = lean_unbox_usize(v_a_1045_);
lean_dec(v_a_1045_);
v_res_1047_ = l_USize_toBitVec32___redArg(v_a_boxed_1046_);
return v_res_1047_;
}
}
lean_object* l_USize_toBitVec32(size_t v_a_1048_, lean_object* v_h_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_usize_to_nat(v_a_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT void l_USize_toBitVec32_0interp(lean_interpreter_value* stack)
{
size_t v_a_1048_ = stack[0].m_num;
lean_object* v_res_1051_;
v_res_1051_ = l_USize_toBitVec32(v_a_1048_, lean_box(0));
stack->m_obj
 = v_res_1051_;
}
LEAN_EXPORT lean_object* l_USize_toBitVec32___boxed(lean_object* v_a_1052_, lean_object* v_h_1053_){
_start:
{
size_t v_a_boxed_1054_; lean_object* v_res_1055_; 
v_a_boxed_1054_ = lean_unbox_usize(v_a_1052_);
lean_dec(v_a_1052_);
v_res_1055_ = l_USize_toBitVec32(v_a_boxed_1054_, v_h_1053_);
return v_res_1055_;
}
}
lean_object* l_USize_toBitVec64___redArg(size_t v_a_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_usize_to_nat(v_a_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT void l_USize_toBitVec64___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_a_1056_ = stack[0].m_num;
lean_object* v_res_1058_;
v_res_1058_ = l_USize_toBitVec64___redArg(v_a_1056_);
stack->m_obj
 = v_res_1058_;
}
LEAN_EXPORT lean_object* l_USize_toBitVec64___redArg___boxed(lean_object* v_a_1059_){
_start:
{
size_t v_a_boxed_1060_; lean_object* v_res_1061_; 
v_a_boxed_1060_ = lean_unbox_usize(v_a_1059_);
lean_dec(v_a_1059_);
v_res_1061_ = l_USize_toBitVec64___redArg(v_a_boxed_1060_);
return v_res_1061_;
}
}
lean_object* l_USize_toBitVec64(size_t v_a_1062_, lean_object* v_h_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_usize_to_nat(v_a_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT void l_USize_toBitVec64_0interp(lean_interpreter_value* stack)
{
size_t v_a_1062_ = stack[0].m_num;
lean_object* v_res_1065_;
v_res_1065_ = l_USize_toBitVec64(v_a_1062_, lean_box(0));
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l_USize_toBitVec64___boxed(lean_object* v_a_1066_, lean_object* v_h_1067_){
_start:
{
size_t v_a_boxed_1068_; lean_object* v_res_1069_; 
v_a_boxed_1068_ = lean_unbox_usize(v_a_1066_);
lean_dec(v_a_1066_);
v_res_1069_ = l_USize_toBitVec64(v_a_boxed_1068_, v_h_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT void l_USize_complement_0interp(lean_interpreter_value* stack)
{
size_t v_a_1080_ = stack[0].m_num;
size_t v_res_1081_;
v_res_1081_ = lean_usize_complement(v_a_1080_);
stack->m_num = v_res_1081_;
}
LEAN_EXPORT lean_object* l_USize_complement___boxed(lean_object* v_a_1082_){
_start:
{
size_t v_a_boxed_1083_; size_t v_res_1084_; lean_object* v_r_1085_; 
v_a_boxed_1083_ = lean_unbox_usize(v_a_1082_);
lean_dec(v_a_1082_);
v_res_1084_ = lean_usize_complement(v_a_boxed_1083_);
v_r_1085_ = lean_box_usize(v_res_1084_);
return v_r_1085_;
}
}
LEAN_EXPORT void l_USize_neg_0interp(lean_interpreter_value* stack)
{
size_t v_a_1086_ = stack[0].m_num;
size_t v_res_1087_;
v_res_1087_ = lean_usize_neg(v_a_1086_);
stack->m_num = v_res_1087_;
}
LEAN_EXPORT lean_object* l_USize_neg___boxed(lean_object* v_a_1088_){
_start:
{
size_t v_a_boxed_1089_; size_t v_res_1090_; lean_object* v_r_1091_; 
v_a_boxed_1089_ = lean_unbox_usize(v_a_1088_);
lean_dec(v_a_1088_);
v_res_1090_ = lean_usize_neg(v_a_boxed_1089_);
v_r_1091_ = lean_box_usize(v_res_1090_);
return v_r_1091_;
}
}
LEAN_EXPORT void l_Bool_toUSize_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_1106_ = stack[0].m_num;
size_t v_res_1107_;
v_res_1107_ = lean_bool_to_usize(v_b_1106_);
stack->m_num = v_res_1107_;
}
LEAN_EXPORT lean_object* l_Bool_toUSize___boxed(lean_object* v_b_1108_){
_start:
{
uint8_t v_b_boxed_1109_; size_t v_res_1110_; lean_object* v_r_1111_; 
v_b_boxed_1109_ = lean_unbox(v_b_1108_);
v_res_1110_ = lean_bool_to_usize(v_b_boxed_1109_);
v_r_1111_ = lean_box_usize(v_res_1110_);
return v_r_1111_;
}
}
size_t l_instMaxUSize___lam__0(size_t v_x_1112_, size_t v_y_1113_){
_start:
{
uint8_t v___x_1114_; 
v___x_1114_ = lean_usize_dec_le(v_x_1112_, v_y_1113_);
if (v___x_1114_ == 0)
{
return v_x_1112_;
}
else
{
return v_y_1113_;
}
}
}
LEAN_EXPORT void l_instMaxUSize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_x_1112_ = stack[0].m_num;
size_t v_y_1113_ = stack[1].m_num;
size_t v_res_1115_;
v_res_1115_ = l_instMaxUSize___lam__0(v_x_1112_, v_y_1113_);
stack->m_num = v_res_1115_;
}
LEAN_EXPORT lean_object* l_instMaxUSize___lam__0___boxed(lean_object* v_x_1116_, lean_object* v_y_1117_){
_start:
{
size_t v_x_boxed_1118_; size_t v_y_boxed_1119_; size_t v_res_1120_; lean_object* v_r_1121_; 
v_x_boxed_1118_ = lean_unbox_usize(v_x_1116_);
lean_dec(v_x_1116_);
v_y_boxed_1119_ = lean_unbox_usize(v_y_1117_);
lean_dec(v_y_1117_);
v_res_1120_ = l_instMaxUSize___lam__0(v_x_boxed_1118_, v_y_boxed_1119_);
v_r_1121_ = lean_box_usize(v_res_1120_);
return v_r_1121_;
}
}
size_t l_instMinUSize___lam__0(size_t v_x_1124_, size_t v_y_1125_){
_start:
{
uint8_t v___x_1126_; 
v___x_1126_ = lean_usize_dec_le(v_x_1124_, v_y_1125_);
if (v___x_1126_ == 0)
{
return v_y_1125_;
}
else
{
return v_x_1124_;
}
}
}
LEAN_EXPORT void l_instMinUSize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_x_1124_ = stack[0].m_num;
size_t v_y_1125_ = stack[1].m_num;
size_t v_res_1127_;
v_res_1127_ = l_instMinUSize___lam__0(v_x_1124_, v_y_1125_);
stack->m_num = v_res_1127_;
}
LEAN_EXPORT lean_object* l_instMinUSize___lam__0___boxed(lean_object* v_x_1128_, lean_object* v_y_1129_){
_start:
{
size_t v_x_boxed_1130_; size_t v_y_boxed_1131_; size_t v_res_1132_; lean_object* v_r_1133_; 
v_x_boxed_1130_ = lean_unbox_usize(v_x_1128_);
lean_dec(v_x_1128_);
v_y_boxed_1131_ = lean_unbox_usize(v_y_1129_);
lean_dec(v_y_1129_);
v_res_1132_ = l_instMinUSize___lam__0(v_x_boxed_1130_, v_y_boxed_1131_);
v_r_1133_ = lean_box_usize(v_res_1132_);
return v_r_1133_;
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
