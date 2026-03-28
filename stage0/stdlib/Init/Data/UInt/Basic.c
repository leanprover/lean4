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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
extern lean_object* l_System_Platform_numBits;
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_of_nat_mk(lean_object*);
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
uint8_t v___y_196_; uint8_t v___x_199_; uint8_t v___x_200_; 
v___x_199_ = 65;
v___x_200_ = lean_uint8_dec_le(v___x_199_, v_b_194_);
if (v___x_200_ == 0)
{
v___y_196_ = v___x_200_;
goto v___jp_195_;
}
else
{
uint8_t v___x_201_; uint8_t v___x_202_; 
v___x_201_ = 90;
v___x_202_ = lean_uint8_dec_le(v_b_194_, v___x_201_);
v___y_196_ = v___x_202_;
goto v___jp_195_;
}
v___jp_195_:
{
if (v___y_196_ == 0)
{
return v_b_194_;
}
else
{
uint8_t v___x_197_; uint8_t v___x_198_; 
v___x_197_ = 32;
v___x_198_ = lean_uint8_add(v_b_194_, v___x_197_);
return v___x_198_;
}
}
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
LEAN_EXPORT uint16_t l_UInt16_ofFin(lean_object* v_a_207_){
_start:
{
uint16_t v___x_208_; 
v___x_208_ = lean_uint16_of_nat_mk(v_a_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofFin___boxed(lean_object* v_a_209_){
_start:
{
uint16_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_UInt16_ofFin(v_a_209_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
static lean_object* _init_l_UInt16_ofInt___closed__0(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_unsigned_to_nat(16u);
v___x_213_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_214_ = l_Int_pow(v___x_213_, v___x_212_);
return v___x_214_;
}
}
LEAN_EXPORT uint16_t l_UInt16_ofInt(lean_object* v_x_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint16_t v___x_219_; 
v___x_216_ = lean_obj_once(&l_UInt16_ofInt___closed__0, &l_UInt16_ofInt___closed__0_once, _init_l_UInt16_ofInt___closed__0);
v___x_217_ = lean_int_emod(v_x_215_, v___x_216_);
v___x_218_ = l_Int_toNat(v___x_217_);
lean_dec(v___x_217_);
v___x_219_ = lean_uint16_of_nat(v___x_218_);
lean_dec(v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofInt___boxed(lean_object* v_x_220_){
_start:
{
uint16_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = l_UInt16_ofInt(v_x_220_);
lean_dec(v_x_220_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT lean_object* l_UInt16_add___boxed(lean_object* v_a_225_, lean_object* v_b_226_){
_start:
{
uint16_t v_a_boxed_227_; uint16_t v_b_boxed_228_; uint16_t v_res_229_; lean_object* v_r_230_; 
v_a_boxed_227_ = lean_unbox(v_a_225_);
v_b_boxed_228_ = lean_unbox(v_b_226_);
v_res_229_ = lean_uint16_add(v_a_boxed_227_, v_b_boxed_228_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT lean_object* l_UInt16_sub___boxed(lean_object* v_a_233_, lean_object* v_b_234_){
_start:
{
uint16_t v_a_boxed_235_; uint16_t v_b_boxed_236_; uint16_t v_res_237_; lean_object* v_r_238_; 
v_a_boxed_235_ = lean_unbox(v_a_233_);
v_b_boxed_236_ = lean_unbox(v_b_234_);
v_res_237_ = lean_uint16_sub(v_a_boxed_235_, v_b_boxed_236_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT lean_object* l_UInt16_mul___boxed(lean_object* v_a_241_, lean_object* v_b_242_){
_start:
{
uint16_t v_a_boxed_243_; uint16_t v_b_boxed_244_; uint16_t v_res_245_; lean_object* v_r_246_; 
v_a_boxed_243_ = lean_unbox(v_a_241_);
v_b_boxed_244_ = lean_unbox(v_b_242_);
v_res_245_ = lean_uint16_mul(v_a_boxed_243_, v_b_boxed_244_);
v_r_246_ = lean_box(v_res_245_);
return v_r_246_;
}
}
LEAN_EXPORT lean_object* l_UInt16_div___boxed(lean_object* v_a_249_, lean_object* v_b_250_){
_start:
{
uint16_t v_a_boxed_251_; uint16_t v_b_boxed_252_; uint16_t v_res_253_; lean_object* v_r_254_; 
v_a_boxed_251_ = lean_unbox(v_a_249_);
v_b_boxed_252_ = lean_unbox(v_b_250_);
v_res_253_ = lean_uint16_div(v_a_boxed_251_, v_b_boxed_252_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT uint16_t l_UInt16_pow(uint16_t v_x_255_, lean_object* v_n_256_){
_start:
{
lean_object* v_zero_257_; uint8_t v_isZero_258_; 
v_zero_257_ = lean_unsigned_to_nat(0u);
v_isZero_258_ = lean_nat_dec_eq(v_n_256_, v_zero_257_);
if (v_isZero_258_ == 1)
{
uint16_t v___x_259_; 
v___x_259_ = 1;
return v___x_259_;
}
else
{
lean_object* v_one_260_; lean_object* v_n_261_; uint16_t v___x_262_; uint16_t v___x_263_; 
v_one_260_ = lean_unsigned_to_nat(1u);
v_n_261_ = lean_nat_sub(v_n_256_, v_one_260_);
v___x_262_ = l_UInt16_pow(v_x_255_, v_n_261_);
lean_dec(v_n_261_);
v___x_263_ = lean_uint16_mul(v___x_262_, v_x_255_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_UInt16_pow___boxed(lean_object* v_x_264_, lean_object* v_n_265_){
_start:
{
uint16_t v_x_boxed_266_; uint16_t v_res_267_; lean_object* v_r_268_; 
v_x_boxed_266_ = lean_unbox(v_x_264_);
v_res_267_ = l_UInt16_pow(v_x_boxed_266_, v_n_265_);
lean_dec(v_n_265_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT lean_object* l_UInt16_mod___boxed(lean_object* v_a_271_, lean_object* v_b_272_){
_start:
{
uint16_t v_a_boxed_273_; uint16_t v_b_boxed_274_; uint16_t v_res_275_; lean_object* v_r_276_; 
v_a_boxed_273_ = lean_unbox(v_a_271_);
v_b_boxed_274_ = lean_unbox(v_b_272_);
v_res_275_ = lean_uint16_mod(v_a_boxed_273_, v_b_boxed_274_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt16_modn_spec__0(lean_object* v_a_277_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(16u);
v___x_279_ = l_BitVec_ofNat(v___x_278_, v_a_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt16_modn_spec__0___boxed(lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Nat_cast___at___00UInt16_modn_spec__0(v_a_280_);
lean_dec(v_a_280_);
return v_res_281_;
}
}
LEAN_EXPORT uint16_t l_UInt16_modn(uint16_t v_a_282_, lean_object* v_n_283_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint16_t v___x_287_; 
v___x_284_ = lean_uint16_to_nat(v_a_282_);
v___x_285_ = lean_nat_mod(v___x_284_, v_n_283_);
lean_dec(v___x_284_);
v___x_286_ = l_Nat_cast___at___00UInt16_modn_spec__0(v___x_285_);
lean_dec(v___x_285_);
v___x_287_ = lean_uint16_of_nat_mk(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_UInt16_modn___boxed(lean_object* v_a_288_, lean_object* v_n_289_){
_start:
{
uint16_t v_a_boxed_290_; uint16_t v_res_291_; lean_object* v_r_292_; 
v_a_boxed_290_ = lean_unbox(v_a_288_);
v_res_291_ = l_UInt16_modn(v_a_boxed_290_, v_n_289_);
lean_dec(v_n_289_);
v_r_292_ = lean_box(v_res_291_);
return v_r_292_;
}
}
LEAN_EXPORT lean_object* l_UInt16_land___boxed(lean_object* v_a_295_, lean_object* v_b_296_){
_start:
{
uint16_t v_a_boxed_297_; uint16_t v_b_boxed_298_; uint16_t v_res_299_; lean_object* v_r_300_; 
v_a_boxed_297_ = lean_unbox(v_a_295_);
v_b_boxed_298_ = lean_unbox(v_b_296_);
v_res_299_ = lean_uint16_land(v_a_boxed_297_, v_b_boxed_298_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT lean_object* l_UInt16_lor___boxed(lean_object* v_a_303_, lean_object* v_b_304_){
_start:
{
uint16_t v_a_boxed_305_; uint16_t v_b_boxed_306_; uint16_t v_res_307_; lean_object* v_r_308_; 
v_a_boxed_305_ = lean_unbox(v_a_303_);
v_b_boxed_306_ = lean_unbox(v_b_304_);
v_res_307_ = lean_uint16_lor(v_a_boxed_305_, v_b_boxed_306_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT lean_object* l_UInt16_xor___boxed(lean_object* v_a_311_, lean_object* v_b_312_){
_start:
{
uint16_t v_a_boxed_313_; uint16_t v_b_boxed_314_; uint16_t v_res_315_; lean_object* v_r_316_; 
v_a_boxed_313_ = lean_unbox(v_a_311_);
v_b_boxed_314_ = lean_unbox(v_b_312_);
v_res_315_ = lean_uint16_xor(v_a_boxed_313_, v_b_boxed_314_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_UInt16_shiftLeft___boxed(lean_object* v_a_319_, lean_object* v_b_320_){
_start:
{
uint16_t v_a_boxed_321_; uint16_t v_b_boxed_322_; uint16_t v_res_323_; lean_object* v_r_324_; 
v_a_boxed_321_ = lean_unbox(v_a_319_);
v_b_boxed_322_ = lean_unbox(v_b_320_);
v_res_323_ = lean_uint16_shift_left(v_a_boxed_321_, v_b_boxed_322_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT lean_object* l_UInt16_shiftRight___boxed(lean_object* v_a_327_, lean_object* v_b_328_){
_start:
{
uint16_t v_a_boxed_329_; uint16_t v_b_boxed_330_; uint16_t v_res_331_; lean_object* v_r_332_; 
v_a_boxed_329_ = lean_unbox(v_a_327_);
v_b_boxed_330_ = lean_unbox(v_b_328_);
v_res_331_ = lean_uint16_shift_right(v_a_boxed_329_, v_b_boxed_330_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
static lean_object* _init_l_instLTUInt16(void){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = lean_box(0);
return v___x_347_;
}
}
static lean_object* _init_l_instLEUInt16(void){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = lean_box(0);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_UInt16_complement___boxed(lean_object* v_a_350_){
_start:
{
uint16_t v_a_boxed_351_; uint16_t v_res_352_; lean_object* v_r_353_; 
v_a_boxed_351_ = lean_unbox(v_a_350_);
v_res_352_ = lean_uint16_complement(v_a_boxed_351_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT lean_object* l_UInt16_neg___boxed(lean_object* v_a_355_){
_start:
{
uint16_t v_a_boxed_356_; uint16_t v_res_357_; lean_object* v_r_358_; 
v_a_boxed_356_ = lean_unbox(v_a_355_);
v_res_357_ = lean_uint16_neg(v_a_boxed_356_);
v_r_358_ = lean_box(v_res_357_);
return v_r_358_;
}
}
LEAN_EXPORT lean_object* l_Bool_toUInt16___boxed(lean_object* v_b_374_){
_start:
{
uint8_t v_b_boxed_375_; uint16_t v_res_376_; lean_object* v_r_377_; 
v_b_boxed_375_ = lean_unbox(v_b_374_);
v_res_376_ = lean_bool_to_uint16(v_b_boxed_375_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT uint8_t l_UInt16_decLt___aux__1(uint16_t v_a_378_, uint16_t v_b_379_){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_380_ = lean_uint16_to_nat(v_a_378_);
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_nat_add(v___x_380_, v___x_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_uint16_to_nat(v_b_379_);
v___x_384_ = lean_nat_dec_le(v___x_382_, v___x_383_);
lean_dec(v___x_383_);
lean_dec(v___x_382_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_UInt16_decLt___aux__1___boxed(lean_object* v_a_385_, lean_object* v_b_386_){
_start:
{
uint16_t v_a_boxed_387_; uint16_t v_b_boxed_388_; uint8_t v_res_389_; lean_object* v_r_390_; 
v_a_boxed_387_ = lean_unbox(v_a_385_);
v_b_boxed_388_ = lean_unbox(v_b_386_);
v_res_389_ = l_UInt16_decLt___aux__1(v_a_boxed_387_, v_b_boxed_388_);
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
LEAN_EXPORT uint8_t l_UInt16_decLe___aux__1(uint16_t v_a_399_, uint16_t v_b_400_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_401_ = lean_uint16_to_nat(v_a_399_);
v___x_402_ = lean_uint16_to_nat(v_b_400_);
v___x_403_ = lean_nat_dec_le(v___x_401_, v___x_402_);
lean_dec(v___x_402_);
lean_dec(v___x_401_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_UInt16_decLe___aux__1___boxed(lean_object* v_a_404_, lean_object* v_b_405_){
_start:
{
uint16_t v_a_boxed_406_; uint16_t v_b_boxed_407_; uint8_t v_res_408_; lean_object* v_r_409_; 
v_a_boxed_406_ = lean_unbox(v_a_404_);
v_b_boxed_407_ = lean_unbox(v_b_405_);
v_res_408_ = l_UInt16_decLe___aux__1(v_a_boxed_406_, v_b_boxed_407_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
LEAN_EXPORT lean_object* l_UInt16_decLe___boxed(lean_object* v_a_412_, lean_object* v_b_413_){
_start:
{
uint16_t v_a_boxed_414_; uint16_t v_b_boxed_415_; uint8_t v_res_416_; lean_object* v_r_417_; 
v_a_boxed_414_ = lean_unbox(v_a_412_);
v_b_boxed_415_ = lean_unbox(v_b_413_);
v_res_416_ = lean_uint16_dec_le(v_a_boxed_414_, v_b_boxed_415_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT uint16_t l_instMaxUInt16___lam__0(uint16_t v_x_418_, uint16_t v_y_419_){
_start:
{
uint8_t v___x_420_; 
v___x_420_ = lean_uint16_dec_le(v_x_418_, v_y_419_);
if (v___x_420_ == 0)
{
return v_x_418_;
}
else
{
return v_y_419_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxUInt16___lam__0___boxed(lean_object* v_x_421_, lean_object* v_y_422_){
_start:
{
uint16_t v_x_boxed_423_; uint16_t v_y_boxed_424_; uint16_t v_res_425_; lean_object* v_r_426_; 
v_x_boxed_423_ = lean_unbox(v_x_421_);
v_y_boxed_424_ = lean_unbox(v_y_422_);
v_res_425_ = l_instMaxUInt16___lam__0(v_x_boxed_423_, v_y_boxed_424_);
v_r_426_ = lean_box(v_res_425_);
return v_r_426_;
}
}
LEAN_EXPORT uint16_t l_instMinUInt16___lam__0(uint16_t v_x_429_, uint16_t v_y_430_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = lean_uint16_dec_le(v_x_429_, v_y_430_);
if (v___x_431_ == 0)
{
return v_y_430_;
}
else
{
return v_x_429_;
}
}
}
LEAN_EXPORT lean_object* l_instMinUInt16___lam__0___boxed(lean_object* v_x_432_, lean_object* v_y_433_){
_start:
{
uint16_t v_x_boxed_434_; uint16_t v_y_boxed_435_; uint16_t v_res_436_; lean_object* v_r_437_; 
v_x_boxed_434_ = lean_unbox(v_x_432_);
v_y_boxed_435_ = lean_unbox(v_y_433_);
v_res_436_ = l_instMinUInt16___lam__0(v_x_boxed_434_, v_y_boxed_435_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofFin(lean_object* v_a_440_){
_start:
{
uint32_t v___x_441_; 
v___x_441_ = lean_uint32_of_nat_mk(v_a_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofFin___boxed(lean_object* v_a_442_){
_start:
{
uint32_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_UInt32_ofFin(v_a_442_);
v_r_444_ = lean_box_uint32(v_res_443_);
return v_r_444_;
}
}
static lean_object* _init_l_UInt32_ofInt___closed__0(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_unsigned_to_nat(32u);
v___x_446_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_447_ = l_Int_pow(v___x_446_, v___x_445_);
return v___x_447_;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofInt(lean_object* v_x_448_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint32_t v___x_452_; 
v___x_449_ = lean_obj_once(&l_UInt32_ofInt___closed__0, &l_UInt32_ofInt___closed__0_once, _init_l_UInt32_ofInt___closed__0);
v___x_450_ = lean_int_emod(v_x_448_, v___x_449_);
v___x_451_ = l_Int_toNat(v___x_450_);
lean_dec(v___x_450_);
v___x_452_ = lean_uint32_of_nat(v___x_451_);
lean_dec(v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofInt___boxed(lean_object* v_x_453_){
_start:
{
uint32_t v_res_454_; lean_object* v_r_455_; 
v_res_454_ = l_UInt32_ofInt(v_x_453_);
lean_dec(v_x_453_);
v_r_455_ = lean_box_uint32(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT lean_object* l_UInt32_mul___boxed(lean_object* v_a_458_, lean_object* v_b_459_){
_start:
{
uint32_t v_a_boxed_460_; uint32_t v_b_boxed_461_; uint32_t v_res_462_; lean_object* v_r_463_; 
v_a_boxed_460_ = lean_unbox_uint32(v_a_458_);
lean_dec(v_a_458_);
v_b_boxed_461_ = lean_unbox_uint32(v_b_459_);
lean_dec(v_b_459_);
v_res_462_ = lean_uint32_mul(v_a_boxed_460_, v_b_boxed_461_);
v_r_463_ = lean_box_uint32(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT lean_object* l_UInt32_div___boxed(lean_object* v_a_466_, lean_object* v_b_467_){
_start:
{
uint32_t v_a_boxed_468_; uint32_t v_b_boxed_469_; uint32_t v_res_470_; lean_object* v_r_471_; 
v_a_boxed_468_ = lean_unbox_uint32(v_a_466_);
lean_dec(v_a_466_);
v_b_boxed_469_ = lean_unbox_uint32(v_b_467_);
lean_dec(v_b_467_);
v_res_470_ = lean_uint32_div(v_a_boxed_468_, v_b_boxed_469_);
v_r_471_ = lean_box_uint32(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT uint32_t l_UInt32_pow(uint32_t v_x_472_, lean_object* v_n_473_){
_start:
{
lean_object* v_zero_474_; uint8_t v_isZero_475_; 
v_zero_474_ = lean_unsigned_to_nat(0u);
v_isZero_475_ = lean_nat_dec_eq(v_n_473_, v_zero_474_);
if (v_isZero_475_ == 1)
{
uint32_t v___x_476_; 
v___x_476_ = 1;
return v___x_476_;
}
else
{
lean_object* v_one_477_; lean_object* v_n_478_; uint32_t v___x_479_; uint32_t v___x_480_; 
v_one_477_ = lean_unsigned_to_nat(1u);
v_n_478_ = lean_nat_sub(v_n_473_, v_one_477_);
v___x_479_ = l_UInt32_pow(v_x_472_, v_n_478_);
lean_dec(v_n_478_);
v___x_480_ = lean_uint32_mul(v___x_479_, v_x_472_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_UInt32_pow___boxed(lean_object* v_x_481_, lean_object* v_n_482_){
_start:
{
uint32_t v_x_boxed_483_; uint32_t v_res_484_; lean_object* v_r_485_; 
v_x_boxed_483_ = lean_unbox_uint32(v_x_481_);
lean_dec(v_x_481_);
v_res_484_ = l_UInt32_pow(v_x_boxed_483_, v_n_482_);
lean_dec(v_n_482_);
v_r_485_ = lean_box_uint32(v_res_484_);
return v_r_485_;
}
}
LEAN_EXPORT lean_object* l_UInt32_mod___boxed(lean_object* v_a_488_, lean_object* v_b_489_){
_start:
{
uint32_t v_a_boxed_490_; uint32_t v_b_boxed_491_; uint32_t v_res_492_; lean_object* v_r_493_; 
v_a_boxed_490_ = lean_unbox_uint32(v_a_488_);
lean_dec(v_a_488_);
v_b_boxed_491_ = lean_unbox_uint32(v_b_489_);
lean_dec(v_b_489_);
v_res_492_ = lean_uint32_mod(v_a_boxed_490_, v_b_boxed_491_);
v_r_493_ = lean_box_uint32(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt32_modn_spec__0(lean_object* v_a_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_unsigned_to_nat(32u);
v___x_496_ = l_BitVec_ofNat(v___x_495_, v_a_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt32_modn_spec__0___boxed(lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Nat_cast___at___00UInt32_modn_spec__0(v_a_497_);
lean_dec(v_a_497_);
return v_res_498_;
}
}
LEAN_EXPORT uint32_t l_UInt32_modn(uint32_t v_a_499_, lean_object* v_n_500_){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint32_t v___x_504_; 
v___x_501_ = lean_uint32_to_nat(v_a_499_);
v___x_502_ = lean_nat_mod(v___x_501_, v_n_500_);
lean_dec(v___x_501_);
v___x_503_ = l_Nat_cast___at___00UInt32_modn_spec__0(v___x_502_);
lean_dec(v___x_502_);
v___x_504_ = lean_uint32_of_nat_mk(v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_UInt32_modn___boxed(lean_object* v_a_505_, lean_object* v_n_506_){
_start:
{
uint32_t v_a_boxed_507_; uint32_t v_res_508_; lean_object* v_r_509_; 
v_a_boxed_507_ = lean_unbox_uint32(v_a_505_);
lean_dec(v_a_505_);
v_res_508_ = l_UInt32_modn(v_a_boxed_507_, v_n_506_);
lean_dec(v_n_506_);
v_r_509_ = lean_box_uint32(v_res_508_);
return v_r_509_;
}
}
LEAN_EXPORT lean_object* l_UInt32_land___boxed(lean_object* v_a_512_, lean_object* v_b_513_){
_start:
{
uint32_t v_a_boxed_514_; uint32_t v_b_boxed_515_; uint32_t v_res_516_; lean_object* v_r_517_; 
v_a_boxed_514_ = lean_unbox_uint32(v_a_512_);
lean_dec(v_a_512_);
v_b_boxed_515_ = lean_unbox_uint32(v_b_513_);
lean_dec(v_b_513_);
v_res_516_ = lean_uint32_land(v_a_boxed_514_, v_b_boxed_515_);
v_r_517_ = lean_box_uint32(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT lean_object* l_UInt32_lor___boxed(lean_object* v_a_520_, lean_object* v_b_521_){
_start:
{
uint32_t v_a_boxed_522_; uint32_t v_b_boxed_523_; uint32_t v_res_524_; lean_object* v_r_525_; 
v_a_boxed_522_ = lean_unbox_uint32(v_a_520_);
lean_dec(v_a_520_);
v_b_boxed_523_ = lean_unbox_uint32(v_b_521_);
lean_dec(v_b_521_);
v_res_524_ = lean_uint32_lor(v_a_boxed_522_, v_b_boxed_523_);
v_r_525_ = lean_box_uint32(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT lean_object* l_UInt32_xor___boxed(lean_object* v_a_528_, lean_object* v_b_529_){
_start:
{
uint32_t v_a_boxed_530_; uint32_t v_b_boxed_531_; uint32_t v_res_532_; lean_object* v_r_533_; 
v_a_boxed_530_ = lean_unbox_uint32(v_a_528_);
lean_dec(v_a_528_);
v_b_boxed_531_ = lean_unbox_uint32(v_b_529_);
lean_dec(v_b_529_);
v_res_532_ = lean_uint32_xor(v_a_boxed_530_, v_b_boxed_531_);
v_r_533_ = lean_box_uint32(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT lean_object* l_UInt32_shiftLeft___boxed(lean_object* v_a_536_, lean_object* v_b_537_){
_start:
{
uint32_t v_a_boxed_538_; uint32_t v_b_boxed_539_; uint32_t v_res_540_; lean_object* v_r_541_; 
v_a_boxed_538_ = lean_unbox_uint32(v_a_536_);
lean_dec(v_a_536_);
v_b_boxed_539_ = lean_unbox_uint32(v_b_537_);
lean_dec(v_b_537_);
v_res_540_ = lean_uint32_shift_left(v_a_boxed_538_, v_b_boxed_539_);
v_r_541_ = lean_box_uint32(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT lean_object* l_UInt32_shiftRight___boxed(lean_object* v_a_544_, lean_object* v_b_545_){
_start:
{
uint32_t v_a_boxed_546_; uint32_t v_b_boxed_547_; uint32_t v_res_548_; lean_object* v_r_549_; 
v_a_boxed_546_ = lean_unbox_uint32(v_a_544_);
lean_dec(v_a_544_);
v_b_boxed_547_ = lean_unbox_uint32(v_b_545_);
lean_dec(v_b_545_);
v_res_548_ = lean_uint32_shift_right(v_a_boxed_546_, v_b_boxed_547_);
v_r_549_ = lean_box_uint32(v_res_548_);
return v_r_549_;
}
}
LEAN_EXPORT lean_object* l_UInt32_complement___boxed(lean_object* v_a_561_){
_start:
{
uint32_t v_a_boxed_562_; uint32_t v_res_563_; lean_object* v_r_564_; 
v_a_boxed_562_ = lean_unbox_uint32(v_a_561_);
lean_dec(v_a_561_);
v_res_563_ = lean_uint32_complement(v_a_boxed_562_);
v_r_564_ = lean_box_uint32(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT lean_object* l_UInt32_neg___boxed(lean_object* v_a_566_){
_start:
{
uint32_t v_a_boxed_567_; uint32_t v_res_568_; lean_object* v_r_569_; 
v_a_boxed_567_ = lean_unbox_uint32(v_a_566_);
lean_dec(v_a_566_);
v_res_568_ = lean_uint32_neg(v_a_boxed_567_);
v_r_569_ = lean_box_uint32(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l_Bool_toUInt32___boxed(lean_object* v_b_585_){
_start:
{
uint8_t v_b_boxed_586_; uint32_t v_res_587_; lean_object* v_r_588_; 
v_b_boxed_586_ = lean_unbox(v_b_585_);
v_res_587_ = lean_bool_to_uint32(v_b_boxed_586_);
v_r_588_ = lean_box_uint32(v_res_587_);
return v_r_588_;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofFin(lean_object* v_a_589_){
_start:
{
uint64_t v___x_590_; 
v___x_590_ = lean_uint64_of_nat_mk(v_a_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofFin___boxed(lean_object* v_a_591_){
_start:
{
uint64_t v_res_592_; lean_object* v_r_593_; 
v_res_592_ = l_UInt64_ofFin(v_a_591_);
v_r_593_ = lean_box_uint64(v_res_592_);
return v_r_593_;
}
}
static lean_object* _init_l_UInt64_ofInt___closed__0(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_unsigned_to_nat(64u);
v___x_595_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_596_ = l_Int_pow(v___x_595_, v___x_594_);
return v___x_596_;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofInt(lean_object* v_x_597_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint64_t v___x_601_; 
v___x_598_ = lean_obj_once(&l_UInt64_ofInt___closed__0, &l_UInt64_ofInt___closed__0_once, _init_l_UInt64_ofInt___closed__0);
v___x_599_ = lean_int_emod(v_x_597_, v___x_598_);
v___x_600_ = l_Int_toNat(v___x_599_);
lean_dec(v___x_599_);
v___x_601_ = lean_uint64_of_nat(v___x_600_);
lean_dec(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofInt___boxed(lean_object* v_x_602_){
_start:
{
uint64_t v_res_603_; lean_object* v_r_604_; 
v_res_603_ = l_UInt64_ofInt(v_x_602_);
lean_dec(v_x_602_);
v_r_604_ = lean_box_uint64(v_res_603_);
return v_r_604_;
}
}
LEAN_EXPORT lean_object* l_UInt64_add___boxed(lean_object* v_a_607_, lean_object* v_b_608_){
_start:
{
uint64_t v_a_boxed_609_; uint64_t v_b_boxed_610_; uint64_t v_res_611_; lean_object* v_r_612_; 
v_a_boxed_609_ = lean_unbox_uint64(v_a_607_);
lean_dec_ref(v_a_607_);
v_b_boxed_610_ = lean_unbox_uint64(v_b_608_);
lean_dec_ref(v_b_608_);
v_res_611_ = lean_uint64_add(v_a_boxed_609_, v_b_boxed_610_);
v_r_612_ = lean_box_uint64(v_res_611_);
return v_r_612_;
}
}
LEAN_EXPORT lean_object* l_UInt64_sub___boxed(lean_object* v_a_615_, lean_object* v_b_616_){
_start:
{
uint64_t v_a_boxed_617_; uint64_t v_b_boxed_618_; uint64_t v_res_619_; lean_object* v_r_620_; 
v_a_boxed_617_ = lean_unbox_uint64(v_a_615_);
lean_dec_ref(v_a_615_);
v_b_boxed_618_ = lean_unbox_uint64(v_b_616_);
lean_dec_ref(v_b_616_);
v_res_619_ = lean_uint64_sub(v_a_boxed_617_, v_b_boxed_618_);
v_r_620_ = lean_box_uint64(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT lean_object* l_UInt64_mul___boxed(lean_object* v_a_623_, lean_object* v_b_624_){
_start:
{
uint64_t v_a_boxed_625_; uint64_t v_b_boxed_626_; uint64_t v_res_627_; lean_object* v_r_628_; 
v_a_boxed_625_ = lean_unbox_uint64(v_a_623_);
lean_dec_ref(v_a_623_);
v_b_boxed_626_ = lean_unbox_uint64(v_b_624_);
lean_dec_ref(v_b_624_);
v_res_627_ = lean_uint64_mul(v_a_boxed_625_, v_b_boxed_626_);
v_r_628_ = lean_box_uint64(v_res_627_);
return v_r_628_;
}
}
LEAN_EXPORT lean_object* l_UInt64_div___boxed(lean_object* v_a_631_, lean_object* v_b_632_){
_start:
{
uint64_t v_a_boxed_633_; uint64_t v_b_boxed_634_; uint64_t v_res_635_; lean_object* v_r_636_; 
v_a_boxed_633_ = lean_unbox_uint64(v_a_631_);
lean_dec_ref(v_a_631_);
v_b_boxed_634_ = lean_unbox_uint64(v_b_632_);
lean_dec_ref(v_b_632_);
v_res_635_ = lean_uint64_div(v_a_boxed_633_, v_b_boxed_634_);
v_r_636_ = lean_box_uint64(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT uint64_t l_UInt64_pow(uint64_t v_x_637_, lean_object* v_n_638_){
_start:
{
lean_object* v_zero_639_; uint8_t v_isZero_640_; 
v_zero_639_ = lean_unsigned_to_nat(0u);
v_isZero_640_ = lean_nat_dec_eq(v_n_638_, v_zero_639_);
if (v_isZero_640_ == 1)
{
uint64_t v___x_641_; 
v___x_641_ = 1ULL;
return v___x_641_;
}
else
{
lean_object* v_one_642_; lean_object* v_n_643_; uint64_t v___x_644_; uint64_t v___x_645_; 
v_one_642_ = lean_unsigned_to_nat(1u);
v_n_643_ = lean_nat_sub(v_n_638_, v_one_642_);
v___x_644_ = l_UInt64_pow(v_x_637_, v_n_643_);
lean_dec(v_n_643_);
v___x_645_ = lean_uint64_mul(v___x_644_, v_x_637_);
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_pow___boxed(lean_object* v_x_646_, lean_object* v_n_647_){
_start:
{
uint64_t v_x_boxed_648_; uint64_t v_res_649_; lean_object* v_r_650_; 
v_x_boxed_648_ = lean_unbox_uint64(v_x_646_);
lean_dec_ref(v_x_646_);
v_res_649_ = l_UInt64_pow(v_x_boxed_648_, v_n_647_);
lean_dec(v_n_647_);
v_r_650_ = lean_box_uint64(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT lean_object* l_UInt64_mod___boxed(lean_object* v_a_653_, lean_object* v_b_654_){
_start:
{
uint64_t v_a_boxed_655_; uint64_t v_b_boxed_656_; uint64_t v_res_657_; lean_object* v_r_658_; 
v_a_boxed_655_ = lean_unbox_uint64(v_a_653_);
lean_dec_ref(v_a_653_);
v_b_boxed_656_ = lean_unbox_uint64(v_b_654_);
lean_dec_ref(v_b_654_);
v_res_657_ = lean_uint64_mod(v_a_boxed_655_, v_b_boxed_656_);
v_r_658_ = lean_box_uint64(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt64_modn_spec__0(lean_object* v_a_659_){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_unsigned_to_nat(64u);
v___x_661_ = l_BitVec_ofNat(v___x_660_, v_a_659_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt64_modn_spec__0___boxed(lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Nat_cast___at___00UInt64_modn_spec__0(v_a_662_);
lean_dec(v_a_662_);
return v_res_663_;
}
}
LEAN_EXPORT uint64_t l_UInt64_modn(uint64_t v_a_664_, lean_object* v_n_665_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint64_t v___x_669_; 
v___x_666_ = lean_uint64_to_nat(v_a_664_);
v___x_667_ = lean_nat_mod(v___x_666_, v_n_665_);
lean_dec(v___x_666_);
v___x_668_ = l_Nat_cast___at___00UInt64_modn_spec__0(v___x_667_);
lean_dec(v___x_667_);
v___x_669_ = lean_uint64_of_nat_mk(v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_UInt64_modn___boxed(lean_object* v_a_670_, lean_object* v_n_671_){
_start:
{
uint64_t v_a_boxed_672_; uint64_t v_res_673_; lean_object* v_r_674_; 
v_a_boxed_672_ = lean_unbox_uint64(v_a_670_);
lean_dec_ref(v_a_670_);
v_res_673_ = l_UInt64_modn(v_a_boxed_672_, v_n_671_);
lean_dec(v_n_671_);
v_r_674_ = lean_box_uint64(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT lean_object* l_UInt64_land___boxed(lean_object* v_a_677_, lean_object* v_b_678_){
_start:
{
uint64_t v_a_boxed_679_; uint64_t v_b_boxed_680_; uint64_t v_res_681_; lean_object* v_r_682_; 
v_a_boxed_679_ = lean_unbox_uint64(v_a_677_);
lean_dec_ref(v_a_677_);
v_b_boxed_680_ = lean_unbox_uint64(v_b_678_);
lean_dec_ref(v_b_678_);
v_res_681_ = lean_uint64_land(v_a_boxed_679_, v_b_boxed_680_);
v_r_682_ = lean_box_uint64(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT lean_object* l_UInt64_lor___boxed(lean_object* v_a_685_, lean_object* v_b_686_){
_start:
{
uint64_t v_a_boxed_687_; uint64_t v_b_boxed_688_; uint64_t v_res_689_; lean_object* v_r_690_; 
v_a_boxed_687_ = lean_unbox_uint64(v_a_685_);
lean_dec_ref(v_a_685_);
v_b_boxed_688_ = lean_unbox_uint64(v_b_686_);
lean_dec_ref(v_b_686_);
v_res_689_ = lean_uint64_lor(v_a_boxed_687_, v_b_boxed_688_);
v_r_690_ = lean_box_uint64(v_res_689_);
return v_r_690_;
}
}
LEAN_EXPORT lean_object* l_UInt64_xor___boxed(lean_object* v_a_693_, lean_object* v_b_694_){
_start:
{
uint64_t v_a_boxed_695_; uint64_t v_b_boxed_696_; uint64_t v_res_697_; lean_object* v_r_698_; 
v_a_boxed_695_ = lean_unbox_uint64(v_a_693_);
lean_dec_ref(v_a_693_);
v_b_boxed_696_ = lean_unbox_uint64(v_b_694_);
lean_dec_ref(v_b_694_);
v_res_697_ = lean_uint64_xor(v_a_boxed_695_, v_b_boxed_696_);
v_r_698_ = lean_box_uint64(v_res_697_);
return v_r_698_;
}
}
LEAN_EXPORT lean_object* l_UInt64_shiftLeft___boxed(lean_object* v_a_701_, lean_object* v_b_702_){
_start:
{
uint64_t v_a_boxed_703_; uint64_t v_b_boxed_704_; uint64_t v_res_705_; lean_object* v_r_706_; 
v_a_boxed_703_ = lean_unbox_uint64(v_a_701_);
lean_dec_ref(v_a_701_);
v_b_boxed_704_ = lean_unbox_uint64(v_b_702_);
lean_dec_ref(v_b_702_);
v_res_705_ = lean_uint64_shift_left(v_a_boxed_703_, v_b_boxed_704_);
v_r_706_ = lean_box_uint64(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT lean_object* l_UInt64_shiftRight___boxed(lean_object* v_a_709_, lean_object* v_b_710_){
_start:
{
uint64_t v_a_boxed_711_; uint64_t v_b_boxed_712_; uint64_t v_res_713_; lean_object* v_r_714_; 
v_a_boxed_711_ = lean_unbox_uint64(v_a_709_);
lean_dec_ref(v_a_709_);
v_b_boxed_712_ = lean_unbox_uint64(v_b_710_);
lean_dec_ref(v_b_710_);
v_res_713_ = lean_uint64_shift_right(v_a_boxed_711_, v_b_boxed_712_);
v_r_714_ = lean_box_uint64(v_res_713_);
return v_r_714_;
}
}
static lean_object* _init_l_instLTUInt64(void){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = lean_box(0);
return v___x_729_;
}
}
static lean_object* _init_l_instLEUInt64(void){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_box(0);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_UInt64_complement___boxed(lean_object* v_a_732_){
_start:
{
uint64_t v_a_boxed_733_; uint64_t v_res_734_; lean_object* v_r_735_; 
v_a_boxed_733_ = lean_unbox_uint64(v_a_732_);
lean_dec_ref(v_a_732_);
v_res_734_ = lean_uint64_complement(v_a_boxed_733_);
v_r_735_ = lean_box_uint64(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT lean_object* l_UInt64_neg___boxed(lean_object* v_a_737_){
_start:
{
uint64_t v_a_boxed_738_; uint64_t v_res_739_; lean_object* v_r_740_; 
v_a_boxed_738_ = lean_unbox_uint64(v_a_737_);
lean_dec_ref(v_a_737_);
v_res_739_ = lean_uint64_neg(v_a_boxed_738_);
v_r_740_ = lean_box_uint64(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT lean_object* l_Bool_toUInt64___boxed(lean_object* v_b_756_){
_start:
{
uint8_t v_b_boxed_757_; uint64_t v_res_758_; lean_object* v_r_759_; 
v_b_boxed_757_ = lean_unbox(v_b_756_);
v_res_758_ = lean_bool_to_uint64(v_b_boxed_757_);
v_r_759_ = lean_box_uint64(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT uint8_t l_UInt64_decLt___aux__1(uint64_t v_a_760_, uint64_t v_b_761_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_762_ = lean_uint64_to_nat(v_a_760_);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_add(v___x_762_, v___x_763_);
lean_dec(v___x_762_);
v___x_765_ = lean_uint64_to_nat(v_b_761_);
v___x_766_ = lean_nat_dec_le(v___x_764_, v___x_765_);
lean_dec(v___x_765_);
lean_dec(v___x_764_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_UInt64_decLt___aux__1___boxed(lean_object* v_a_767_, lean_object* v_b_768_){
_start:
{
uint64_t v_a_boxed_769_; uint64_t v_b_boxed_770_; uint8_t v_res_771_; lean_object* v_r_772_; 
v_a_boxed_769_ = lean_unbox_uint64(v_a_767_);
lean_dec_ref(v_a_767_);
v_b_boxed_770_ = lean_unbox_uint64(v_b_768_);
lean_dec_ref(v_b_768_);
v_res_771_ = l_UInt64_decLt___aux__1(v_a_boxed_769_, v_b_boxed_770_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT lean_object* l_UInt64_decLt___boxed(lean_object* v_a_775_, lean_object* v_b_776_){
_start:
{
uint64_t v_a_boxed_777_; uint64_t v_b_boxed_778_; uint8_t v_res_779_; lean_object* v_r_780_; 
v_a_boxed_777_ = lean_unbox_uint64(v_a_775_);
lean_dec_ref(v_a_775_);
v_b_boxed_778_ = lean_unbox_uint64(v_b_776_);
lean_dec_ref(v_b_776_);
v_res_779_ = lean_uint64_dec_lt(v_a_boxed_777_, v_b_boxed_778_);
v_r_780_ = lean_box(v_res_779_);
return v_r_780_;
}
}
LEAN_EXPORT uint8_t l_UInt64_decLe___aux__1(uint64_t v_a_781_, uint64_t v_b_782_){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_783_ = lean_uint64_to_nat(v_a_781_);
v___x_784_ = lean_uint64_to_nat(v_b_782_);
v___x_785_ = lean_nat_dec_le(v___x_783_, v___x_784_);
lean_dec(v___x_784_);
lean_dec(v___x_783_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_UInt64_decLe___aux__1___boxed(lean_object* v_a_786_, lean_object* v_b_787_){
_start:
{
uint64_t v_a_boxed_788_; uint64_t v_b_boxed_789_; uint8_t v_res_790_; lean_object* v_r_791_; 
v_a_boxed_788_ = lean_unbox_uint64(v_a_786_);
lean_dec_ref(v_a_786_);
v_b_boxed_789_ = lean_unbox_uint64(v_b_787_);
lean_dec_ref(v_b_787_);
v_res_790_ = l_UInt64_decLe___aux__1(v_a_boxed_788_, v_b_boxed_789_);
v_r_791_ = lean_box(v_res_790_);
return v_r_791_;
}
}
LEAN_EXPORT lean_object* l_UInt64_decLe___boxed(lean_object* v_a_794_, lean_object* v_b_795_){
_start:
{
uint64_t v_a_boxed_796_; uint64_t v_b_boxed_797_; uint8_t v_res_798_; lean_object* v_r_799_; 
v_a_boxed_796_ = lean_unbox_uint64(v_a_794_);
lean_dec_ref(v_a_794_);
v_b_boxed_797_ = lean_unbox_uint64(v_b_795_);
lean_dec_ref(v_b_795_);
v_res_798_ = lean_uint64_dec_le(v_a_boxed_796_, v_b_boxed_797_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT uint64_t l_instMaxUInt64___lam__0(uint64_t v_x_800_, uint64_t v_y_801_){
_start:
{
uint8_t v___x_802_; 
v___x_802_ = lean_uint64_dec_le(v_x_800_, v_y_801_);
if (v___x_802_ == 0)
{
return v_x_800_;
}
else
{
return v_y_801_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxUInt64___lam__0___boxed(lean_object* v_x_803_, lean_object* v_y_804_){
_start:
{
uint64_t v_x_boxed_805_; uint64_t v_y_boxed_806_; uint64_t v_res_807_; lean_object* v_r_808_; 
v_x_boxed_805_ = lean_unbox_uint64(v_x_803_);
lean_dec_ref(v_x_803_);
v_y_boxed_806_ = lean_unbox_uint64(v_y_804_);
lean_dec_ref(v_y_804_);
v_res_807_ = l_instMaxUInt64___lam__0(v_x_boxed_805_, v_y_boxed_806_);
v_r_808_ = lean_box_uint64(v_res_807_);
return v_r_808_;
}
}
LEAN_EXPORT uint64_t l_instMinUInt64___lam__0(uint64_t v_x_811_, uint64_t v_y_812_){
_start:
{
uint8_t v___x_813_; 
v___x_813_ = lean_uint64_dec_le(v_x_811_, v_y_812_);
if (v___x_813_ == 0)
{
return v_y_812_;
}
else
{
return v_x_811_;
}
}
}
LEAN_EXPORT lean_object* l_instMinUInt64___lam__0___boxed(lean_object* v_x_814_, lean_object* v_y_815_){
_start:
{
uint64_t v_x_boxed_816_; uint64_t v_y_boxed_817_; uint64_t v_res_818_; lean_object* v_r_819_; 
v_x_boxed_816_ = lean_unbox_uint64(v_x_814_);
lean_dec_ref(v_x_814_);
v_y_boxed_817_ = lean_unbox_uint64(v_y_815_);
lean_dec_ref(v_y_815_);
v_res_818_ = l_instMinUInt64___lam__0(v_x_boxed_816_, v_y_boxed_817_);
v_r_819_ = lean_box_uint64(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT size_t l_USize_ofFin(lean_object* v_a_822_){
_start:
{
size_t v___x_823_; 
v___x_823_ = lean_usize_of_nat_mk(v_a_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_USize_ofFin___boxed(lean_object* v_a_824_){
_start:
{
size_t v_res_825_; lean_object* v_r_826_; 
v_res_825_ = l_USize_ofFin(v_a_824_);
v_r_826_ = lean_box_usize(v_res_825_);
return v_r_826_;
}
}
static lean_object* _init_l_USize_ofInt___closed__0(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = l_System_Platform_numBits;
v___x_828_ = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
v___x_829_ = l_Int_pow(v___x_828_, v___x_827_);
return v___x_829_;
}
}
LEAN_EXPORT size_t l_USize_ofInt(lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; size_t v___x_834_; 
v___x_831_ = lean_obj_once(&l_USize_ofInt___closed__0, &l_USize_ofInt___closed__0_once, _init_l_USize_ofInt___closed__0);
v___x_832_ = lean_int_emod(v_x_830_, v___x_831_);
v___x_833_ = l_Int_toNat(v___x_832_);
lean_dec(v___x_832_);
v___x_834_ = lean_usize_of_nat(v___x_833_);
lean_dec(v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_USize_ofInt___boxed(lean_object* v_x_835_){
_start:
{
size_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_USize_ofInt(v_x_835_);
lean_dec(v_x_835_);
v_r_837_ = lean_box_usize(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT lean_object* l_USize_mul___boxed(lean_object* v_a_840_, lean_object* v_b_841_){
_start:
{
size_t v_a_boxed_842_; size_t v_b_boxed_843_; size_t v_res_844_; lean_object* v_r_845_; 
v_a_boxed_842_ = lean_unbox_usize(v_a_840_);
lean_dec(v_a_840_);
v_b_boxed_843_ = lean_unbox_usize(v_b_841_);
lean_dec(v_b_841_);
v_res_844_ = lean_usize_mul(v_a_boxed_842_, v_b_boxed_843_);
v_r_845_ = lean_box_usize(v_res_844_);
return v_r_845_;
}
}
LEAN_EXPORT lean_object* l_USize_div___boxed(lean_object* v_a_848_, lean_object* v_b_849_){
_start:
{
size_t v_a_boxed_850_; size_t v_b_boxed_851_; size_t v_res_852_; lean_object* v_r_853_; 
v_a_boxed_850_ = lean_unbox_usize(v_a_848_);
lean_dec(v_a_848_);
v_b_boxed_851_ = lean_unbox_usize(v_b_849_);
lean_dec(v_b_849_);
v_res_852_ = lean_usize_div(v_a_boxed_850_, v_b_boxed_851_);
v_r_853_ = lean_box_usize(v_res_852_);
return v_r_853_;
}
}
LEAN_EXPORT size_t l_USize_pow(size_t v_x_854_, lean_object* v_n_855_){
_start:
{
lean_object* v_zero_856_; uint8_t v_isZero_857_; 
v_zero_856_ = lean_unsigned_to_nat(0u);
v_isZero_857_ = lean_nat_dec_eq(v_n_855_, v_zero_856_);
if (v_isZero_857_ == 1)
{
size_t v___x_858_; 
v___x_858_ = ((size_t)1ULL);
return v___x_858_;
}
else
{
lean_object* v_one_859_; lean_object* v_n_860_; size_t v___x_861_; size_t v___x_862_; 
v_one_859_ = lean_unsigned_to_nat(1u);
v_n_860_ = lean_nat_sub(v_n_855_, v_one_859_);
v___x_861_ = l_USize_pow(v_x_854_, v_n_860_);
lean_dec(v_n_860_);
v___x_862_ = lean_usize_mul(v___x_861_, v_x_854_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_USize_pow___boxed(lean_object* v_x_863_, lean_object* v_n_864_){
_start:
{
size_t v_x_boxed_865_; size_t v_res_866_; lean_object* v_r_867_; 
v_x_boxed_865_ = lean_unbox_usize(v_x_863_);
lean_dec(v_x_863_);
v_res_866_ = l_USize_pow(v_x_boxed_865_, v_n_864_);
lean_dec(v_n_864_);
v_r_867_ = lean_box_usize(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT lean_object* l_USize_mod___boxed(lean_object* v_a_870_, lean_object* v_b_871_){
_start:
{
size_t v_a_boxed_872_; size_t v_b_boxed_873_; size_t v_res_874_; lean_object* v_r_875_; 
v_a_boxed_872_ = lean_unbox_usize(v_a_870_);
lean_dec(v_a_870_);
v_b_boxed_873_ = lean_unbox_usize(v_b_871_);
lean_dec(v_b_871_);
v_res_874_ = lean_usize_mod(v_a_boxed_872_, v_b_boxed_873_);
v_r_875_ = lean_box_usize(v_res_874_);
return v_r_875_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00USize_modn_spec__0(lean_object* v_a_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = l_System_Platform_numBits;
v___x_878_ = l_BitVec_ofNat(v___x_877_, v_a_876_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00USize_modn_spec__0___boxed(lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Nat_cast___at___00USize_modn_spec__0(v_a_879_);
lean_dec(v_a_879_);
return v_res_880_;
}
}
LEAN_EXPORT size_t l_USize_modn(size_t v_a_881_, lean_object* v_n_882_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; size_t v___x_886_; 
v___x_883_ = lean_usize_to_nat(v_a_881_);
v___x_884_ = lean_nat_mod(v___x_883_, v_n_882_);
lean_dec(v___x_883_);
v___x_885_ = l_Nat_cast___at___00USize_modn_spec__0(v___x_884_);
lean_dec(v___x_884_);
v___x_886_ = lean_usize_of_nat_mk(v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_USize_modn___boxed(lean_object* v_a_887_, lean_object* v_n_888_){
_start:
{
size_t v_a_boxed_889_; size_t v_res_890_; lean_object* v_r_891_; 
v_a_boxed_889_ = lean_unbox_usize(v_a_887_);
lean_dec(v_a_887_);
v_res_890_ = l_USize_modn(v_a_boxed_889_, v_n_888_);
lean_dec(v_n_888_);
v_r_891_ = lean_box_usize(v_res_890_);
return v_r_891_;
}
}
LEAN_EXPORT lean_object* l_USize_land___boxed(lean_object* v_a_894_, lean_object* v_b_895_){
_start:
{
size_t v_a_boxed_896_; size_t v_b_boxed_897_; size_t v_res_898_; lean_object* v_r_899_; 
v_a_boxed_896_ = lean_unbox_usize(v_a_894_);
lean_dec(v_a_894_);
v_b_boxed_897_ = lean_unbox_usize(v_b_895_);
lean_dec(v_b_895_);
v_res_898_ = lean_usize_land(v_a_boxed_896_, v_b_boxed_897_);
v_r_899_ = lean_box_usize(v_res_898_);
return v_r_899_;
}
}
LEAN_EXPORT lean_object* l_USize_lor___boxed(lean_object* v_a_902_, lean_object* v_b_903_){
_start:
{
size_t v_a_boxed_904_; size_t v_b_boxed_905_; size_t v_res_906_; lean_object* v_r_907_; 
v_a_boxed_904_ = lean_unbox_usize(v_a_902_);
lean_dec(v_a_902_);
v_b_boxed_905_ = lean_unbox_usize(v_b_903_);
lean_dec(v_b_903_);
v_res_906_ = lean_usize_lor(v_a_boxed_904_, v_b_boxed_905_);
v_r_907_ = lean_box_usize(v_res_906_);
return v_r_907_;
}
}
LEAN_EXPORT lean_object* l_USize_xor___boxed(lean_object* v_a_910_, lean_object* v_b_911_){
_start:
{
size_t v_a_boxed_912_; size_t v_b_boxed_913_; size_t v_res_914_; lean_object* v_r_915_; 
v_a_boxed_912_ = lean_unbox_usize(v_a_910_);
lean_dec(v_a_910_);
v_b_boxed_913_ = lean_unbox_usize(v_b_911_);
lean_dec(v_b_911_);
v_res_914_ = lean_usize_xor(v_a_boxed_912_, v_b_boxed_913_);
v_r_915_ = lean_box_usize(v_res_914_);
return v_r_915_;
}
}
LEAN_EXPORT lean_object* l_USize_shiftLeft___boxed(lean_object* v_a_918_, lean_object* v_b_919_){
_start:
{
size_t v_a_boxed_920_; size_t v_b_boxed_921_; size_t v_res_922_; lean_object* v_r_923_; 
v_a_boxed_920_ = lean_unbox_usize(v_a_918_);
lean_dec(v_a_918_);
v_b_boxed_921_ = lean_unbox_usize(v_b_919_);
lean_dec(v_b_919_);
v_res_922_ = lean_usize_shift_left(v_a_boxed_920_, v_b_boxed_921_);
v_r_923_ = lean_box_usize(v_res_922_);
return v_r_923_;
}
}
LEAN_EXPORT lean_object* l_USize_shiftRight___boxed(lean_object* v_a_926_, lean_object* v_b_927_){
_start:
{
size_t v_a_boxed_928_; size_t v_b_boxed_929_; size_t v_res_930_; lean_object* v_r_931_; 
v_a_boxed_928_ = lean_unbox_usize(v_a_926_);
lean_dec(v_a_926_);
v_b_boxed_929_ = lean_unbox_usize(v_b_927_);
lean_dec(v_b_927_);
v_res_930_ = lean_usize_shift_right(v_a_boxed_928_, v_b_boxed_929_);
v_r_931_ = lean_box_usize(v_res_930_);
return v_r_931_;
}
}
LEAN_EXPORT lean_object* l_USize_ofNat32___boxed(lean_object* v_n_934_, lean_object* v_h_935_){
_start:
{
size_t v_res_936_; lean_object* v_r_937_; 
v_res_936_ = lean_usize_of_nat(v_n_934_);
lean_dec(v_n_934_);
v_r_937_ = lean_box_usize(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUSize___boxed(lean_object* v_a_939_){
_start:
{
uint8_t v_a_boxed_940_; size_t v_res_941_; lean_object* v_r_942_; 
v_a_boxed_940_ = lean_unbox(v_a_939_);
v_res_941_ = lean_uint8_to_usize(v_a_boxed_940_);
v_r_942_ = lean_box_usize(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt8___boxed(lean_object* v_a_944_){
_start:
{
size_t v_a_boxed_945_; uint8_t v_res_946_; lean_object* v_r_947_; 
v_a_boxed_945_ = lean_unbox_usize(v_a_944_);
lean_dec(v_a_944_);
v_res_946_ = lean_usize_to_uint8(v_a_boxed_945_);
v_r_947_ = lean_box(v_res_946_);
return v_r_947_;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUSize___boxed(lean_object* v_a_949_){
_start:
{
uint16_t v_a_boxed_950_; size_t v_res_951_; lean_object* v_r_952_; 
v_a_boxed_950_ = lean_unbox(v_a_949_);
v_res_951_ = lean_uint16_to_usize(v_a_boxed_950_);
v_r_952_ = lean_box_usize(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt16___boxed(lean_object* v_a_954_){
_start:
{
size_t v_a_boxed_955_; uint16_t v_res_956_; lean_object* v_r_957_; 
v_a_boxed_955_ = lean_unbox_usize(v_a_954_);
lean_dec(v_a_954_);
v_res_956_ = lean_usize_to_uint16(v_a_boxed_955_);
v_r_957_ = lean_box(v_res_956_);
return v_r_957_;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUSize___boxed(lean_object* v_a_959_){
_start:
{
uint32_t v_a_boxed_960_; size_t v_res_961_; lean_object* v_r_962_; 
v_a_boxed_960_ = lean_unbox_uint32(v_a_959_);
lean_dec(v_a_959_);
v_res_961_ = lean_uint32_to_usize(v_a_boxed_960_);
v_r_962_ = lean_box_usize(v_res_961_);
return v_r_962_;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt32___boxed(lean_object* v_a_964_){
_start:
{
size_t v_a_boxed_965_; uint32_t v_res_966_; lean_object* v_r_967_; 
v_a_boxed_965_ = lean_unbox_usize(v_a_964_);
lean_dec(v_a_964_);
v_res_966_ = lean_usize_to_uint32(v_a_boxed_965_);
v_r_967_ = lean_box_uint32(v_res_966_);
return v_r_967_;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUSize___boxed(lean_object* v_a_969_){
_start:
{
uint64_t v_a_boxed_970_; size_t v_res_971_; lean_object* v_r_972_; 
v_a_boxed_970_ = lean_unbox_uint64(v_a_969_);
lean_dec_ref(v_a_969_);
v_res_971_ = lean_uint64_to_usize(v_a_boxed_970_);
v_r_972_ = lean_box_usize(v_res_971_);
return v_r_972_;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt64___boxed(lean_object* v_a_974_){
_start:
{
size_t v_a_boxed_975_; uint64_t v_res_976_; lean_object* v_r_977_; 
v_a_boxed_975_ = lean_unbox_usize(v_a_974_);
lean_dec(v_a_974_);
v_res_976_ = lean_usize_to_uint64(v_a_boxed_975_);
v_r_977_ = lean_box_uint64(v_res_976_);
return v_r_977_;
}
}
LEAN_EXPORT lean_object* l_USize_complement___boxed(lean_object* v_a_989_){
_start:
{
size_t v_a_boxed_990_; size_t v_res_991_; lean_object* v_r_992_; 
v_a_boxed_990_ = lean_unbox_usize(v_a_989_);
lean_dec(v_a_989_);
v_res_991_ = lean_usize_complement(v_a_boxed_990_);
v_r_992_ = lean_box_usize(v_res_991_);
return v_r_992_;
}
}
LEAN_EXPORT lean_object* l_USize_neg___boxed(lean_object* v_a_994_){
_start:
{
size_t v_a_boxed_995_; size_t v_res_996_; lean_object* v_r_997_; 
v_a_boxed_995_ = lean_unbox_usize(v_a_994_);
lean_dec(v_a_994_);
v_res_996_ = lean_usize_neg(v_a_boxed_995_);
v_r_997_ = lean_box_usize(v_res_996_);
return v_r_997_;
}
}
LEAN_EXPORT lean_object* l_Bool_toUSize___boxed(lean_object* v_b_1013_){
_start:
{
uint8_t v_b_boxed_1014_; size_t v_res_1015_; lean_object* v_r_1016_; 
v_b_boxed_1014_ = lean_unbox(v_b_1013_);
v_res_1015_ = lean_bool_to_usize(v_b_boxed_1014_);
v_r_1016_ = lean_box_usize(v_res_1015_);
return v_r_1016_;
}
}
LEAN_EXPORT size_t l_instMaxUSize___lam__0(size_t v_x_1017_, size_t v_y_1018_){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_usize_dec_le(v_x_1017_, v_y_1018_);
if (v___x_1019_ == 0)
{
return v_x_1017_;
}
else
{
return v_y_1018_;
}
}
}
LEAN_EXPORT lean_object* l_instMaxUSize___lam__0___boxed(lean_object* v_x_1020_, lean_object* v_y_1021_){
_start:
{
size_t v_x_boxed_1022_; size_t v_y_boxed_1023_; size_t v_res_1024_; lean_object* v_r_1025_; 
v_x_boxed_1022_ = lean_unbox_usize(v_x_1020_);
lean_dec(v_x_1020_);
v_y_boxed_1023_ = lean_unbox_usize(v_y_1021_);
lean_dec(v_y_1021_);
v_res_1024_ = l_instMaxUSize___lam__0(v_x_boxed_1022_, v_y_boxed_1023_);
v_r_1025_ = lean_box_usize(v_res_1024_);
return v_r_1025_;
}
}
LEAN_EXPORT size_t l_instMinUSize___lam__0(size_t v_x_1028_, size_t v_y_1029_){
_start:
{
uint8_t v___x_1030_; 
v___x_1030_ = lean_usize_dec_le(v_x_1028_, v_y_1029_);
if (v___x_1030_ == 0)
{
return v_y_1029_;
}
else
{
return v_x_1028_;
}
}
}
LEAN_EXPORT lean_object* l_instMinUSize___lam__0___boxed(lean_object* v_x_1031_, lean_object* v_y_1032_){
_start:
{
size_t v_x_boxed_1033_; size_t v_y_boxed_1034_; size_t v_res_1035_; lean_object* v_r_1036_; 
v_x_boxed_1033_ = lean_unbox_usize(v_x_1031_);
lean_dec(v_x_1031_);
v_y_boxed_1034_ = lean_unbox_usize(v_y_1032_);
lean_dec(v_y_1032_);
v_res_1035_ = l_instMinUSize___lam__0(v_x_boxed_1033_, v_y_boxed_1034_);
v_r_1036_ = lean_box_usize(v_res_1035_);
return v_r_1036_;
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
