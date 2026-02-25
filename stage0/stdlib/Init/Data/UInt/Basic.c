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
uint8_t lean_uint8_of_nat_mk(lean_object*);
LEAN_EXPORT uint8_t l_UInt8_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_ofFin___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_UInt8_ofInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt8_ofInt___closed__0;
lean_object* l_Int_pow(lean_object*, lean_object*);
static lean_once_cell_t l_UInt8_ofInt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt8_ofInt___closed__1;
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_UInt8_pow(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_UInt8_pow___boxed(lean_object*, lean_object*);
uint8_t lean_uint8_mod(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_mod___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt8_modn_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt8_modn_spec__0___boxed(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_nat_mod(lean_object*, lean_object*);
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
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
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
uint16_t lean_uint16_of_nat_mk(lean_object*);
LEAN_EXPORT uint16_t l_UInt16_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_ofFin___boxed(lean_object*);
static lean_once_cell_t l_UInt16_ofInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt16_ofInt___closed__0;
uint16_t lean_uint16_of_nat(lean_object*);
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
lean_object* lean_uint16_to_nat(uint16_t);
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
uint32_t lean_uint32_of_nat_mk(lean_object*);
LEAN_EXPORT uint32_t l_UInt32_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_UInt32_ofFin___boxed(lean_object*);
static lean_once_cell_t l_UInt32_ofInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt32_ofInt___closed__0;
uint32_t lean_uint32_of_nat(lean_object*);
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
lean_object* lean_uint32_to_nat(uint32_t);
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
uint64_t lean_uint64_of_nat_mk(lean_object*);
LEAN_EXPORT uint64_t l_UInt64_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_UInt64_ofFin___boxed(lean_object*);
static lean_once_cell_t l_UInt64_ofInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt64_ofInt___closed__0;
uint64_t lean_uint64_of_nat(lean_object*);
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
lean_object* lean_uint64_to_nat(uint64_t);
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
size_t lean_usize_of_nat_mk(lean_object*);
LEAN_EXPORT size_t l_USize_ofFin(lean_object*);
LEAN_EXPORT lean_object* l_USize_ofFin___boxed(lean_object*);
extern lean_object* l_System_Platform_numBits;
static lean_once_cell_t l_USize_ofInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_USize_ofInt___closed__0;
size_t lean_usize_of_nat(lean_object*);
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
lean_object* lean_usize_to_nat(size_t);
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
uint8_t lean_usize_dec_le(size_t, size_t);
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
LEAN_EXPORT uint8_t l_UInt8_ofFin(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_uint8_of_nat_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_UInt8_ofFin___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_UInt8_ofFin(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_UInt8_ofInt___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_UInt8_ofInt___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
x_3 = l_Int_pow(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_UInt8_ofInt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_obj_once(&l_UInt8_ofInt___closed__1, &l_UInt8_ofInt___closed__1_once, _init_l_UInt8_ofInt___closed__1);
x_3 = lean_int_emod(x_1, x_2);
x_4 = l_Int_toNat(x_3);
lean_dec(x_3);
x_5 = lean_uint8_of_nat(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt8_ofInt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_UInt8_ofInt(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt8_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint8_add(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint8_sub(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint8_mul(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint8_div(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_UInt8_pow(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = l_UInt8_pow(x_1, x_7);
lean_dec(x_7);
x_9 = lean_uint8_mul(x_8, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_UInt8_pow(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt8_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint8_mod(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt8_modn_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(8u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt8_modn_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_cast___at___00UInt8_modn_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_UInt8_modn(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_uint8_to_nat(x_1);
x_4 = lean_nat_mod(x_3, x_2);
lean_dec(x_3);
x_5 = l_Nat_cast___at___00UInt8_modn_spec__0(x_4);
lean_dec(x_4);
x_6 = lean_uint8_of_nat_mk(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_UInt8_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt8_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint8_land(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint8_lor(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint8_xor(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint8_shift_left(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint8_shift_right(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt8_complement___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_uint8_complement(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt8_neg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_uint8_neg(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Bool_toUInt8___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_bool_to_uint8(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_instMaxUInt8___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint8_dec_le(x_1, x_2);
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
LEAN_EXPORT lean_object* l_instMaxUInt8___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_instMaxUInt8___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_instMinUInt8___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint8_dec_le(x_1, x_2);
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
LEAN_EXPORT lean_object* l_instMinUInt8___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_instMinUInt8___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_UInt8_toAsciiLower(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_6; uint8_t x_7; 
x_6 = 65;
x_7 = lean_uint8_dec_le(x_6, x_1);
if (x_7 == 0)
{
x_2 = x_7;
goto block_5;
}
else
{
uint8_t x_8; uint8_t x_9; 
x_8 = 90;
x_9 = lean_uint8_dec_le(x_1, x_8);
x_2 = x_9;
goto block_5;
}
block_5:
{
if (x_2 == 0)
{
return x_1;
}
else
{
uint8_t x_3; uint8_t x_4; 
x_3 = 32;
x_4 = lean_uint8_add(x_1, x_3);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_UInt8_toAsciiLower___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_UInt8_toAsciiLower(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint16_t l_UInt16_ofFin(lean_object* x_1) {
_start:
{
uint16_t x_2; 
x_2 = lean_uint16_of_nat_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofFin___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = l_UInt16_ofFin(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_UInt16_ofInt___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(16u);
x_2 = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
x_3 = l_Int_pow(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint16_t l_UInt16_ofInt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint16_t x_5; 
x_2 = lean_obj_once(&l_UInt16_ofInt___closed__0, &l_UInt16_ofInt___closed__0_once, _init_l_UInt16_ofInt___closed__0);
x_3 = lean_int_emod(x_1, x_2);
x_4 = l_Int_toNat(x_3);
lean_dec(x_3);
x_5 = lean_uint16_of_nat(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt16_ofInt___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = l_UInt16_ofInt(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt16_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint16_add(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint16_sub(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint16_mul(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint16_div(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint16_t l_UInt16_pow(uint16_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
uint16_t x_5; 
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint16_t x_8; uint16_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = l_UInt16_pow(x_1, x_7);
lean_dec(x_7);
x_9 = lean_uint16_mul(x_8, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_UInt16_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_UInt16_pow(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt16_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint16_mod(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt16_modn_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(16u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt16_modn_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_cast___at___00UInt16_modn_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint16_t l_UInt16_modn(uint16_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint16_t x_6; 
x_3 = lean_uint16_to_nat(x_1);
x_4 = lean_nat_mod(x_3, x_2);
lean_dec(x_3);
x_5 = l_Nat_cast___at___00UInt16_modn_spec__0(x_4);
lean_dec(x_4);
x_6 = lean_uint16_of_nat_mk(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_UInt16_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt16_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint16_land(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint16_lor(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint16_xor(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint16_shift_left(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint16_shift_right(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_instLTUInt16(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instLEUInt16(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt16_complement___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_uint16_complement(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt16_neg___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_uint16_neg(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Bool_toUInt16___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_bool_to_uint16(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt16_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint16_dec_lt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt16_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lean_uint16_dec_le(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint16_t l_instMaxUInt16___lam__0(uint16_t x_1, uint16_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint16_dec_le(x_1, x_2);
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
LEAN_EXPORT lean_object* l_instMaxUInt16___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_instMaxUInt16___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint16_t l_instMinUInt16___lam__0(uint16_t x_1, uint16_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint16_dec_le(x_1, x_2);
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
LEAN_EXPORT lean_object* l_instMinUInt16___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; uint16_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_instMinUInt16___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofFin(lean_object* x_1) {
_start:
{
uint32_t x_2; 
x_2 = lean_uint32_of_nat_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofFin___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_UInt32_ofFin(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
static lean_object* _init_l_UInt32_ofInt___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
x_3 = l_Int_pow(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint32_t l_UInt32_ofInt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint32_t x_5; 
x_2 = lean_obj_once(&l_UInt32_ofInt___closed__0, &l_UInt32_ofInt___closed__0_once, _init_l_UInt32_ofInt___closed__0);
x_3 = lean_int_emod(x_1, x_2);
x_4 = l_Int_toNat(x_3);
lean_dec(x_3);
x_5 = lean_uint32_of_nat(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt32_ofInt___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_UInt32_ofInt(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt32_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_uint32_mul(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_uint32_div(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT uint32_t l_UInt32_pow(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
uint32_t x_5; 
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint32_t x_8; uint32_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = l_UInt32_pow(x_1, x_7);
lean_dec(x_7);
x_9 = lean_uint32_mul(x_8, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_UInt32_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_UInt32_pow(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt32_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_uint32_mod(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt32_modn_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(32u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt32_modn_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_cast___at___00UInt32_modn_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint32_t l_UInt32_modn(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; 
x_3 = lean_uint32_to_nat(x_1);
x_4 = lean_nat_mod(x_3, x_2);
lean_dec(x_3);
x_5 = l_Nat_cast___at___00UInt32_modn_spec__0(x_4);
lean_dec(x_4);
x_6 = lean_uint32_of_nat_mk(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_UInt32_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt32_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_uint32_land(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_uint32_lor(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_uint32_xor(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_uint32_shift_left(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = lean_uint32_shift_right(x_3, x_4);
x_6 = lean_box_uint32(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt32_complement___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = lean_uint32_complement(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt32_neg___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = lean_uint32_neg(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Bool_toUInt32___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_bool_to_uint32(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofFin(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_uint64_of_nat_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofFin___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_UInt64_ofFin(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_UInt64_ofInt___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
x_3 = l_Int_pow(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint64_t l_UInt64_ofInt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; 
x_2 = lean_obj_once(&l_UInt64_ofInt___closed__0, &l_UInt64_ofInt___closed__0_once, _init_l_UInt64_ofInt___closed__0);
x_3 = lean_int_emod(x_1, x_2);
x_4 = l_Int_toNat(x_3);
lean_dec(x_3);
x_5 = lean_uint64_of_nat(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt64_ofInt___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_UInt64_ofInt(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt64_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = lean_uint64_add(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = lean_uint64_sub(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = lean_uint64_mul(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = lean_uint64_div(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT uint64_t l_UInt64_pow(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
uint64_t x_5; 
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = l_UInt64_pow(x_1, x_7);
lean_dec(x_7);
x_9 = lean_uint64_mul(x_8, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = l_UInt64_pow(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt64_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = lean_uint64_mod(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt64_modn_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(64u);
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00UInt64_modn_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_cast___at___00UInt64_modn_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint64_t l_UInt64_modn(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; 
x_3 = lean_uint64_to_nat(x_1);
x_4 = lean_nat_mod(x_3, x_2);
lean_dec(x_3);
x_5 = l_Nat_cast___at___00UInt64_modn_spec__0(x_4);
lean_dec(x_4);
x_6 = lean_uint64_of_nat_mk(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = l_UInt64_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt64_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = lean_uint64_land(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = lean_uint64_lor(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = lean_uint64_xor(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = lean_uint64_shift_left(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = lean_uint64_shift_right(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
static lean_object* _init_l_instLTUInt64(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_instLEUInt64(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt64_complement___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_3 = lean_uint64_complement(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt64_neg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_3 = lean_uint64_neg(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Bool_toUInt64___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_bool_to_uint64(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt64_decLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = lean_uint64_dec_lt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_UInt64_decLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = lean_uint64_dec_le(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint64_t l_instMaxUInt64___lam__0(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_le(x_1, x_2);
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
LEAN_EXPORT lean_object* l_instMaxUInt64___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_instMaxUInt64___lam__0(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT uint64_t l_instMinUInt64___lam__0(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_le(x_1, x_2);
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
LEAN_EXPORT lean_object* l_instMinUInt64___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_instMinUInt64___lam__0(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT size_t l_USize_ofFin(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_usize_of_nat_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_USize_ofFin___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_USize_ofFin(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
static lean_object* _init_l_USize_ofInt___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_Platform_numBits;
x_2 = lean_obj_once(&l_UInt8_ofInt___closed__0, &l_UInt8_ofInt___closed__0_once, _init_l_UInt8_ofInt___closed__0);
x_3 = l_Int_pow(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT size_t l_USize_ofInt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; size_t x_5; 
x_2 = lean_obj_once(&l_USize_ofInt___closed__0, &l_USize_ofInt___closed__0_once, _init_l_USize_ofInt___closed__0);
x_3 = lean_int_emod(x_1, x_2);
x_4 = l_Int_toNat(x_3);
lean_dec(x_3);
x_5 = lean_usize_of_nat(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_USize_ofInt___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_USize_ofInt(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_USize_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_usize_mul(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_div___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_usize_div(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT size_t l_USize_pow(size_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 1)
{
size_t x_5; 
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = l_USize_pow(x_1, x_7);
lean_dec(x_7);
x_9 = lean_usize_mul(x_8, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_USize_pow___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_USize_pow(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_usize(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_USize_mod___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_usize_mod(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00USize_modn_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_System_Platform_numBits;
x_3 = l_BitVec_ofNat(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00USize_modn_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Nat_cast___at___00USize_modn_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT size_t l_USize_modn(size_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; 
x_3 = lean_usize_to_nat(x_1);
x_4 = lean_nat_mod(x_3, x_2);
lean_dec(x_3);
x_5 = l_Nat_cast___at___00USize_modn_spec__0(x_4);
lean_dec(x_4);
x_6 = lean_usize_of_nat_mk(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_modn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_USize_modn(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box_usize(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_USize_land___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_usize_land(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_lor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_usize_lor(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_usize_xor(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_shiftLeft___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_usize_shift_left(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_shiftRight___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_usize_shift_right(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_USize_ofNat32___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_usize_of_nat(x_1);
lean_dec(x_1);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt8_toUSize___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_uint8_to_usize(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt8___boxed(lean_object* x_1) {
_start:
{
size_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_usize_to_uint8(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt16_toUSize___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_uint16_to_usize(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt16___boxed(lean_object* x_1) {
_start:
{
size_t x_2; uint16_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_usize_to_uint16(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt32_toUSize___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = lean_uint32_to_usize(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt32___boxed(lean_object* x_1) {
_start:
{
size_t x_2; uint32_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_usize_to_uint32(x_2);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt64_toUSize___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_3 = lean_uint64_to_usize(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_USize_toUInt64___boxed(lean_object* x_1) {
_start:
{
size_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_usize_to_uint64(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_USize_complement___boxed(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_usize_complement(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_USize_neg___boxed(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = lean_usize_neg(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Bool_toUSize___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; size_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lean_bool_to_usize(x_2);
x_4 = lean_box_usize(x_3);
return x_4;
}
}
LEAN_EXPORT size_t l_instMaxUSize___lam__0(size_t x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_usize_dec_le(x_1, x_2);
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
LEAN_EXPORT lean_object* l_instMaxUSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_instMaxUSize___lam__0(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT size_t l_instMinUSize___lam__0(size_t x_1, size_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_usize_dec_le(x_1, x_2);
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
LEAN_EXPORT lean_object* l_instMinUSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_instMinUSize___lam__0(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
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
#ifdef __cplusplus
}
#endif
