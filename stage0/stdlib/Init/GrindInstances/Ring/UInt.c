// Lean compiler output
// Module: Init.GrindInstances.Ring.UInt
// Imports: import all Init.Data.UInt.Basic public import Init.Data.UInt.Lemmas public import Init.Grind.Ring.Basic import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.LemmasAux import Init.Data.Int.Order import Init.Data.Int.Pow
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
uint8_t l_UInt8_ofInt(lean_object*);
uint8_t lean_uint8_mul(uint8_t, uint8_t);
lean_object* l_UInt8_ofInt___boxed(lean_object*);
lean_object* l_UInt8_sub___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_neg___boxed(lean_object*);
lean_object* l_UInt8_pow___boxed(lean_object*, lean_object*);
lean_object* l_instHAdd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
lean_object* l_UInt8_instOfNat___boxed(lean_object*);
lean_object* l_UInt8_ofNat___boxed(lean_object*);
lean_object* l_UInt8_mul___boxed(lean_object*, lean_object*);
lean_object* l_UInt8_add___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_pow___boxed(lean_object*, lean_object*);
uint32_t l_UInt32_ofInt(lean_object*);
uint32_t lean_uint32_mul(uint32_t, uint32_t);
lean_object* l_UInt32_ofInt___boxed(lean_object*);
lean_object* l_UInt32_sub___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_neg___boxed(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_UInt32_instOfNat___boxed(lean_object*);
lean_object* l_UInt32_ofNat___boxed(lean_object*);
lean_object* l_UInt32_mul___boxed(lean_object*, lean_object*);
lean_object* l_UInt32_add___boxed(lean_object*, lean_object*);
uint64_t l_UInt64_ofInt(lean_object*);
uint64_t lean_uint64_mul(uint64_t, uint64_t);
lean_object* l_UInt64_ofInt___boxed(lean_object*);
lean_object* l_UInt64_sub___boxed(lean_object*, lean_object*);
lean_object* l_UInt64_neg___boxed(lean_object*);
lean_object* l_UInt64_pow___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_UInt64_instOfNat___boxed(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_UInt64_mul___boxed(lean_object*, lean_object*);
lean_object* l_UInt64_add___boxed(lean_object*, lean_object*);
lean_object* l_UInt16_ofNat___boxed(lean_object*);
lean_object* l_USize_ofInt___boxed(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
uint16_t lean_uint16_mul(uint16_t, uint16_t);
lean_object* l_USize_pow___boxed(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_USize_instOfNat___boxed(lean_object*);
lean_object* l_USize_ofNat___boxed(lean_object*);
lean_object* l_USize_mul___boxed(lean_object*, lean_object*);
lean_object* l_USize_add___boxed(lean_object*, lean_object*);
lean_object* l_UInt16_pow___boxed(lean_object*, lean_object*);
uint16_t l_UInt16_ofInt(lean_object*);
lean_object* l_UInt16_ofInt___boxed(lean_object*);
lean_object* l_UInt16_sub___boxed(lean_object*, lean_object*);
lean_object* l_UInt16_neg___boxed(lean_object*);
lean_object* l_UInt16_instOfNat___boxed(lean_object*);
lean_object* l_UInt16_mul___boxed(lean_object*, lean_object*);
lean_object* l_UInt16_add___boxed(lean_object*, lean_object*);
lean_object* l_USize_sub___boxed(lean_object*, lean_object*);
size_t l_USize_ofInt(lean_object*);
lean_object* l_USize_neg___boxed(lean_object*);
static const lean_closure_object l_UInt8_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt8_natCast___closed__0 = (const lean_object*)&l_UInt8_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt8_natCast = (const lean_object*)&l_UInt8_natCast___closed__0_value;
static const lean_closure_object l_UInt8_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt8_intCast___closed__0 = (const lean_object*)&l_UInt8_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt8_intCast = (const lean_object*)&l_UInt8_intCast___closed__0_value;
static const lean_closure_object l_UInt16_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt16_natCast___closed__0 = (const lean_object*)&l_UInt16_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt16_natCast = (const lean_object*)&l_UInt16_natCast___closed__0_value;
static const lean_closure_object l_UInt16_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt16_intCast___closed__0 = (const lean_object*)&l_UInt16_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt16_intCast = (const lean_object*)&l_UInt16_intCast___closed__0_value;
static const lean_closure_object l_UInt32_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt32_natCast___closed__0 = (const lean_object*)&l_UInt32_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt32_natCast = (const lean_object*)&l_UInt32_natCast___closed__0_value;
static const lean_closure_object l_UInt32_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt32_intCast___closed__0 = (const lean_object*)&l_UInt32_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt32_intCast = (const lean_object*)&l_UInt32_intCast___closed__0_value;
static const lean_closure_object l_UInt64_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt64_natCast___closed__0 = (const lean_object*)&l_UInt64_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt64_natCast = (const lean_object*)&l_UInt64_natCast___closed__0_value;
static const lean_closure_object l_UInt64_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt64_intCast___closed__0 = (const lean_object*)&l_UInt64_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt64_intCast = (const lean_object*)&l_UInt64_intCast___closed__0_value;
static const lean_closure_object l_USize_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_USize_natCast___closed__0 = (const lean_object*)&l_USize_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_USize_natCast = (const lean_object*)&l_USize_natCast___closed__0_value;
static const lean_closure_object l_USize_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_USize_intCast___closed__0 = (const lean_object*)&l_USize_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_USize_intCast = (const lean_object*)&l_USize_intCast___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Grind_instCommRingUInt8___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt8___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_instCommRingUInt8___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt8___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingUInt8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt8___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingUInt8___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt8___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__1_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt8___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__2_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt8___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__3_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt8___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingUInt8___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__5_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt8___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__6_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt8___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__7_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt8___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingUInt8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__3_value),((lean_object*)&l_UInt8_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingUInt8___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingUInt8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__7_value),((lean_object*)&l_UInt8_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingUInt8___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingUInt8 = (const lean_object*)&l_Lean_Grind_instCommRingUInt8___closed__10_value;
LEAN_EXPORT uint16_t l_Lean_Grind_instCommRingUInt16___lam__0(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt16___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Grind_instCommRingUInt16___lam__1(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt16___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingUInt16___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt16___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingUInt16___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt16___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__1_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt16___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__2_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt16___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt16___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__3_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt16___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt16___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt16___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingUInt16___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__5_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt16___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt16___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__6_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt16___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt16___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__7_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt16___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt16___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingUInt16___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__3_value),((lean_object*)&l_UInt16_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingUInt16___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingUInt16___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__7_value),((lean_object*)&l_UInt16_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingUInt16___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingUInt16 = (const lean_object*)&l_Lean_Grind_instCommRingUInt16___closed__10_value;
LEAN_EXPORT uint32_t l_Lean_Grind_instCommRingUInt32___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt32___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Grind_instCommRingUInt32___lam__1(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt32___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingUInt32___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt32___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt32___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingUInt32___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt32___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__1_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt32___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt32___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__2_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt32___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt32___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__3_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt32___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt32___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt32___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingUInt32___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__5_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt32___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt32___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__6_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt32___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt32___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__7_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt32___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt32___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingUInt32___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__3_value),((lean_object*)&l_UInt32_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingUInt32___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingUInt32___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__7_value),((lean_object*)&l_UInt32_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingUInt32___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingUInt32 = (const lean_object*)&l_Lean_Grind_instCommRingUInt32___closed__10_value;
LEAN_EXPORT uint64_t l_Lean_Grind_instCommRingUInt64___lam__0(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt64___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Grind_instCommRingUInt64___lam__1(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt64___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingUInt64___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt64___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt64___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingUInt64___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt64___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__1_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt64___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt64___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__2_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt64___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt64___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__3_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt64___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt64___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt64___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingUInt64___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__5_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt64___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt64___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__6_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt64___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt64___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__7_value;
static const lean_closure_object l_Lean_Grind_instCommRingUInt64___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUInt64___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingUInt64___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__3_value),((lean_object*)&l_UInt64_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingUInt64___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingUInt64___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__7_value),((lean_object*)&l_UInt64_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingUInt64___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingUInt64 = (const lean_object*)&l_Lean_Grind_instCommRingUInt64___closed__10_value;
LEAN_EXPORT size_t l_Lean_Grind_instCommRingUSize___lam__0(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUSize___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_Grind_instCommRingUSize___lam__1(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUSize___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingUSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUSize___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingUSize___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingUSize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingUSize___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUSize___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingUSize___closed__1_value;
static const lean_closure_object l_Lean_Grind_instCommRingUSize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUSize___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingUSize___closed__2_value;
static const lean_closure_object l_Lean_Grind_instCommRingUSize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUSize___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingUSize___closed__3_value;
static const lean_closure_object l_Lean_Grind_instCommRingUSize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUSize___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingUSize___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingUSize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUSize___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingUSize___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingUSize___closed__5_value;
static const lean_closure_object l_Lean_Grind_instCommRingUSize___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUSize___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingUSize___closed__6_value;
static const lean_closure_object l_Lean_Grind_instCommRingUSize___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUSize___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingUSize___closed__7_value;
static const lean_closure_object l_Lean_Grind_instCommRingUSize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingUSize___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingUSize___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingUSize___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUSize___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingUSize___closed__3_value),((lean_object*)&l_USize_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUSize___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingUSize___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUSize___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingUSize___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingUSize___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingUSize___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingUSize___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingUSize___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingUSize___closed__7_value),((lean_object*)&l_USize_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingUSize___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingUSize___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingUSize___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingUSize = (const lean_object*)&l_Lean_Grind_instCommRingUSize___closed__10_value;
uint8_t l_Lean_Grind_instCommRingUInt8___lam__0(lean_object* v_x1_21_, uint8_t v_x2_22_){
_start:
{
uint8_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = lean_uint8_of_nat(v_x1_21_);
v___x_24_ = lean_uint8_mul(v___x_23_, v_x2_22_);
return v___x_24_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingUInt8___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_21_ = stack[0].m_obj;
uint8_t v_x2_22_ = stack[1].m_num;
uint8_t v_res_25_;
v_res_25_ = l_Lean_Grind_instCommRingUInt8___lam__0(v_x1_21_, v_x2_22_);
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt8___lam__0___boxed(lean_object* v_x1_26_, lean_object* v_x2_27_){
_start:
{
uint8_t v_x2_64__boxed_28_; uint8_t v_res_29_; lean_object* v_r_30_; 
v_x2_64__boxed_28_ = lean_unbox(v_x2_27_);
v_res_29_ = l_Lean_Grind_instCommRingUInt8___lam__0(v_x1_26_, v_x2_64__boxed_28_);
lean_dec(v_x1_26_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
uint8_t l_Lean_Grind_instCommRingUInt8___lam__1(lean_object* v_x1_31_, uint8_t v_x2_32_){
_start:
{
uint8_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = l_UInt8_ofInt(v_x1_31_);
v___x_34_ = lean_uint8_mul(v___x_33_, v_x2_32_);
return v___x_34_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingUInt8___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_31_ = stack[0].m_obj;
uint8_t v_x2_32_ = stack[1].m_num;
uint8_t v_res_35_;
v_res_35_ = l_Lean_Grind_instCommRingUInt8___lam__1(v_x1_31_, v_x2_32_);
stack->m_num = v_res_35_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt8___lam__1___boxed(lean_object* v_x1_36_, lean_object* v_x2_37_){
_start:
{
uint8_t v_x2_80__boxed_38_; uint8_t v_res_39_; lean_object* v_r_40_; 
v_x2_80__boxed_38_ = lean_unbox(v_x2_37_);
v_res_39_ = l_Lean_Grind_instCommRingUInt8___lam__1(v_x1_36_, v_x2_80__boxed_38_);
lean_dec(v_x1_36_);
v_r_40_ = lean_box(v_res_39_);
return v_r_40_;
}
}
uint16_t l_Lean_Grind_instCommRingUInt16___lam__0(lean_object* v_x1_65_, uint16_t v_x2_66_){
_start:
{
uint16_t v___x_67_; uint16_t v___x_68_; 
v___x_67_ = lean_uint16_of_nat(v_x1_65_);
v___x_68_ = lean_uint16_mul(v___x_67_, v_x2_66_);
return v___x_68_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingUInt16___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_65_ = stack[0].m_obj;
uint16_t v_x2_66_ = stack[1].m_num;
uint16_t v_res_69_;
v_res_69_ = l_Lean_Grind_instCommRingUInt16___lam__0(v_x1_65_, v_x2_66_);
stack->m_num = v_res_69_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt16___lam__0___boxed(lean_object* v_x1_70_, lean_object* v_x2_71_){
_start:
{
uint16_t v_x2_64__boxed_72_; uint16_t v_res_73_; lean_object* v_r_74_; 
v_x2_64__boxed_72_ = lean_unbox(v_x2_71_);
v_res_73_ = l_Lean_Grind_instCommRingUInt16___lam__0(v_x1_70_, v_x2_64__boxed_72_);
lean_dec(v_x1_70_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
uint16_t l_Lean_Grind_instCommRingUInt16___lam__1(lean_object* v_x1_75_, uint16_t v_x2_76_){
_start:
{
uint16_t v___x_77_; uint16_t v___x_78_; 
v___x_77_ = l_UInt16_ofInt(v_x1_75_);
v___x_78_ = lean_uint16_mul(v___x_77_, v_x2_76_);
return v___x_78_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingUInt16___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_75_ = stack[0].m_obj;
uint16_t v_x2_76_ = stack[1].m_num;
uint16_t v_res_79_;
v_res_79_ = l_Lean_Grind_instCommRingUInt16___lam__1(v_x1_75_, v_x2_76_);
stack->m_num = v_res_79_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt16___lam__1___boxed(lean_object* v_x1_80_, lean_object* v_x2_81_){
_start:
{
uint16_t v_x2_80__boxed_82_; uint16_t v_res_83_; lean_object* v_r_84_; 
v_x2_80__boxed_82_ = lean_unbox(v_x2_81_);
v_res_83_ = l_Lean_Grind_instCommRingUInt16___lam__1(v_x1_80_, v_x2_80__boxed_82_);
lean_dec(v_x1_80_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
uint32_t l_Lean_Grind_instCommRingUInt32___lam__0(lean_object* v_x1_109_, uint32_t v_x2_110_){
_start:
{
uint32_t v___x_111_; uint32_t v___x_112_; 
v___x_111_ = lean_uint32_of_nat(v_x1_109_);
v___x_112_ = lean_uint32_mul(v___x_111_, v_x2_110_);
return v___x_112_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingUInt32___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_109_ = stack[0].m_obj;
uint32_t v_x2_110_ = stack[1].m_num;
uint32_t v_res_113_;
v_res_113_ = l_Lean_Grind_instCommRingUInt32___lam__0(v_x1_109_, v_x2_110_);
stack->m_num = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt32___lam__0___boxed(lean_object* v_x1_114_, lean_object* v_x2_115_){
_start:
{
uint32_t v_x2_64__boxed_116_; uint32_t v_res_117_; lean_object* v_r_118_; 
v_x2_64__boxed_116_ = lean_unbox_uint32(v_x2_115_);
lean_dec(v_x2_115_);
v_res_117_ = l_Lean_Grind_instCommRingUInt32___lam__0(v_x1_114_, v_x2_64__boxed_116_);
lean_dec(v_x1_114_);
v_r_118_ = lean_box_uint32(v_res_117_);
return v_r_118_;
}
}
uint32_t l_Lean_Grind_instCommRingUInt32___lam__1(lean_object* v_x1_119_, uint32_t v_x2_120_){
_start:
{
uint32_t v___x_121_; uint32_t v___x_122_; 
v___x_121_ = l_UInt32_ofInt(v_x1_119_);
v___x_122_ = lean_uint32_mul(v___x_121_, v_x2_120_);
return v___x_122_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingUInt32___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_119_ = stack[0].m_obj;
uint32_t v_x2_120_ = stack[1].m_num;
uint32_t v_res_123_;
v_res_123_ = l_Lean_Grind_instCommRingUInt32___lam__1(v_x1_119_, v_x2_120_);
stack->m_num = v_res_123_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt32___lam__1___boxed(lean_object* v_x1_124_, lean_object* v_x2_125_){
_start:
{
uint32_t v_x2_80__boxed_126_; uint32_t v_res_127_; lean_object* v_r_128_; 
v_x2_80__boxed_126_ = lean_unbox_uint32(v_x2_125_);
lean_dec(v_x2_125_);
v_res_127_ = l_Lean_Grind_instCommRingUInt32___lam__1(v_x1_124_, v_x2_80__boxed_126_);
lean_dec(v_x1_124_);
v_r_128_ = lean_box_uint32(v_res_127_);
return v_r_128_;
}
}
uint64_t l_Lean_Grind_instCommRingUInt64___lam__0(lean_object* v_x1_153_, uint64_t v_x2_154_){
_start:
{
uint64_t v___x_155_; uint64_t v___x_156_; 
v___x_155_ = lean_uint64_of_nat(v_x1_153_);
v___x_156_ = lean_uint64_mul(v___x_155_, v_x2_154_);
return v___x_156_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingUInt64___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_153_ = stack[0].m_obj;
uint64_t v_x2_154_ = stack[1].m_num;
uint64_t v_res_157_;
v_res_157_ = l_Lean_Grind_instCommRingUInt64___lam__0(v_x1_153_, v_x2_154_);
stack->m_num = v_res_157_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt64___lam__0___boxed(lean_object* v_x1_158_, lean_object* v_x2_159_){
_start:
{
uint64_t v_x2_64__boxed_160_; uint64_t v_res_161_; lean_object* v_r_162_; 
v_x2_64__boxed_160_ = lean_unbox_uint64(v_x2_159_);
lean_dec_ref(v_x2_159_);
v_res_161_ = l_Lean_Grind_instCommRingUInt64___lam__0(v_x1_158_, v_x2_64__boxed_160_);
lean_dec(v_x1_158_);
v_r_162_ = lean_box_uint64(v_res_161_);
return v_r_162_;
}
}
uint64_t l_Lean_Grind_instCommRingUInt64___lam__1(lean_object* v_x1_163_, uint64_t v_x2_164_){
_start:
{
uint64_t v___x_165_; uint64_t v___x_166_; 
v___x_165_ = l_UInt64_ofInt(v_x1_163_);
v___x_166_ = lean_uint64_mul(v___x_165_, v_x2_164_);
return v___x_166_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingUInt64___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_163_ = stack[0].m_obj;
uint64_t v_x2_164_ = stack[1].m_num;
uint64_t v_res_167_;
v_res_167_ = l_Lean_Grind_instCommRingUInt64___lam__1(v_x1_163_, v_x2_164_);
stack->m_num = v_res_167_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt64___lam__1___boxed(lean_object* v_x1_168_, lean_object* v_x2_169_){
_start:
{
uint64_t v_x2_80__boxed_170_; uint64_t v_res_171_; lean_object* v_r_172_; 
v_x2_80__boxed_170_ = lean_unbox_uint64(v_x2_169_);
lean_dec_ref(v_x2_169_);
v_res_171_ = l_Lean_Grind_instCommRingUInt64___lam__1(v_x1_168_, v_x2_80__boxed_170_);
lean_dec(v_x1_168_);
v_r_172_ = lean_box_uint64(v_res_171_);
return v_r_172_;
}
}
size_t l_Lean_Grind_instCommRingUSize___lam__0(lean_object* v_x1_197_, size_t v_x2_198_){
_start:
{
size_t v___x_199_; size_t v___x_200_; 
v___x_199_ = lean_usize_of_nat(v_x1_197_);
v___x_200_ = lean_usize_mul(v___x_199_, v_x2_198_);
return v___x_200_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingUSize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_197_ = stack[0].m_obj;
size_t v_x2_198_ = stack[1].m_num;
size_t v_res_201_;
v_res_201_ = l_Lean_Grind_instCommRingUSize___lam__0(v_x1_197_, v_x2_198_);
stack->m_num = v_res_201_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUSize___lam__0___boxed(lean_object* v_x1_202_, lean_object* v_x2_203_){
_start:
{
size_t v_x2_64__boxed_204_; size_t v_res_205_; lean_object* v_r_206_; 
v_x2_64__boxed_204_ = lean_unbox_usize(v_x2_203_);
lean_dec(v_x2_203_);
v_res_205_ = l_Lean_Grind_instCommRingUSize___lam__0(v_x1_202_, v_x2_64__boxed_204_);
lean_dec(v_x1_202_);
v_r_206_ = lean_box_usize(v_res_205_);
return v_r_206_;
}
}
size_t l_Lean_Grind_instCommRingUSize___lam__1(lean_object* v_x1_207_, size_t v_x2_208_){
_start:
{
size_t v___x_209_; size_t v___x_210_; 
v___x_209_ = l_USize_ofInt(v_x1_207_);
v___x_210_ = lean_usize_mul(v___x_209_, v_x2_208_);
return v___x_210_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingUSize___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_207_ = stack[0].m_obj;
size_t v_x2_208_ = stack[1].m_num;
size_t v_res_211_;
v_res_211_ = l_Lean_Grind_instCommRingUSize___lam__1(v_x1_207_, v_x2_208_);
stack->m_num = v_res_211_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUSize___lam__1___boxed(lean_object* v_x1_212_, lean_object* v_x2_213_){
_start:
{
size_t v_x2_80__boxed_214_; size_t v_res_215_; lean_object* v_r_216_; 
v_x2_80__boxed_214_ = lean_unbox_usize(v_x2_213_);
lean_dec(v_x2_213_);
v_res_215_ = l_Lean_Grind_instCommRingUSize___lam__1(v_x1_212_, v_x2_80__boxed_214_);
lean_dec(v_x1_212_);
v_r_216_ = lean_box_usize(v_res_215_);
return v_r_216_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_GrindInstances_Ring_UInt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_GrindInstances_Ring_UInt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_Ring_UInt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances_Ring_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_GrindInstances_Ring_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_GrindInstances_Ring_UInt(builtin);
}
#ifdef __cplusplus
}
#endif
