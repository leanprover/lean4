// Lean compiler output
// Module: Init.GrindInstances.Ring.UInt
// Imports: public import Init.GrindInstances.ToInt import all Init.GrindInstances.ToInt import all Init.Data.UInt.Basic public import Init.Data.UInt.Lemmas public import Init.Grind.Ring.Basic import Init.Grind.Ring.ToInt
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
LEAN_EXPORT uint8_t l_Lean_Grind_instCommRingUInt8___lam__0(lean_object* v_x1_21_, uint8_t v_x2_22_){
_start:
{
uint8_t v___x_23_; uint8_t v___x_24_; 
v___x_23_ = lean_uint8_of_nat(v_x1_21_);
v___x_24_ = lean_uint8_mul(v___x_23_, v_x2_22_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt8___lam__0___boxed(lean_object* v_x1_25_, lean_object* v_x2_26_){
_start:
{
uint8_t v_x2_64__boxed_27_; uint8_t v_res_28_; lean_object* v_r_29_; 
v_x2_64__boxed_27_ = lean_unbox(v_x2_26_);
v_res_28_ = l_Lean_Grind_instCommRingUInt8___lam__0(v_x1_25_, v_x2_64__boxed_27_);
lean_dec(v_x1_25_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_instCommRingUInt8___lam__1(lean_object* v_x1_30_, uint8_t v_x2_31_){
_start:
{
uint8_t v___x_32_; uint8_t v___x_33_; 
v___x_32_ = l_UInt8_ofInt(v_x1_30_);
v___x_33_ = lean_uint8_mul(v___x_32_, v_x2_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt8___lam__1___boxed(lean_object* v_x1_34_, lean_object* v_x2_35_){
_start:
{
uint8_t v_x2_74__boxed_36_; uint8_t v_res_37_; lean_object* v_r_38_; 
v_x2_74__boxed_36_ = lean_unbox(v_x2_35_);
v_res_37_ = l_Lean_Grind_instCommRingUInt8___lam__1(v_x1_34_, v_x2_74__boxed_36_);
lean_dec(v_x1_34_);
v_r_38_ = lean_box(v_res_37_);
return v_r_38_;
}
}
LEAN_EXPORT uint16_t l_Lean_Grind_instCommRingUInt16___lam__0(lean_object* v_x1_63_, uint16_t v_x2_64_){
_start:
{
uint16_t v___x_65_; uint16_t v___x_66_; 
v___x_65_ = lean_uint16_of_nat(v_x1_63_);
v___x_66_ = lean_uint16_mul(v___x_65_, v_x2_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt16___lam__0___boxed(lean_object* v_x1_67_, lean_object* v_x2_68_){
_start:
{
uint16_t v_x2_64__boxed_69_; uint16_t v_res_70_; lean_object* v_r_71_; 
v_x2_64__boxed_69_ = lean_unbox(v_x2_68_);
v_res_70_ = l_Lean_Grind_instCommRingUInt16___lam__0(v_x1_67_, v_x2_64__boxed_69_);
lean_dec(v_x1_67_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint16_t l_Lean_Grind_instCommRingUInt16___lam__1(lean_object* v_x1_72_, uint16_t v_x2_73_){
_start:
{
uint16_t v___x_74_; uint16_t v___x_75_; 
v___x_74_ = l_UInt16_ofInt(v_x1_72_);
v___x_75_ = lean_uint16_mul(v___x_74_, v_x2_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt16___lam__1___boxed(lean_object* v_x1_76_, lean_object* v_x2_77_){
_start:
{
uint16_t v_x2_74__boxed_78_; uint16_t v_res_79_; lean_object* v_r_80_; 
v_x2_74__boxed_78_ = lean_unbox(v_x2_77_);
v_res_79_ = l_Lean_Grind_instCommRingUInt16___lam__1(v_x1_76_, v_x2_74__boxed_78_);
lean_dec(v_x1_76_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT uint32_t l_Lean_Grind_instCommRingUInt32___lam__0(lean_object* v_x1_105_, uint32_t v_x2_106_){
_start:
{
uint32_t v___x_107_; uint32_t v___x_108_; 
v___x_107_ = lean_uint32_of_nat(v_x1_105_);
v___x_108_ = lean_uint32_mul(v___x_107_, v_x2_106_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt32___lam__0___boxed(lean_object* v_x1_109_, lean_object* v_x2_110_){
_start:
{
uint32_t v_x2_64__boxed_111_; uint32_t v_res_112_; lean_object* v_r_113_; 
v_x2_64__boxed_111_ = lean_unbox_uint32(v_x2_110_);
lean_dec(v_x2_110_);
v_res_112_ = l_Lean_Grind_instCommRingUInt32___lam__0(v_x1_109_, v_x2_64__boxed_111_);
lean_dec(v_x1_109_);
v_r_113_ = lean_box_uint32(v_res_112_);
return v_r_113_;
}
}
LEAN_EXPORT uint32_t l_Lean_Grind_instCommRingUInt32___lam__1(lean_object* v_x1_114_, uint32_t v_x2_115_){
_start:
{
uint32_t v___x_116_; uint32_t v___x_117_; 
v___x_116_ = l_UInt32_ofInt(v_x1_114_);
v___x_117_ = lean_uint32_mul(v___x_116_, v_x2_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt32___lam__1___boxed(lean_object* v_x1_118_, lean_object* v_x2_119_){
_start:
{
uint32_t v_x2_74__boxed_120_; uint32_t v_res_121_; lean_object* v_r_122_; 
v_x2_74__boxed_120_ = lean_unbox_uint32(v_x2_119_);
lean_dec(v_x2_119_);
v_res_121_ = l_Lean_Grind_instCommRingUInt32___lam__1(v_x1_118_, v_x2_74__boxed_120_);
lean_dec(v_x1_118_);
v_r_122_ = lean_box_uint32(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_instCommRingUInt64___lam__0(lean_object* v_x1_147_, uint64_t v_x2_148_){
_start:
{
uint64_t v___x_149_; uint64_t v___x_150_; 
v___x_149_ = lean_uint64_of_nat(v_x1_147_);
v___x_150_ = lean_uint64_mul(v___x_149_, v_x2_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt64___lam__0___boxed(lean_object* v_x1_151_, lean_object* v_x2_152_){
_start:
{
uint64_t v_x2_64__boxed_153_; uint64_t v_res_154_; lean_object* v_r_155_; 
v_x2_64__boxed_153_ = lean_unbox_uint64(v_x2_152_);
lean_dec_ref(v_x2_152_);
v_res_154_ = l_Lean_Grind_instCommRingUInt64___lam__0(v_x1_151_, v_x2_64__boxed_153_);
lean_dec(v_x1_151_);
v_r_155_ = lean_box_uint64(v_res_154_);
return v_r_155_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_instCommRingUInt64___lam__1(lean_object* v_x1_156_, uint64_t v_x2_157_){
_start:
{
uint64_t v___x_158_; uint64_t v___x_159_; 
v___x_158_ = l_UInt64_ofInt(v_x1_156_);
v___x_159_ = lean_uint64_mul(v___x_158_, v_x2_157_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUInt64___lam__1___boxed(lean_object* v_x1_160_, lean_object* v_x2_161_){
_start:
{
uint64_t v_x2_74__boxed_162_; uint64_t v_res_163_; lean_object* v_r_164_; 
v_x2_74__boxed_162_ = lean_unbox_uint64(v_x2_161_);
lean_dec_ref(v_x2_161_);
v_res_163_ = l_Lean_Grind_instCommRingUInt64___lam__1(v_x1_160_, v_x2_74__boxed_162_);
lean_dec(v_x1_160_);
v_r_164_ = lean_box_uint64(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT size_t l_Lean_Grind_instCommRingUSize___lam__0(lean_object* v_x1_189_, size_t v_x2_190_){
_start:
{
size_t v___x_191_; size_t v___x_192_; 
v___x_191_ = lean_usize_of_nat(v_x1_189_);
v___x_192_ = lean_usize_mul(v___x_191_, v_x2_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUSize___lam__0___boxed(lean_object* v_x1_193_, lean_object* v_x2_194_){
_start:
{
size_t v_x2_64__boxed_195_; size_t v_res_196_; lean_object* v_r_197_; 
v_x2_64__boxed_195_ = lean_unbox_usize(v_x2_194_);
lean_dec(v_x2_194_);
v_res_196_ = l_Lean_Grind_instCommRingUSize___lam__0(v_x1_193_, v_x2_64__boxed_195_);
lean_dec(v_x1_193_);
v_r_197_ = lean_box_usize(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT size_t l_Lean_Grind_instCommRingUSize___lam__1(lean_object* v_x1_198_, size_t v_x2_199_){
_start:
{
size_t v___x_200_; size_t v___x_201_; 
v___x_200_ = l_USize_ofInt(v_x1_198_);
v___x_201_ = lean_usize_mul(v___x_200_, v_x2_199_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingUSize___lam__1___boxed(lean_object* v_x1_202_, lean_object* v_x2_203_){
_start:
{
size_t v_x2_74__boxed_204_; size_t v_res_205_; lean_object* v_r_206_; 
v_x2_74__boxed_204_ = lean_unbox_usize(v_x2_203_);
lean_dec(v_x2_203_);
v_res_205_ = l_Lean_Grind_instCommRingUSize___lam__1(v_x1_202_, v_x2_74__boxed_204_);
lean_dec(v_x1_202_);
v_r_206_ = lean_box_usize(v_res_205_);
return v_r_206_;
}
}
lean_object* runtime_initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_ToInt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_GrindInstances_Ring_UInt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_ToInt(builtin);
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
lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_ToInt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_Ring_UInt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_ToInt(builtin);
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
