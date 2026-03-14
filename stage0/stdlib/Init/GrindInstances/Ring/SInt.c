// Lean compiler output
// Module: Init.GrindInstances.Ring.SInt
// Imports: import all Init.Grind.ToInt public import Init.GrindInstances.ToInt import all Init.Data.BitVec.Basic import all Init.Data.SInt.Basic public import Init.Data.SInt.Lemmas public import Init.Grind.Ring.Basic import Init.Data.Int.Pow import Init.Data.Nat.Dvd import Init.Grind.Ring.ToInt
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
lean_object* l_ISize_pow___boxed(lean_object*, lean_object*);
lean_object* l_instHAdd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
size_t lean_isize_of_int(lean_object*);
size_t lean_isize_mul(size_t, size_t);
lean_object* l_ISize_ofInt___boxed(lean_object*);
lean_object* l_ISize_sub___boxed(lean_object*, lean_object*);
lean_object* l_ISize_neg___boxed(lean_object*);
size_t lean_isize_of_nat(lean_object*);
lean_object* l_ISize_instOfNat___boxed(lean_object*);
lean_object* l_ISize_ofNat___boxed(lean_object*);
lean_object* l_ISize_mul___boxed(lean_object*, lean_object*);
lean_object* l_ISize_add___boxed(lean_object*, lean_object*);
lean_object* l_Int16_ofNat___boxed(lean_object*);
lean_object* l_Int32_pow___boxed(lean_object*, lean_object*);
uint32_t lean_int32_of_nat(lean_object*);
uint32_t lean_int32_mul(uint32_t, uint32_t);
lean_object* l_Int32_instOfNat___boxed(lean_object*);
lean_object* l_Int32_ofNat___boxed(lean_object*);
lean_object* l_Int32_mul___boxed(lean_object*, lean_object*);
lean_object* l_Int32_add___boxed(lean_object*, lean_object*);
lean_object* l_Int16_sub___boxed(lean_object*, lean_object*);
uint16_t lean_int16_of_nat(lean_object*);
uint16_t lean_int16_mul(uint16_t, uint16_t);
uint16_t lean_int16_of_int(lean_object*);
lean_object* l_Int16_ofInt___boxed(lean_object*);
lean_object* l_Int16_neg___boxed(lean_object*);
lean_object* l_Int16_pow___boxed(lean_object*, lean_object*);
lean_object* l_Int16_instOfNat___boxed(lean_object*);
lean_object* l_Int16_mul___boxed(lean_object*, lean_object*);
lean_object* l_Int16_add___boxed(lean_object*, lean_object*);
lean_object* l_Int64_neg___boxed(lean_object*);
uint8_t lean_int8_of_int(lean_object*);
uint8_t lean_int8_mul(uint8_t, uint8_t);
lean_object* l_Int64_pow___boxed(lean_object*, lean_object*);
lean_object* l_Int8_instOfNat___boxed(lean_object*);
lean_object* l_Int64_ofInt___boxed(lean_object*);
lean_object* l_Int64_instOfNat___boxed(lean_object*);
lean_object* l_Int32_sub___boxed(lean_object*, lean_object*);
lean_object* l_Int8_ofInt___boxed(lean_object*);
lean_object* l_Int32_ofInt___boxed(lean_object*);
lean_object* l_Int8_add___boxed(lean_object*, lean_object*);
uint32_t lean_int32_of_int(lean_object*);
lean_object* l_Int32_neg___boxed(lean_object*);
uint8_t lean_int8_of_nat(lean_object*);
lean_object* l_Int8_pow___boxed(lean_object*, lean_object*);
lean_object* l_Int8_ofNat___boxed(lean_object*);
lean_object* l_Int8_mul___boxed(lean_object*, lean_object*);
lean_object* l_Int8_neg___boxed(lean_object*);
uint64_t lean_int64_of_int(lean_object*);
uint64_t lean_int64_mul(uint64_t, uint64_t);
lean_object* l_Int64_sub___boxed(lean_object*, lean_object*);
uint64_t lean_int64_of_nat(lean_object*);
lean_object* l_Int64_ofNat___boxed(lean_object*);
lean_object* l_Int64_mul___boxed(lean_object*, lean_object*);
lean_object* l_Int64_add___boxed(lean_object*, lean_object*);
lean_object* l_Int8_sub___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_Int8_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int8_natCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int8_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int8_natCast = (const lean_object*)&l_Lean_Grind_Int8_natCast___closed__0_value;
static const lean_closure_object l_Lean_Grind_Int8_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int8_intCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int8_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int8_intCast = (const lean_object*)&l_Lean_Grind_Int8_intCast___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Grind_instCommRingInt8___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt8___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_instCommRingInt8___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt8___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt8___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__1_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__2_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__3_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__5_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__6_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__7_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__3_value),((lean_object*)&l_Lean_Grind_Int8_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__7_value),((lean_object*)&l_Lean_Grind_Int8_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingInt8 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__10_value;
static const lean_closure_object l_Lean_Grind_Int16_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int16_natCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int16_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int16_natCast = (const lean_object*)&l_Lean_Grind_Int16_natCast___closed__0_value;
static const lean_closure_object l_Lean_Grind_Int16_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int16_intCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int16_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int16_intCast = (const lean_object*)&l_Lean_Grind_Int16_intCast___closed__0_value;
LEAN_EXPORT uint16_t l_Lean_Grind_instCommRingInt16___lam__0(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt16___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint16_t l_Lean_Grind_instCommRingInt16___lam__1(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt16___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt16___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt16___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__1_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__2_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__3_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__5_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__6_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__7_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt16___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__3_value),((lean_object*)&l_Lean_Grind_Int16_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt16___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__7_value),((lean_object*)&l_Lean_Grind_Int16_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingInt16 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__10_value;
static const lean_closure_object l_Lean_Grind_Int32_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int32_natCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int32_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int32_natCast = (const lean_object*)&l_Lean_Grind_Int32_natCast___closed__0_value;
static const lean_closure_object l_Lean_Grind_Int32_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int32_intCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int32_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int32_intCast = (const lean_object*)&l_Lean_Grind_Int32_intCast___closed__0_value;
LEAN_EXPORT uint32_t l_Lean_Grind_instCommRingInt32___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt32___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Grind_instCommRingInt32___lam__1(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt32___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt32___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt32___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__1_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__2_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__3_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__5_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__6_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__7_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt32___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__3_value),((lean_object*)&l_Lean_Grind_Int32_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt32___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__7_value),((lean_object*)&l_Lean_Grind_Int32_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingInt32 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__10_value;
static const lean_closure_object l_Lean_Grind_Int64_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int64_natCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int64_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int64_natCast = (const lean_object*)&l_Lean_Grind_Int64_natCast___closed__0_value;
static const lean_closure_object l_Lean_Grind_Int64_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int64_intCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int64_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int64_intCast = (const lean_object*)&l_Lean_Grind_Int64_intCast___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Grind_instCommRingInt64___lam__0(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt64___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Grind_instCommRingInt64___lam__1(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt64___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt64___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt64___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__1_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__2_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__3_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__5_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__6_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__7_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt64___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__3_value),((lean_object*)&l_Lean_Grind_Int64_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt64___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__7_value),((lean_object*)&l_Lean_Grind_Int64_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingInt64 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__10_value;
static const lean_closure_object l_Lean_Grind_ISize_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_ISize_natCast___closed__0 = (const lean_object*)&l_Lean_Grind_ISize_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_ISize_natCast = (const lean_object*)&l_Lean_Grind_ISize_natCast___closed__0_value;
static const lean_closure_object l_Lean_Grind_ISize_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_ISize_intCast___closed__0 = (const lean_object*)&l_Lean_Grind_ISize_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_ISize_intCast = (const lean_object*)&l_Lean_Grind_ISize_intCast___closed__0_value;
LEAN_EXPORT size_t l_Lean_Grind_instCommRingISize___lam__0(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingISize___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_Grind_instCommRingISize___lam__1(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingISize___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingISize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingISize___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__1_value;
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__2_value;
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__3_value;
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingISize___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__5_value;
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__6_value;
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__7_value;
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingISize___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingISize___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingISize___closed__3_value),((lean_object*)&l_Lean_Grind_ISize_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingISize___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingISize___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingISize___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingISize___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingISize___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingISize___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingISize___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingISize___closed__7_value),((lean_object*)&l_Lean_Grind_ISize_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingISize___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingISize___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingISize = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__10_value;
LEAN_EXPORT uint8_t l_Lean_Grind_instCommRingInt8___lam__0(lean_object* v_x1_5_, uint8_t v_x2_6_){
_start:
{
uint8_t v___x_7_; uint8_t v___x_8_; 
v___x_7_ = lean_int8_of_nat(v_x1_5_);
v___x_8_ = lean_int8_mul(v___x_7_, v_x2_6_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt8___lam__0___boxed(lean_object* v_x1_9_, lean_object* v_x2_10_){
_start:
{
uint8_t v_x2_64__boxed_11_; uint8_t v_res_12_; lean_object* v_r_13_; 
v_x2_64__boxed_11_ = lean_unbox(v_x2_10_);
v_res_12_ = l_Lean_Grind_instCommRingInt8___lam__0(v_x1_9_, v_x2_64__boxed_11_);
lean_dec(v_x1_9_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_instCommRingInt8___lam__1(lean_object* v_x1_14_, uint8_t v_x2_15_){
_start:
{
uint8_t v___x_16_; uint8_t v___x_17_; 
v___x_16_ = lean_int8_of_int(v_x1_14_);
v___x_17_ = lean_int8_mul(v___x_16_, v_x2_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt8___lam__1___boxed(lean_object* v_x1_18_, lean_object* v_x2_19_){
_start:
{
uint8_t v_x2_74__boxed_20_; uint8_t v_res_21_; lean_object* v_r_22_; 
v_x2_74__boxed_20_ = lean_unbox(v_x2_19_);
v_res_21_ = l_Lean_Grind_instCommRingInt8___lam__1(v_x1_18_, v_x2_74__boxed_20_);
lean_dec(v_x1_18_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT uint16_t l_Lean_Grind_instCommRingInt16___lam__0(lean_object* v_x1_51_, uint16_t v_x2_52_){
_start:
{
uint16_t v___x_53_; uint16_t v___x_54_; 
v___x_53_ = lean_int16_of_nat(v_x1_51_);
v___x_54_ = lean_int16_mul(v___x_53_, v_x2_52_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt16___lam__0___boxed(lean_object* v_x1_55_, lean_object* v_x2_56_){
_start:
{
uint16_t v_x2_64__boxed_57_; uint16_t v_res_58_; lean_object* v_r_59_; 
v_x2_64__boxed_57_ = lean_unbox(v_x2_56_);
v_res_58_ = l_Lean_Grind_instCommRingInt16___lam__0(v_x1_55_, v_x2_64__boxed_57_);
lean_dec(v_x1_55_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint16_t l_Lean_Grind_instCommRingInt16___lam__1(lean_object* v_x1_60_, uint16_t v_x2_61_){
_start:
{
uint16_t v___x_62_; uint16_t v___x_63_; 
v___x_62_ = lean_int16_of_int(v_x1_60_);
v___x_63_ = lean_int16_mul(v___x_62_, v_x2_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt16___lam__1___boxed(lean_object* v_x1_64_, lean_object* v_x2_65_){
_start:
{
uint16_t v_x2_74__boxed_66_; uint16_t v_res_67_; lean_object* v_r_68_; 
v_x2_74__boxed_66_ = lean_unbox(v_x2_65_);
v_res_67_ = l_Lean_Grind_instCommRingInt16___lam__1(v_x1_64_, v_x2_74__boxed_66_);
lean_dec(v_x1_64_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
LEAN_EXPORT uint32_t l_Lean_Grind_instCommRingInt32___lam__0(lean_object* v_x1_97_, uint32_t v_x2_98_){
_start:
{
uint32_t v___x_99_; uint32_t v___x_100_; 
v___x_99_ = lean_int32_of_nat(v_x1_97_);
v___x_100_ = lean_int32_mul(v___x_99_, v_x2_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt32___lam__0___boxed(lean_object* v_x1_101_, lean_object* v_x2_102_){
_start:
{
uint32_t v_x2_64__boxed_103_; uint32_t v_res_104_; lean_object* v_r_105_; 
v_x2_64__boxed_103_ = lean_unbox_uint32(v_x2_102_);
lean_dec(v_x2_102_);
v_res_104_ = l_Lean_Grind_instCommRingInt32___lam__0(v_x1_101_, v_x2_64__boxed_103_);
lean_dec(v_x1_101_);
v_r_105_ = lean_box_uint32(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT uint32_t l_Lean_Grind_instCommRingInt32___lam__1(lean_object* v_x1_106_, uint32_t v_x2_107_){
_start:
{
uint32_t v___x_108_; uint32_t v___x_109_; 
v___x_108_ = lean_int32_of_int(v_x1_106_);
v___x_109_ = lean_int32_mul(v___x_108_, v_x2_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt32___lam__1___boxed(lean_object* v_x1_110_, lean_object* v_x2_111_){
_start:
{
uint32_t v_x2_74__boxed_112_; uint32_t v_res_113_; lean_object* v_r_114_; 
v_x2_74__boxed_112_ = lean_unbox_uint32(v_x2_111_);
lean_dec(v_x2_111_);
v_res_113_ = l_Lean_Grind_instCommRingInt32___lam__1(v_x1_110_, v_x2_74__boxed_112_);
lean_dec(v_x1_110_);
v_r_114_ = lean_box_uint32(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_instCommRingInt64___lam__0(lean_object* v_x1_143_, uint64_t v_x2_144_){
_start:
{
uint64_t v___x_145_; uint64_t v___x_146_; 
v___x_145_ = lean_int64_of_nat(v_x1_143_);
v___x_146_ = lean_int64_mul(v___x_145_, v_x2_144_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt64___lam__0___boxed(lean_object* v_x1_147_, lean_object* v_x2_148_){
_start:
{
uint64_t v_x2_64__boxed_149_; uint64_t v_res_150_; lean_object* v_r_151_; 
v_x2_64__boxed_149_ = lean_unbox_uint64(v_x2_148_);
lean_dec_ref(v_x2_148_);
v_res_150_ = l_Lean_Grind_instCommRingInt64___lam__0(v_x1_147_, v_x2_64__boxed_149_);
lean_dec(v_x1_147_);
v_r_151_ = lean_box_uint64(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_instCommRingInt64___lam__1(lean_object* v_x1_152_, uint64_t v_x2_153_){
_start:
{
uint64_t v___x_154_; uint64_t v___x_155_; 
v___x_154_ = lean_int64_of_int(v_x1_152_);
v___x_155_ = lean_int64_mul(v___x_154_, v_x2_153_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt64___lam__1___boxed(lean_object* v_x1_156_, lean_object* v_x2_157_){
_start:
{
uint64_t v_x2_74__boxed_158_; uint64_t v_res_159_; lean_object* v_r_160_; 
v_x2_74__boxed_158_ = lean_unbox_uint64(v_x2_157_);
lean_dec_ref(v_x2_157_);
v_res_159_ = l_Lean_Grind_instCommRingInt64___lam__1(v_x1_156_, v_x2_74__boxed_158_);
lean_dec(v_x1_156_);
v_r_160_ = lean_box_uint64(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT size_t l_Lean_Grind_instCommRingISize___lam__0(lean_object* v_x1_189_, size_t v_x2_190_){
_start:
{
size_t v___x_191_; size_t v___x_192_; 
v___x_191_ = lean_isize_of_nat(v_x1_189_);
v___x_192_ = lean_isize_mul(v___x_191_, v_x2_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingISize___lam__0___boxed(lean_object* v_x1_193_, lean_object* v_x2_194_){
_start:
{
size_t v_x2_64__boxed_195_; size_t v_res_196_; lean_object* v_r_197_; 
v_x2_64__boxed_195_ = lean_unbox_usize(v_x2_194_);
lean_dec(v_x2_194_);
v_res_196_ = l_Lean_Grind_instCommRingISize___lam__0(v_x1_193_, v_x2_64__boxed_195_);
lean_dec(v_x1_193_);
v_r_197_ = lean_box_usize(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT size_t l_Lean_Grind_instCommRingISize___lam__1(lean_object* v_x1_198_, size_t v_x2_199_){
_start:
{
size_t v___x_200_; size_t v___x_201_; 
v___x_200_ = lean_isize_of_int(v_x1_198_);
v___x_201_ = lean_isize_mul(v___x_200_, v_x2_199_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingISize___lam__1___boxed(lean_object* v_x1_202_, lean_object* v_x2_203_){
_start:
{
size_t v_x2_74__boxed_204_; size_t v_res_205_; lean_object* v_r_206_; 
v_x2_74__boxed_204_ = lean_unbox_usize(v_x2_203_);
lean_dec(v_x2_203_);
v_res_205_ = l_Lean_Grind_instCommRingISize___lam__1(v_x1_202_, v_x2_74__boxed_204_);
lean_dec(v_x1_202_);
v_r_206_ = lean_box_usize(v_res_205_);
return v_r_206_;
}
}
lean_object* runtime_initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_ToInt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_GrindInstances_Ring_SInt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_GrindInstances_Ring_SInt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* initialize_Init_GrindInstances_ToInt(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_ToInt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_Ring_SInt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GrindInstances_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GrindInstances_Ring_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_GrindInstances_Ring_SInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_GrindInstances_Ring_SInt(builtin);
}
#ifdef __cplusplus
}
#endif
