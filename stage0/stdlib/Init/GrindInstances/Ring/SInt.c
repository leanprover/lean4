// Lean compiler output
// Module: Init.GrindInstances.Ring.SInt
// Imports: import all Init.Data.BitVec.Basic import all Init.Data.SInt.Basic public import Init.Data.SInt.Lemmas public import Init.Grind.Ring.Basic import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.Pow import Init.Data.Nat.Dvd
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
uint8_t l_Lean_Grind_instCommRingInt8___lam__0(lean_object* v_x1_5_, uint8_t v_x2_6_){
_start:
{
uint8_t v___x_7_; uint8_t v___x_8_; 
v___x_7_ = lean_int8_of_nat(v_x1_5_);
v___x_8_ = lean_int8_mul(v___x_7_, v_x2_6_);
return v___x_8_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingInt8___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_5_ = stack[0].m_obj;
uint8_t v_x2_6_ = stack[1].m_num;
uint8_t v_res_9_;
v_res_9_ = l_Lean_Grind_instCommRingInt8___lam__0(v_x1_5_, v_x2_6_);
stack->m_num = v_res_9_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt8___lam__0___boxed(lean_object* v_x1_10_, lean_object* v_x2_11_){
_start:
{
uint8_t v_x2_64__boxed_12_; uint8_t v_res_13_; lean_object* v_r_14_; 
v_x2_64__boxed_12_ = lean_unbox(v_x2_11_);
v_res_13_ = l_Lean_Grind_instCommRingInt8___lam__0(v_x1_10_, v_x2_64__boxed_12_);
lean_dec(v_x1_10_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
uint8_t l_Lean_Grind_instCommRingInt8___lam__1(lean_object* v_x1_15_, uint8_t v_x2_16_){
_start:
{
uint8_t v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_int8_of_int(v_x1_15_);
v___x_18_ = lean_int8_mul(v___x_17_, v_x2_16_);
return v___x_18_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingInt8___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_15_ = stack[0].m_obj;
uint8_t v_x2_16_ = stack[1].m_num;
uint8_t v_res_19_;
v_res_19_ = l_Lean_Grind_instCommRingInt8___lam__1(v_x1_15_, v_x2_16_);
stack->m_num = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt8___lam__1___boxed(lean_object* v_x1_20_, lean_object* v_x2_21_){
_start:
{
uint8_t v_x2_80__boxed_22_; uint8_t v_res_23_; lean_object* v_r_24_; 
v_x2_80__boxed_22_ = lean_unbox(v_x2_21_);
v_res_23_ = l_Lean_Grind_instCommRingInt8___lam__1(v_x1_20_, v_x2_80__boxed_22_);
lean_dec(v_x1_20_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
uint16_t l_Lean_Grind_instCommRingInt16___lam__0(lean_object* v_x1_53_, uint16_t v_x2_54_){
_start:
{
uint16_t v___x_55_; uint16_t v___x_56_; 
v___x_55_ = lean_int16_of_nat(v_x1_53_);
v___x_56_ = lean_int16_mul(v___x_55_, v_x2_54_);
return v___x_56_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingInt16___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_53_ = stack[0].m_obj;
uint16_t v_x2_54_ = stack[1].m_num;
uint16_t v_res_57_;
v_res_57_ = l_Lean_Grind_instCommRingInt16___lam__0(v_x1_53_, v_x2_54_);
stack->m_num = v_res_57_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt16___lam__0___boxed(lean_object* v_x1_58_, lean_object* v_x2_59_){
_start:
{
uint16_t v_x2_64__boxed_60_; uint16_t v_res_61_; lean_object* v_r_62_; 
v_x2_64__boxed_60_ = lean_unbox(v_x2_59_);
v_res_61_ = l_Lean_Grind_instCommRingInt16___lam__0(v_x1_58_, v_x2_64__boxed_60_);
lean_dec(v_x1_58_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
uint16_t l_Lean_Grind_instCommRingInt16___lam__1(lean_object* v_x1_63_, uint16_t v_x2_64_){
_start:
{
uint16_t v___x_65_; uint16_t v___x_66_; 
v___x_65_ = lean_int16_of_int(v_x1_63_);
v___x_66_ = lean_int16_mul(v___x_65_, v_x2_64_);
return v___x_66_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingInt16___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_63_ = stack[0].m_obj;
uint16_t v_x2_64_ = stack[1].m_num;
uint16_t v_res_67_;
v_res_67_ = l_Lean_Grind_instCommRingInt16___lam__1(v_x1_63_, v_x2_64_);
stack->m_num = v_res_67_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt16___lam__1___boxed(lean_object* v_x1_68_, lean_object* v_x2_69_){
_start:
{
uint16_t v_x2_80__boxed_70_; uint16_t v_res_71_; lean_object* v_r_72_; 
v_x2_80__boxed_70_ = lean_unbox(v_x2_69_);
v_res_71_ = l_Lean_Grind_instCommRingInt16___lam__1(v_x1_68_, v_x2_80__boxed_70_);
lean_dec(v_x1_68_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
uint32_t l_Lean_Grind_instCommRingInt32___lam__0(lean_object* v_x1_101_, uint32_t v_x2_102_){
_start:
{
uint32_t v___x_103_; uint32_t v___x_104_; 
v___x_103_ = lean_int32_of_nat(v_x1_101_);
v___x_104_ = lean_int32_mul(v___x_103_, v_x2_102_);
return v___x_104_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingInt32___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_101_ = stack[0].m_obj;
uint32_t v_x2_102_ = stack[1].m_num;
uint32_t v_res_105_;
v_res_105_ = l_Lean_Grind_instCommRingInt32___lam__0(v_x1_101_, v_x2_102_);
stack->m_num = v_res_105_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt32___lam__0___boxed(lean_object* v_x1_106_, lean_object* v_x2_107_){
_start:
{
uint32_t v_x2_64__boxed_108_; uint32_t v_res_109_; lean_object* v_r_110_; 
v_x2_64__boxed_108_ = lean_unbox_uint32(v_x2_107_);
lean_dec(v_x2_107_);
v_res_109_ = l_Lean_Grind_instCommRingInt32___lam__0(v_x1_106_, v_x2_64__boxed_108_);
lean_dec(v_x1_106_);
v_r_110_ = lean_box_uint32(v_res_109_);
return v_r_110_;
}
}
uint32_t l_Lean_Grind_instCommRingInt32___lam__1(lean_object* v_x1_111_, uint32_t v_x2_112_){
_start:
{
uint32_t v___x_113_; uint32_t v___x_114_; 
v___x_113_ = lean_int32_of_int(v_x1_111_);
v___x_114_ = lean_int32_mul(v___x_113_, v_x2_112_);
return v___x_114_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingInt32___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_111_ = stack[0].m_obj;
uint32_t v_x2_112_ = stack[1].m_num;
uint32_t v_res_115_;
v_res_115_ = l_Lean_Grind_instCommRingInt32___lam__1(v_x1_111_, v_x2_112_);
stack->m_num = v_res_115_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt32___lam__1___boxed(lean_object* v_x1_116_, lean_object* v_x2_117_){
_start:
{
uint32_t v_x2_80__boxed_118_; uint32_t v_res_119_; lean_object* v_r_120_; 
v_x2_80__boxed_118_ = lean_unbox_uint32(v_x2_117_);
lean_dec(v_x2_117_);
v_res_119_ = l_Lean_Grind_instCommRingInt32___lam__1(v_x1_116_, v_x2_80__boxed_118_);
lean_dec(v_x1_116_);
v_r_120_ = lean_box_uint32(v_res_119_);
return v_r_120_;
}
}
uint64_t l_Lean_Grind_instCommRingInt64___lam__0(lean_object* v_x1_149_, uint64_t v_x2_150_){
_start:
{
uint64_t v___x_151_; uint64_t v___x_152_; 
v___x_151_ = lean_int64_of_nat(v_x1_149_);
v___x_152_ = lean_int64_mul(v___x_151_, v_x2_150_);
return v___x_152_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingInt64___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_149_ = stack[0].m_obj;
uint64_t v_x2_150_ = stack[1].m_num;
uint64_t v_res_153_;
v_res_153_ = l_Lean_Grind_instCommRingInt64___lam__0(v_x1_149_, v_x2_150_);
stack->m_num = v_res_153_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt64___lam__0___boxed(lean_object* v_x1_154_, lean_object* v_x2_155_){
_start:
{
uint64_t v_x2_64__boxed_156_; uint64_t v_res_157_; lean_object* v_r_158_; 
v_x2_64__boxed_156_ = lean_unbox_uint64(v_x2_155_);
lean_dec_ref(v_x2_155_);
v_res_157_ = l_Lean_Grind_instCommRingInt64___lam__0(v_x1_154_, v_x2_64__boxed_156_);
lean_dec(v_x1_154_);
v_r_158_ = lean_box_uint64(v_res_157_);
return v_r_158_;
}
}
uint64_t l_Lean_Grind_instCommRingInt64___lam__1(lean_object* v_x1_159_, uint64_t v_x2_160_){
_start:
{
uint64_t v___x_161_; uint64_t v___x_162_; 
v___x_161_ = lean_int64_of_int(v_x1_159_);
v___x_162_ = lean_int64_mul(v___x_161_, v_x2_160_);
return v___x_162_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingInt64___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_159_ = stack[0].m_obj;
uint64_t v_x2_160_ = stack[1].m_num;
uint64_t v_res_163_;
v_res_163_ = l_Lean_Grind_instCommRingInt64___lam__1(v_x1_159_, v_x2_160_);
stack->m_num = v_res_163_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt64___lam__1___boxed(lean_object* v_x1_164_, lean_object* v_x2_165_){
_start:
{
uint64_t v_x2_80__boxed_166_; uint64_t v_res_167_; lean_object* v_r_168_; 
v_x2_80__boxed_166_ = lean_unbox_uint64(v_x2_165_);
lean_dec_ref(v_x2_165_);
v_res_167_ = l_Lean_Grind_instCommRingInt64___lam__1(v_x1_164_, v_x2_80__boxed_166_);
lean_dec(v_x1_164_);
v_r_168_ = lean_box_uint64(v_res_167_);
return v_r_168_;
}
}
size_t l_Lean_Grind_instCommRingISize___lam__0(lean_object* v_x1_197_, size_t v_x2_198_){
_start:
{
size_t v___x_199_; size_t v___x_200_; 
v___x_199_ = lean_isize_of_nat(v_x1_197_);
v___x_200_ = lean_isize_mul(v___x_199_, v_x2_198_);
return v___x_200_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingISize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_197_ = stack[0].m_obj;
size_t v_x2_198_ = stack[1].m_num;
size_t v_res_201_;
v_res_201_ = l_Lean_Grind_instCommRingISize___lam__0(v_x1_197_, v_x2_198_);
stack->m_num = v_res_201_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingISize___lam__0___boxed(lean_object* v_x1_202_, lean_object* v_x2_203_){
_start:
{
size_t v_x2_64__boxed_204_; size_t v_res_205_; lean_object* v_r_206_; 
v_x2_64__boxed_204_ = lean_unbox_usize(v_x2_203_);
lean_dec(v_x2_203_);
v_res_205_ = l_Lean_Grind_instCommRingISize___lam__0(v_x1_202_, v_x2_64__boxed_204_);
lean_dec(v_x1_202_);
v_r_206_ = lean_box_usize(v_res_205_);
return v_r_206_;
}
}
size_t l_Lean_Grind_instCommRingISize___lam__1(lean_object* v_x1_207_, size_t v_x2_208_){
_start:
{
size_t v___x_209_; size_t v___x_210_; 
v___x_209_ = lean_isize_of_int(v_x1_207_);
v___x_210_ = lean_isize_mul(v___x_209_, v_x2_208_);
return v___x_210_;
}
}
LEAN_EXPORT void l_Lean_Grind_instCommRingISize___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_207_ = stack[0].m_obj;
size_t v_x2_208_ = stack[1].m_num;
size_t v_res_211_;
v_res_211_ = l_Lean_Grind_instCommRingISize___lam__1(v_x1_207_, v_x2_208_);
stack->m_num = v_res_211_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingISize___lam__1___boxed(lean_object* v_x1_212_, lean_object* v_x2_213_){
_start:
{
size_t v_x2_80__boxed_214_; size_t v_res_215_; lean_object* v_r_216_; 
v_x2_80__boxed_214_ = lean_unbox_usize(v_x2_213_);
lean_dec(v_x2_213_);
v_res_215_ = l_Lean_Grind_instCommRingISize___lam__1(v_x1_212_, v_x2_80__boxed_214_);
lean_dec(v_x1_212_);
v_r_216_ = lean_box_usize(v_res_215_);
return v_r_216_;
}
}
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_GrindInstances_Ring_SInt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
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
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_GrindInstances_Ring_SInt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
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
