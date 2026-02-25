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
lean_object* l_Int8_ofNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_Int8_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int8_natCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int8_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int8_natCast = (const lean_object*)&l_Lean_Grind_Int8_natCast___closed__0_value;
lean_object* l_Int8_ofInt___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_Int8_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int8_intCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int8_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int8_intCast = (const lean_object*)&l_Lean_Grind_Int8_intCast___closed__0_value;
uint8_t lean_int8_of_nat(lean_object*);
uint8_t lean_int8_mul(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Grind_instCommRingInt8___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt8___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_int8_of_int(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_instCommRingInt8___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt8___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt8___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__1_value;
lean_object* l_Int8_add___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__2_value;
lean_object* l_Int8_mul___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__3_value;
lean_object* l_Int8_pow___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__4_value;
lean_object* l_instHAdd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__5_value;
lean_object* l_Int8_neg___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__6_value;
lean_object* l_Int8_sub___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__7_value;
lean_object* l_Int8_instOfNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int8_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__3_value),((lean_object*)&l_Lean_Grind_Int8_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__7_value),((lean_object*)&l_Lean_Grind_Int8_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt8___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt8___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingInt8 = (const lean_object*)&l_Lean_Grind_instCommRingInt8___closed__10_value;
lean_object* l_Int16_ofNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_Int16_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int16_natCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int16_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int16_natCast = (const lean_object*)&l_Lean_Grind_Int16_natCast___closed__0_value;
lean_object* l_Int16_ofInt___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_Int16_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int16_intCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int16_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int16_intCast = (const lean_object*)&l_Lean_Grind_Int16_intCast___closed__0_value;
uint16_t lean_int16_of_nat(lean_object*);
uint16_t lean_int16_mul(uint16_t, uint16_t);
LEAN_EXPORT uint16_t l_Lean_Grind_instCommRingInt16___lam__0(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt16___lam__0___boxed(lean_object*, lean_object*);
uint16_t lean_int16_of_int(lean_object*);
LEAN_EXPORT uint16_t l_Lean_Grind_instCommRingInt16___lam__1(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt16___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt16___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt16___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__1_value;
lean_object* l_Int16_add___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__2_value;
lean_object* l_Int16_mul___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__3_value;
lean_object* l_Int16_pow___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__5_value;
lean_object* l_Int16_neg___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__6_value;
lean_object* l_Int16_sub___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__7_value;
lean_object* l_Int16_instOfNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt16___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int16_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt16___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__3_value),((lean_object*)&l_Lean_Grind_Int16_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt16___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__7_value),((lean_object*)&l_Lean_Grind_Int16_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt16___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt16___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingInt16 = (const lean_object*)&l_Lean_Grind_instCommRingInt16___closed__10_value;
lean_object* l_Int32_ofNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_Int32_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int32_natCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int32_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int32_natCast = (const lean_object*)&l_Lean_Grind_Int32_natCast___closed__0_value;
lean_object* l_Int32_ofInt___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_Int32_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int32_intCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int32_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int32_intCast = (const lean_object*)&l_Lean_Grind_Int32_intCast___closed__0_value;
uint32_t lean_int32_of_nat(lean_object*);
uint32_t lean_int32_mul(uint32_t, uint32_t);
LEAN_EXPORT uint32_t l_Lean_Grind_instCommRingInt32___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt32___lam__0___boxed(lean_object*, lean_object*);
uint32_t lean_int32_of_int(lean_object*);
LEAN_EXPORT uint32_t l_Lean_Grind_instCommRingInt32___lam__1(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt32___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt32___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt32___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__1_value;
lean_object* l_Int32_add___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__2_value;
lean_object* l_Int32_mul___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__3_value;
lean_object* l_Int32_pow___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__5_value;
lean_object* l_Int32_neg___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__6_value;
lean_object* l_Int32_sub___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__7_value;
lean_object* l_Int32_instOfNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt32___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int32_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt32___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__3_value),((lean_object*)&l_Lean_Grind_Int32_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt32___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__7_value),((lean_object*)&l_Lean_Grind_Int32_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt32___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt32___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingInt32 = (const lean_object*)&l_Lean_Grind_instCommRingInt32___closed__10_value;
lean_object* l_Int64_ofNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_Int64_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int64_natCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int64_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int64_natCast = (const lean_object*)&l_Lean_Grind_Int64_natCast___closed__0_value;
lean_object* l_Int64_ofInt___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_Int64_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_Int64_intCast___closed__0 = (const lean_object*)&l_Lean_Grind_Int64_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_Int64_intCast = (const lean_object*)&l_Lean_Grind_Int64_intCast___closed__0_value;
uint64_t lean_int64_of_nat(lean_object*);
uint64_t lean_int64_mul(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_Lean_Grind_instCommRingInt64___lam__0(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt64___lam__0___boxed(lean_object*, lean_object*);
uint64_t lean_int64_of_int(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Grind_instCommRingInt64___lam__1(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt64___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt64___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingInt64___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__1_value;
lean_object* l_Int64_add___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__2_value;
lean_object* l_Int64_mul___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__3_value;
lean_object* l_Int64_pow___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__5_value;
lean_object* l_Int64_neg___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__6_value;
lean_object* l_Int64_sub___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__7_value;
lean_object* l_Int64_instOfNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingInt64___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int64_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt64___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__3_value),((lean_object*)&l_Lean_Grind_Int64_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingInt64___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__7_value),((lean_object*)&l_Lean_Grind_Int64_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingInt64___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingInt64___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingInt64 = (const lean_object*)&l_Lean_Grind_instCommRingInt64___closed__10_value;
lean_object* l_ISize_ofNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_ISize_natCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_ISize_natCast___closed__0 = (const lean_object*)&l_Lean_Grind_ISize_natCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_ISize_natCast = (const lean_object*)&l_Lean_Grind_ISize_natCast___closed__0_value;
lean_object* l_ISize_ofInt___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_ISize_intCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_ofInt___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_ISize_intCast___closed__0 = (const lean_object*)&l_Lean_Grind_ISize_intCast___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_ISize_intCast = (const lean_object*)&l_Lean_Grind_ISize_intCast___closed__0_value;
size_t lean_isize_of_nat(lean_object*);
size_t lean_isize_mul(size_t, size_t);
LEAN_EXPORT size_t l_Lean_Grind_instCommRingISize___lam__0(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingISize___lam__0___boxed(lean_object*, lean_object*);
size_t lean_isize_of_int(lean_object*);
LEAN_EXPORT size_t l_Lean_Grind_instCommRingISize___lam__1(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingISize___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingISize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__0 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__0_value;
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instCommRingISize___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__1 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__1_value;
lean_object* l_ISize_add___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__2 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__2_value;
lean_object* l_ISize_mul___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__3 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__3_value;
lean_object* l_ISize_pow___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_pow___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__4 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__4_value;
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHAdd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingISize___closed__4_value)} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__5 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__5_value;
lean_object* l_ISize_neg___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_neg___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__6 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__6_value;
lean_object* l_ISize_sub___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__7 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__7_value;
lean_object* l_ISize_instOfNat___boxed(lean_object*);
static const lean_closure_object l_Lean_Grind_instCommRingISize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ISize_instOfNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instCommRingISize___closed__8 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__8_value;
static const lean_ctor_object l_Lean_Grind_instCommRingISize___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 0, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingISize___closed__2_value),((lean_object*)&l_Lean_Grind_instCommRingISize___closed__3_value),((lean_object*)&l_Lean_Grind_ISize_natCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingISize___closed__8_value),((lean_object*)&l_Lean_Grind_instCommRingISize___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingISize___closed__5_value)}};
static const lean_object* l_Lean_Grind_instCommRingISize___closed__9 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__9_value;
static const lean_ctor_object l_Lean_Grind_instCommRingISize___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Grind_instCommRingISize___closed__9_value),((lean_object*)&l_Lean_Grind_instCommRingISize___closed__6_value),((lean_object*)&l_Lean_Grind_instCommRingISize___closed__7_value),((lean_object*)&l_Lean_Grind_ISize_intCast___closed__0_value),((lean_object*)&l_Lean_Grind_instCommRingISize___closed__1_value)}};
static const lean_object* l_Lean_Grind_instCommRingISize___closed__10 = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instCommRingISize = (const lean_object*)&l_Lean_Grind_instCommRingISize___closed__10_value;
LEAN_EXPORT uint8_t l_Lean_Grind_instCommRingInt8___lam__0(lean_object* x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = lean_int8_of_nat(x_1);
x_4 = lean_int8_mul(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt8___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Grind_instCommRingInt8___lam__0(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_instCommRingInt8___lam__1(lean_object* x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = lean_int8_of_int(x_1);
x_4 = lean_int8_mul(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt8___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Grind_instCommRingInt8___lam__1(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint16_t l_Lean_Grind_instCommRingInt16___lam__0(lean_object* x_1, uint16_t x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; 
x_3 = lean_int16_of_nat(x_1);
x_4 = lean_int16_mul(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt16___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Grind_instCommRingInt16___lam__0(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint16_t l_Lean_Grind_instCommRingInt16___lam__1(lean_object* x_1, uint16_t x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; 
x_3 = lean_int16_of_int(x_1);
x_4 = lean_int16_mul(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt16___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
x_4 = l_Lean_Grind_instCommRingInt16___lam__1(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint32_t l_Lean_Grind_instCommRingInt32___lam__0(lean_object* x_1, uint32_t x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; 
x_3 = lean_int32_of_nat(x_1);
x_4 = lean_int32_mul(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt32___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Lean_Grind_instCommRingInt32___lam__0(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT uint32_t l_Lean_Grind_instCommRingInt32___lam__1(lean_object* x_1, uint32_t x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; 
x_3 = lean_int32_of_int(x_1);
x_4 = lean_int32_mul(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt32___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Lean_Grind_instCommRingInt32___lam__1(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box_uint32(x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_instCommRingInt64___lam__0(lean_object* x_1, uint64_t x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; 
x_3 = lean_int64_of_nat(x_1);
x_4 = lean_int64_mul(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt64___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_4 = l_Lean_Grind_instCommRingInt64___lam__0(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l_Lean_Grind_instCommRingInt64___lam__1(lean_object* x_1, uint64_t x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; 
x_3 = lean_int64_of_int(x_1);
x_4 = lean_int64_mul(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt64___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_4 = l_Lean_Grind_instCommRingInt64___lam__1(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT size_t l_Lean_Grind_instCommRingISize___lam__0(lean_object* x_1, size_t x_2) {
_start:
{
size_t x_3; size_t x_4; 
x_3 = lean_isize_of_nat(x_1);
x_4 = lean_isize_mul(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingISize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_4 = l_Lean_Grind_instCommRingISize___lam__0(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box_usize(x_4);
return x_5;
}
}
LEAN_EXPORT size_t l_Lean_Grind_instCommRingISize___lam__1(lean_object* x_1, size_t x_2) {
_start:
{
size_t x_3; size_t x_4; 
x_3 = lean_isize_of_int(x_1);
x_4 = lean_isize_mul(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingISize___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_4 = l_Lean_Grind_instCommRingISize___lam__1(x_1, x_3);
lean_dec(x_1);
x_5 = lean_box_usize(x_4);
return x_5;
}
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
