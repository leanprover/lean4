// Lean compiler output
// Module: Init.Data.Range.Polymorphic.UInt
// Imports: public import Init.Data.Range.Polymorphic.BitVec public import Init.Data.UInt import Init.ByCases import Init.Data.BitVec.Lemmas import Init.Data.Option.Lemmas
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
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
uint16_t lean_uint16_of_nat(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint16_t lean_uint16_add(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt8_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_instUpwardEnumerable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt8_instUpwardEnumerable___closed__0 = (const lean_object*)&l_UInt8_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_UInt8_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_instUpwardEnumerable___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt8_instUpwardEnumerable___closed__1 = (const lean_object*)&l_UInt8_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_UInt8_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_UInt8_instUpwardEnumerable___closed__0_value),((lean_object*)&l_UInt8_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_UInt8_instUpwardEnumerable___closed__2 = (const lean_object*)&l_UInt8_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_UInt8_instUpwardEnumerable = (const lean_object*)&l_UInt8_instUpwardEnumerable___closed__2_value;
static const lean_ctor_object l_UInt8_instLeast_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_UInt8_instLeast_x3f___closed__0 = (const lean_object*)&l_UInt8_instLeast_x3f___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt8_instLeast_x3f = (const lean_object*)&l_UInt8_instLeast_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_UInt8_instHasSize___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_instHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt8_instHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_instHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt8_instHasSize___closed__0 = (const lean_object*)&l_UInt8_instHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt8_instHasSize = (const lean_object*)&l_UInt8_instHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_UInt8_instHasSize__1___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_instHasSize__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt8_instHasSize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_instHasSize__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt8_instHasSize__1___closed__0 = (const lean_object*)&l_UInt8_instHasSize__1___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt8_instHasSize__1 = (const lean_object*)&l_UInt8_instHasSize__1___closed__0_value;
LEAN_EXPORT lean_object* l_UInt8_instHasSize__2___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_instHasSize__2___lam__0___boxed(lean_object*);
static const lean_closure_object l_UInt8_instHasSize__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_instHasSize__2___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt8_instHasSize__2___closed__0 = (const lean_object*)&l_UInt8_instHasSize__2___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt8_instHasSize__2 = (const lean_object*)&l_UInt8_instHasSize__2___closed__0_value;
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__1(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt16_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_instUpwardEnumerable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt16_instUpwardEnumerable___closed__0 = (const lean_object*)&l_UInt16_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_UInt16_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_instUpwardEnumerable___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt16_instUpwardEnumerable___closed__1 = (const lean_object*)&l_UInt16_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_UInt16_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_UInt16_instUpwardEnumerable___closed__0_value),((lean_object*)&l_UInt16_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_UInt16_instUpwardEnumerable___closed__2 = (const lean_object*)&l_UInt16_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_UInt16_instUpwardEnumerable = (const lean_object*)&l_UInt16_instUpwardEnumerable___closed__2_value;
static const lean_ctor_object l_UInt16_instLeast_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_UInt16_instLeast_x3f___closed__0 = (const lean_object*)&l_UInt16_instLeast_x3f___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt16_instLeast_x3f = (const lean_object*)&l_UInt16_instLeast_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_UInt16_instHasSize___lam__0(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_instHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt16_instHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_instHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt16_instHasSize___closed__0 = (const lean_object*)&l_UInt16_instHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt16_instHasSize = (const lean_object*)&l_UInt16_instHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_UInt16_instHasSize__1___lam__0(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_instHasSize__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt16_instHasSize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_instHasSize__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt16_instHasSize__1___closed__0 = (const lean_object*)&l_UInt16_instHasSize__1___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt16_instHasSize__1 = (const lean_object*)&l_UInt16_instHasSize__1___closed__0_value;
LEAN_EXPORT lean_object* l_UInt16_instHasSize__2___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_instHasSize__2___lam__0___boxed(lean_object*);
static const lean_closure_object l_UInt16_instHasSize__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_instHasSize__2___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt16_instHasSize__2___closed__0 = (const lean_object*)&l_UInt16_instHasSize__2___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt16_instHasSize__2 = (const lean_object*)&l_UInt16_instHasSize__2___closed__0_value;
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__1(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt32_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_instUpwardEnumerable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt32_instUpwardEnumerable___closed__0 = (const lean_object*)&l_UInt32_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_UInt32_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_instUpwardEnumerable___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt32_instUpwardEnumerable___closed__1 = (const lean_object*)&l_UInt32_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_UInt32_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_UInt32_instUpwardEnumerable___closed__0_value),((lean_object*)&l_UInt32_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_UInt32_instUpwardEnumerable___closed__2 = (const lean_object*)&l_UInt32_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_UInt32_instUpwardEnumerable = (const lean_object*)&l_UInt32_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT lean_object* l_UInt32_instLeast_x3f___closed__0___boxed__const__1;
static lean_once_cell_t l_UInt32_instLeast_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt32_instLeast_x3f___closed__0;
LEAN_EXPORT lean_object* l_UInt32_instLeast_x3f;
LEAN_EXPORT lean_object* l_UInt32_instHasSize___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_instHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt32_instHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_instHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt32_instHasSize___closed__0 = (const lean_object*)&l_UInt32_instHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt32_instHasSize = (const lean_object*)&l_UInt32_instHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_UInt32_instHasSize__1___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_instHasSize__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt32_instHasSize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_instHasSize__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt32_instHasSize__1___closed__0 = (const lean_object*)&l_UInt32_instHasSize__1___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt32_instHasSize__1 = (const lean_object*)&l_UInt32_instHasSize__1___closed__0_value;
LEAN_EXPORT lean_object* l_UInt32_instHasSize__2___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_UInt32_instHasSize__2___lam__0___boxed(lean_object*);
static const lean_closure_object l_UInt32_instHasSize__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_instHasSize__2___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt32_instHasSize__2___closed__0 = (const lean_object*)&l_UInt32_instHasSize__2___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt32_instHasSize__2 = (const lean_object*)&l_UInt32_instHasSize__2___closed__0_value;
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__0___boxed(lean_object*);
static lean_once_cell_t l_UInt64_instUpwardEnumerable___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt64_instUpwardEnumerable___lam__1___closed__0;
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__1(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt64_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_instUpwardEnumerable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt64_instUpwardEnumerable___closed__0 = (const lean_object*)&l_UInt64_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_UInt64_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_instUpwardEnumerable___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt64_instUpwardEnumerable___closed__1 = (const lean_object*)&l_UInt64_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_UInt64_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_UInt64_instUpwardEnumerable___closed__0_value),((lean_object*)&l_UInt64_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_UInt64_instUpwardEnumerable___closed__2 = (const lean_object*)&l_UInt64_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_UInt64_instUpwardEnumerable = (const lean_object*)&l_UInt64_instUpwardEnumerable___closed__2_value;
static const lean_ctor_object l_UInt64_instLeast_x3f___closed__0___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
LEAN_EXPORT const lean_object* l_UInt64_instLeast_x3f___closed__0___boxed__const__1 = (const lean_object*)&l_UInt64_instLeast_x3f___closed__0___boxed__const__1_value;
static const lean_ctor_object l_UInt64_instLeast_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_UInt64_instLeast_x3f___closed__0___boxed__const__1_value)}};
static const lean_object* l_UInt64_instLeast_x3f___closed__0 = (const lean_object*)&l_UInt64_instLeast_x3f___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt64_instLeast_x3f = (const lean_object*)&l_UInt64_instLeast_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_UInt64_instHasSize___lam__0(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_instHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt64_instHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_instHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt64_instHasSize___closed__0 = (const lean_object*)&l_UInt64_instHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt64_instHasSize = (const lean_object*)&l_UInt64_instHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_UInt64_instHasSize__1___lam__0(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_instHasSize__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt64_instHasSize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_instHasSize__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt64_instHasSize__1___closed__0 = (const lean_object*)&l_UInt64_instHasSize__1___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt64_instHasSize__1 = (const lean_object*)&l_UInt64_instHasSize__1___closed__0_value;
LEAN_EXPORT lean_object* l_UInt64_instHasSize__2___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_instHasSize__2___lam__0___boxed(lean_object*);
static const lean_closure_object l_UInt64_instHasSize__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_instHasSize__2___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt64_instHasSize__2___closed__0 = (const lean_object*)&l_UInt64_instHasSize__2___closed__0_value;
LEAN_EXPORT const lean_object* l_UInt64_instHasSize__2 = (const lean_object*)&l_UInt64_instHasSize__2___closed__0_value;
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__0(size_t);
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__0___boxed(lean_object*);
static lean_once_cell_t l_USize_instUpwardEnumerable___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_USize_instUpwardEnumerable___lam__1___closed__0;
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__1(lean_object*, size_t);
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_USize_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_instUpwardEnumerable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_USize_instUpwardEnumerable___closed__0 = (const lean_object*)&l_USize_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_USize_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_instUpwardEnumerable___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_USize_instUpwardEnumerable___closed__1 = (const lean_object*)&l_USize_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_USize_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_USize_instUpwardEnumerable___closed__0_value),((lean_object*)&l_USize_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_USize_instUpwardEnumerable___closed__2 = (const lean_object*)&l_USize_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_USize_instUpwardEnumerable = (const lean_object*)&l_USize_instUpwardEnumerable___closed__2_value;
static const lean_ctor_object l_USize_instLeast_x3f___closed__0___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_USize_instLeast_x3f___closed__0___boxed__const__1 = (const lean_object*)&l_USize_instLeast_x3f___closed__0___boxed__const__1_value;
static const lean_ctor_object l_USize_instLeast_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_USize_instLeast_x3f___closed__0___boxed__const__1_value)}};
static const lean_object* l_USize_instLeast_x3f___closed__0 = (const lean_object*)&l_USize_instLeast_x3f___closed__0_value;
LEAN_EXPORT const lean_object* l_USize_instLeast_x3f = (const lean_object*)&l_USize_instLeast_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_USize_instHasSize___lam__0(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_instHasSize___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_USize_instHasSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_instHasSize___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_USize_instHasSize___closed__0 = (const lean_object*)&l_USize_instHasSize___closed__0_value;
LEAN_EXPORT const lean_object* l_USize_instHasSize = (const lean_object*)&l_USize_instHasSize___closed__0_value;
LEAN_EXPORT lean_object* l_USize_instHasSize__1___lam__0(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_instHasSize__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_USize_instHasSize__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_instHasSize__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_USize_instHasSize__1___closed__0 = (const lean_object*)&l_USize_instHasSize__1___closed__0_value;
LEAN_EXPORT const lean_object* l_USize_instHasSize__1 = (const lean_object*)&l_USize_instHasSize__1___closed__0_value;
LEAN_EXPORT lean_object* l_USize_instHasSize__2___lam__0(size_t);
LEAN_EXPORT lean_object* l_USize_instHasSize__2___lam__0___boxed(lean_object*);
static const lean_closure_object l_USize_instHasSize__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_instHasSize__2___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_USize_instHasSize__2___closed__0 = (const lean_object*)&l_USize_instHasSize__2___closed__0_value;
LEAN_EXPORT const lean_object* l_USize_instHasSize__2 = (const lean_object*)&l_USize_instHasSize__2___closed__0_value;
lean_object* l_UInt8_instUpwardEnumerable___lam__0(uint8_t v_i_1_){
_start:
{
uint8_t v___x_2_; uint8_t v___x_3_; uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_2_ = 1;
v___x_3_ = lean_uint8_add(v_i_1_, v___x_2_);
v___x_4_ = 0;
v___x_5_ = lean_uint8_dec_eq(v___x_3_, v___x_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_box(v___x_3_);
v___x_7_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
return v___x_7_;
}
else
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
}
LEAN_EXPORT void l_UInt8_instUpwardEnumerable___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_i_1_ = stack[0].m_num;
lean_object* v_res_9_;
v_res_9_ = l_UInt8_instUpwardEnumerable___lam__0(v_i_1_);
stack->m_obj
 = v_res_9_;
}
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_10_){
_start:
{
uint8_t v_i_boxed_11_; lean_object* v_res_12_; 
v_i_boxed_11_ = lean_unbox(v_i_10_);
v_res_12_ = l_UInt8_instUpwardEnumerable___lam__0(v_i_boxed_11_);
return v_res_12_;
}
}
lean_object* l_UInt8_instUpwardEnumerable___lam__1(lean_object* v_n_13_, uint8_t v_i_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_15_ = lean_uint8_to_nat(v_i_14_);
v___x_16_ = lean_nat_add(v___x_15_, v_n_13_);
v___x_17_ = lean_unsigned_to_nat(256u);
v___x_18_ = lean_nat_dec_lt(v___x_16_, v___x_17_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
lean_dec(v___x_16_);
v___x_19_ = lean_box(0);
return v___x_19_;
}
else
{
uint8_t v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_20_ = lean_uint8_of_nat(v___x_16_);
lean_dec(v___x_16_);
v___x_21_ = lean_box(v___x_20_);
v___x_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT void l_UInt8_instUpwardEnumerable___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_13_ = stack[0].m_obj;
uint8_t v_i_14_ = stack[1].m_num;
lean_object* v_res_23_;
v_res_23_ = l_UInt8_instUpwardEnumerable___lam__1(v_n_13_, v_i_14_);
stack->m_obj
 = v_res_23_;
}
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_24_, lean_object* v_i_25_){
_start:
{
uint8_t v_i_boxed_26_; lean_object* v_res_27_; 
v_i_boxed_26_ = lean_unbox(v_i_25_);
v_res_27_ = l_UInt8_instUpwardEnumerable___lam__1(v_n_24_, v_i_boxed_26_);
lean_dec(v_n_24_);
return v_res_27_;
}
}
lean_object* l_UInt8_instHasSize___lam__0(uint8_t v_lo_38_, uint8_t v_hi_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_40_ = lean_uint8_to_nat(v_hi_39_);
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_add(v___x_40_, v___x_41_);
v___x_43_ = lean_uint8_to_nat(v_lo_38_);
v___x_44_ = lean_nat_sub(v___x_42_, v___x_43_);
lean_dec(v___x_42_);
return v___x_44_;
}
}
LEAN_EXPORT void l_UInt8_instHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_lo_38_ = stack[0].m_num;
uint8_t v_hi_39_ = stack[1].m_num;
lean_object* v_res_45_;
v_res_45_ = l_UInt8_instHasSize___lam__0(v_lo_38_, v_hi_39_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize___lam__0___boxed(lean_object* v_lo_46_, lean_object* v_hi_47_){
_start:
{
uint8_t v_lo_boxed_48_; uint8_t v_hi_boxed_49_; lean_object* v_res_50_; 
v_lo_boxed_48_ = lean_unbox(v_lo_46_);
v_hi_boxed_49_ = lean_unbox(v_hi_47_);
v_res_50_ = l_UInt8_instHasSize___lam__0(v_lo_boxed_48_, v_hi_boxed_49_);
return v_res_50_;
}
}
lean_object* l_UInt8_instHasSize__1___lam__0(uint8_t v_lo_53_, uint8_t v_hi_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_55_ = lean_uint8_to_nat(v_hi_54_);
v___x_56_ = lean_unsigned_to_nat(1u);
v___x_57_ = lean_nat_add(v___x_55_, v___x_56_);
v___x_58_ = lean_uint8_to_nat(v_lo_53_);
v___x_59_ = lean_nat_sub(v___x_57_, v___x_58_);
lean_dec(v___x_57_);
v___x_60_ = lean_nat_sub(v___x_59_, v___x_56_);
lean_dec(v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT void l_UInt8_instHasSize__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_lo_53_ = stack[0].m_num;
uint8_t v_hi_54_ = stack[1].m_num;
lean_object* v_res_61_;
v_res_61_ = l_UInt8_instHasSize__1___lam__0(v_lo_53_, v_hi_54_);
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize__1___lam__0___boxed(lean_object* v_lo_62_, lean_object* v_hi_63_){
_start:
{
uint8_t v_lo_boxed_64_; uint8_t v_hi_boxed_65_; lean_object* v_res_66_; 
v_lo_boxed_64_ = lean_unbox(v_lo_62_);
v_hi_boxed_65_ = lean_unbox(v_hi_63_);
v_res_66_ = l_UInt8_instHasSize__1___lam__0(v_lo_boxed_64_, v_hi_boxed_65_);
return v_res_66_;
}
}
lean_object* l_UInt8_instHasSize__2___lam__0(uint8_t v_lo_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = lean_unsigned_to_nat(256u);
v___x_71_ = lean_uint8_to_nat(v_lo_69_);
v___x_72_ = lean_nat_sub(v___x_70_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT void l_UInt8_instHasSize__2___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_lo_69_ = stack[0].m_num;
lean_object* v_res_73_;
v_res_73_ = l_UInt8_instHasSize__2___lam__0(v_lo_69_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize__2___lam__0___boxed(lean_object* v_lo_74_){
_start:
{
uint8_t v_lo_boxed_75_; lean_object* v_res_76_; 
v_lo_boxed_75_ = lean_unbox(v_lo_74_);
v_res_76_ = l_UInt8_instHasSize__2___lam__0(v_lo_boxed_75_);
return v_res_76_;
}
}
lean_object* l_UInt16_instUpwardEnumerable___lam__0(uint16_t v_i_79_){
_start:
{
uint16_t v___x_80_; uint16_t v___x_81_; uint16_t v___x_82_; uint8_t v___x_83_; 
v___x_80_ = 1;
v___x_81_ = lean_uint16_add(v_i_79_, v___x_80_);
v___x_82_ = 0;
v___x_83_ = lean_uint16_dec_eq(v___x_81_, v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_box(v___x_81_);
v___x_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
else
{
lean_object* v___x_86_; 
v___x_86_ = lean_box(0);
return v___x_86_;
}
}
}
LEAN_EXPORT void l_UInt16_instUpwardEnumerable___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_i_79_ = stack[0].m_num;
lean_object* v_res_87_;
v_res_87_ = l_UInt16_instUpwardEnumerable___lam__0(v_i_79_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_88_){
_start:
{
uint16_t v_i_boxed_89_; lean_object* v_res_90_; 
v_i_boxed_89_ = lean_unbox(v_i_88_);
v_res_90_ = l_UInt16_instUpwardEnumerable___lam__0(v_i_boxed_89_);
return v_res_90_;
}
}
lean_object* l_UInt16_instUpwardEnumerable___lam__1(lean_object* v_n_91_, uint16_t v_i_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_93_ = lean_uint16_to_nat(v_i_92_);
v___x_94_ = lean_nat_add(v___x_93_, v_n_91_);
v___x_95_ = lean_unsigned_to_nat(65536u);
v___x_96_ = lean_nat_dec_lt(v___x_94_, v___x_95_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec(v___x_94_);
v___x_97_ = lean_box(0);
return v___x_97_;
}
else
{
uint16_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = lean_uint16_of_nat(v___x_94_);
lean_dec(v___x_94_);
v___x_99_ = lean_box(v___x_98_);
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
}
LEAN_EXPORT void l_UInt16_instUpwardEnumerable___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_91_ = stack[0].m_obj;
uint16_t v_i_92_ = stack[1].m_num;
lean_object* v_res_101_;
v_res_101_ = l_UInt16_instUpwardEnumerable___lam__1(v_n_91_, v_i_92_);
stack->m_obj
 = v_res_101_;
}
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_102_, lean_object* v_i_103_){
_start:
{
uint16_t v_i_boxed_104_; lean_object* v_res_105_; 
v_i_boxed_104_ = lean_unbox(v_i_103_);
v_res_105_ = l_UInt16_instUpwardEnumerable___lam__1(v_n_102_, v_i_boxed_104_);
lean_dec(v_n_102_);
return v_res_105_;
}
}
lean_object* l_UInt16_instHasSize___lam__0(uint16_t v_lo_116_, uint16_t v_hi_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_118_ = lean_uint16_to_nat(v_hi_117_);
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_add(v___x_118_, v___x_119_);
v___x_121_ = lean_uint16_to_nat(v_lo_116_);
v___x_122_ = lean_nat_sub(v___x_120_, v___x_121_);
lean_dec(v___x_120_);
return v___x_122_;
}
}
LEAN_EXPORT void l_UInt16_instHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_lo_116_ = stack[0].m_num;
uint16_t v_hi_117_ = stack[1].m_num;
lean_object* v_res_123_;
v_res_123_ = l_UInt16_instHasSize___lam__0(v_lo_116_, v_hi_117_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize___lam__0___boxed(lean_object* v_lo_124_, lean_object* v_hi_125_){
_start:
{
uint16_t v_lo_boxed_126_; uint16_t v_hi_boxed_127_; lean_object* v_res_128_; 
v_lo_boxed_126_ = lean_unbox(v_lo_124_);
v_hi_boxed_127_ = lean_unbox(v_hi_125_);
v_res_128_ = l_UInt16_instHasSize___lam__0(v_lo_boxed_126_, v_hi_boxed_127_);
return v_res_128_;
}
}
lean_object* l_UInt16_instHasSize__1___lam__0(uint16_t v_lo_131_, uint16_t v_hi_132_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_133_ = lean_uint16_to_nat(v_hi_132_);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_add(v___x_133_, v___x_134_);
v___x_136_ = lean_uint16_to_nat(v_lo_131_);
v___x_137_ = lean_nat_sub(v___x_135_, v___x_136_);
lean_dec(v___x_135_);
v___x_138_ = lean_nat_sub(v___x_137_, v___x_134_);
lean_dec(v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT void l_UInt16_instHasSize__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_lo_131_ = stack[0].m_num;
uint16_t v_hi_132_ = stack[1].m_num;
lean_object* v_res_139_;
v_res_139_ = l_UInt16_instHasSize__1___lam__0(v_lo_131_, v_hi_132_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize__1___lam__0___boxed(lean_object* v_lo_140_, lean_object* v_hi_141_){
_start:
{
uint16_t v_lo_boxed_142_; uint16_t v_hi_boxed_143_; lean_object* v_res_144_; 
v_lo_boxed_142_ = lean_unbox(v_lo_140_);
v_hi_boxed_143_ = lean_unbox(v_hi_141_);
v_res_144_ = l_UInt16_instHasSize__1___lam__0(v_lo_boxed_142_, v_hi_boxed_143_);
return v_res_144_;
}
}
lean_object* l_UInt16_instHasSize__2___lam__0(uint16_t v_lo_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(65536u);
v___x_149_ = lean_uint16_to_nat(v_lo_147_);
v___x_150_ = lean_nat_sub(v___x_148_, v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT void l_UInt16_instHasSize__2___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_lo_147_ = stack[0].m_num;
lean_object* v_res_151_;
v_res_151_ = l_UInt16_instHasSize__2___lam__0(v_lo_147_);
stack->m_obj
 = v_res_151_;
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize__2___lam__0___boxed(lean_object* v_lo_152_){
_start:
{
uint16_t v_lo_boxed_153_; lean_object* v_res_154_; 
v_lo_boxed_153_ = lean_unbox(v_lo_152_);
v_res_154_ = l_UInt16_instHasSize__2___lam__0(v_lo_boxed_153_);
return v_res_154_;
}
}
lean_object* l_UInt32_instUpwardEnumerable___lam__0(uint32_t v_i_157_){
_start:
{
uint32_t v___x_158_; uint32_t v___x_159_; uint32_t v___x_160_; uint8_t v___x_161_; 
v___x_158_ = 1;
v___x_159_ = lean_uint32_add(v_i_157_, v___x_158_);
v___x_160_ = 0;
v___x_161_ = lean_uint32_dec_eq(v___x_159_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_box_uint32(v___x_159_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = lean_box(0);
return v___x_164_;
}
}
}
LEAN_EXPORT void l_UInt32_instUpwardEnumerable___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_i_157_ = stack[0].m_num;
lean_object* v_res_165_;
v_res_165_ = l_UInt32_instUpwardEnumerable___lam__0(v_i_157_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_166_){
_start:
{
uint32_t v_i_boxed_167_; lean_object* v_res_168_; 
v_i_boxed_167_ = lean_unbox_uint32(v_i_166_);
lean_dec(v_i_166_);
v_res_168_ = l_UInt32_instUpwardEnumerable___lam__0(v_i_boxed_167_);
return v_res_168_;
}
}
lean_object* l_UInt32_instUpwardEnumerable___lam__1(lean_object* v_n_169_, uint32_t v_i_170_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_171_ = lean_uint32_to_nat(v_i_170_);
v___x_172_ = lean_nat_add(v___x_171_, v_n_169_);
lean_dec(v___x_171_);
v___x_173_ = lean_cstr_to_nat("4294967296");
v___x_174_ = lean_nat_dec_lt(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
uint32_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_uint32_of_nat(v___x_172_);
lean_dec(v___x_172_);
v___x_177_ = lean_box_uint32(v___x_176_);
v___x_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
}
LEAN_EXPORT void l_UInt32_instUpwardEnumerable___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_169_ = stack[0].m_obj;
uint32_t v_i_170_ = stack[1].m_num;
lean_object* v_res_179_;
v_res_179_ = l_UInt32_instUpwardEnumerable___lam__1(v_n_169_, v_i_170_);
stack->m_obj
 = v_res_179_;
}
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_180_, lean_object* v_i_181_){
_start:
{
uint32_t v_i_boxed_182_; lean_object* v_res_183_; 
v_i_boxed_182_ = lean_unbox_uint32(v_i_181_);
lean_dec(v_i_181_);
v_res_183_ = l_UInt32_instUpwardEnumerable___lam__1(v_n_180_, v_i_boxed_182_);
lean_dec(v_n_180_);
return v_res_183_;
}
}
static lean_object* _init_l_UInt32_instLeast_x3f___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_190_; lean_object* v___x_191_; 
v___x_190_ = 0;
v___x_191_ = lean_box_uint32(v___x_190_);
return v___x_191_;
}
}
static lean_object* _init_l_UInt32_instLeast_x3f___closed__0(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = l_UInt32_instLeast_x3f___closed__0___boxed__const__1;
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_UInt32_instLeast_x3f(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_obj_once(&l_UInt32_instLeast_x3f___closed__0, &l_UInt32_instLeast_x3f___closed__0_once, _init_l_UInt32_instLeast_x3f___closed__0);
return v___x_194_;
}
}
lean_object* l_UInt32_instHasSize___lam__0(uint32_t v_lo_195_, uint32_t v_hi_196_){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_197_ = lean_uint32_to_nat(v_hi_196_);
v___x_198_ = lean_unsigned_to_nat(1u);
v___x_199_ = lean_nat_add(v___x_197_, v___x_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_uint32_to_nat(v_lo_195_);
v___x_201_ = lean_nat_sub(v___x_199_, v___x_200_);
lean_dec(v___x_200_);
lean_dec(v___x_199_);
return v___x_201_;
}
}
LEAN_EXPORT void l_UInt32_instHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_lo_195_ = stack[0].m_num;
uint32_t v_hi_196_ = stack[1].m_num;
lean_object* v_res_202_;
v_res_202_ = l_UInt32_instHasSize___lam__0(v_lo_195_, v_hi_196_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize___lam__0___boxed(lean_object* v_lo_203_, lean_object* v_hi_204_){
_start:
{
uint32_t v_lo_boxed_205_; uint32_t v_hi_boxed_206_; lean_object* v_res_207_; 
v_lo_boxed_205_ = lean_unbox_uint32(v_lo_203_);
lean_dec(v_lo_203_);
v_hi_boxed_206_ = lean_unbox_uint32(v_hi_204_);
lean_dec(v_hi_204_);
v_res_207_ = l_UInt32_instHasSize___lam__0(v_lo_boxed_205_, v_hi_boxed_206_);
return v_res_207_;
}
}
lean_object* l_UInt32_instHasSize__1___lam__0(uint32_t v_lo_210_, uint32_t v_hi_211_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_212_ = lean_uint32_to_nat(v_hi_211_);
v___x_213_ = lean_unsigned_to_nat(1u);
v___x_214_ = lean_nat_add(v___x_212_, v___x_213_);
lean_dec(v___x_212_);
v___x_215_ = lean_uint32_to_nat(v_lo_210_);
v___x_216_ = lean_nat_sub(v___x_214_, v___x_215_);
lean_dec(v___x_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_nat_sub(v___x_216_, v___x_213_);
lean_dec(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT void l_UInt32_instHasSize__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_lo_210_ = stack[0].m_num;
uint32_t v_hi_211_ = stack[1].m_num;
lean_object* v_res_218_;
v_res_218_ = l_UInt32_instHasSize__1___lam__0(v_lo_210_, v_hi_211_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize__1___lam__0___boxed(lean_object* v_lo_219_, lean_object* v_hi_220_){
_start:
{
uint32_t v_lo_boxed_221_; uint32_t v_hi_boxed_222_; lean_object* v_res_223_; 
v_lo_boxed_221_ = lean_unbox_uint32(v_lo_219_);
lean_dec(v_lo_219_);
v_hi_boxed_222_ = lean_unbox_uint32(v_hi_220_);
lean_dec(v_hi_220_);
v_res_223_ = l_UInt32_instHasSize__1___lam__0(v_lo_boxed_221_, v_hi_boxed_222_);
return v_res_223_;
}
}
lean_object* l_UInt32_instHasSize__2___lam__0(uint32_t v_lo_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_cstr_to_nat("4294967296");
v___x_228_ = lean_uint32_to_nat(v_lo_226_);
v___x_229_ = lean_nat_sub(v___x_227_, v___x_228_);
lean_dec(v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT void l_UInt32_instHasSize__2___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_lo_226_ = stack[0].m_num;
lean_object* v_res_230_;
v_res_230_ = l_UInt32_instHasSize__2___lam__0(v_lo_226_);
stack->m_obj
 = v_res_230_;
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize__2___lam__0___boxed(lean_object* v_lo_231_){
_start:
{
uint32_t v_lo_boxed_232_; lean_object* v_res_233_; 
v_lo_boxed_232_ = lean_unbox_uint32(v_lo_231_);
lean_dec(v_lo_231_);
v_res_233_ = l_UInt32_instHasSize__2___lam__0(v_lo_boxed_232_);
return v_res_233_;
}
}
lean_object* l_UInt64_instUpwardEnumerable___lam__0(uint64_t v_i_236_){
_start:
{
uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; uint8_t v___x_240_; 
v___x_237_ = 1ULL;
v___x_238_ = lean_uint64_add(v_i_236_, v___x_237_);
v___x_239_ = 0ULL;
v___x_240_ = lean_uint64_dec_eq(v___x_238_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_box_uint64(v___x_238_);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
else
{
lean_object* v___x_243_; 
v___x_243_ = lean_box(0);
return v___x_243_;
}
}
}
LEAN_EXPORT void l_UInt64_instUpwardEnumerable___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_i_236_ = stack[0].m_num;
lean_object* v_res_244_;
v_res_244_ = l_UInt64_instUpwardEnumerable___lam__0(v_i_236_);
stack->m_obj
 = v_res_244_;
}
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_245_){
_start:
{
uint64_t v_i_boxed_246_; lean_object* v_res_247_; 
v_i_boxed_246_ = lean_unbox_uint64(v_i_245_);
lean_dec_ref(v_i_245_);
v_res_247_ = l_UInt64_instUpwardEnumerable___lam__0(v_i_boxed_246_);
return v_res_247_;
}
}
static lean_object* _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0(void){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_cstr_to_nat("18446744073709551616");
return v___x_248_;
}
}
lean_object* l_UInt64_instUpwardEnumerable___lam__1(lean_object* v_n_249_, uint64_t v_i_250_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_251_ = lean_uint64_to_nat(v_i_250_);
v___x_252_ = lean_nat_add(v___x_251_, v_n_249_);
lean_dec(v___x_251_);
v___x_253_ = lean_obj_once(&l_UInt64_instUpwardEnumerable___lam__1___closed__0, &l_UInt64_instUpwardEnumerable___lam__1___closed__0_once, _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0);
v___x_254_ = lean_nat_dec_lt(v___x_252_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
return v___x_255_;
}
else
{
uint64_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_uint64_of_nat(v___x_252_);
lean_dec(v___x_252_);
v___x_257_ = lean_box_uint64(v___x_256_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
}
LEAN_EXPORT void l_UInt64_instUpwardEnumerable___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_249_ = stack[0].m_obj;
uint64_t v_i_250_ = stack[1].m_num;
lean_object* v_res_259_;
v_res_259_ = l_UInt64_instUpwardEnumerable___lam__1(v_n_249_, v_i_250_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_260_, lean_object* v_i_261_){
_start:
{
uint64_t v_i_boxed_262_; lean_object* v_res_263_; 
v_i_boxed_262_ = lean_unbox_uint64(v_i_261_);
lean_dec_ref(v_i_261_);
v_res_263_ = l_UInt64_instUpwardEnumerable___lam__1(v_n_260_, v_i_boxed_262_);
lean_dec(v_n_260_);
return v_res_263_;
}
}
lean_object* l_UInt64_instHasSize___lam__0(uint64_t v_lo_275_, uint64_t v_hi_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_277_ = lean_uint64_to_nat(v_hi_276_);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v___x_277_, v___x_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_uint64_to_nat(v_lo_275_);
v___x_281_ = lean_nat_sub(v___x_279_, v___x_280_);
lean_dec(v___x_280_);
lean_dec(v___x_279_);
return v___x_281_;
}
}
LEAN_EXPORT void l_UInt64_instHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_lo_275_ = stack[0].m_num;
uint64_t v_hi_276_ = stack[1].m_num;
lean_object* v_res_282_;
v_res_282_ = l_UInt64_instHasSize___lam__0(v_lo_275_, v_hi_276_);
stack->m_obj
 = v_res_282_;
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize___lam__0___boxed(lean_object* v_lo_283_, lean_object* v_hi_284_){
_start:
{
uint64_t v_lo_boxed_285_; uint64_t v_hi_boxed_286_; lean_object* v_res_287_; 
v_lo_boxed_285_ = lean_unbox_uint64(v_lo_283_);
lean_dec_ref(v_lo_283_);
v_hi_boxed_286_ = lean_unbox_uint64(v_hi_284_);
lean_dec_ref(v_hi_284_);
v_res_287_ = l_UInt64_instHasSize___lam__0(v_lo_boxed_285_, v_hi_boxed_286_);
return v_res_287_;
}
}
lean_object* l_UInt64_instHasSize__1___lam__0(uint64_t v_lo_290_, uint64_t v_hi_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_292_ = lean_uint64_to_nat(v_hi_291_);
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_add(v___x_292_, v___x_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_uint64_to_nat(v_lo_290_);
v___x_296_ = lean_nat_sub(v___x_294_, v___x_295_);
lean_dec(v___x_295_);
lean_dec(v___x_294_);
v___x_297_ = lean_nat_sub(v___x_296_, v___x_293_);
lean_dec(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT void l_UInt64_instHasSize__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_lo_290_ = stack[0].m_num;
uint64_t v_hi_291_ = stack[1].m_num;
lean_object* v_res_298_;
v_res_298_ = l_UInt64_instHasSize__1___lam__0(v_lo_290_, v_hi_291_);
stack->m_obj
 = v_res_298_;
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize__1___lam__0___boxed(lean_object* v_lo_299_, lean_object* v_hi_300_){
_start:
{
uint64_t v_lo_boxed_301_; uint64_t v_hi_boxed_302_; lean_object* v_res_303_; 
v_lo_boxed_301_ = lean_unbox_uint64(v_lo_299_);
lean_dec_ref(v_lo_299_);
v_hi_boxed_302_ = lean_unbox_uint64(v_hi_300_);
lean_dec_ref(v_hi_300_);
v_res_303_ = l_UInt64_instHasSize__1___lam__0(v_lo_boxed_301_, v_hi_boxed_302_);
return v_res_303_;
}
}
lean_object* l_UInt64_instHasSize__2___lam__0(uint64_t v_lo_306_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_obj_once(&l_UInt64_instUpwardEnumerable___lam__1___closed__0, &l_UInt64_instUpwardEnumerable___lam__1___closed__0_once, _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0);
v___x_308_ = lean_uint64_to_nat(v_lo_306_);
v___x_309_ = lean_nat_sub(v___x_307_, v___x_308_);
lean_dec(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT void l_UInt64_instHasSize__2___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_lo_306_ = stack[0].m_num;
lean_object* v_res_310_;
v_res_310_ = l_UInt64_instHasSize__2___lam__0(v_lo_306_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize__2___lam__0___boxed(lean_object* v_lo_311_){
_start:
{
uint64_t v_lo_boxed_312_; lean_object* v_res_313_; 
v_lo_boxed_312_ = lean_unbox_uint64(v_lo_311_);
lean_dec_ref(v_lo_311_);
v_res_313_ = l_UInt64_instHasSize__2___lam__0(v_lo_boxed_312_);
return v_res_313_;
}
}
lean_object* l_USize_instUpwardEnumerable___lam__0(size_t v_i_316_){
_start:
{
size_t v___x_317_; size_t v___x_318_; size_t v___x_319_; uint8_t v___x_320_; 
v___x_317_ = ((size_t)1ULL);
v___x_318_ = lean_usize_add(v_i_316_, v___x_317_);
v___x_319_ = ((size_t)0ULL);
v___x_320_ = lean_usize_dec_eq(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_box_usize(v___x_318_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
else
{
lean_object* v___x_323_; 
v___x_323_ = lean_box(0);
return v___x_323_;
}
}
}
LEAN_EXPORT void l_USize_instUpwardEnumerable___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_316_ = stack[0].m_num;
lean_object* v_res_324_;
v_res_324_ = l_USize_instUpwardEnumerable___lam__0(v_i_316_);
stack->m_obj
 = v_res_324_;
}
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_325_){
_start:
{
size_t v_i_boxed_326_; lean_object* v_res_327_; 
v_i_boxed_326_ = lean_unbox_usize(v_i_325_);
lean_dec(v_i_325_);
v_res_327_ = l_USize_instUpwardEnumerable___lam__0(v_i_boxed_326_);
return v_res_327_;
}
}
static lean_object* _init_l_USize_instUpwardEnumerable___lam__1___closed__0(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = l_System_Platform_numBits;
v___x_329_ = lean_unsigned_to_nat(2u);
v___x_330_ = lean_nat_pow(v___x_329_, v___x_328_);
return v___x_330_;
}
}
lean_object* l_USize_instUpwardEnumerable___lam__1(lean_object* v_n_331_, size_t v_i_332_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_333_ = lean_usize_to_nat(v_i_332_);
v___x_334_ = lean_nat_add(v___x_333_, v_n_331_);
lean_dec(v___x_333_);
v___x_335_ = lean_obj_once(&l_USize_instUpwardEnumerable___lam__1___closed__0, &l_USize_instUpwardEnumerable___lam__1___closed__0_once, _init_l_USize_instUpwardEnumerable___lam__1___closed__0);
v___x_336_ = lean_nat_dec_lt(v___x_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_object* v___x_337_; 
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
return v___x_337_;
}
else
{
size_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = lean_usize_of_nat(v___x_334_);
lean_dec(v___x_334_);
v___x_339_ = lean_box_usize(v___x_338_);
v___x_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
}
LEAN_EXPORT void l_USize_instUpwardEnumerable___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_331_ = stack[0].m_obj;
size_t v_i_332_ = stack[1].m_num;
lean_object* v_res_341_;
v_res_341_ = l_USize_instUpwardEnumerable___lam__1(v_n_331_, v_i_332_);
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_342_, lean_object* v_i_343_){
_start:
{
size_t v_i_boxed_344_; lean_object* v_res_345_; 
v_i_boxed_344_ = lean_unbox_usize(v_i_343_);
lean_dec(v_i_343_);
v_res_345_ = l_USize_instUpwardEnumerable___lam__1(v_n_342_, v_i_boxed_344_);
lean_dec(v_n_342_);
return v_res_345_;
}
}
lean_object* l_USize_instHasSize___lam__0(size_t v_lo_357_, size_t v_hi_358_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_359_ = lean_usize_to_nat(v_hi_358_);
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = lean_nat_add(v___x_359_, v___x_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_usize_to_nat(v_lo_357_);
v___x_363_ = lean_nat_sub(v___x_361_, v___x_362_);
lean_dec(v___x_362_);
lean_dec(v___x_361_);
return v___x_363_;
}
}
LEAN_EXPORT void l_USize_instHasSize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_lo_357_ = stack[0].m_num;
size_t v_hi_358_ = stack[1].m_num;
lean_object* v_res_364_;
v_res_364_ = l_USize_instHasSize___lam__0(v_lo_357_, v_hi_358_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l_USize_instHasSize___lam__0___boxed(lean_object* v_lo_365_, lean_object* v_hi_366_){
_start:
{
size_t v_lo_boxed_367_; size_t v_hi_boxed_368_; lean_object* v_res_369_; 
v_lo_boxed_367_ = lean_unbox_usize(v_lo_365_);
lean_dec(v_lo_365_);
v_hi_boxed_368_ = lean_unbox_usize(v_hi_366_);
lean_dec(v_hi_366_);
v_res_369_ = l_USize_instHasSize___lam__0(v_lo_boxed_367_, v_hi_boxed_368_);
return v_res_369_;
}
}
lean_object* l_USize_instHasSize__1___lam__0(size_t v_lo_372_, size_t v_hi_373_){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_374_ = lean_usize_to_nat(v_hi_373_);
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = lean_nat_add(v___x_374_, v___x_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_usize_to_nat(v_lo_372_);
v___x_378_ = lean_nat_sub(v___x_376_, v___x_377_);
lean_dec(v___x_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_nat_sub(v___x_378_, v___x_375_);
lean_dec(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT void l_USize_instHasSize__1___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_lo_372_ = stack[0].m_num;
size_t v_hi_373_ = stack[1].m_num;
lean_object* v_res_380_;
v_res_380_ = l_USize_instHasSize__1___lam__0(v_lo_372_, v_hi_373_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l_USize_instHasSize__1___lam__0___boxed(lean_object* v_lo_381_, lean_object* v_hi_382_){
_start:
{
size_t v_lo_boxed_383_; size_t v_hi_boxed_384_; lean_object* v_res_385_; 
v_lo_boxed_383_ = lean_unbox_usize(v_lo_381_);
lean_dec(v_lo_381_);
v_hi_boxed_384_ = lean_unbox_usize(v_hi_382_);
lean_dec(v_hi_382_);
v_res_385_ = l_USize_instHasSize__1___lam__0(v_lo_boxed_383_, v_hi_boxed_384_);
return v_res_385_;
}
}
lean_object* l_USize_instHasSize__2___lam__0(size_t v_lo_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = lean_obj_once(&l_USize_instUpwardEnumerable___lam__1___closed__0, &l_USize_instUpwardEnumerable___lam__1___closed__0_once, _init_l_USize_instUpwardEnumerable___lam__1___closed__0);
v___x_390_ = lean_usize_to_nat(v_lo_388_);
v___x_391_ = lean_nat_sub(v___x_389_, v___x_390_);
lean_dec(v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT void l_USize_instHasSize__2___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_lo_388_ = stack[0].m_num;
lean_object* v_res_392_;
v_res_392_ = l_USize_instHasSize__2___lam__0(v_lo_388_);
stack->m_obj
 = v_res_392_;
}
LEAN_EXPORT lean_object* l_USize_instHasSize__2___lam__0___boxed(lean_object* v_lo_393_){
_start:
{
size_t v_lo_boxed_394_; lean_object* v_res_395_; 
v_lo_boxed_394_ = lean_unbox_usize(v_lo_393_);
lean_dec(v_lo_393_);
v_res_395_ = l_USize_instHasSize__2___lam__0(v_lo_boxed_394_);
return v_res_395_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_BitVec(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_UInt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_UInt32_instLeast_x3f___closed__0___boxed__const__1 = _init_l_UInt32_instLeast_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l_UInt32_instLeast_x3f___closed__0___boxed__const__1);
l_UInt32_instLeast_x3f = _init_l_UInt32_instLeast_x3f();
lean_mark_persistent(l_UInt32_instLeast_x3f);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_UInt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range_Polymorphic_BitVec(uint8_t builtin);
lean_object* initialize_Init_Data_UInt(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_UInt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_UInt(builtin);
}
#ifdef __cplusplus
}
#endif
