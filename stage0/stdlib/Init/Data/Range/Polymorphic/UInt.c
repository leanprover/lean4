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
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__0(uint8_t v_i_1_){
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
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_9_){
_start:
{
uint8_t v_i_boxed_10_; lean_object* v_res_11_; 
v_i_boxed_10_ = lean_unbox(v_i_9_);
v_res_11_ = l_UInt8_instUpwardEnumerable___lam__0(v_i_boxed_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__1(lean_object* v_n_12_, uint8_t v_i_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_14_ = lean_uint8_to_nat(v_i_13_);
v___x_15_ = lean_nat_add(v___x_14_, v_n_12_);
v___x_16_ = lean_unsigned_to_nat(256u);
v___x_17_ = lean_nat_dec_lt(v___x_15_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; 
lean_dec(v___x_15_);
v___x_18_ = lean_box(0);
return v___x_18_;
}
else
{
uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_19_ = lean_uint8_of_nat(v___x_15_);
lean_dec(v___x_15_);
v___x_20_ = lean_box(v___x_19_);
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_22_, lean_object* v_i_23_){
_start:
{
uint8_t v_i_boxed_24_; lean_object* v_res_25_; 
v_i_boxed_24_ = lean_unbox(v_i_23_);
v_res_25_ = l_UInt8_instUpwardEnumerable___lam__1(v_n_22_, v_i_boxed_24_);
lean_dec(v_n_22_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize___lam__0(uint8_t v_lo_36_, uint8_t v_hi_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_38_ = lean_uint8_to_nat(v_hi_37_);
v___x_39_ = lean_unsigned_to_nat(1u);
v___x_40_ = lean_nat_add(v___x_38_, v___x_39_);
v___x_41_ = lean_uint8_to_nat(v_lo_36_);
v___x_42_ = lean_nat_sub(v___x_40_, v___x_41_);
lean_dec(v___x_40_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize___lam__0___boxed(lean_object* v_lo_43_, lean_object* v_hi_44_){
_start:
{
uint8_t v_lo_boxed_45_; uint8_t v_hi_boxed_46_; lean_object* v_res_47_; 
v_lo_boxed_45_ = lean_unbox(v_lo_43_);
v_hi_boxed_46_ = lean_unbox(v_hi_44_);
v_res_47_ = l_UInt8_instHasSize___lam__0(v_lo_boxed_45_, v_hi_boxed_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize__1___lam__0(uint8_t v_lo_50_, uint8_t v_hi_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_52_ = lean_uint8_to_nat(v_hi_51_);
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_add(v___x_52_, v___x_53_);
v___x_55_ = lean_uint8_to_nat(v_lo_50_);
v___x_56_ = lean_nat_sub(v___x_54_, v___x_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_nat_sub(v___x_56_, v___x_53_);
lean_dec(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize__1___lam__0___boxed(lean_object* v_lo_58_, lean_object* v_hi_59_){
_start:
{
uint8_t v_lo_boxed_60_; uint8_t v_hi_boxed_61_; lean_object* v_res_62_; 
v_lo_boxed_60_ = lean_unbox(v_lo_58_);
v_hi_boxed_61_ = lean_unbox(v_hi_59_);
v_res_62_ = l_UInt8_instHasSize__1___lam__0(v_lo_boxed_60_, v_hi_boxed_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize__2___lam__0(uint8_t v_lo_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_unsigned_to_nat(256u);
v___x_67_ = lean_uint8_to_nat(v_lo_65_);
v___x_68_ = lean_nat_sub(v___x_66_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize__2___lam__0___boxed(lean_object* v_lo_69_){
_start:
{
uint8_t v_lo_boxed_70_; lean_object* v_res_71_; 
v_lo_boxed_70_ = lean_unbox(v_lo_69_);
v_res_71_ = l_UInt8_instHasSize__2___lam__0(v_lo_boxed_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__0(uint16_t v_i_74_){
_start:
{
uint16_t v___x_75_; uint16_t v___x_76_; uint16_t v___x_77_; uint8_t v___x_78_; 
v___x_75_ = 1;
v___x_76_ = lean_uint16_add(v_i_74_, v___x_75_);
v___x_77_ = 0;
v___x_78_ = lean_uint16_dec_eq(v___x_76_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_box(v___x_76_);
v___x_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
return v___x_80_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(0);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_82_){
_start:
{
uint16_t v_i_boxed_83_; lean_object* v_res_84_; 
v_i_boxed_83_ = lean_unbox(v_i_82_);
v_res_84_ = l_UInt16_instUpwardEnumerable___lam__0(v_i_boxed_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__1(lean_object* v_n_85_, uint16_t v_i_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_87_ = lean_uint16_to_nat(v_i_86_);
v___x_88_ = lean_nat_add(v___x_87_, v_n_85_);
v___x_89_ = lean_unsigned_to_nat(65536u);
v___x_90_ = lean_nat_dec_lt(v___x_88_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
return v___x_91_;
}
else
{
uint16_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_uint16_of_nat(v___x_88_);
lean_dec(v___x_88_);
v___x_93_ = lean_box(v___x_92_);
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_95_, lean_object* v_i_96_){
_start:
{
uint16_t v_i_boxed_97_; lean_object* v_res_98_; 
v_i_boxed_97_ = lean_unbox(v_i_96_);
v_res_98_ = l_UInt16_instUpwardEnumerable___lam__1(v_n_95_, v_i_boxed_97_);
lean_dec(v_n_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize___lam__0(uint16_t v_lo_109_, uint16_t v_hi_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_111_ = lean_uint16_to_nat(v_hi_110_);
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = lean_nat_add(v___x_111_, v___x_112_);
v___x_114_ = lean_uint16_to_nat(v_lo_109_);
v___x_115_ = lean_nat_sub(v___x_113_, v___x_114_);
lean_dec(v___x_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize___lam__0___boxed(lean_object* v_lo_116_, lean_object* v_hi_117_){
_start:
{
uint16_t v_lo_boxed_118_; uint16_t v_hi_boxed_119_; lean_object* v_res_120_; 
v_lo_boxed_118_ = lean_unbox(v_lo_116_);
v_hi_boxed_119_ = lean_unbox(v_hi_117_);
v_res_120_ = l_UInt16_instHasSize___lam__0(v_lo_boxed_118_, v_hi_boxed_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize__1___lam__0(uint16_t v_lo_123_, uint16_t v_hi_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_125_ = lean_uint16_to_nat(v_hi_124_);
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_add(v___x_125_, v___x_126_);
v___x_128_ = lean_uint16_to_nat(v_lo_123_);
v___x_129_ = lean_nat_sub(v___x_127_, v___x_128_);
lean_dec(v___x_127_);
v___x_130_ = lean_nat_sub(v___x_129_, v___x_126_);
lean_dec(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize__1___lam__0___boxed(lean_object* v_lo_131_, lean_object* v_hi_132_){
_start:
{
uint16_t v_lo_boxed_133_; uint16_t v_hi_boxed_134_; lean_object* v_res_135_; 
v_lo_boxed_133_ = lean_unbox(v_lo_131_);
v_hi_boxed_134_ = lean_unbox(v_hi_132_);
v_res_135_ = l_UInt16_instHasSize__1___lam__0(v_lo_boxed_133_, v_hi_boxed_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize__2___lam__0(uint16_t v_lo_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_unsigned_to_nat(65536u);
v___x_140_ = lean_uint16_to_nat(v_lo_138_);
v___x_141_ = lean_nat_sub(v___x_139_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize__2___lam__0___boxed(lean_object* v_lo_142_){
_start:
{
uint16_t v_lo_boxed_143_; lean_object* v_res_144_; 
v_lo_boxed_143_ = lean_unbox(v_lo_142_);
v_res_144_ = l_UInt16_instHasSize__2___lam__0(v_lo_boxed_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__0(uint32_t v_i_147_){
_start:
{
uint32_t v___x_148_; uint32_t v___x_149_; uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_148_ = 1;
v___x_149_ = lean_uint32_add(v_i_147_, v___x_148_);
v___x_150_ = 0;
v___x_151_ = lean_uint32_dec_eq(v___x_149_, v___x_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_box_uint32(v___x_149_);
v___x_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; 
v___x_154_ = lean_box(0);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_155_){
_start:
{
uint32_t v_i_boxed_156_; lean_object* v_res_157_; 
v_i_boxed_156_ = lean_unbox_uint32(v_i_155_);
lean_dec(v_i_155_);
v_res_157_ = l_UInt32_instUpwardEnumerable___lam__0(v_i_boxed_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__1(lean_object* v_n_158_, uint32_t v_i_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_160_ = lean_uint32_to_nat(v_i_159_);
v___x_161_ = lean_nat_add(v___x_160_, v_n_158_);
lean_dec(v___x_160_);
v___x_162_ = lean_cstr_to_nat("4294967296");
v___x_163_ = lean_nat_dec_lt(v___x_161_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
return v___x_164_;
}
else
{
uint32_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_uint32_of_nat(v___x_161_);
lean_dec(v___x_161_);
v___x_166_ = lean_box_uint32(v___x_165_);
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_168_, lean_object* v_i_169_){
_start:
{
uint32_t v_i_boxed_170_; lean_object* v_res_171_; 
v_i_boxed_170_ = lean_unbox_uint32(v_i_169_);
lean_dec(v_i_169_);
v_res_171_ = l_UInt32_instUpwardEnumerable___lam__1(v_n_168_, v_i_boxed_170_);
lean_dec(v_n_168_);
return v_res_171_;
}
}
static lean_object* _init_l_UInt32_instLeast_x3f___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_178_; lean_object* v___x_179_; 
v___x_178_ = 0;
v___x_179_ = lean_box_uint32(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_UInt32_instLeast_x3f___closed__0(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = l_UInt32_instLeast_x3f___closed__0___boxed__const__1;
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_UInt32_instLeast_x3f(void){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_UInt32_instLeast_x3f___closed__0, &l_UInt32_instLeast_x3f___closed__0_once, _init_l_UInt32_instLeast_x3f___closed__0);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize___lam__0(uint32_t v_lo_183_, uint32_t v_hi_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_185_ = lean_uint32_to_nat(v_hi_184_);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v___x_185_, v___x_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_uint32_to_nat(v_lo_183_);
v___x_189_ = lean_nat_sub(v___x_187_, v___x_188_);
lean_dec(v___x_188_);
lean_dec(v___x_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize___lam__0___boxed(lean_object* v_lo_190_, lean_object* v_hi_191_){
_start:
{
uint32_t v_lo_boxed_192_; uint32_t v_hi_boxed_193_; lean_object* v_res_194_; 
v_lo_boxed_192_ = lean_unbox_uint32(v_lo_190_);
lean_dec(v_lo_190_);
v_hi_boxed_193_ = lean_unbox_uint32(v_hi_191_);
lean_dec(v_hi_191_);
v_res_194_ = l_UInt32_instHasSize___lam__0(v_lo_boxed_192_, v_hi_boxed_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize__1___lam__0(uint32_t v_lo_197_, uint32_t v_hi_198_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_199_ = lean_uint32_to_nat(v_hi_198_);
v___x_200_ = lean_unsigned_to_nat(1u);
v___x_201_ = lean_nat_add(v___x_199_, v___x_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_uint32_to_nat(v_lo_197_);
v___x_203_ = lean_nat_sub(v___x_201_, v___x_202_);
lean_dec(v___x_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_nat_sub(v___x_203_, v___x_200_);
lean_dec(v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize__1___lam__0___boxed(lean_object* v_lo_205_, lean_object* v_hi_206_){
_start:
{
uint32_t v_lo_boxed_207_; uint32_t v_hi_boxed_208_; lean_object* v_res_209_; 
v_lo_boxed_207_ = lean_unbox_uint32(v_lo_205_);
lean_dec(v_lo_205_);
v_hi_boxed_208_ = lean_unbox_uint32(v_hi_206_);
lean_dec(v_hi_206_);
v_res_209_ = l_UInt32_instHasSize__1___lam__0(v_lo_boxed_207_, v_hi_boxed_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize__2___lam__0(uint32_t v_lo_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_cstr_to_nat("4294967296");
v___x_214_ = lean_uint32_to_nat(v_lo_212_);
v___x_215_ = lean_nat_sub(v___x_213_, v___x_214_);
lean_dec(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize__2___lam__0___boxed(lean_object* v_lo_216_){
_start:
{
uint32_t v_lo_boxed_217_; lean_object* v_res_218_; 
v_lo_boxed_217_ = lean_unbox_uint32(v_lo_216_);
lean_dec(v_lo_216_);
v_res_218_ = l_UInt32_instHasSize__2___lam__0(v_lo_boxed_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__0(uint64_t v_i_221_){
_start:
{
uint64_t v___x_222_; uint64_t v___x_223_; uint64_t v___x_224_; uint8_t v___x_225_; 
v___x_222_ = 1ULL;
v___x_223_ = lean_uint64_add(v_i_221_, v___x_222_);
v___x_224_ = 0ULL;
v___x_225_ = lean_uint64_dec_eq(v___x_223_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_box_uint64(v___x_223_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
else
{
lean_object* v___x_228_; 
v___x_228_ = lean_box(0);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_229_){
_start:
{
uint64_t v_i_boxed_230_; lean_object* v_res_231_; 
v_i_boxed_230_ = lean_unbox_uint64(v_i_229_);
lean_dec_ref(v_i_229_);
v_res_231_ = l_UInt64_instUpwardEnumerable___lam__0(v_i_boxed_230_);
return v_res_231_;
}
}
static lean_object* _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0(void){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_cstr_to_nat("18446744073709551616");
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__1(lean_object* v_n_233_, uint64_t v_i_234_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_235_ = lean_uint64_to_nat(v_i_234_);
v___x_236_ = lean_nat_add(v___x_235_, v_n_233_);
lean_dec(v___x_235_);
v___x_237_ = lean_obj_once(&l_UInt64_instUpwardEnumerable___lam__1___closed__0, &l_UInt64_instUpwardEnumerable___lam__1___closed__0_once, _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0);
v___x_238_ = lean_nat_dec_lt(v___x_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
lean_dec(v___x_236_);
v___x_239_ = lean_box(0);
return v___x_239_;
}
else
{
uint64_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_uint64_of_nat(v___x_236_);
lean_dec(v___x_236_);
v___x_241_ = lean_box_uint64(v___x_240_);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_243_, lean_object* v_i_244_){
_start:
{
uint64_t v_i_boxed_245_; lean_object* v_res_246_; 
v_i_boxed_245_ = lean_unbox_uint64(v_i_244_);
lean_dec_ref(v_i_244_);
v_res_246_ = l_UInt64_instUpwardEnumerable___lam__1(v_n_243_, v_i_boxed_245_);
lean_dec(v_n_243_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize___lam__0(uint64_t v_lo_258_, uint64_t v_hi_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_260_ = lean_uint64_to_nat(v_hi_259_);
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_add(v___x_260_, v___x_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_uint64_to_nat(v_lo_258_);
v___x_264_ = lean_nat_sub(v___x_262_, v___x_263_);
lean_dec(v___x_263_);
lean_dec(v___x_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize___lam__0___boxed(lean_object* v_lo_265_, lean_object* v_hi_266_){
_start:
{
uint64_t v_lo_boxed_267_; uint64_t v_hi_boxed_268_; lean_object* v_res_269_; 
v_lo_boxed_267_ = lean_unbox_uint64(v_lo_265_);
lean_dec_ref(v_lo_265_);
v_hi_boxed_268_ = lean_unbox_uint64(v_hi_266_);
lean_dec_ref(v_hi_266_);
v_res_269_ = l_UInt64_instHasSize___lam__0(v_lo_boxed_267_, v_hi_boxed_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize__1___lam__0(uint64_t v_lo_272_, uint64_t v_hi_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_274_ = lean_uint64_to_nat(v_hi_273_);
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_add(v___x_274_, v___x_275_);
lean_dec(v___x_274_);
v___x_277_ = lean_uint64_to_nat(v_lo_272_);
v___x_278_ = lean_nat_sub(v___x_276_, v___x_277_);
lean_dec(v___x_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_nat_sub(v___x_278_, v___x_275_);
lean_dec(v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize__1___lam__0___boxed(lean_object* v_lo_280_, lean_object* v_hi_281_){
_start:
{
uint64_t v_lo_boxed_282_; uint64_t v_hi_boxed_283_; lean_object* v_res_284_; 
v_lo_boxed_282_ = lean_unbox_uint64(v_lo_280_);
lean_dec_ref(v_lo_280_);
v_hi_boxed_283_ = lean_unbox_uint64(v_hi_281_);
lean_dec_ref(v_hi_281_);
v_res_284_ = l_UInt64_instHasSize__1___lam__0(v_lo_boxed_282_, v_hi_boxed_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize__2___lam__0(uint64_t v_lo_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_obj_once(&l_UInt64_instUpwardEnumerable___lam__1___closed__0, &l_UInt64_instUpwardEnumerable___lam__1___closed__0_once, _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0);
v___x_289_ = lean_uint64_to_nat(v_lo_287_);
v___x_290_ = lean_nat_sub(v___x_288_, v___x_289_);
lean_dec(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize__2___lam__0___boxed(lean_object* v_lo_291_){
_start:
{
uint64_t v_lo_boxed_292_; lean_object* v_res_293_; 
v_lo_boxed_292_ = lean_unbox_uint64(v_lo_291_);
lean_dec_ref(v_lo_291_);
v_res_293_ = l_UInt64_instHasSize__2___lam__0(v_lo_boxed_292_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__0(size_t v_i_296_){
_start:
{
size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; uint8_t v___x_300_; 
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_add(v_i_296_, v___x_297_);
v___x_299_ = ((size_t)0ULL);
v___x_300_ = lean_usize_dec_eq(v___x_298_, v___x_299_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_box_usize(v___x_298_);
v___x_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_box(0);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__0___boxed(lean_object* v_i_304_){
_start:
{
size_t v_i_boxed_305_; lean_object* v_res_306_; 
v_i_boxed_305_ = lean_unbox_usize(v_i_304_);
lean_dec(v_i_304_);
v_res_306_ = l_USize_instUpwardEnumerable___lam__0(v_i_boxed_305_);
return v_res_306_;
}
}
static lean_object* _init_l_USize_instUpwardEnumerable___lam__1___closed__0(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = l_System_Platform_numBits;
v___x_308_ = lean_unsigned_to_nat(2u);
v___x_309_ = lean_nat_pow(v___x_308_, v___x_307_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__1(lean_object* v_n_310_, size_t v_i_311_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_312_ = lean_usize_to_nat(v_i_311_);
v___x_313_ = lean_nat_add(v___x_312_, v_n_310_);
lean_dec(v___x_312_);
v___x_314_ = lean_obj_once(&l_USize_instUpwardEnumerable___lam__1___closed__0, &l_USize_instUpwardEnumerable___lam__1___closed__0_once, _init_l_USize_instUpwardEnumerable___lam__1___closed__0);
v___x_315_ = lean_nat_dec_lt(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
return v___x_316_;
}
else
{
size_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_usize_of_nat(v___x_313_);
lean_dec(v___x_313_);
v___x_318_ = lean_box_usize(v___x_317_);
v___x_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__1___boxed(lean_object* v_n_320_, lean_object* v_i_321_){
_start:
{
size_t v_i_boxed_322_; lean_object* v_res_323_; 
v_i_boxed_322_ = lean_unbox_usize(v_i_321_);
lean_dec(v_i_321_);
v_res_323_ = l_USize_instUpwardEnumerable___lam__1(v_n_320_, v_i_boxed_322_);
lean_dec(v_n_320_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_USize_instHasSize___lam__0(size_t v_lo_335_, size_t v_hi_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_337_ = lean_usize_to_nat(v_hi_336_);
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = lean_nat_add(v___x_337_, v___x_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_usize_to_nat(v_lo_335_);
v___x_341_ = lean_nat_sub(v___x_339_, v___x_340_);
lean_dec(v___x_340_);
lean_dec(v___x_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_USize_instHasSize___lam__0___boxed(lean_object* v_lo_342_, lean_object* v_hi_343_){
_start:
{
size_t v_lo_boxed_344_; size_t v_hi_boxed_345_; lean_object* v_res_346_; 
v_lo_boxed_344_ = lean_unbox_usize(v_lo_342_);
lean_dec(v_lo_342_);
v_hi_boxed_345_ = lean_unbox_usize(v_hi_343_);
lean_dec(v_hi_343_);
v_res_346_ = l_USize_instHasSize___lam__0(v_lo_boxed_344_, v_hi_boxed_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_USize_instHasSize__1___lam__0(size_t v_lo_349_, size_t v_hi_350_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_351_ = lean_usize_to_nat(v_hi_350_);
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_add(v___x_351_, v___x_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_usize_to_nat(v_lo_349_);
v___x_355_ = lean_nat_sub(v___x_353_, v___x_354_);
lean_dec(v___x_354_);
lean_dec(v___x_353_);
v___x_356_ = lean_nat_sub(v___x_355_, v___x_352_);
lean_dec(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_USize_instHasSize__1___lam__0___boxed(lean_object* v_lo_357_, lean_object* v_hi_358_){
_start:
{
size_t v_lo_boxed_359_; size_t v_hi_boxed_360_; lean_object* v_res_361_; 
v_lo_boxed_359_ = lean_unbox_usize(v_lo_357_);
lean_dec(v_lo_357_);
v_hi_boxed_360_ = lean_unbox_usize(v_hi_358_);
lean_dec(v_hi_358_);
v_res_361_ = l_USize_instHasSize__1___lam__0(v_lo_boxed_359_, v_hi_boxed_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_USize_instHasSize__2___lam__0(size_t v_lo_364_){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = lean_obj_once(&l_USize_instUpwardEnumerable___lam__1___closed__0, &l_USize_instUpwardEnumerable___lam__1___closed__0_once, _init_l_USize_instUpwardEnumerable___lam__1___closed__0);
v___x_366_ = lean_usize_to_nat(v_lo_364_);
v___x_367_ = lean_nat_sub(v___x_365_, v___x_366_);
lean_dec(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_USize_instHasSize__2___lam__0___boxed(lean_object* v_lo_368_){
_start:
{
size_t v_lo_boxed_369_; lean_object* v_res_370_; 
v_lo_boxed_369_ = lean_unbox_usize(v_lo_368_);
lean_dec(v_lo_368_);
v_res_370_ = l_USize_instHasSize__2___lam__0(v_lo_boxed_369_);
return v_res_370_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_BitVec(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_UInt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
