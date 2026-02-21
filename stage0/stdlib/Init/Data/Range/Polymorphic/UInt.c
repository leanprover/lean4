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
uint8_t lean_uint8_add(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__0___boxed(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt8_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_instUpwardEnumerable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt8_instUpwardEnumerable___closed__0 = (const lean_object*)&l_UInt8_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_UInt8_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_instUpwardEnumerable___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt8_instUpwardEnumerable___closed__1 = (const lean_object*)&l_UInt8_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_UInt8_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_UInt8_instUpwardEnumerable___closed__0_value),((lean_object*)&l_UInt8_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_UInt8_instUpwardEnumerable___closed__2 = (const lean_object*)&l_UInt8_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_UInt8_instUpwardEnumerable = (const lean_object*)&l_UInt8_instUpwardEnumerable___closed__2_value;
static lean_once_cell_t l_UInt8_instLeast_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt8_instLeast_x3f___closed__0;
LEAN_EXPORT lean_object* l_UInt8_instLeast_x3f;
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
uint16_t lean_uint16_add(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__0___boxed(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
uint16_t lean_uint16_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__1(lean_object*, uint16_t);
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt16_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_instUpwardEnumerable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt16_instUpwardEnumerable___closed__0 = (const lean_object*)&l_UInt16_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_UInt16_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_instUpwardEnumerable___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt16_instUpwardEnumerable___closed__1 = (const lean_object*)&l_UInt16_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_UInt16_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_UInt16_instUpwardEnumerable___closed__0_value),((lean_object*)&l_UInt16_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_UInt16_instUpwardEnumerable___closed__2 = (const lean_object*)&l_UInt16_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_UInt16_instUpwardEnumerable = (const lean_object*)&l_UInt16_instUpwardEnumerable___closed__2_value;
static lean_once_cell_t l_UInt16_instLeast_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt16_instLeast_x3f___closed__0;
LEAN_EXPORT lean_object* l_UInt16_instLeast_x3f;
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
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__0___boxed(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint32_t lean_uint32_of_nat(lean_object*);
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
uint64_t lean_uint64_add(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__0___boxed(lean_object*);
static lean_once_cell_t l_UInt64_instUpwardEnumerable___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt64_instUpwardEnumerable___lam__1___closed__0;
lean_object* lean_uint64_to_nat(uint64_t);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__1(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_UInt64_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_instUpwardEnumerable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt64_instUpwardEnumerable___closed__0 = (const lean_object*)&l_UInt64_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_UInt64_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_instUpwardEnumerable___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_UInt64_instUpwardEnumerable___closed__1 = (const lean_object*)&l_UInt64_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_UInt64_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_UInt64_instUpwardEnumerable___closed__0_value),((lean_object*)&l_UInt64_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_UInt64_instUpwardEnumerable___closed__2 = (const lean_object*)&l_UInt64_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_UInt64_instUpwardEnumerable = (const lean_object*)&l_UInt64_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT lean_object* l_UInt64_instLeast_x3f___closed__0___boxed__const__1;
static lean_once_cell_t l_UInt64_instLeast_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_UInt64_instLeast_x3f___closed__0;
LEAN_EXPORT lean_object* l_UInt64_instLeast_x3f;
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__0(size_t);
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__0___boxed(lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
static lean_once_cell_t l_USize_instUpwardEnumerable___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_USize_instUpwardEnumerable___lam__1___closed__0;
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__1(lean_object*, size_t);
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_USize_instUpwardEnumerable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_instUpwardEnumerable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_USize_instUpwardEnumerable___closed__0 = (const lean_object*)&l_USize_instUpwardEnumerable___closed__0_value;
static const lean_closure_object l_USize_instUpwardEnumerable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_instUpwardEnumerable___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_USize_instUpwardEnumerable___closed__1 = (const lean_object*)&l_USize_instUpwardEnumerable___closed__1_value;
static const lean_ctor_object l_USize_instUpwardEnumerable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_USize_instUpwardEnumerable___closed__0_value),((lean_object*)&l_USize_instUpwardEnumerable___closed__1_value)}};
static const lean_object* l_USize_instUpwardEnumerable___closed__2 = (const lean_object*)&l_USize_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT const lean_object* l_USize_instUpwardEnumerable = (const lean_object*)&l_USize_instUpwardEnumerable___closed__2_value;
LEAN_EXPORT lean_object* l_USize_instLeast_x3f___closed__0___boxed__const__1;
static lean_once_cell_t l_USize_instLeast_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_USize_instLeast_x3f___closed__0;
LEAN_EXPORT lean_object* l_USize_instLeast_x3f;
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
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__0(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_2 = 1;
x_3 = lean_uint8_add(x_1, x_2);
x_4 = 0;
x_5 = lean_uint8_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_UInt8_instUpwardEnumerable___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__1(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_uint8_to_nat(x_2);
x_4 = lean_nat_add(x_3, x_1);
x_5 = lean_unsigned_to_nat(256u);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_uint8_of_nat(x_4);
lean_dec(x_4);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_UInt8_instUpwardEnumerable___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_UInt8_instUpwardEnumerable___lam__1(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_UInt8_instLeast_x3f___closed__0(void) {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_UInt8_instLeast_x3f(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_UInt8_instLeast_x3f___closed__0, &l_UInt8_instLeast_x3f___closed__0_once, _init_l_UInt8_instLeast_x3f___closed__0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_uint8_to_nat(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_uint8_to_nat(x_1);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_UInt8_instHasSize___lam__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize__1___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_uint8_to_nat(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_uint8_to_nat(x_1);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = lean_nat_sub(x_7, x_4);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_UInt8_instHasSize__1___lam__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize__2___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(256u);
x_3 = lean_uint8_to_nat(x_1);
x_4 = lean_nat_sub(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt8_instHasSize__2___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_UInt8_instHasSize__2___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__0(uint16_t x_1) {
_start:
{
uint16_t x_2; uint16_t x_3; uint16_t x_4; uint8_t x_5; 
x_2 = 1;
x_3 = lean_uint16_add(x_1, x_2);
x_4 = 0;
x_5 = lean_uint16_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__0___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_UInt16_instUpwardEnumerable___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__1(lean_object* x_1, uint16_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_uint16_to_nat(x_2);
x_4 = lean_nat_add(x_3, x_1);
x_5 = lean_unsigned_to_nat(65536u);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_box(0);
return x_7;
}
else
{
uint16_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_uint16_of_nat(x_4);
lean_dec(x_4);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_UInt16_instUpwardEnumerable___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_UInt16_instUpwardEnumerable___lam__1(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_UInt16_instLeast_x3f___closed__0(void) {
_start:
{
uint16_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_UInt16_instLeast_x3f(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_UInt16_instLeast_x3f___closed__0, &l_UInt16_instLeast_x3f___closed__0_once, _init_l_UInt16_instLeast_x3f___closed__0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize___lam__0(uint16_t x_1, uint16_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_uint16_to_nat(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_uint16_to_nat(x_1);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_UInt16_instHasSize___lam__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize__1___lam__0(uint16_t x_1, uint16_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_uint16_to_nat(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_uint16_to_nat(x_1);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_8 = lean_nat_sub(x_7, x_4);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint16_t x_3; uint16_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_UInt16_instHasSize__1___lam__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize__2___lam__0(uint16_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(65536u);
x_3 = lean_uint16_to_nat(x_1);
x_4 = lean_nat_sub(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt16_instHasSize__2___lam__0___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_UInt16_instHasSize__2___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__0(uint32_t x_1) {
_start:
{
uint32_t x_2; uint32_t x_3; uint32_t x_4; uint8_t x_5; 
x_2 = 1;
x_3 = lean_uint32_add(x_1, x_2);
x_4 = 0;
x_5 = lean_uint32_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box_uint32(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_UInt32_instUpwardEnumerable___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__1(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_uint32_to_nat(x_2);
x_4 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_5 = lean_cstr_to_nat("4294967296");
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_box(0);
return x_7;
}
else
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_uint32_of_nat(x_4);
lean_dec(x_4);
x_9 = lean_box_uint32(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_UInt32_instUpwardEnumerable___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_UInt32_instUpwardEnumerable___lam__1(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_UInt32_instLeast_x3f___closed__0___boxed__const__1(void) {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_UInt32_instLeast_x3f___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_UInt32_instLeast_x3f___closed__0___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_UInt32_instLeast_x3f(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_UInt32_instLeast_x3f___closed__0, &l_UInt32_instLeast_x3f___closed__0_once, _init_l_UInt32_instLeast_x3f___closed__0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize___lam__0(uint32_t x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_uint32_to_nat(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
x_6 = lean_uint32_to_nat(x_1);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_UInt32_instHasSize___lam__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize__1___lam__0(uint32_t x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_uint32_to_nat(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
x_6 = lean_uint32_to_nat(x_1);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_nat_sub(x_7, x_4);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint32_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_UInt32_instHasSize__1___lam__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize__2___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_cstr_to_nat("4294967296");
x_3 = lean_uint32_to_nat(x_1);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt32_instHasSize__2___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_UInt32_instHasSize__2___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__0(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint8_t x_5; 
x_2 = 1;
x_3 = lean_uint64_add(x_1, x_2);
x_4 = 0;
x_5 = lean_uint64_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box_uint64(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_3 = l_UInt64_instUpwardEnumerable___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("18446744073709551616");
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__1(lean_object* x_1, uint64_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_uint64_to_nat(x_2);
x_4 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_5 = lean_obj_once(&l_UInt64_instUpwardEnumerable___lam__1___closed__0, &l_UInt64_instUpwardEnumerable___lam__1___closed__0_once, _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_box(0);
return x_7;
}
else
{
uint64_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_uint64_of_nat(x_4);
lean_dec(x_4);
x_9 = lean_box_uint64(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_UInt64_instUpwardEnumerable___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_4 = l_UInt64_instUpwardEnumerable___lam__1(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_UInt64_instLeast_x3f___closed__0___boxed__const__1(void) {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_UInt64_instLeast_x3f___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_UInt64_instLeast_x3f___closed__0___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_UInt64_instLeast_x3f(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_UInt64_instLeast_x3f___closed__0, &l_UInt64_instLeast_x3f___closed__0_once, _init_l_UInt64_instLeast_x3f___closed__0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize___lam__0(uint64_t x_1, uint64_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_uint64_to_nat(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
x_6 = lean_uint64_to_nat(x_1);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_UInt64_instHasSize___lam__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize__1___lam__0(uint64_t x_1, uint64_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_uint64_to_nat(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
x_6 = lean_uint64_to_nat(x_1);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_nat_sub(x_7, x_4);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec_ref(x_2);
x_5 = l_UInt64_instHasSize__1___lam__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize__2___lam__0(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_obj_once(&l_UInt64_instUpwardEnumerable___lam__1___closed__0, &l_UInt64_instUpwardEnumerable___lam__1___closed__0_once, _init_l_UInt64_instUpwardEnumerable___lam__1___closed__0);
x_3 = lean_uint64_to_nat(x_1);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_UInt64_instHasSize__2___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_3 = l_UInt64_instHasSize__2___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__0(size_t x_1) {
_start:
{
size_t x_2; size_t x_3; size_t x_4; uint8_t x_5; 
x_2 = 1;
x_3 = lean_usize_add(x_1, x_2);
x_4 = 0;
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box_usize(x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__0___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_USize_instUpwardEnumerable___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_USize_instUpwardEnumerable___lam__1___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_Platform_numBits;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_pow(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__1(lean_object* x_1, size_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_usize_to_nat(x_2);
x_4 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_5 = lean_obj_once(&l_USize_instUpwardEnumerable___lam__1___closed__0, &l_USize_instUpwardEnumerable___lam__1___closed__0_once, _init_l_USize_instUpwardEnumerable___lam__1___closed__0);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_box(0);
return x_7;
}
else
{
size_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = lean_box_usize(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_USize_instUpwardEnumerable___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; 
x_3 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_4 = l_USize_instUpwardEnumerable___lam__1(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_USize_instLeast_x3f___closed__0___boxed__const__1(void) {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
static lean_object* _init_l_USize_instLeast_x3f___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_USize_instLeast_x3f___closed__0___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_USize_instLeast_x3f(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_USize_instLeast_x3f___closed__0, &l_USize_instLeast_x3f___closed__0_once, _init_l_USize_instLeast_x3f___closed__0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_USize_instHasSize___lam__0(size_t x_1, size_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_usize_to_nat(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
x_6 = lean_usize_to_nat(x_1);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_USize_instHasSize___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_USize_instHasSize___lam__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_USize_instHasSize__1___lam__0(size_t x_1, size_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_usize_to_nat(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
x_6 = lean_usize_to_nat(x_1);
x_7 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_nat_sub(x_7, x_4);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_USize_instHasSize__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_USize_instHasSize__1___lam__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_USize_instHasSize__2___lam__0(size_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_obj_once(&l_USize_instUpwardEnumerable___lam__1___closed__0, &l_USize_instUpwardEnumerable___lam__1___closed__0_once, _init_l_USize_instUpwardEnumerable___lam__1___closed__0);
x_3 = lean_usize_to_nat(x_1);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_USize_instHasSize__2___lam__0___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_USize_instHasSize__2___lam__0(x_2);
return x_3;
}
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
l_UInt8_instLeast_x3f = _init_l_UInt8_instLeast_x3f();
lean_mark_persistent(l_UInt8_instLeast_x3f);
l_UInt16_instLeast_x3f = _init_l_UInt16_instLeast_x3f();
lean_mark_persistent(l_UInt16_instLeast_x3f);
l_UInt32_instLeast_x3f___closed__0___boxed__const__1 = _init_l_UInt32_instLeast_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l_UInt32_instLeast_x3f___closed__0___boxed__const__1);
l_UInt32_instLeast_x3f = _init_l_UInt32_instLeast_x3f();
lean_mark_persistent(l_UInt32_instLeast_x3f);
l_UInt64_instLeast_x3f___closed__0___boxed__const__1 = _init_l_UInt64_instLeast_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l_UInt64_instLeast_x3f___closed__0___boxed__const__1);
l_UInt64_instLeast_x3f = _init_l_UInt64_instLeast_x3f();
lean_mark_persistent(l_UInt64_instLeast_x3f);
l_USize_instLeast_x3f___closed__0___boxed__const__1 = _init_l_USize_instLeast_x3f___closed__0___boxed__const__1();
lean_mark_persistent(l_USize_instLeast_x3f___closed__0___boxed__const__1);
l_USize_instLeast_x3f = _init_l_USize_instLeast_x3f();
lean_mark_persistent(l_USize_instLeast_x3f);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
