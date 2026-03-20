// Lean compiler output
// Module: Std.Data.ByteSlice
// Imports: public import Init.Data.ByteArray public import Init.Data.Slice.Basic public import Init.Data.Slice.Notation public import Init.Data.Range.Polymorphic.Nat import Init.Omega
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_ByteArray_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_byteArray(lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_byteArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_start(lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_start___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_stop(lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_stop___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_size(lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_size___boxed(lean_object*);
LEAN_EXPORT uint8_t l_ByteSlice_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteSlice_instGetElemNatUInt8LtSize___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_instGetElemNatUInt8LtSize___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_ByteSlice_instGetElemNatUInt8LtSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteSlice_instGetElemNatUInt8LtSize___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteSlice_instGetElemNatUInt8LtSize___closed__0 = (const lean_object*)&l_ByteSlice_instGetElemNatUInt8LtSize___closed__0_value;
LEAN_EXPORT const lean_object* l_ByteSlice_instGetElemNatUInt8LtSize = (const lean_object*)&l_ByteSlice_instGetElemNatUInt8LtSize___closed__0_value;
LEAN_EXPORT uint8_t l_ByteSlice_getD(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_ByteSlice_getD___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteSlice_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_get_x21___boxed(lean_object*, lean_object*);
static const lean_array_object l_ByteSlice_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_ByteSlice_empty___closed__0 = (const lean_object*)&l_ByteSlice_empty___closed__0_value;
static const lean_sarray_object l_ByteSlice_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_sarray_object) + 0, .m_other = 1, .m_tag = 248}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_ByteSlice_empty___closed__1 = (const lean_object*)&l_ByteSlice_empty___closed__1_value;
static const lean_ctor_object l_ByteSlice_empty___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_ByteSlice_empty___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_ByteSlice_empty___closed__2 = (const lean_object*)&l_ByteSlice_empty___closed__2_value;
LEAN_EXPORT const lean_object* l_ByteSlice_empty = (const lean_object*)&l_ByteSlice_empty___closed__2_value;
LEAN_EXPORT lean_object* l_ByteSlice_ofByteArray(lean_object*);
LEAN_EXPORT const lean_object* l_ByteSlice_instEmptyCollection = (const lean_object*)&l_ByteSlice_empty___closed__2_value;
LEAN_EXPORT const lean_object* l_ByteSlice_instInhabited = (const lean_object*)&l_ByteSlice_empty___closed__2_value;
LEAN_EXPORT lean_object* l_ByteSlice_toByteArray(lean_object*);
uint8_t lean_byteslice_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_ByteSlice_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ByteSlice_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteSlice_instBEq___closed__0 = (const lean_object*)&l_ByteSlice_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_ByteSlice_instBEq = (const lean_object*)&l_ByteSlice_instBEq___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_forM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_foldr___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_foldr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_ByteSlice_foldr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteSlice_foldr___redArg___closed__0 = (const lean_object*)&l_ByteSlice_foldr___redArg___closed__0_value;
static const lean_closure_object l_ByteSlice_foldr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteSlice_foldr___redArg___closed__1 = (const lean_object*)&l_ByteSlice_foldr___redArg___closed__1_value;
static const lean_closure_object l_ByteSlice_foldr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteSlice_foldr___redArg___closed__2 = (const lean_object*)&l_ByteSlice_foldr___redArg___closed__2_value;
static const lean_closure_object l_ByteSlice_foldr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteSlice_foldr___redArg___closed__3 = (const lean_object*)&l_ByteSlice_foldr___redArg___closed__3_value;
static const lean_closure_object l_ByteSlice_foldr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteSlice_foldr___redArg___closed__4 = (const lean_object*)&l_ByteSlice_foldr___redArg___closed__4_value;
static const lean_closure_object l_ByteSlice_foldr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteSlice_foldr___redArg___closed__5 = (const lean_object*)&l_ByteSlice_foldr___redArg___closed__5_value;
static const lean_closure_object l_ByteSlice_foldr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ByteSlice_foldr___redArg___closed__6 = (const lean_object*)&l_ByteSlice_foldr___redArg___closed__6_value;
static const lean_ctor_object l_ByteSlice_foldr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_ByteSlice_foldr___redArg___closed__0_value),((lean_object*)&l_ByteSlice_foldr___redArg___closed__1_value)}};
static const lean_object* l_ByteSlice_foldr___redArg___closed__7 = (const lean_object*)&l_ByteSlice_foldr___redArg___closed__7_value;
static const lean_ctor_object l_ByteSlice_foldr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_ByteSlice_foldr___redArg___closed__7_value),((lean_object*)&l_ByteSlice_foldr___redArg___closed__2_value),((lean_object*)&l_ByteSlice_foldr___redArg___closed__3_value),((lean_object*)&l_ByteSlice_foldr___redArg___closed__4_value),((lean_object*)&l_ByteSlice_foldr___redArg___closed__5_value)}};
static const lean_object* l_ByteSlice_foldr___redArg___closed__8 = (const lean_object*)&l_ByteSlice_foldr___redArg___closed__8_value;
static const lean_ctor_object l_ByteSlice_foldr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_ByteSlice_foldr___redArg___closed__8_value),((lean_object*)&l_ByteSlice_foldr___redArg___closed__6_value)}};
static const lean_object* l_ByteSlice_foldr___redArg___closed__9 = (const lean_object*)&l_ByteSlice_foldr___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_ByteSlice_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_foldr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_slice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteSlice_slice___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ByteSlice_contains(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_ByteSlice_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_toByteSlice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteArrayNatByteSlice___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteArrayNatByteSlice___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteArrayNatByteSlice___closed__0 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteArrayNatByteSlice = (const lean_object*)&l_instSliceableByteArrayNatByteSlice___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__1___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteArrayNatByteSlice__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteArrayNatByteSlice__1___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteArrayNatByteSlice__1___closed__0 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__1___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteArrayNatByteSlice__1 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__1___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__2___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteArrayNatByteSlice__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteArrayNatByteSlice__2___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteArrayNatByteSlice__2___closed__0 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__2___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteArrayNatByteSlice__2 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__2___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteArrayNatByteSlice__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteArrayNatByteSlice__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteArrayNatByteSlice__3___closed__0 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__3___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteArrayNatByteSlice__3 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__3___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__4___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteArrayNatByteSlice__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteArrayNatByteSlice__4___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteArrayNatByteSlice__4___closed__0 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__4___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteArrayNatByteSlice__4 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__4___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__5___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteArrayNatByteSlice__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteArrayNatByteSlice__5___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteArrayNatByteSlice__5___closed__0 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__5___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteArrayNatByteSlice__5 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__5___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__6___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteArrayNatByteSlice__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteArrayNatByteSlice__6___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteArrayNatByteSlice__6___closed__0 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__6___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteArrayNatByteSlice__6 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__6___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__7___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteArrayNatByteSlice__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteArrayNatByteSlice__7___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteArrayNatByteSlice__7___closed__0 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__7___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteArrayNatByteSlice__7 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__7___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__8___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteArrayNatByteSlice__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteArrayNatByteSlice__8___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteArrayNatByteSlice__8___closed__0 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__8___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteArrayNatByteSlice__8 = (const lean_object*)&l_instSliceableByteArrayNatByteSlice__8___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteSliceNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteSliceNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteSliceNat___closed__0 = (const lean_object*)&l_instSliceableByteSliceNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteSliceNat = (const lean_object*)&l_instSliceableByteSliceNat___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteSliceNat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteSliceNat__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteSliceNat__1___closed__0 = (const lean_object*)&l_instSliceableByteSliceNat__1___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteSliceNat__1 = (const lean_object*)&l_instSliceableByteSliceNat__1___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteSliceNat__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteSliceNat__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteSliceNat__2___closed__0 = (const lean_object*)&l_instSliceableByteSliceNat__2___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteSliceNat__2 = (const lean_object*)&l_instSliceableByteSliceNat__2___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteSliceNat__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteSliceNat__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteSliceNat__3___closed__0 = (const lean_object*)&l_instSliceableByteSliceNat__3___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteSliceNat__3 = (const lean_object*)&l_instSliceableByteSliceNat__3___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__4___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteSliceNat__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteSliceNat__4___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteSliceNat__4___closed__0 = (const lean_object*)&l_instSliceableByteSliceNat__4___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteSliceNat__4 = (const lean_object*)&l_instSliceableByteSliceNat__4___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__5___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteSliceNat__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteSliceNat__5___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteSliceNat__5___closed__0 = (const lean_object*)&l_instSliceableByteSliceNat__5___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteSliceNat__5 = (const lean_object*)&l_instSliceableByteSliceNat__5___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__6___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteSliceNat__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteSliceNat__6___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteSliceNat__6___closed__0 = (const lean_object*)&l_instSliceableByteSliceNat__6___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteSliceNat__6 = (const lean_object*)&l_instSliceableByteSliceNat__6___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__7___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__7___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteSliceNat__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteSliceNat__7___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteSliceNat__7___closed__0 = (const lean_object*)&l_instSliceableByteSliceNat__7___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteSliceNat__7 = (const lean_object*)&l_instSliceableByteSliceNat__7___closed__0_value;
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__8___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instSliceableByteSliceNat__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instSliceableByteSliceNat__8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instSliceableByteSliceNat__8___closed__0 = (const lean_object*)&l_instSliceableByteSliceNat__8___closed__0_value;
LEAN_EXPORT const lean_object* l_instSliceableByteSliceNat__8 = (const lean_object*)&l_instSliceableByteSliceNat__8___closed__0_value;
LEAN_EXPORT lean_object* l_ByteSlice_byteArray(lean_object* v_xs_1_){
_start:
{
lean_object* v_byteArray_2_; 
v_byteArray_2_ = lean_ctor_get(v_xs_1_, 0);
lean_inc_ref(v_byteArray_2_);
return v_byteArray_2_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_byteArray___boxed(lean_object* v_xs_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_ByteSlice_byteArray(v_xs_3_);
lean_dec_ref(v_xs_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_start(lean_object* v_xs_5_){
_start:
{
lean_object* v_start_6_; 
v_start_6_ = lean_ctor_get(v_xs_5_, 1);
lean_inc(v_start_6_);
return v_start_6_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_start___boxed(lean_object* v_xs_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_ByteSlice_start(v_xs_7_);
lean_dec_ref(v_xs_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_stop(lean_object* v_xs_9_){
_start:
{
lean_object* v_stop_10_; 
v_stop_10_ = lean_ctor_get(v_xs_9_, 2);
lean_inc(v_stop_10_);
return v_stop_10_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_stop___boxed(lean_object* v_xs_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_ByteSlice_stop(v_xs_11_);
lean_dec_ref(v_xs_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_size(lean_object* v_s_13_){
_start:
{
lean_object* v_start_14_; lean_object* v_stop_15_; lean_object* v___x_16_; 
v_start_14_ = lean_ctor_get(v_s_13_, 1);
v_stop_15_ = lean_ctor_get(v_s_13_, 2);
v___x_16_ = lean_nat_sub(v_stop_15_, v_start_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_size___boxed(lean_object* v_s_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_ByteSlice_size(v_s_17_);
lean_dec_ref(v_s_17_);
return v_res_18_;
}
}
LEAN_EXPORT uint8_t l_ByteSlice_get(lean_object* v_s_19_, lean_object* v_i_20_){
_start:
{
lean_object* v_byteArray_21_; lean_object* v_start_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v_byteArray_21_ = lean_ctor_get(v_s_19_, 0);
v_start_22_ = lean_ctor_get(v_s_19_, 1);
v___x_23_ = lean_nat_add(v_start_22_, v_i_20_);
v___x_24_ = lean_byte_array_fget(v_byteArray_21_, v___x_23_);
lean_dec(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_get___boxed(lean_object* v_s_25_, lean_object* v_i_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_ByteSlice_get(v_s_25_, v_i_26_);
lean_dec(v_i_26_);
lean_dec_ref(v_s_25_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT uint8_t l_ByteSlice_instGetElemNatUInt8LtSize___lam__0(lean_object* v_xs_29_, lean_object* v_i_30_, lean_object* v_h_31_){
_start:
{
uint8_t v___x_32_; 
v___x_32_ = l_ByteSlice_get(v_xs_29_, v_i_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_instGetElemNatUInt8LtSize___lam__0___boxed(lean_object* v_xs_33_, lean_object* v_i_34_, lean_object* v_h_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_ByteSlice_instGetElemNatUInt8LtSize___lam__0(v_xs_33_, v_i_34_, v_h_35_);
lean_dec(v_i_34_);
lean_dec_ref(v_xs_33_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT uint8_t l_ByteSlice_getD(lean_object* v_s_40_, lean_object* v_i_41_, uint8_t v_v_u2080_42_){
_start:
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = l_ByteSlice_size(v_s_40_);
v___x_44_ = lean_nat_dec_lt(v_i_41_, v___x_43_);
lean_dec(v___x_43_);
if (v___x_44_ == 0)
{
return v_v_u2080_42_;
}
else
{
uint8_t v___x_45_; 
v___x_45_ = l_ByteSlice_get(v_s_40_, v_i_41_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l_ByteSlice_getD___boxed(lean_object* v_s_46_, lean_object* v_i_47_, lean_object* v_v_u2080_48_){
_start:
{
uint8_t v_v_u2080_boxed_49_; uint8_t v_res_50_; lean_object* v_r_51_; 
v_v_u2080_boxed_49_ = lean_unbox(v_v_u2080_48_);
v_res_50_ = l_ByteSlice_getD(v_s_46_, v_i_47_, v_v_u2080_boxed_49_);
lean_dec(v_i_47_);
lean_dec_ref(v_s_46_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
LEAN_EXPORT uint8_t l_ByteSlice_get_x21(lean_object* v_s_52_, lean_object* v_i_53_){
_start:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = l_ByteSlice_size(v_s_52_);
v___x_55_ = lean_nat_dec_lt(v_i_53_, v___x_54_);
lean_dec(v___x_54_);
if (v___x_55_ == 0)
{
uint8_t v___x_56_; 
v___x_56_ = 0;
return v___x_56_;
}
else
{
uint8_t v___x_57_; 
v___x_57_ = l_ByteSlice_get(v_s_52_, v_i_53_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_ByteSlice_get_x21___boxed(lean_object* v_s_58_, lean_object* v_i_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_ByteSlice_get_x21(v_s_58_, v_i_59_);
lean_dec(v_i_59_);
lean_dec_ref(v_s_58_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_ofByteArray(lean_object* v_ba_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_unsigned_to_nat(0u);
v___x_72_ = lean_byte_array_size(v_ba_70_);
v___x_73_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_73_, 0, v_ba_70_);
lean_ctor_set(v___x_73_, 1, v___x_71_);
lean_ctor_set(v___x_73_, 2, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_toByteArray(lean_object* v_s_76_){
_start:
{
lean_object* v_byteArray_77_; lean_object* v_start_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_byteArray_77_ = lean_ctor_get(v_s_76_, 0);
lean_inc_ref(v_byteArray_77_);
v_start_78_ = lean_ctor_get(v_s_76_, 1);
lean_inc(v_start_78_);
v___x_79_ = l_ByteSlice_size(v_s_76_);
lean_dec_ref(v_s_76_);
v___x_80_ = lean_nat_add(v_start_78_, v___x_79_);
lean_dec(v___x_79_);
v___x_81_ = l_ByteArray_extract(v_byteArray_77_, v_start_78_, v___x_80_);
lean_dec(v___x_80_);
lean_dec_ref(v_byteArray_77_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_beq___boxed(lean_object* v_a_84_, lean_object* v_b_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = lean_byteslice_beq(v_a_84_, v_b_85_);
lean_dec_ref(v_b_85_);
lean_dec_ref(v_a_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg___lam__0___boxed(lean_object* v_i_90_, lean_object* v___x_91_, lean_object* v_inst_92_, lean_object* v_f_93_, lean_object* v_as_94_, lean_object* v_newAcc_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg___lam__0(v_i_90_, v___x_91_, v_inst_92_, v_f_93_, v_as_94_, v_newAcc_95_);
lean_dec(v___x_91_);
lean_dec(v_i_90_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(lean_object* v_inst_97_, lean_object* v_f_98_, lean_object* v_as_99_, lean_object* v_i_100_, lean_object* v_acc_101_){
_start:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = l_ByteSlice_size(v_as_99_);
v___x_103_ = lean_nat_dec_lt(v_i_100_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v_toApplicative_104_; lean_object* v_toPure_105_; lean_object* v___x_106_; 
lean_dec(v___x_102_);
lean_dec(v_i_100_);
lean_dec_ref(v_as_99_);
lean_dec(v_f_98_);
v_toApplicative_104_ = lean_ctor_get(v_inst_97_, 0);
lean_inc_ref(v_toApplicative_104_);
lean_dec_ref(v_inst_97_);
v_toPure_105_ = lean_ctor_get(v_toApplicative_104_, 1);
lean_inc(v_toPure_105_);
lean_dec_ref(v_toApplicative_104_);
v___x_106_ = lean_apply_2(v_toPure_105_, lean_box(0), v_acc_101_);
return v___x_106_;
}
else
{
lean_object* v_toBind_107_; lean_object* v___x_108_; lean_object* v___f_109_; lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_toBind_107_ = lean_ctor_get(v_inst_97_, 1);
lean_inc(v_toBind_107_);
v___x_108_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_as_99_);
lean_inc(v_f_98_);
lean_inc(v_i_100_);
v___f_109_ = lean_alloc_closure((void*)(l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_109_, 0, v_i_100_);
lean_closure_set(v___f_109_, 1, v___x_108_);
lean_closure_set(v___f_109_, 2, v_inst_97_);
lean_closure_set(v___f_109_, 3, v_f_98_);
lean_closure_set(v___f_109_, 4, v_as_99_);
v___x_110_ = lean_nat_sub(v___x_102_, v___x_108_);
lean_dec(v___x_102_);
v___x_111_ = lean_nat_sub(v___x_110_, v_i_100_);
lean_dec(v_i_100_);
lean_dec(v___x_110_);
v___x_112_ = l_ByteSlice_get(v_as_99_, v___x_111_);
lean_dec(v___x_111_);
lean_dec_ref(v_as_99_);
v___x_113_ = lean_box(v___x_112_);
v___x_114_ = lean_apply_2(v_f_98_, v___x_113_, v_acc_101_);
v___x_115_ = lean_apply_4(v_toBind_107_, lean_box(0), lean_box(0), v___x_114_, v___f_109_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg___lam__0(lean_object* v_i_116_, lean_object* v___x_117_, lean_object* v_inst_118_, lean_object* v_f_119_, lean_object* v_as_120_, lean_object* v_newAcc_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_nat_add(v_i_116_, v___x_117_);
v___x_123_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(v_inst_118_, v_f_119_, v_as_120_, v___x_122_, v_newAcc_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop(lean_object* v_00_u03b2_124_, lean_object* v_m_125_, lean_object* v_inst_126_, lean_object* v_f_127_, lean_object* v_as_128_, lean_object* v_i_129_, lean_object* v_acc_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(v_inst_126_, v_f_127_, v_as_128_, v_i_129_, v_acc_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_foldrM___redArg(lean_object* v_inst_132_, lean_object* v_f_133_, lean_object* v_init_134_, lean_object* v_as_135_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(v_inst_132_, v_f_133_, v_as_135_, v___x_136_, v_init_134_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_foldrM(lean_object* v_00_u03b2_138_, lean_object* v_m_139_, lean_object* v_inst_140_, lean_object* v_f_141_, lean_object* v_init_142_, lean_object* v_as_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(v_inst_140_, v_f_141_, v_as_143_, v___x_144_, v_init_142_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg___lam__0___boxed(lean_object* v_i_146_, lean_object* v_inst_147_, lean_object* v_f_148_, lean_object* v_as_149_, lean_object* v_____r_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg___lam__0(v_i_146_, v_inst_147_, v_f_148_, v_as_149_, v_____r_150_);
lean_dec(v_i_146_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(lean_object* v_inst_152_, lean_object* v_f_153_, lean_object* v_as_154_, lean_object* v_i_155_){
_start:
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = l_ByteSlice_size(v_as_154_);
v___x_157_ = lean_nat_dec_lt(v_i_155_, v___x_156_);
lean_dec(v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v_toApplicative_158_; lean_object* v_toPure_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v_i_155_);
lean_dec_ref(v_as_154_);
lean_dec(v_f_153_);
v_toApplicative_158_ = lean_ctor_get(v_inst_152_, 0);
lean_inc_ref(v_toApplicative_158_);
lean_dec_ref(v_inst_152_);
v_toPure_159_ = lean_ctor_get(v_toApplicative_158_, 1);
lean_inc(v_toPure_159_);
lean_dec_ref(v_toApplicative_158_);
v___x_160_ = lean_box(0);
v___x_161_ = lean_apply_2(v_toPure_159_, lean_box(0), v___x_160_);
return v___x_161_;
}
else
{
lean_object* v_toBind_162_; lean_object* v___f_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_toBind_162_ = lean_ctor_get(v_inst_152_, 1);
lean_inc(v_toBind_162_);
lean_inc_ref(v_as_154_);
lean_inc(v_f_153_);
lean_inc(v_i_155_);
v___f_163_ = lean_alloc_closure((void*)(l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_163_, 0, v_i_155_);
lean_closure_set(v___f_163_, 1, v_inst_152_);
lean_closure_set(v___f_163_, 2, v_f_153_);
lean_closure_set(v___f_163_, 3, v_as_154_);
v___x_164_ = l_ByteSlice_get(v_as_154_, v_i_155_);
lean_dec(v_i_155_);
lean_dec_ref(v_as_154_);
v___x_165_ = lean_box(v___x_164_);
v___x_166_ = lean_apply_1(v_f_153_, v___x_165_);
v___x_167_ = lean_apply_4(v_toBind_162_, lean_box(0), lean_box(0), v___x_166_, v___f_163_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg___lam__0(lean_object* v_i_168_, lean_object* v_inst_169_, lean_object* v_f_170_, lean_object* v_as_171_, lean_object* v_____r_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_add(v_i_168_, v___x_173_);
v___x_175_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(v_inst_169_, v_f_170_, v_as_171_, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop(lean_object* v_m_176_, lean_object* v_inst_177_, lean_object* v_f_178_, lean_object* v_as_179_, lean_object* v_i_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(v_inst_177_, v_f_178_, v_as_179_, v_i_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_forM___redArg(lean_object* v_inst_182_, lean_object* v_f_183_, lean_object* v_as_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(v_inst_182_, v_f_183_, v_as_184_, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_forM(lean_object* v_m_187_, lean_object* v_inst_188_, lean_object* v_f_189_, lean_object* v_as_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(v_inst_188_, v_f_189_, v_as_190_, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_foldr___redArg___lam__0(lean_object* v_f_193_, uint8_t v_x1_194_, lean_object* v_x2_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_box(v_x1_194_);
v___x_197_ = lean_apply_2(v_f_193_, v___x_196_, v_x2_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_foldr___redArg___lam__0___boxed(lean_object* v_f_198_, lean_object* v_x1_199_, lean_object* v_x2_200_){
_start:
{
uint8_t v_x1_85__boxed_201_; lean_object* v_res_202_; 
v_x1_85__boxed_201_ = lean_unbox(v_x1_199_);
v_res_202_ = l_ByteSlice_foldr___redArg___lam__0(v_f_198_, v_x1_85__boxed_201_, v_x2_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_foldr___redArg(lean_object* v_f_222_, lean_object* v_init_223_, lean_object* v_as_224_){
_start:
{
lean_object* v___f_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___f_225_ = lean_alloc_closure((void*)(l_ByteSlice_foldr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_225_, 0, v_f_222_);
v___x_226_ = ((lean_object*)(l_ByteSlice_foldr___redArg___closed__9));
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(v___x_226_, v___f_225_, v_as_224_, v___x_227_, v_init_223_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_foldr(lean_object* v_00_u03b2_229_, lean_object* v_f_230_, lean_object* v_init_231_, lean_object* v_as_232_){
_start:
{
lean_object* v___f_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___f_233_ = lean_alloc_closure((void*)(l_ByteSlice_foldr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_233_, 0, v_f_230_);
v___x_234_ = ((lean_object*)(l_ByteSlice_foldr___redArg___closed__9));
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(v___x_234_, v___f_233_, v_as_232_, v___x_235_, v_init_231_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_slice(lean_object* v_s_237_, lean_object* v_start_238_, lean_object* v_stop_239_){
_start:
{
lean_object* v_byteArray_240_; lean_object* v_start_241_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___x_252_; lean_object* v___y_254_; uint8_t v___x_257_; 
v_byteArray_240_ = lean_ctor_get(v_s_237_, 0);
v_start_241_ = lean_ctor_get(v_s_237_, 1);
v___x_252_ = l_ByteSlice_size(v_s_237_);
v___x_257_ = lean_nat_dec_le(v_start_238_, v___x_252_);
if (v___x_257_ == 0)
{
lean_dec(v_start_238_);
lean_inc(v___x_252_);
v___y_254_ = v___x_252_;
goto v___jp_253_;
}
else
{
v___y_254_ = v_start_238_;
goto v___jp_253_;
}
v___jp_242_:
{
lean_object* v_actualStop_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v_actualStop_245_ = lean_nat_add(v_start_241_, v___y_244_);
lean_dec(v___y_244_);
v___x_246_ = lean_byte_array_size(v_byteArray_240_);
v___x_247_ = lean_nat_dec_le(v_actualStop_245_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
lean_dec(v_actualStop_245_);
lean_dec(v___y_243_);
lean_inc_n(v_start_241_, 2);
lean_inc_ref(v_byteArray_240_);
v___x_248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_248_, 0, v_byteArray_240_);
lean_ctor_set(v___x_248_, 1, v_start_241_);
lean_ctor_set(v___x_248_, 2, v_start_241_);
return v___x_248_;
}
else
{
uint8_t v___x_249_; 
v___x_249_ = lean_nat_dec_le(v___y_243_, v_actualStop_245_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec(v___y_243_);
lean_inc(v_actualStop_245_);
lean_inc_ref(v_byteArray_240_);
v___x_250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_250_, 0, v_byteArray_240_);
lean_ctor_set(v___x_250_, 1, v_actualStop_245_);
lean_ctor_set(v___x_250_, 2, v_actualStop_245_);
return v___x_250_;
}
else
{
lean_object* v___x_251_; 
lean_inc_ref(v_byteArray_240_);
v___x_251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_251_, 0, v_byteArray_240_);
lean_ctor_set(v___x_251_, 1, v___y_243_);
lean_ctor_set(v___x_251_, 2, v_actualStop_245_);
return v___x_251_;
}
}
}
v___jp_253_:
{
lean_object* v_actualStart_255_; uint8_t v___x_256_; 
v_actualStart_255_ = lean_nat_add(v_start_241_, v___y_254_);
lean_dec(v___y_254_);
v___x_256_ = lean_nat_dec_le(v_stop_239_, v___x_252_);
if (v___x_256_ == 0)
{
lean_dec(v_stop_239_);
v___y_243_ = v_actualStart_255_;
v___y_244_ = v___x_252_;
goto v___jp_242_;
}
else
{
lean_dec(v___x_252_);
v___y_243_ = v_actualStart_255_;
v___y_244_ = v_stop_239_;
goto v___jp_242_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteSlice_slice___boxed(lean_object* v_s_258_, lean_object* v_start_259_, lean_object* v_stop_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_ByteSlice_slice(v_s_258_, v_start_259_, v_stop_260_);
lean_dec_ref(v_s_258_);
return v_res_261_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop(lean_object* v_s_262_, uint8_t v_byte_263_, lean_object* v_i_264_){
_start:
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = l_ByteSlice_size(v_s_262_);
v___x_266_ = lean_nat_dec_lt(v_i_264_, v___x_265_);
lean_dec(v___x_265_);
if (v___x_266_ == 0)
{
lean_dec(v_i_264_);
return v___x_266_;
}
else
{
uint8_t v___x_267_; uint8_t v___x_268_; 
v___x_267_ = l_ByteSlice_get(v_s_262_, v_i_264_);
v___x_268_ = lean_uint8_dec_eq(v___x_267_, v_byte_263_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_nat_add(v_i_264_, v___x_269_);
lean_dec(v_i_264_);
v_i_264_ = v___x_270_;
goto _start;
}
else
{
lean_dec(v_i_264_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop___boxed(lean_object* v_s_272_, lean_object* v_byte_273_, lean_object* v_i_274_){
_start:
{
uint8_t v_byte_boxed_275_; uint8_t v_res_276_; lean_object* v_r_277_; 
v_byte_boxed_275_ = lean_unbox(v_byte_273_);
v_res_276_ = l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop(v_s_272_, v_byte_boxed_275_, v_i_274_);
lean_dec_ref(v_s_272_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT uint8_t l_ByteSlice_contains(lean_object* v_s_278_, uint8_t v_byte_279_){
_start:
{
lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop(v_s_278_, v_byte_279_, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_contains___boxed(lean_object* v_s_282_, lean_object* v_byte_283_){
_start:
{
uint8_t v_byte_boxed_284_; uint8_t v_res_285_; lean_object* v_r_286_; 
v_byte_boxed_284_ = lean_unbox(v_byte_283_);
v_res_285_ = l_ByteSlice_contains(v_s_282_, v_byte_boxed_284_);
lean_dec_ref(v_s_282_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toByteSlice(lean_object* v_as_287_, lean_object* v_start_288_, lean_object* v_stop_289_){
_start:
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_byte_array_size(v_as_287_);
v___x_291_ = lean_nat_dec_le(v_stop_289_, v___x_290_);
if (v___x_291_ == 0)
{
uint8_t v___x_292_; 
lean_dec(v_stop_289_);
v___x_292_ = lean_nat_dec_le(v_start_288_, v___x_290_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; 
lean_dec(v_start_288_);
v___x_293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_293_, 0, v_as_287_);
lean_ctor_set(v___x_293_, 1, v___x_290_);
lean_ctor_set(v___x_293_, 2, v___x_290_);
return v___x_293_;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_294_, 0, v_as_287_);
lean_ctor_set(v___x_294_, 1, v_start_288_);
lean_ctor_set(v___x_294_, 2, v___x_290_);
return v___x_294_;
}
}
else
{
uint8_t v___x_295_; 
v___x_295_ = lean_nat_dec_le(v_start_288_, v_stop_289_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; 
lean_dec(v_start_288_);
lean_inc(v_stop_289_);
v___x_296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_296_, 0, v_as_287_);
lean_ctor_set(v___x_296_, 1, v_stop_289_);
lean_ctor_set(v___x_296_, 2, v_stop_289_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_297_, 0, v_as_287_);
lean_ctor_set(v___x_297_, 1, v_start_288_);
lean_ctor_set(v___x_297_, 2, v_stop_289_);
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice___lam__0(lean_object* v_xs_298_, lean_object* v_range_299_){
_start:
{
lean_object* v_lower_300_; lean_object* v_upper_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___y_305_; uint8_t v___x_311_; 
v_lower_300_ = lean_ctor_get(v_range_299_, 0);
lean_inc(v_lower_300_);
v_upper_301_ = lean_ctor_get(v_range_299_, 1);
lean_inc(v_upper_301_);
lean_dec_ref(v_range_299_);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_byte_array_size(v_xs_298_);
v___x_311_ = lean_nat_dec_le(v_lower_300_, v___x_302_);
if (v___x_311_ == 0)
{
v___y_305_ = v_lower_300_;
goto v___jp_304_;
}
else
{
lean_dec(v_lower_300_);
v___y_305_ = v___x_302_;
goto v___jp_304_;
}
v___jp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_306_ = lean_unsigned_to_nat(1u);
v___x_307_ = lean_nat_add(v_upper_301_, v___x_306_);
lean_dec(v_upper_301_);
v___x_308_ = lean_nat_dec_le(v___x_307_, v___x_303_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_dec(v___x_307_);
v___x_309_ = l_ByteArray_toByteSlice(v_xs_298_, v___y_305_, v___x_303_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = l_ByteArray_toByteSlice(v_xs_298_, v___y_305_, v___x_307_);
return v___x_310_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__1___lam__0(lean_object* v_xs_314_, lean_object* v_range_315_){
_start:
{
lean_object* v_lower_316_; lean_object* v_upper_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___y_321_; uint8_t v___x_325_; 
v_lower_316_ = lean_ctor_get(v_range_315_, 0);
lean_inc(v_lower_316_);
v_upper_317_ = lean_ctor_get(v_range_315_, 1);
lean_inc(v_upper_317_);
lean_dec_ref(v_range_315_);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_byte_array_size(v_xs_314_);
v___x_325_ = lean_nat_dec_le(v_lower_316_, v___x_318_);
if (v___x_325_ == 0)
{
v___y_321_ = v_lower_316_;
goto v___jp_320_;
}
else
{
lean_dec(v_lower_316_);
v___y_321_ = v___x_318_;
goto v___jp_320_;
}
v___jp_320_:
{
uint8_t v___x_322_; 
v___x_322_ = lean_nat_dec_le(v_upper_317_, v___x_319_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
lean_dec(v_upper_317_);
v___x_323_ = l_ByteArray_toByteSlice(v_xs_314_, v___y_321_, v___x_319_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; 
v___x_324_ = l_ByteArray_toByteSlice(v_xs_314_, v___y_321_, v_upper_317_);
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__2___lam__0(lean_object* v_xs_328_, lean_object* v_range_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_byte_array_size(v_xs_328_);
v___x_332_ = lean_nat_dec_le(v_range_329_, v___x_330_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = l_ByteArray_toByteSlice(v_xs_328_, v_range_329_, v___x_331_);
return v___x_333_;
}
else
{
lean_object* v___x_334_; 
lean_dec(v_range_329_);
v___x_334_ = l_ByteArray_toByteSlice(v_xs_328_, v___x_330_, v___x_331_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__3___lam__0(lean_object* v_xs_337_, lean_object* v_range_338_){
_start:
{
lean_object* v_lower_339_; lean_object* v_upper_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___y_345_; lean_object* v___x_350_; uint8_t v___x_351_; 
v_lower_339_ = lean_ctor_get(v_range_338_, 0);
v_upper_340_ = lean_ctor_get(v_range_338_, 1);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_byte_array_size(v_xs_337_);
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_350_ = lean_nat_add(v_lower_339_, v___x_343_);
v___x_351_ = lean_nat_dec_le(v___x_350_, v___x_341_);
if (v___x_351_ == 0)
{
v___y_345_ = v___x_350_;
goto v___jp_344_;
}
else
{
lean_dec(v___x_350_);
v___y_345_ = v___x_341_;
goto v___jp_344_;
}
v___jp_344_:
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = lean_nat_add(v_upper_340_, v___x_343_);
v___x_347_ = lean_nat_dec_le(v___x_346_, v___x_342_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
lean_dec(v___x_346_);
v___x_348_ = l_ByteArray_toByteSlice(v_xs_337_, v___y_345_, v___x_342_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = l_ByteArray_toByteSlice(v_xs_337_, v___y_345_, v___x_346_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__3___lam__0___boxed(lean_object* v_xs_352_, lean_object* v_range_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_instSliceableByteArrayNatByteSlice__3___lam__0(v_xs_352_, v_range_353_);
lean_dec_ref(v_range_353_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__4___lam__0(lean_object* v_xs_357_, lean_object* v_range_358_){
_start:
{
lean_object* v_lower_359_; lean_object* v_upper_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___y_364_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_lower_359_ = lean_ctor_get(v_range_358_, 0);
lean_inc(v_lower_359_);
v_upper_360_ = lean_ctor_get(v_range_358_, 1);
lean_inc(v_upper_360_);
lean_dec_ref(v_range_358_);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_byte_array_size(v_xs_357_);
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = lean_nat_add(v_lower_359_, v___x_368_);
lean_dec(v_lower_359_);
v___x_370_ = lean_nat_dec_le(v___x_369_, v___x_361_);
if (v___x_370_ == 0)
{
v___y_364_ = v___x_369_;
goto v___jp_363_;
}
else
{
lean_dec(v___x_369_);
v___y_364_ = v___x_361_;
goto v___jp_363_;
}
v___jp_363_:
{
uint8_t v___x_365_; 
v___x_365_ = lean_nat_dec_le(v_upper_360_, v___x_362_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec(v_upper_360_);
v___x_366_ = l_ByteArray_toByteSlice(v_xs_357_, v___y_364_, v___x_362_);
return v___x_366_;
}
else
{
lean_object* v___x_367_; 
v___x_367_ = l_ByteArray_toByteSlice(v_xs_357_, v___y_364_, v_upper_360_);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__5___lam__0(lean_object* v_xs_373_, lean_object* v_range_374_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_byte_array_size(v_xs_373_);
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_nat_add(v_range_374_, v___x_377_);
v___x_379_ = lean_nat_dec_le(v___x_378_, v___x_375_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; 
v___x_380_ = l_ByteArray_toByteSlice(v_xs_373_, v___x_378_, v___x_376_);
return v___x_380_;
}
else
{
lean_object* v___x_381_; 
lean_dec(v___x_378_);
v___x_381_ = l_ByteArray_toByteSlice(v_xs_373_, v___x_375_, v___x_376_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__5___lam__0___boxed(lean_object* v_xs_382_, lean_object* v_range_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_instSliceableByteArrayNatByteSlice__5___lam__0(v_xs_382_, v_range_383_);
lean_dec(v_range_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__6___lam__0(lean_object* v_xs_387_, lean_object* v_range_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = lean_byte_array_size(v_xs_387_);
v___x_391_ = lean_unsigned_to_nat(1u);
v___x_392_ = lean_nat_add(v_range_388_, v___x_391_);
v___x_393_ = lean_nat_dec_le(v___x_392_, v___x_390_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
lean_dec(v___x_392_);
v___x_394_ = l_ByteArray_toByteSlice(v_xs_387_, v___x_389_, v___x_390_);
return v___x_394_;
}
else
{
lean_object* v___x_395_; 
v___x_395_ = l_ByteArray_toByteSlice(v_xs_387_, v___x_389_, v___x_392_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__6___lam__0___boxed(lean_object* v_xs_396_, lean_object* v_range_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_instSliceableByteArrayNatByteSlice__6___lam__0(v_xs_396_, v_range_397_);
lean_dec(v_range_397_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__7___lam__0(lean_object* v_xs_401_, lean_object* v_range_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_byte_array_size(v_xs_401_);
v___x_405_ = lean_nat_dec_le(v_range_402_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; 
lean_dec(v_range_402_);
v___x_406_ = l_ByteArray_toByteSlice(v_xs_401_, v___x_403_, v___x_404_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; 
v___x_407_ = l_ByteArray_toByteSlice(v_xs_401_, v___x_403_, v_range_402_);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__8___lam__0(lean_object* v_xs_410_, lean_object* v_x_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_byte_array_size(v_xs_410_);
v___x_414_ = l_ByteArray_toByteSlice(v_xs_410_, v___x_412_, v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat___lam__0(lean_object* v_xs_417_, lean_object* v_range_418_){
_start:
{
lean_object* v_lower_419_; lean_object* v_upper_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___y_424_; uint8_t v___x_430_; 
v_lower_419_ = lean_ctor_get(v_range_418_, 0);
lean_inc(v_lower_419_);
v_upper_420_ = lean_ctor_get(v_range_418_, 1);
lean_inc(v_upper_420_);
lean_dec_ref(v_range_418_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = l_ByteSlice_size(v_xs_417_);
v___x_430_ = lean_nat_dec_le(v_lower_419_, v___x_421_);
if (v___x_430_ == 0)
{
v___y_424_ = v_lower_419_;
goto v___jp_423_;
}
else
{
lean_dec(v_lower_419_);
v___y_424_ = v___x_421_;
goto v___jp_423_;
}
v___jp_423_:
{
lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_425_ = lean_unsigned_to_nat(1u);
v___x_426_ = lean_nat_add(v_upper_420_, v___x_425_);
lean_dec(v_upper_420_);
v___x_427_ = lean_nat_dec_le(v___x_426_, v___x_422_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
lean_dec(v___x_426_);
v___x_428_ = l_ByteSlice_slice(v_xs_417_, v___y_424_, v___x_422_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; 
lean_dec(v___x_422_);
v___x_429_ = l_ByteSlice_slice(v_xs_417_, v___y_424_, v___x_426_);
return v___x_429_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat___lam__0___boxed(lean_object* v_xs_431_, lean_object* v_range_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_instSliceableByteSliceNat___lam__0(v_xs_431_, v_range_432_);
lean_dec_ref(v_xs_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__1___lam__0(lean_object* v_xs_436_, lean_object* v_range_437_){
_start:
{
lean_object* v_lower_438_; lean_object* v_upper_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___y_443_; uint8_t v___x_447_; 
v_lower_438_ = lean_ctor_get(v_range_437_, 0);
lean_inc(v_lower_438_);
v_upper_439_ = lean_ctor_get(v_range_437_, 1);
lean_inc(v_upper_439_);
lean_dec_ref(v_range_437_);
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = l_ByteSlice_size(v_xs_436_);
v___x_447_ = lean_nat_dec_le(v_lower_438_, v___x_440_);
if (v___x_447_ == 0)
{
v___y_443_ = v_lower_438_;
goto v___jp_442_;
}
else
{
lean_dec(v_lower_438_);
v___y_443_ = v___x_440_;
goto v___jp_442_;
}
v___jp_442_:
{
uint8_t v___x_444_; 
v___x_444_ = lean_nat_dec_le(v_upper_439_, v___x_441_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
lean_dec(v_upper_439_);
v___x_445_ = l_ByteSlice_slice(v_xs_436_, v___y_443_, v___x_441_);
return v___x_445_;
}
else
{
lean_object* v___x_446_; 
lean_dec(v___x_441_);
v___x_446_ = l_ByteSlice_slice(v_xs_436_, v___y_443_, v_upper_439_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__1___lam__0___boxed(lean_object* v_xs_448_, lean_object* v_range_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_instSliceableByteSliceNat__1___lam__0(v_xs_448_, v_range_449_);
lean_dec_ref(v_xs_448_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__2___lam__0(lean_object* v_xs_453_, lean_object* v_range_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = l_ByteSlice_size(v_xs_453_);
v___x_457_ = lean_nat_dec_le(v_range_454_, v___x_455_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
v___x_458_ = l_ByteSlice_slice(v_xs_453_, v_range_454_, v___x_456_);
return v___x_458_;
}
else
{
lean_object* v___x_459_; 
lean_dec(v_range_454_);
v___x_459_ = l_ByteSlice_slice(v_xs_453_, v___x_455_, v___x_456_);
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__2___lam__0___boxed(lean_object* v_xs_460_, lean_object* v_range_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_instSliceableByteSliceNat__2___lam__0(v_xs_460_, v_range_461_);
lean_dec_ref(v_xs_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__3___lam__0(lean_object* v_xs_465_, lean_object* v_range_466_){
_start:
{
lean_object* v_lower_467_; lean_object* v_upper_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___y_473_; lean_object* v___x_478_; uint8_t v___x_479_; 
v_lower_467_ = lean_ctor_get(v_range_466_, 0);
v_upper_468_ = lean_ctor_get(v_range_466_, 1);
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = l_ByteSlice_size(v_xs_465_);
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_478_ = lean_nat_add(v_lower_467_, v___x_471_);
v___x_479_ = lean_nat_dec_le(v___x_478_, v___x_469_);
if (v___x_479_ == 0)
{
v___y_473_ = v___x_478_;
goto v___jp_472_;
}
else
{
lean_dec(v___x_478_);
v___y_473_ = v___x_469_;
goto v___jp_472_;
}
v___jp_472_:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_nat_add(v_upper_468_, v___x_471_);
v___x_475_ = lean_nat_dec_le(v___x_474_, v___x_470_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
lean_dec(v___x_474_);
v___x_476_ = l_ByteSlice_slice(v_xs_465_, v___y_473_, v___x_470_);
return v___x_476_;
}
else
{
lean_object* v___x_477_; 
lean_dec(v___x_470_);
v___x_477_ = l_ByteSlice_slice(v_xs_465_, v___y_473_, v___x_474_);
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__3___lam__0___boxed(lean_object* v_xs_480_, lean_object* v_range_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_instSliceableByteSliceNat__3___lam__0(v_xs_480_, v_range_481_);
lean_dec_ref(v_range_481_);
lean_dec_ref(v_xs_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__4___lam__0(lean_object* v_xs_485_, lean_object* v_range_486_){
_start:
{
lean_object* v_lower_487_; lean_object* v_upper_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___y_492_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v_lower_487_ = lean_ctor_get(v_range_486_, 0);
lean_inc(v_lower_487_);
v_upper_488_ = lean_ctor_get(v_range_486_, 1);
lean_inc(v_upper_488_);
lean_dec_ref(v_range_486_);
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = l_ByteSlice_size(v_xs_485_);
v___x_496_ = lean_unsigned_to_nat(1u);
v___x_497_ = lean_nat_add(v_lower_487_, v___x_496_);
lean_dec(v_lower_487_);
v___x_498_ = lean_nat_dec_le(v___x_497_, v___x_489_);
if (v___x_498_ == 0)
{
v___y_492_ = v___x_497_;
goto v___jp_491_;
}
else
{
lean_dec(v___x_497_);
v___y_492_ = v___x_489_;
goto v___jp_491_;
}
v___jp_491_:
{
uint8_t v___x_493_; 
v___x_493_ = lean_nat_dec_le(v_upper_488_, v___x_490_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
lean_dec(v_upper_488_);
v___x_494_ = l_ByteSlice_slice(v_xs_485_, v___y_492_, v___x_490_);
return v___x_494_;
}
else
{
lean_object* v___x_495_; 
lean_dec(v___x_490_);
v___x_495_ = l_ByteSlice_slice(v_xs_485_, v___y_492_, v_upper_488_);
return v___x_495_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__4___lam__0___boxed(lean_object* v_xs_499_, lean_object* v_range_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_instSliceableByteSliceNat__4___lam__0(v_xs_499_, v_range_500_);
lean_dec_ref(v_xs_499_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__5___lam__0(lean_object* v_xs_504_, lean_object* v_range_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = l_ByteSlice_size(v_xs_504_);
v___x_508_ = lean_unsigned_to_nat(1u);
v___x_509_ = lean_nat_add(v_range_505_, v___x_508_);
v___x_510_ = lean_nat_dec_le(v___x_509_, v___x_506_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
v___x_511_ = l_ByteSlice_slice(v_xs_504_, v___x_509_, v___x_507_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; 
lean_dec(v___x_509_);
v___x_512_ = l_ByteSlice_slice(v_xs_504_, v___x_506_, v___x_507_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__5___lam__0___boxed(lean_object* v_xs_513_, lean_object* v_range_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_instSliceableByteSliceNat__5___lam__0(v_xs_513_, v_range_514_);
lean_dec(v_range_514_);
lean_dec_ref(v_xs_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__6___lam__0(lean_object* v_xs_518_, lean_object* v_range_519_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = l_ByteSlice_size(v_xs_518_);
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_range_519_, v___x_522_);
v___x_524_ = lean_nat_dec_le(v___x_523_, v___x_521_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec(v___x_523_);
v___x_525_ = l_ByteSlice_slice(v_xs_518_, v___x_520_, v___x_521_);
return v___x_525_;
}
else
{
lean_object* v___x_526_; 
lean_dec(v___x_521_);
v___x_526_ = l_ByteSlice_slice(v_xs_518_, v___x_520_, v___x_523_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__6___lam__0___boxed(lean_object* v_xs_527_, lean_object* v_range_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_instSliceableByteSliceNat__6___lam__0(v_xs_527_, v_range_528_);
lean_dec(v_range_528_);
lean_dec_ref(v_xs_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__7___lam__0(lean_object* v_xs_532_, lean_object* v_range_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = l_ByteSlice_size(v_xs_532_);
v___x_536_ = lean_nat_dec_le(v_range_533_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; 
lean_dec(v_range_533_);
v___x_537_ = l_ByteSlice_slice(v_xs_532_, v___x_534_, v___x_535_);
return v___x_537_;
}
else
{
lean_object* v___x_538_; 
lean_dec(v___x_535_);
v___x_538_ = l_ByteSlice_slice(v_xs_532_, v___x_534_, v_range_533_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__7___lam__0___boxed(lean_object* v_xs_539_, lean_object* v_range_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_instSliceableByteSliceNat__7___lam__0(v_xs_539_, v_range_540_);
lean_dec_ref(v_xs_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__8___lam__0(lean_object* v_xs_544_, lean_object* v_x_545_){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = l_ByteSlice_size(v_xs_544_);
v___x_548_ = l_ByteSlice_slice(v_xs_544_, v___x_546_, v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__8___lam__0___boxed(lean_object* v_xs_549_, lean_object* v_x_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_instSliceableByteSliceNat__8___lam__0(v_xs_549_, v_x_550_);
lean_dec_ref(v_xs_549_);
return v_res_551_;
}
}
lean_object* runtime_initialize_Init_Data_ByteArray(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_ByteSlice(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_ByteSlice(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ByteArray(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Notation(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_ByteSlice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Slice_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_ByteSlice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_ByteSlice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_ByteSlice(builtin);
}
#ifdef __cplusplus
}
#endif
