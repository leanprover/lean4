// Lean compiler output
// Module: Std.Data.ByteSlice
// Imports: public import Init.Data.ByteArray.Basic public import Init.Data.Slice.Basic public import Init.Data.Slice.Notation public import Init.Data.Range.Polymorphic.Nat import Init.Omega
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
uint8_t l_ByteSlice_get(lean_object* v_s_19_, lean_object* v_i_20_){
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
LEAN_EXPORT void l_ByteSlice_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_19_ = stack[0].m_obj;
lean_object* v_i_20_ = stack[1].m_obj;
uint8_t v_res_25_;
v_res_25_ = l_ByteSlice_get(v_s_19_, v_i_20_);
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l_ByteSlice_get___boxed(lean_object* v_s_26_, lean_object* v_i_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_ByteSlice_get(v_s_26_, v_i_27_);
lean_dec(v_i_27_);
lean_dec_ref(v_s_26_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
uint8_t l_ByteSlice_instGetElemNatUInt8LtSize___lam__0(lean_object* v_xs_30_, lean_object* v_i_31_, lean_object* v_h_32_){
_start:
{
uint8_t v___x_33_; 
v___x_33_ = l_ByteSlice_get(v_xs_30_, v_i_31_);
return v___x_33_;
}
}
LEAN_EXPORT void l_ByteSlice_instGetElemNatUInt8LtSize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_30_ = stack[0].m_obj;
lean_object* v_i_31_ = stack[1].m_obj;
uint8_t v_res_34_;
v_res_34_ = l_ByteSlice_instGetElemNatUInt8LtSize___lam__0(v_xs_30_, v_i_31_, lean_box(0));
stack->m_num = v_res_34_;
}
LEAN_EXPORT lean_object* l_ByteSlice_instGetElemNatUInt8LtSize___lam__0___boxed(lean_object* v_xs_35_, lean_object* v_i_36_, lean_object* v_h_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_ByteSlice_instGetElemNatUInt8LtSize___lam__0(v_xs_35_, v_i_36_, v_h_37_);
lean_dec(v_i_36_);
lean_dec_ref(v_xs_35_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
uint8_t l_ByteSlice_getD(lean_object* v_s_42_, lean_object* v_i_43_, uint8_t v_v_u2080_44_){
_start:
{
lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_45_ = l_ByteSlice_size(v_s_42_);
v___x_46_ = lean_nat_dec_lt(v_i_43_, v___x_45_);
lean_dec(v___x_45_);
if (v___x_46_ == 0)
{
return v_v_u2080_44_;
}
else
{
uint8_t v___x_47_; 
v___x_47_ = l_ByteSlice_get(v_s_42_, v_i_43_);
return v___x_47_;
}
}
}
LEAN_EXPORT void l_ByteSlice_getD_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_42_ = stack[0].m_obj;
lean_object* v_i_43_ = stack[1].m_obj;
uint8_t v_v_u2080_44_ = stack[2].m_num;
uint8_t v_res_48_;
v_res_48_ = l_ByteSlice_getD(v_s_42_, v_i_43_, v_v_u2080_44_);
stack->m_num = v_res_48_;
}
LEAN_EXPORT lean_object* l_ByteSlice_getD___boxed(lean_object* v_s_49_, lean_object* v_i_50_, lean_object* v_v_u2080_51_){
_start:
{
uint8_t v_v_u2080_boxed_52_; uint8_t v_res_53_; lean_object* v_r_54_; 
v_v_u2080_boxed_52_ = lean_unbox(v_v_u2080_51_);
v_res_53_ = l_ByteSlice_getD(v_s_49_, v_i_50_, v_v_u2080_boxed_52_);
lean_dec(v_i_50_);
lean_dec_ref(v_s_49_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
uint8_t l_ByteSlice_get_x21(lean_object* v_s_55_, lean_object* v_i_56_){
_start:
{
lean_object* v___x_57_; uint8_t v___x_58_; 
v___x_57_ = l_ByteSlice_size(v_s_55_);
v___x_58_ = lean_nat_dec_lt(v_i_56_, v___x_57_);
lean_dec(v___x_57_);
if (v___x_58_ == 0)
{
uint8_t v___x_59_; 
v___x_59_ = 0;
return v___x_59_;
}
else
{
uint8_t v___x_60_; 
v___x_60_ = l_ByteSlice_get(v_s_55_, v_i_56_);
return v___x_60_;
}
}
}
LEAN_EXPORT void l_ByteSlice_get_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_55_ = stack[0].m_obj;
lean_object* v_i_56_ = stack[1].m_obj;
uint8_t v_res_61_;
v_res_61_ = l_ByteSlice_get_x21(v_s_55_, v_i_56_);
stack->m_num = v_res_61_;
}
LEAN_EXPORT lean_object* l_ByteSlice_get_x21___boxed(lean_object* v_s_62_, lean_object* v_i_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_ByteSlice_get_x21(v_s_62_, v_i_63_);
lean_dec(v_i_63_);
lean_dec_ref(v_s_62_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_ofByteArray(lean_object* v_ba_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_byte_array_size(v_ba_74_);
v___x_77_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_77_, 0, v_ba_74_);
lean_ctor_set(v___x_77_, 1, v___x_75_);
lean_ctor_set(v___x_77_, 2, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_toByteArray(lean_object* v_s_80_){
_start:
{
lean_object* v_byteArray_81_; lean_object* v_start_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_byteArray_81_ = lean_ctor_get(v_s_80_, 0);
lean_inc_ref(v_byteArray_81_);
v_start_82_ = lean_ctor_get(v_s_80_, 1);
lean_inc(v_start_82_);
v___x_83_ = l_ByteSlice_size(v_s_80_);
lean_dec_ref(v_s_80_);
v___x_84_ = lean_nat_add(v_start_82_, v___x_83_);
lean_dec(v___x_83_);
v___x_85_ = l_ByteArray_extract(v_byteArray_81_, v_start_82_, v___x_84_);
lean_dec(v___x_84_);
lean_dec_ref(v_byteArray_81_);
return v___x_85_;
}
}
LEAN_EXPORT void l_ByteSlice_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_86_ = stack[0].m_obj;
lean_object* v_b_87_ = stack[1].m_obj;
uint8_t v_res_88_;
v_res_88_ = lean_byteslice_beq(v_a_86_, v_b_87_);
stack->m_num = v_res_88_;
}
LEAN_EXPORT lean_object* l_ByteSlice_beq___boxed(lean_object* v_a_89_, lean_object* v_b_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = lean_byteslice_beq(v_a_89_, v_b_90_);
lean_dec_ref(v_b_90_);
lean_dec_ref(v_a_89_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg___lam__0___boxed(lean_object* v_i_95_, lean_object* v___x_96_, lean_object* v_inst_97_, lean_object* v_f_98_, lean_object* v_as_99_, lean_object* v_newAcc_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg___lam__0(v_i_95_, v___x_96_, v_inst_97_, v_f_98_, v_as_99_, v_newAcc_100_);
lean_dec(v___x_96_);
lean_dec(v_i_95_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(lean_object* v_inst_102_, lean_object* v_f_103_, lean_object* v_as_104_, lean_object* v_i_105_, lean_object* v_acc_106_){
_start:
{
lean_object* v_toApplicative_107_; lean_object* v_toBind_108_; lean_object* v_toPure_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_toApplicative_107_ = lean_ctor_get(v_inst_102_, 0);
v_toBind_108_ = lean_ctor_get(v_inst_102_, 1);
lean_inc(v_toBind_108_);
v_toPure_109_ = lean_ctor_get(v_toApplicative_107_, 1);
v___x_110_ = l_ByteSlice_size(v_as_104_);
v___x_111_ = lean_nat_dec_lt(v_i_105_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
lean_inc(v_toPure_109_);
lean_dec(v___x_110_);
lean_dec(v_toBind_108_);
lean_dec(v_i_105_);
lean_dec_ref(v_as_104_);
lean_dec(v_f_103_);
lean_dec_ref(v_inst_102_);
v___x_112_ = lean_apply_2(v_toPure_109_, lean_box(0), v_acc_106_);
return v___x_112_;
}
else
{
lean_object* v___x_113_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_113_ = lean_unsigned_to_nat(1u);
lean_inc_ref(v_as_104_);
lean_inc(v_f_103_);
lean_inc(v_i_105_);
v___f_114_ = lean_alloc_closure((void*)(l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_114_, 0, v_i_105_);
lean_closure_set(v___f_114_, 1, v___x_113_);
lean_closure_set(v___f_114_, 2, v_inst_102_);
lean_closure_set(v___f_114_, 3, v_f_103_);
lean_closure_set(v___f_114_, 4, v_as_104_);
v___x_115_ = lean_nat_sub(v___x_110_, v___x_113_);
lean_dec(v___x_110_);
v___x_116_ = lean_nat_sub(v___x_115_, v_i_105_);
lean_dec(v_i_105_);
lean_dec(v___x_115_);
v___x_117_ = l_ByteSlice_get(v_as_104_, v___x_116_);
lean_dec(v___x_116_);
lean_dec_ref(v_as_104_);
v___x_118_ = lean_box(v___x_117_);
v___x_119_ = lean_apply_2(v_f_103_, v___x_118_, v_acc_106_);
v___x_120_ = lean_apply_4(v_toBind_108_, lean_box(0), lean_box(0), v___x_119_, v___f_114_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg___lam__0(lean_object* v_i_121_, lean_object* v___x_122_, lean_object* v_inst_123_, lean_object* v_f_124_, lean_object* v_as_125_, lean_object* v_newAcc_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = lean_nat_add(v_i_121_, v___x_122_);
v___x_128_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(v_inst_123_, v_f_124_, v_as_125_, v___x_127_, v_newAcc_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop(lean_object* v_00_u03b2_129_, lean_object* v_m_130_, lean_object* v_inst_131_, lean_object* v_f_132_, lean_object* v_as_133_, lean_object* v_i_134_, lean_object* v_acc_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(v_inst_131_, v_f_132_, v_as_133_, v_i_134_, v_acc_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_foldrM___redArg(lean_object* v_inst_137_, lean_object* v_f_138_, lean_object* v_init_139_, lean_object* v_as_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(v_inst_137_, v_f_138_, v_as_140_, v___x_141_, v_init_139_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_foldrM(lean_object* v_00_u03b2_143_, lean_object* v_m_144_, lean_object* v_inst_145_, lean_object* v_f_146_, lean_object* v_init_147_, lean_object* v_as_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(v_inst_145_, v_f_146_, v_as_148_, v___x_149_, v_init_147_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg___lam__0___boxed(lean_object* v_i_151_, lean_object* v_inst_152_, lean_object* v_f_153_, lean_object* v_as_154_, lean_object* v_____r_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg___lam__0(v_i_151_, v_inst_152_, v_f_153_, v_as_154_, v_____r_155_);
lean_dec(v_i_151_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(lean_object* v_inst_157_, lean_object* v_f_158_, lean_object* v_as_159_, lean_object* v_i_160_){
_start:
{
lean_object* v_toApplicative_161_; lean_object* v_toBind_162_; lean_object* v_toPure_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v_toApplicative_161_ = lean_ctor_get(v_inst_157_, 0);
v_toBind_162_ = lean_ctor_get(v_inst_157_, 1);
lean_inc(v_toBind_162_);
v_toPure_163_ = lean_ctor_get(v_toApplicative_161_, 1);
v___x_164_ = l_ByteSlice_size(v_as_159_);
v___x_165_ = lean_nat_dec_lt(v_i_160_, v___x_164_);
lean_dec(v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_inc(v_toPure_163_);
lean_dec(v_toBind_162_);
lean_dec(v_i_160_);
lean_dec_ref(v_as_159_);
lean_dec(v_f_158_);
lean_dec_ref(v_inst_157_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_apply_2(v_toPure_163_, lean_box(0), v___x_166_);
return v___x_167_;
}
else
{
lean_object* v___f_168_; uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
lean_inc_ref(v_as_159_);
lean_inc(v_f_158_);
lean_inc(v_i_160_);
v___f_168_ = lean_alloc_closure((void*)(l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_168_, 0, v_i_160_);
lean_closure_set(v___f_168_, 1, v_inst_157_);
lean_closure_set(v___f_168_, 2, v_f_158_);
lean_closure_set(v___f_168_, 3, v_as_159_);
v___x_169_ = l_ByteSlice_get(v_as_159_, v_i_160_);
lean_dec(v_i_160_);
lean_dec_ref(v_as_159_);
v___x_170_ = lean_box(v___x_169_);
v___x_171_ = lean_apply_1(v_f_158_, v___x_170_);
v___x_172_ = lean_apply_4(v_toBind_162_, lean_box(0), lean_box(0), v___x_171_, v___f_168_);
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg___lam__0(lean_object* v_i_173_, lean_object* v_inst_174_, lean_object* v_f_175_, lean_object* v_as_176_, lean_object* v_____r_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_add(v_i_173_, v___x_178_);
v___x_180_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(v_inst_174_, v_f_175_, v_as_176_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop(lean_object* v_m_181_, lean_object* v_inst_182_, lean_object* v_f_183_, lean_object* v_as_184_, lean_object* v_i_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(v_inst_182_, v_f_183_, v_as_184_, v_i_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_forM___redArg(lean_object* v_inst_187_, lean_object* v_f_188_, lean_object* v_as_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(v_inst_187_, v_f_188_, v_as_189_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_forM(lean_object* v_m_192_, lean_object* v_inst_193_, lean_object* v_f_194_, lean_object* v_as_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = l___private_Std_Data_ByteSlice_0__ByteSlice_forM_loop___redArg(v_inst_193_, v_f_194_, v_as_195_, v___x_196_);
return v___x_197_;
}
}
lean_object* l_ByteSlice_foldr___redArg___lam__0(lean_object* v_f_198_, uint8_t v_x1_199_, lean_object* v_x2_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_box(v_x1_199_);
v___x_202_ = lean_apply_2(v_f_198_, v___x_201_, v_x2_200_);
return v___x_202_;
}
}
LEAN_EXPORT void l_ByteSlice_foldr___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_198_ = stack[0].m_obj;
uint8_t v_x1_199_ = stack[1].m_num;
lean_object* v_x2_200_ = stack[2].m_obj;
lean_object* v_res_203_;
v_res_203_ = l_ByteSlice_foldr___redArg___lam__0(v_f_198_, v_x1_199_, v_x2_200_);
stack->m_obj
 = v_res_203_;
}
LEAN_EXPORT lean_object* l_ByteSlice_foldr___redArg___lam__0___boxed(lean_object* v_f_204_, lean_object* v_x1_205_, lean_object* v_x2_206_){
_start:
{
uint8_t v_x1_86__boxed_207_; lean_object* v_res_208_; 
v_x1_86__boxed_207_ = lean_unbox(v_x1_205_);
v_res_208_ = l_ByteSlice_foldr___redArg___lam__0(v_f_204_, v_x1_86__boxed_207_, v_x2_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_foldr___redArg(lean_object* v_f_228_, lean_object* v_init_229_, lean_object* v_as_230_){
_start:
{
lean_object* v___f_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___f_231_ = lean_alloc_closure((void*)(l_ByteSlice_foldr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_231_, 0, v_f_228_);
v___x_232_ = ((lean_object*)(l_ByteSlice_foldr___redArg___closed__9));
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(v___x_232_, v___f_231_, v_as_230_, v___x_233_, v_init_229_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_foldr(lean_object* v_00_u03b2_235_, lean_object* v_f_236_, lean_object* v_init_237_, lean_object* v_as_238_){
_start:
{
lean_object* v___f_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___f_239_ = lean_alloc_closure((void*)(l_ByteSlice_foldr___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_239_, 0, v_f_236_);
v___x_240_ = ((lean_object*)(l_ByteSlice_foldr___redArg___closed__9));
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = l___private_Std_Data_ByteSlice_0__ByteSlice_foldrM_loop___redArg(v___x_240_, v___f_239_, v_as_238_, v___x_241_, v_init_237_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_ByteSlice_slice(lean_object* v_s_243_, lean_object* v_start_244_, lean_object* v_stop_245_){
_start:
{
lean_object* v_byteArray_246_; lean_object* v_start_247_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___x_258_; lean_object* v___y_260_; uint8_t v___x_263_; 
v_byteArray_246_ = lean_ctor_get(v_s_243_, 0);
v_start_247_ = lean_ctor_get(v_s_243_, 1);
v___x_258_ = l_ByteSlice_size(v_s_243_);
v___x_263_ = lean_nat_dec_le(v_start_244_, v___x_258_);
if (v___x_263_ == 0)
{
lean_dec(v_start_244_);
lean_inc(v___x_258_);
v___y_260_ = v___x_258_;
goto v___jp_259_;
}
else
{
v___y_260_ = v_start_244_;
goto v___jp_259_;
}
v___jp_248_:
{
lean_object* v_actualStop_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_actualStop_251_ = lean_nat_add(v_start_247_, v___y_250_);
lean_dec(v___y_250_);
v___x_252_ = lean_byte_array_size(v_byteArray_246_);
v___x_253_ = lean_nat_dec_le(v_actualStop_251_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; 
lean_dec(v_actualStop_251_);
lean_dec(v___y_249_);
lean_inc_n(v_start_247_, 2);
lean_inc_ref(v_byteArray_246_);
v___x_254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_254_, 0, v_byteArray_246_);
lean_ctor_set(v___x_254_, 1, v_start_247_);
lean_ctor_set(v___x_254_, 2, v_start_247_);
return v___x_254_;
}
else
{
uint8_t v___x_255_; 
v___x_255_ = lean_nat_dec_le(v___y_249_, v_actualStop_251_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec(v___y_249_);
lean_inc(v_actualStop_251_);
lean_inc_ref(v_byteArray_246_);
v___x_256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_256_, 0, v_byteArray_246_);
lean_ctor_set(v___x_256_, 1, v_actualStop_251_);
lean_ctor_set(v___x_256_, 2, v_actualStop_251_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; 
lean_inc_ref(v_byteArray_246_);
v___x_257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_257_, 0, v_byteArray_246_);
lean_ctor_set(v___x_257_, 1, v___y_249_);
lean_ctor_set(v___x_257_, 2, v_actualStop_251_);
return v___x_257_;
}
}
}
v___jp_259_:
{
lean_object* v_actualStart_261_; uint8_t v___x_262_; 
v_actualStart_261_ = lean_nat_add(v_start_247_, v___y_260_);
lean_dec(v___y_260_);
v___x_262_ = lean_nat_dec_le(v_stop_245_, v___x_258_);
if (v___x_262_ == 0)
{
lean_dec(v_stop_245_);
v___y_249_ = v_actualStart_261_;
v___y_250_ = v___x_258_;
goto v___jp_248_;
}
else
{
lean_dec(v___x_258_);
v___y_249_ = v_actualStart_261_;
v___y_250_ = v_stop_245_;
goto v___jp_248_;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteSlice_slice___boxed(lean_object* v_s_264_, lean_object* v_start_265_, lean_object* v_stop_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_ByteSlice_slice(v_s_264_, v_start_265_, v_stop_266_);
lean_dec_ref(v_s_264_);
return v_res_267_;
}
}
uint8_t l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop(lean_object* v_s_268_, uint8_t v_byte_269_, lean_object* v_i_270_){
_start:
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = l_ByteSlice_size(v_s_268_);
v___x_272_ = lean_nat_dec_lt(v_i_270_, v___x_271_);
lean_dec(v___x_271_);
if (v___x_272_ == 0)
{
lean_dec(v_i_270_);
return v___x_272_;
}
else
{
uint8_t v___x_273_; uint8_t v___x_274_; 
v___x_273_ = l_ByteSlice_get(v_s_268_, v_i_270_);
v___x_274_ = lean_uint8_dec_eq(v___x_273_, v_byte_269_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_add(v_i_270_, v___x_275_);
lean_dec(v_i_270_);
v_i_270_ = v___x_276_;
goto _start;
}
else
{
lean_dec(v_i_270_);
return v___x_272_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_268_ = stack[0].m_obj;
uint8_t v_byte_269_ = stack[1].m_num;
lean_object* v_i_270_ = stack[2].m_obj;
uint8_t v_res_278_;
v_res_278_ = l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop(v_s_268_, v_byte_269_, v_i_270_);
stack->m_num = v_res_278_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop___boxed(lean_object* v_s_279_, lean_object* v_byte_280_, lean_object* v_i_281_){
_start:
{
uint8_t v_byte_boxed_282_; uint8_t v_res_283_; lean_object* v_r_284_; 
v_byte_boxed_282_ = lean_unbox(v_byte_280_);
v_res_283_ = l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop(v_s_279_, v_byte_boxed_282_, v_i_281_);
lean_dec_ref(v_s_279_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
uint8_t l_ByteSlice_contains(lean_object* v_s_285_, uint8_t v_byte_286_){
_start:
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = l___private_Std_Data_ByteSlice_0__ByteSlice_contains_loop(v_s_285_, v_byte_286_, v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT void l_ByteSlice_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_285_ = stack[0].m_obj;
uint8_t v_byte_286_ = stack[1].m_num;
uint8_t v_res_289_;
v_res_289_ = l_ByteSlice_contains(v_s_285_, v_byte_286_);
stack->m_num = v_res_289_;
}
LEAN_EXPORT lean_object* l_ByteSlice_contains___boxed(lean_object* v_s_290_, lean_object* v_byte_291_){
_start:
{
uint8_t v_byte_boxed_292_; uint8_t v_res_293_; lean_object* v_r_294_; 
v_byte_boxed_292_ = lean_unbox(v_byte_291_);
v_res_293_ = l_ByteSlice_contains(v_s_290_, v_byte_boxed_292_);
lean_dec_ref(v_s_290_);
v_r_294_ = lean_box(v_res_293_);
return v_r_294_;
}
}
LEAN_EXPORT lean_object* l_ByteArray_toByteSlice(lean_object* v_as_295_, lean_object* v_start_296_, lean_object* v_stop_297_){
_start:
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = lean_byte_array_size(v_as_295_);
v___x_299_ = lean_nat_dec_le(v_stop_297_, v___x_298_);
if (v___x_299_ == 0)
{
uint8_t v___x_300_; 
lean_dec(v_stop_297_);
v___x_300_ = lean_nat_dec_le(v_start_296_, v___x_298_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
lean_dec(v_start_296_);
v___x_301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_301_, 0, v_as_295_);
lean_ctor_set(v___x_301_, 1, v___x_298_);
lean_ctor_set(v___x_301_, 2, v___x_298_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; 
v___x_302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_302_, 0, v_as_295_);
lean_ctor_set(v___x_302_, 1, v_start_296_);
lean_ctor_set(v___x_302_, 2, v___x_298_);
return v___x_302_;
}
}
else
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_le(v_start_296_, v_stop_297_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
lean_dec(v_start_296_);
lean_inc(v_stop_297_);
v___x_304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_304_, 0, v_as_295_);
lean_ctor_set(v___x_304_, 1, v_stop_297_);
lean_ctor_set(v___x_304_, 2, v_stop_297_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_305_, 0, v_as_295_);
lean_ctor_set(v___x_305_, 1, v_start_296_);
lean_ctor_set(v___x_305_, 2, v_stop_297_);
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice___lam__0(lean_object* v_xs_306_, lean_object* v_range_307_){
_start:
{
lean_object* v_lower_308_; lean_object* v_upper_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___y_313_; uint8_t v___x_319_; 
v_lower_308_ = lean_ctor_get(v_range_307_, 0);
lean_inc(v_lower_308_);
v_upper_309_ = lean_ctor_get(v_range_307_, 1);
lean_inc(v_upper_309_);
lean_dec_ref(v_range_307_);
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = lean_byte_array_size(v_xs_306_);
v___x_319_ = lean_nat_dec_le(v_lower_308_, v___x_310_);
if (v___x_319_ == 0)
{
v___y_313_ = v_lower_308_;
goto v___jp_312_;
}
else
{
lean_dec(v_lower_308_);
v___y_313_ = v___x_310_;
goto v___jp_312_;
}
v___jp_312_:
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_314_ = lean_unsigned_to_nat(1u);
v___x_315_ = lean_nat_add(v_upper_309_, v___x_314_);
lean_dec(v_upper_309_);
v___x_316_ = lean_nat_dec_le(v___x_315_, v___x_311_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
lean_dec(v___x_315_);
v___x_317_ = l_ByteArray_toByteSlice(v_xs_306_, v___y_313_, v___x_311_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; 
v___x_318_ = l_ByteArray_toByteSlice(v_xs_306_, v___y_313_, v___x_315_);
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__1___lam__0(lean_object* v_xs_322_, lean_object* v_range_323_){
_start:
{
lean_object* v_lower_324_; lean_object* v_upper_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___y_329_; uint8_t v___x_333_; 
v_lower_324_ = lean_ctor_get(v_range_323_, 0);
lean_inc(v_lower_324_);
v_upper_325_ = lean_ctor_get(v_range_323_, 1);
lean_inc(v_upper_325_);
lean_dec_ref(v_range_323_);
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_byte_array_size(v_xs_322_);
v___x_333_ = lean_nat_dec_le(v_lower_324_, v___x_326_);
if (v___x_333_ == 0)
{
v___y_329_ = v_lower_324_;
goto v___jp_328_;
}
else
{
lean_dec(v_lower_324_);
v___y_329_ = v___x_326_;
goto v___jp_328_;
}
v___jp_328_:
{
uint8_t v___x_330_; 
v___x_330_ = lean_nat_dec_le(v_upper_325_, v___x_327_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec(v_upper_325_);
v___x_331_ = l_ByteArray_toByteSlice(v_xs_322_, v___y_329_, v___x_327_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; 
v___x_332_ = l_ByteArray_toByteSlice(v_xs_322_, v___y_329_, v_upper_325_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__2___lam__0(lean_object* v_xs_336_, lean_object* v_range_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_byte_array_size(v_xs_336_);
v___x_340_ = lean_nat_dec_le(v_range_337_, v___x_338_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
v___x_341_ = l_ByteArray_toByteSlice(v_xs_336_, v_range_337_, v___x_339_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; 
lean_dec(v_range_337_);
v___x_342_ = l_ByteArray_toByteSlice(v_xs_336_, v___x_338_, v___x_339_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__3___lam__0(lean_object* v_xs_345_, lean_object* v_range_346_){
_start:
{
lean_object* v_lower_347_; lean_object* v_upper_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___y_353_; lean_object* v___x_358_; uint8_t v___x_359_; 
v_lower_347_ = lean_ctor_get(v_range_346_, 0);
v_upper_348_ = lean_ctor_get(v_range_346_, 1);
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_byte_array_size(v_xs_345_);
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_358_ = lean_nat_add(v_lower_347_, v___x_351_);
v___x_359_ = lean_nat_dec_le(v___x_358_, v___x_349_);
if (v___x_359_ == 0)
{
v___y_353_ = v___x_358_;
goto v___jp_352_;
}
else
{
lean_dec(v___x_358_);
v___y_353_ = v___x_349_;
goto v___jp_352_;
}
v___jp_352_:
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_nat_add(v_upper_348_, v___x_351_);
v___x_355_ = lean_nat_dec_le(v___x_354_, v___x_350_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
lean_dec(v___x_354_);
v___x_356_ = l_ByteArray_toByteSlice(v_xs_345_, v___y_353_, v___x_350_);
return v___x_356_;
}
else
{
lean_object* v___x_357_; 
v___x_357_ = l_ByteArray_toByteSlice(v_xs_345_, v___y_353_, v___x_354_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__3___lam__0___boxed(lean_object* v_xs_360_, lean_object* v_range_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_instSliceableByteArrayNatByteSlice__3___lam__0(v_xs_360_, v_range_361_);
lean_dec_ref(v_range_361_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__4___lam__0(lean_object* v_xs_365_, lean_object* v_range_366_){
_start:
{
lean_object* v_lower_367_; lean_object* v_upper_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___y_372_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_lower_367_ = lean_ctor_get(v_range_366_, 0);
lean_inc(v_lower_367_);
v_upper_368_ = lean_ctor_get(v_range_366_, 1);
lean_inc(v_upper_368_);
lean_dec_ref(v_range_366_);
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = lean_byte_array_size(v_xs_365_);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_add(v_lower_367_, v___x_376_);
lean_dec(v_lower_367_);
v___x_378_ = lean_nat_dec_le(v___x_377_, v___x_369_);
if (v___x_378_ == 0)
{
v___y_372_ = v___x_377_;
goto v___jp_371_;
}
else
{
lean_dec(v___x_377_);
v___y_372_ = v___x_369_;
goto v___jp_371_;
}
v___jp_371_:
{
uint8_t v___x_373_; 
v___x_373_ = lean_nat_dec_le(v_upper_368_, v___x_370_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
lean_dec(v_upper_368_);
v___x_374_ = l_ByteArray_toByteSlice(v_xs_365_, v___y_372_, v___x_370_);
return v___x_374_;
}
else
{
lean_object* v___x_375_; 
v___x_375_ = l_ByteArray_toByteSlice(v_xs_365_, v___y_372_, v_upper_368_);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__5___lam__0(lean_object* v_xs_381_, lean_object* v_range_382_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_byte_array_size(v_xs_381_);
v___x_385_ = lean_unsigned_to_nat(1u);
v___x_386_ = lean_nat_add(v_range_382_, v___x_385_);
v___x_387_ = lean_nat_dec_le(v___x_386_, v___x_383_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
v___x_388_ = l_ByteArray_toByteSlice(v_xs_381_, v___x_386_, v___x_384_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; 
lean_dec(v___x_386_);
v___x_389_ = l_ByteArray_toByteSlice(v_xs_381_, v___x_383_, v___x_384_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__5___lam__0___boxed(lean_object* v_xs_390_, lean_object* v_range_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_instSliceableByteArrayNatByteSlice__5___lam__0(v_xs_390_, v_range_391_);
lean_dec(v_range_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__6___lam__0(lean_object* v_xs_395_, lean_object* v_range_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_byte_array_size(v_xs_395_);
v___x_399_ = lean_unsigned_to_nat(1u);
v___x_400_ = lean_nat_add(v_range_396_, v___x_399_);
v___x_401_ = lean_nat_dec_le(v___x_400_, v___x_398_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_dec(v___x_400_);
v___x_402_ = l_ByteArray_toByteSlice(v_xs_395_, v___x_397_, v___x_398_);
return v___x_402_;
}
else
{
lean_object* v___x_403_; 
v___x_403_ = l_ByteArray_toByteSlice(v_xs_395_, v___x_397_, v___x_400_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__6___lam__0___boxed(lean_object* v_xs_404_, lean_object* v_range_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_instSliceableByteArrayNatByteSlice__6___lam__0(v_xs_404_, v_range_405_);
lean_dec(v_range_405_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__7___lam__0(lean_object* v_xs_409_, lean_object* v_range_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_byte_array_size(v_xs_409_);
v___x_413_ = lean_nat_dec_le(v_range_410_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
lean_dec(v_range_410_);
v___x_414_ = l_ByteArray_toByteSlice(v_xs_409_, v___x_411_, v___x_412_);
return v___x_414_;
}
else
{
lean_object* v___x_415_; 
v___x_415_ = l_ByteArray_toByteSlice(v_xs_409_, v___x_411_, v_range_410_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteArrayNatByteSlice__8___lam__0(lean_object* v_xs_418_, lean_object* v_x_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_byte_array_size(v_xs_418_);
v___x_422_ = l_ByteArray_toByteSlice(v_xs_418_, v___x_420_, v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat___lam__0(lean_object* v_xs_425_, lean_object* v_range_426_){
_start:
{
lean_object* v_lower_427_; lean_object* v_upper_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___y_432_; uint8_t v___x_438_; 
v_lower_427_ = lean_ctor_get(v_range_426_, 0);
lean_inc(v_lower_427_);
v_upper_428_ = lean_ctor_get(v_range_426_, 1);
lean_inc(v_upper_428_);
lean_dec_ref(v_range_426_);
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = l_ByteSlice_size(v_xs_425_);
v___x_438_ = lean_nat_dec_le(v_lower_427_, v___x_429_);
if (v___x_438_ == 0)
{
v___y_432_ = v_lower_427_;
goto v___jp_431_;
}
else
{
lean_dec(v_lower_427_);
v___y_432_ = v___x_429_;
goto v___jp_431_;
}
v___jp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = lean_nat_add(v_upper_428_, v___x_433_);
lean_dec(v_upper_428_);
v___x_435_ = lean_nat_dec_le(v___x_434_, v___x_430_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
lean_dec(v___x_434_);
v___x_436_ = l_ByteSlice_slice(v_xs_425_, v___y_432_, v___x_430_);
return v___x_436_;
}
else
{
lean_object* v___x_437_; 
lean_dec(v___x_430_);
v___x_437_ = l_ByteSlice_slice(v_xs_425_, v___y_432_, v___x_434_);
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat___lam__0___boxed(lean_object* v_xs_439_, lean_object* v_range_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_instSliceableByteSliceNat___lam__0(v_xs_439_, v_range_440_);
lean_dec_ref(v_xs_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__1___lam__0(lean_object* v_xs_444_, lean_object* v_range_445_){
_start:
{
lean_object* v_lower_446_; lean_object* v_upper_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___y_451_; uint8_t v___x_455_; 
v_lower_446_ = lean_ctor_get(v_range_445_, 0);
lean_inc(v_lower_446_);
v_upper_447_ = lean_ctor_get(v_range_445_, 1);
lean_inc(v_upper_447_);
lean_dec_ref(v_range_445_);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = l_ByteSlice_size(v_xs_444_);
v___x_455_ = lean_nat_dec_le(v_lower_446_, v___x_448_);
if (v___x_455_ == 0)
{
v___y_451_ = v_lower_446_;
goto v___jp_450_;
}
else
{
lean_dec(v_lower_446_);
v___y_451_ = v___x_448_;
goto v___jp_450_;
}
v___jp_450_:
{
uint8_t v___x_452_; 
v___x_452_ = lean_nat_dec_le(v_upper_447_, v___x_449_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
lean_dec(v_upper_447_);
v___x_453_ = l_ByteSlice_slice(v_xs_444_, v___y_451_, v___x_449_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; 
lean_dec(v___x_449_);
v___x_454_ = l_ByteSlice_slice(v_xs_444_, v___y_451_, v_upper_447_);
return v___x_454_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__1___lam__0___boxed(lean_object* v_xs_456_, lean_object* v_range_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_instSliceableByteSliceNat__1___lam__0(v_xs_456_, v_range_457_);
lean_dec_ref(v_xs_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__2___lam__0(lean_object* v_xs_461_, lean_object* v_range_462_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = l_ByteSlice_size(v_xs_461_);
v___x_465_ = lean_nat_dec_le(v_range_462_, v___x_463_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
v___x_466_ = l_ByteSlice_slice(v_xs_461_, v_range_462_, v___x_464_);
return v___x_466_;
}
else
{
lean_object* v___x_467_; 
lean_dec(v_range_462_);
v___x_467_ = l_ByteSlice_slice(v_xs_461_, v___x_463_, v___x_464_);
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__2___lam__0___boxed(lean_object* v_xs_468_, lean_object* v_range_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_instSliceableByteSliceNat__2___lam__0(v_xs_468_, v_range_469_);
lean_dec_ref(v_xs_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__3___lam__0(lean_object* v_xs_473_, lean_object* v_range_474_){
_start:
{
lean_object* v_lower_475_; lean_object* v_upper_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___y_481_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_lower_475_ = lean_ctor_get(v_range_474_, 0);
v_upper_476_ = lean_ctor_get(v_range_474_, 1);
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = l_ByteSlice_size(v_xs_473_);
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_486_ = lean_nat_add(v_lower_475_, v___x_479_);
v___x_487_ = lean_nat_dec_le(v___x_486_, v___x_477_);
if (v___x_487_ == 0)
{
v___y_481_ = v___x_486_;
goto v___jp_480_;
}
else
{
lean_dec(v___x_486_);
v___y_481_ = v___x_477_;
goto v___jp_480_;
}
v___jp_480_:
{
lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_482_ = lean_nat_add(v_upper_476_, v___x_479_);
v___x_483_ = lean_nat_dec_le(v___x_482_, v___x_478_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; 
lean_dec(v___x_482_);
v___x_484_ = l_ByteSlice_slice(v_xs_473_, v___y_481_, v___x_478_);
return v___x_484_;
}
else
{
lean_object* v___x_485_; 
lean_dec(v___x_478_);
v___x_485_ = l_ByteSlice_slice(v_xs_473_, v___y_481_, v___x_482_);
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__3___lam__0___boxed(lean_object* v_xs_488_, lean_object* v_range_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_instSliceableByteSliceNat__3___lam__0(v_xs_488_, v_range_489_);
lean_dec_ref(v_range_489_);
lean_dec_ref(v_xs_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__4___lam__0(lean_object* v_xs_493_, lean_object* v_range_494_){
_start:
{
lean_object* v_lower_495_; lean_object* v_upper_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___y_500_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_lower_495_ = lean_ctor_get(v_range_494_, 0);
lean_inc(v_lower_495_);
v_upper_496_ = lean_ctor_get(v_range_494_, 1);
lean_inc(v_upper_496_);
lean_dec_ref(v_range_494_);
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = l_ByteSlice_size(v_xs_493_);
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_add(v_lower_495_, v___x_504_);
lean_dec(v_lower_495_);
v___x_506_ = lean_nat_dec_le(v___x_505_, v___x_497_);
if (v___x_506_ == 0)
{
v___y_500_ = v___x_505_;
goto v___jp_499_;
}
else
{
lean_dec(v___x_505_);
v___y_500_ = v___x_497_;
goto v___jp_499_;
}
v___jp_499_:
{
uint8_t v___x_501_; 
v___x_501_ = lean_nat_dec_le(v_upper_496_, v___x_498_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_dec(v_upper_496_);
v___x_502_ = l_ByteSlice_slice(v_xs_493_, v___y_500_, v___x_498_);
return v___x_502_;
}
else
{
lean_object* v___x_503_; 
lean_dec(v___x_498_);
v___x_503_ = l_ByteSlice_slice(v_xs_493_, v___y_500_, v_upper_496_);
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__4___lam__0___boxed(lean_object* v_xs_507_, lean_object* v_range_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_instSliceableByteSliceNat__4___lam__0(v_xs_507_, v_range_508_);
lean_dec_ref(v_xs_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__5___lam__0(lean_object* v_xs_512_, lean_object* v_range_513_){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = l_ByteSlice_size(v_xs_512_);
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_add(v_range_513_, v___x_516_);
v___x_518_ = lean_nat_dec_le(v___x_517_, v___x_514_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
v___x_519_ = l_ByteSlice_slice(v_xs_512_, v___x_517_, v___x_515_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; 
lean_dec(v___x_517_);
v___x_520_ = l_ByteSlice_slice(v_xs_512_, v___x_514_, v___x_515_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__5___lam__0___boxed(lean_object* v_xs_521_, lean_object* v_range_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_instSliceableByteSliceNat__5___lam__0(v_xs_521_, v_range_522_);
lean_dec(v_range_522_);
lean_dec_ref(v_xs_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__6___lam__0(lean_object* v_xs_526_, lean_object* v_range_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = l_ByteSlice_size(v_xs_526_);
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_add(v_range_527_, v___x_530_);
v___x_532_ = lean_nat_dec_le(v___x_531_, v___x_529_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; 
lean_dec(v___x_531_);
v___x_533_ = l_ByteSlice_slice(v_xs_526_, v___x_528_, v___x_529_);
return v___x_533_;
}
else
{
lean_object* v___x_534_; 
lean_dec(v___x_529_);
v___x_534_ = l_ByteSlice_slice(v_xs_526_, v___x_528_, v___x_531_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__6___lam__0___boxed(lean_object* v_xs_535_, lean_object* v_range_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_instSliceableByteSliceNat__6___lam__0(v_xs_535_, v_range_536_);
lean_dec(v_range_536_);
lean_dec_ref(v_xs_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__7___lam__0(lean_object* v_xs_540_, lean_object* v_range_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = l_ByteSlice_size(v_xs_540_);
v___x_544_ = lean_nat_dec_le(v_range_541_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; 
lean_dec(v_range_541_);
v___x_545_ = l_ByteSlice_slice(v_xs_540_, v___x_542_, v___x_543_);
return v___x_545_;
}
else
{
lean_object* v___x_546_; 
lean_dec(v___x_543_);
v___x_546_ = l_ByteSlice_slice(v_xs_540_, v___x_542_, v_range_541_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__7___lam__0___boxed(lean_object* v_xs_547_, lean_object* v_range_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_instSliceableByteSliceNat__7___lam__0(v_xs_547_, v_range_548_);
lean_dec_ref(v_xs_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__8___lam__0(lean_object* v_xs_552_, lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = l_ByteSlice_size(v_xs_552_);
v___x_556_ = l_ByteSlice_slice(v_xs_552_, v___x_554_, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_instSliceableByteSliceNat__8___lam__0___boxed(lean_object* v_xs_557_, lean_object* v_x_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_instSliceableByteSliceNat__8___lam__0(v_xs_557_, v_x_558_);
lean_dec_ref(v_xs_557_);
return v_res_559_;
}
}
lean_object* runtime_initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Slice_Notation(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_ByteSlice(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
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
lean_object* initialize_Init_Data_ByteArray_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Slice_Notation(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_ByteSlice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ByteArray_Basic(builtin);
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
