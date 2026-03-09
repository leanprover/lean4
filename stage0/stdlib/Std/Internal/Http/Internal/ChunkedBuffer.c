// Lean compiler output
// Module: Std.Internal.Http.Internal.ChunkedBuffer
// Imports: import Init.Data.ToString import Init.Data.Array.Lemmas public import Init.Data.String public import Init.Data.ByteArray
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_empty___closed__0 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value;
static const lean_ctor_object l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_empty___closed__1 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_ChunkedBuffer_empty = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_write(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_append(lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
lean_object* lean_byte_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeChar(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeChar___boxed(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeString___boxed(lean_object*, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value;
static const lean_ctor_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value),((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value)}};
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value;
static const lean_ctor_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value),((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value),((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value),((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value),((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value)}};
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value;
static const lean_ctor_object l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value),((lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value)}};
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9_value;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_byte_array(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofByteArray(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_ChunkedBuffer_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_isEmpty___boxed(lean_object*);
LEAN_EXPORT const lean_object* l_Std_Http_Internal_ChunkedBuffer_instInhabited = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_ChunkedBuffer_instEmptyCollection = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value;
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_ChunkedBuffer_ofByteArray, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value;
static const lean_closure_object l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_ChunkedBuffer_ofArray, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0 = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray = (const lean_object*)&l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_push(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_14; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_5 = x_1;
x_6 = x_14;
goto block_13;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc_ref(x_2);
x_7 = lean_array_push(x_3, x_2);
x_8 = lean_byte_array_size(x_2);
lean_dec_ref(x_2);
x_9 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_7);
x_10 = x_5;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_write(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_14; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
x_5 = x_1;
x_6 = x_14;
goto block_13;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc_ref(x_2);
x_7 = lean_array_push(x_3, x_2);
x_8 = lean_byte_array_size(x_2);
lean_dec_ref(x_2);
x_9 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_5, 0, x_7);
x_10 = x_5;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_append(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_15; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
x_7 = x_2;
x_8 = x_15;
goto block_14;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Array_append___redArg(x_3, x_5);
lean_dec_ref(x_5);
x_10 = lean_nat_add(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_10);
lean_ctor_set(x_7, 0, x_9);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeChar(lean_object* x_1, uint32_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_20; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
x_5 = x_1;
x_6 = x_20;
goto block_19;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_20;
goto block_19;
}
block_19:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_uint32_to_uint8(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_mk_empty_array_with_capacity(x_8);
x_10 = lean_box(x_7);
x_11 = lean_array_push(x_9, x_10);
x_12 = lean_byte_array_mk(x_11);
lean_inc_ref(x_12);
x_13 = lean_array_push(x_3, x_12);
x_14 = lean_byte_array_size(x_12);
lean_dec_ref(x_12);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_15);
lean_ctor_set(x_5, 0, x_13);
x_16 = x_5;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l_Std_Http_Internal_ChunkedBuffer_writeChar(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_15; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
x_5 = x_1;
x_6 = x_15;
goto block_14;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_string_to_utf8(x_2);
lean_inc_ref(x_7);
x_8 = lean_array_push(x_3, x_7);
x_9 = lean_byte_array_size(x_7);
lean_dec_ref(x_7);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_10);
lean_ctor_set(x_5, 0, x_8);
x_11 = x_5;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_writeString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Http_Internal_ChunkedBuffer_writeString(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_byte_array_size(x_2);
x_6 = lean_byte_array_size(x_3);
x_7 = lean_byte_array_copy_slice(x_3, x_4, x_2, x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(x_4, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_toByteArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_empty_byte_array(x_3);
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = ((lean_object*)(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9));
x_10 = lean_nat_dec_lt(x_8, x_5);
if (x_10 == 0)
{
lean_dec_ref(x_2);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_box(x_6);
x_12 = lean_alloc_closure((void*)(l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed), 3, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_nat_dec_le(x_5, x_5);
if (x_13 == 0)
{
if (x_10 == 0)
{
lean_dec_ref(x_12);
lean_dec_ref(x_2);
return x_7;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_5);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_9, x_12, x_2, x_14, x_15, x_7);
return x_16;
}
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_5);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_9, x_12, x_2, x_17, x_18, x_7);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_fget(x_2, x_20);
lean_dec_ref(x_2);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofByteArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
lean_inc_ref(x_1);
x_4 = lean_array_push(x_3, x_1);
x_5 = lean_byte_array_size(x_1);
lean_dec_ref(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_byte_array_size(x_2);
x_4 = lean_nat_add(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_ofArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_get_size(x_1);
x_4 = ((lean_object*)(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9));
x_5 = lean_nat_dec_lt(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = ((lean_object*)(l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0));
x_8 = lean_nat_dec_le(x_3, x_3);
if (x_8 == 0)
{
if (x_5 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_3);
lean_inc_ref(x_1);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_4, x_7, x_1, x_10, x_11, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_3);
lean_inc_ref(x_1);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_4, x_7, x_1, x_14, x_15, x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_ChunkedBuffer_isEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_ChunkedBuffer_isEmpty___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Http_Internal_ChunkedBuffer_isEmpty(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Internal_ChunkedBuffer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Internal_ChunkedBuffer(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Internal_ChunkedBuffer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Internal_ChunkedBuffer(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Internal_ChunkedBuffer(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Internal_ChunkedBuffer(builtin);
}
#ifdef __cplusplus
}
#endif
