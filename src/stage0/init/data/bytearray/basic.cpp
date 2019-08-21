// Lean compiler output
// Module: init.data.bytearray.basic
// Imports: init.data.array.basic init.data.uint init.data.option.basic
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
namespace lean {
obj* uint8_to_nat(uint8);
}
obj* l_ByteArray_mk___boxed(obj*);
obj* l_ByteArray_mkEmpty___boxed(obj*);
obj* l_ByteArray_toList___boxed(obj*);
obj* l_ByteArray_toListAux___boxed(obj*, obj*, obj*);
extern obj* l_List_repr___rarg___closed__3;
obj* l_ByteArray_isEmpty___boxed(obj*);
obj* l_List_toByteArrayAux(obj*, obj*);
namespace lean {
obj* byte_array_size(obj*);
}
obj* l_ByteArray_data___boxed(obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_ByteArray_toList(obj*);
obj* l_List_toStringAux___main___at_ByteArray_HasToString___spec__2___boxed(obj*, obj*);
obj* l_ByteArray_toListAux___main___boxed(obj*, obj*, obj*);
namespace lean {
obj* byte_array_mk(obj*);
}
obj* l_Nat_repr(obj*);
extern obj* l_List_repr___rarg___closed__2;
obj* l_ByteArray_HasToString(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
extern obj* l_List_reprAux___main___rarg___closed__1;
obj* l_ByteArray_empty;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_List_toString___at_ByteArray_HasToString___spec__1(obj*);
obj* l_ByteArray_get___boxed(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_ByteArray_mkEmpty(obj*);
namespace lean {
obj* byte_array_data(obj*);
}
obj* l_ByteArray_toListAux___main(obj*, obj*, obj*);
obj* l_ByteArray_empty___closed__1;
obj* l_List_toByteArray(obj*);
obj* l_ByteArray_HasToString___boxed(obj*);
obj* l_ByteArray_set___boxed(obj*, obj*, obj*);
namespace lean {
uint8 byte_array_get(obj*, obj*);
}
obj* l_ByteArray_push___boxed(obj*, obj*);
obj* l_List_toStringAux___main___at_ByteArray_HasToString___spec__2(uint8, obj*);
obj* l_List_toByteArrayAux___main(obj*, obj*);
obj* l_ByteArray_Inhabited;
obj* l_ByteArray_toListAux(obj*, obj*, obj*);
uint8 l_ByteArray_isEmpty(obj*);
obj* l_ByteArray_size___boxed(obj*);
extern obj* l_List_repr___rarg___closed__1;
namespace lean {
obj* byte_array_set(obj*, obj*, uint8);
}
namespace lean {
obj* byte_array_push(obj*, uint8);
}
extern obj* l_String_splitAux___main___closed__1;
obj* l_ByteArray_mk___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::byte_array_mk(x_1);
return x_2;
}
}
obj* l_ByteArray_data___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::byte_array_data(x_1);
return x_2;
}
}
obj* l_ByteArray_mkEmpty___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::mk_empty_byte_array(x_1);
return x_2;
}
}
obj* _init_l_ByteArray_empty___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::mk_empty_byte_array(x_1);
return x_2;
}
}
obj* _init_l_ByteArray_empty() {
_start:
{
obj* x_1; 
x_1 = l_ByteArray_empty___closed__1;
return x_1;
}
}
obj* _init_l_ByteArray_Inhabited() {
_start:
{
obj* x_1; 
x_1 = l_ByteArray_empty;
return x_1;
}
}
obj* l_ByteArray_push___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = lean::byte_array_push(x_1, x_3);
return x_4;
}
}
obj* l_ByteArray_size___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::byte_array_size(x_1);
return x_2;
}
}
obj* l_ByteArray_get___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::byte_array_get(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_ByteArray_set___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
x_5 = lean::byte_array_set(x_1, x_2, x_4);
return x_5;
}
}
uint8 l_ByteArray_isEmpty(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::byte_array_size(x_1);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_ByteArray_isEmpty___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_ByteArray_isEmpty(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_ByteArray_toListAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::byte_array_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = l_List_reverse___rarg(x_3);
return x_6;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_add(x_2, x_7);
x_9 = lean::byte_array_get(x_1, x_2);
lean::dec(x_2);
x_10 = lean::box(x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_3);
x_2 = x_8;
x_3 = x_11;
goto _start;
}
}
}
obj* l_ByteArray_toListAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_ByteArray_toListAux___main(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_ByteArray_toListAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_ByteArray_toListAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_ByteArray_toListAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_ByteArray_toListAux(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_ByteArray_toList(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(0u);
x_4 = l_ByteArray_toListAux___main(x_1, x_3, x_2);
return x_4;
}
}
obj* l_ByteArray_toList___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ByteArray_toList(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_toByteArrayAux___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_2;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::unbox(x_3);
lean::dec(x_3);
x_6 = lean::byte_array_push(x_2, x_5);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
obj* l_List_toByteArrayAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_toByteArrayAux___main(x_1, x_2);
return x_3;
}
}
obj* l_List_toByteArray(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_ByteArray_empty;
x_3 = l_List_toByteArrayAux___main(x_1, x_2);
return x_3;
}
}
obj* l_List_toStringAux___main___at_ByteArray_HasToString___spec__2(uint8 x_1, obj* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_6 = lean::unbox(x_4);
lean::dec(x_4);
x_7 = lean::uint8_to_nat(x_6);
x_8 = l_Nat_repr(x_7);
x_9 = l_List_reprAux___main___rarg___closed__1;
x_10 = lean::string_append(x_9, x_8);
lean::dec(x_8);
x_11 = l_List_toStringAux___main___at_ByteArray_HasToString___spec__2(x_1, x_5);
x_12 = lean::string_append(x_10, x_11);
lean::dec(x_11);
return x_12;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_13; 
x_13 = l_String_splitAux___main___closed__1;
return x_13;
}
else
{
obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; 
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_2, 1);
lean::inc(x_15);
lean::dec(x_2);
x_16 = lean::unbox(x_14);
lean::dec(x_14);
x_17 = lean::uint8_to_nat(x_16);
x_18 = l_Nat_repr(x_17);
x_19 = 0;
x_20 = l_List_toStringAux___main___at_ByteArray_HasToString___spec__2(x_19, x_15);
x_21 = lean::string_append(x_18, x_20);
lean::dec(x_20);
return x_21;
}
}
}
}
obj* l_List_toString___at_ByteArray_HasToString___spec__1(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8 x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_ByteArray_HasToString___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean::string_append(x_5, x_4);
lean::dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean::string_append(x_6, x_7);
return x_8;
}
}
}
obj* l_ByteArray_HasToString(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_ByteArray_toList(x_1);
x_3 = l_List_toString___at_ByteArray_HasToString___spec__1(x_2);
return x_3;
}
}
obj* l_List_toStringAux___main___at_ByteArray_HasToString___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_List_toStringAux___main___at_ByteArray_HasToString___spec__2(x_3, x_2);
return x_4;
}
}
obj* l_ByteArray_HasToString___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ByteArray_HasToString(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_data_array_basic(obj*);
obj* initialize_init_data_uint(obj*);
obj* initialize_init_data_option_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_bytearray_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_array_basic(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_uint(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_option_basic(w);
if (lean::io_result_is_error(w)) return w;
l_ByteArray_empty___closed__1 = _init_l_ByteArray_empty___closed__1();
lean::mark_persistent(l_ByteArray_empty___closed__1);
l_ByteArray_empty = _init_l_ByteArray_empty();
lean::mark_persistent(l_ByteArray_empty);
l_ByteArray_Inhabited = _init_l_ByteArray_Inhabited();
lean::mark_persistent(l_ByteArray_Inhabited);
return w;
}
