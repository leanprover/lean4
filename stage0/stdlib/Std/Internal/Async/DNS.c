// Lean compiler output
// Module: Std.Internal.Async.DNS
// Imports: public import Std.Time public import Std.Internal.UV public import Std.Internal.Async.Basic
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_dns_get_name(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__1(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___closed__4;
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_dns_get_info(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
static lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__1;
static lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___closed__1;
static lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___closed__2;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Function_uncurry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___closed__3;
static lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__0(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_io_user_error(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec_ref(x_9);
x_16 = lean_io_promise_result_opt(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = lean_task_map(x_1, x_16, x_17, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__1(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("the promise linked to the Async was dropped", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__1;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_DNS_getAddrInfo___lam__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_14; 
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_24; 
x_24 = 0;
x_14 = x_24;
goto block_23;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_unbox(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = 1;
x_14 = x_27;
goto block_23;
}
else
{
uint8_t x_28; 
x_28 = 2;
x_14 = x_28;
goto block_23;
}
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = 0;
x_12 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_10, x_11, x_9, x_5);
return x_12;
}
block_23:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__2;
x_16 = lean_uv_dns_get_info(x_1, x_2, x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 1);
x_5 = x_15;
x_6 = x_16;
x_7 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_5 = x_15;
x_6 = x_19;
x_7 = lean_box(0);
goto block_13;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_ctor_set_tag(x_16, 0);
x_5 = x_15;
x_6 = x_16;
x_7 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_5 = x_15;
x_6 = x_22;
x_7 = lean_box(0);
goto block_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getAddrInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_DNS_getAddrInfo(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_io_user_error(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_DNS_getNameInfo___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec_ref(x_9);
x_16 = lean_io_promise_result_opt(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = lean_task_map(x_1, x_16, x_17, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_DNS_getNameInfo___lam__2(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_DNS_getNameInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_DNS_getNameInfo___lam__0), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_DNS_getNameInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_DNS_getNameInfo___closed__0;
x_2 = lean_alloc_closure((void*)(l_Function_uncurry), 5, 4);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, lean_box(0));
lean_closure_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_DNS_getNameInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_DNS_getNameInfo___lam__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_DNS_getNameInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_DNS_getNameInfo___closed__2;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_DNS_getNameInfo___lam__2___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_DNS_getNameInfo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_DNS_getNameInfo___closed__1;
x_2 = lean_alloc_closure((void*)(l_Except_map), 5, 4);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, lean_box(0));
lean_closure_set(x_2, 3, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_40; 
x_7 = l_Std_Internal_IO_Async_DNS_getNameInfo___closed__3;
x_40 = lean_uv_dns_get_name(x_1);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_ctor_set_tag(x_40, 1);
x_8 = x_40;
x_9 = lean_box(0);
goto block_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_8 = x_43;
x_9 = lean_box(0);
goto block_39;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_ctor_set_tag(x_40, 0);
x_8 = x_40;
x_9 = lean_box(0);
goto block_39;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_8 = x_46;
x_9 = lean_box(0);
goto block_39;
}
}
block_6:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
block_39:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 0;
x_14 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_12, x_13, x_11, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
x_3 = lean_box(0);
x_4 = x_15;
goto block_6;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_3 = lean_box(0);
x_4 = x_18;
goto block_6;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
x_3 = lean_box(0);
x_4 = x_15;
goto block_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_15, 0, x_24);
x_3 = lean_box(0);
x_4 = x_15;
goto block_6;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_3 = lean_box(0);
x_4 = x_30;
goto block_6;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = l_Std_Internal_IO_Async_DNS_getNameInfo___closed__4;
x_34 = lean_task_map(x_33, x_32, x_12, x_13);
lean_ctor_set(x_14, 0, x_34);
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_14, 0);
lean_inc(x_35);
lean_dec(x_14);
x_36 = l_Std_Internal_IO_Async_DNS_getNameInfo___closed__4;
x_37 = lean_task_map(x_36, x_35, x_12, x_13);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_DNS_getNameInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_DNS_getNameInfo(x_1);
lean_dec_ref(x_1);
return x_3;
}
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async_DNS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__0 = _init_l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__0);
l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__1 = _init_l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__1);
l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__2 = _init_l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__2();
lean_mark_persistent(l_Std_Internal_IO_Async_DNS_getAddrInfo___closed__2);
l_Std_Internal_IO_Async_DNS_getNameInfo___closed__0 = _init_l_Std_Internal_IO_Async_DNS_getNameInfo___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_DNS_getNameInfo___closed__0);
l_Std_Internal_IO_Async_DNS_getNameInfo___closed__1 = _init_l_Std_Internal_IO_Async_DNS_getNameInfo___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_DNS_getNameInfo___closed__1);
l_Std_Internal_IO_Async_DNS_getNameInfo___closed__2 = _init_l_Std_Internal_IO_Async_DNS_getNameInfo___closed__2();
lean_mark_persistent(l_Std_Internal_IO_Async_DNS_getNameInfo___closed__2);
l_Std_Internal_IO_Async_DNS_getNameInfo___closed__3 = _init_l_Std_Internal_IO_Async_DNS_getNameInfo___closed__3();
lean_mark_persistent(l_Std_Internal_IO_Async_DNS_getNameInfo___closed__3);
l_Std_Internal_IO_Async_DNS_getNameInfo___closed__4 = _init_l_Std_Internal_IO_Async_DNS_getNameInfo___closed__4();
lean_mark_persistent(l_Std_Internal_IO_Async_DNS_getNameInfo___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
