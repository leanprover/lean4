// Lean compiler output
// Module: init.data.nat.basic
// Imports: init.core
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
obj* l_Nat_decLe___boxed(obj*, obj*);
uint8 l_Prod_allI(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Prod_foldI(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Nat_anyAux___main___at_Nat_all___spec__1___boxed(obj*, obj*, obj*);
obj* l_Nat_repeatAux(obj*);
obj* l_Nat_HasPow;
obj* l_Prod_foldI___rarg___boxed(obj*, obj*, obj*);
obj* l_Nat_fold___rarg(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Nat_fold(obj*);
obj* l_Nat_anyAux___boxed(obj*, obj*, obj*);
uint8 l_Prod_anyI(obj*, obj*);
obj* l_Nat_foldAux___rarg(obj*, obj*, obj*, obj*);
obj* l_Prod_allI___boxed(obj*, obj*);
obj* l_Nat_repeatAux___main(obj*);
obj* l_Nat_decEq___boxed(obj*, obj*);
uint8 l_Nat_all(obj*, obj*);
uint8 l_Nat_any(obj*, obj*);
obj* l_Nat_foldAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Nat_any___boxed(obj*, obj*);
obj* l_Nat_pred(obj*);
obj* l_Nat_sub___boxed(obj*, obj*);
obj* l_Nat_foldAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Nat_mul___boxed(obj*, obj*);
obj* l_Nat_all___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Nat_ble___boxed(obj*, obj*);
uint8 l_Nat_anyAux___main___at_Prod_allI___spec__1(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_Nat_anyAux___main(obj*, obj*, obj*);
uint8 l_Nat_anyAux(obj*, obj*, obj*);
obj* l_Nat_repeat___rarg(obj*, obj*, obj*);
obj* l_Nat_foldAux(obj*);
obj* l_Prod_anyI___boxed(obj*, obj*);
obj* l_Nat_pow___main(obj*, obj*);
obj* l_Nat_HasSub;
obj* l_Nat_decLt___boxed(obj*, obj*);
obj* l_Nat_pow___main___boxed(obj*, obj*);
obj* l_Nat_beq___boxed(obj*, obj*);
obj* l_Nat_pow(obj*, obj*);
obj* l_Prod_foldI___rarg(obj*, obj*, obj*);
obj* l_Nat_foldAux___main(obj*);
uint8 l_Nat_anyAux___main___at_Nat_all___spec__1(obj*, obj*, obj*);
obj* l_Nat_pred___boxed(obj*);
obj* l_Nat_HasLessEq;
obj* l_Nat_pow___boxed(obj*, obj*);
obj* l_Nat_HasLess;
obj* l_Nat_foldAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Nat_HasMul;
obj* l_Nat_repeatAux___rarg(obj*, obj*, obj*);
obj* l_Nat_anyAux___main___at_Prod_allI___spec__1___boxed(obj*, obj*, obj*);
obj* l_Nat_repeatAux___main___rarg(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Nat_anyAux___main___boxed(obj*, obj*, obj*);
obj* l_Nat_repeat(obj*);
obj* l_Nat_max___boxed(obj*, obj*);
obj* l_Nat_max(obj*, obj*);
obj* l_Nat_DecidableEq;
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Nat_beq___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::nat_dec_eq(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Nat_decEq___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::nat_dec_eq(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _init_l_Nat_DecidableEq() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_decEq___boxed), 2, 0);
return x_1;
}
}
obj* l_Nat_ble___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::nat_dec_le(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _init_l_Nat_HasLessEq() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* _init_l_Nat_HasLess() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_Nat_pred___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::nat_sub(x_1, lean::box(1));
return x_2;
}
}
obj* l_Nat_sub___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::nat_sub(x_1, x_2);
return x_3;
}
}
obj* l_Nat_mul___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::nat_mul(x_1, x_2);
return x_3;
}
}
obj* _init_l_Nat_HasSub() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_sub___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Nat_HasMul() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_mul___boxed), 2, 0);
return x_1;
}
}
obj* l_Nat_foldAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_3, x_7);
x_9 = lean::nat_sub(x_2, x_3);
lean::dec(x_3);
lean::inc(x_1);
x_10 = lean::apply_2(x_1, x_9, x_4);
x_3 = x_8;
x_4 = x_10;
goto _start;
}
else
{
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
}
obj* l_Nat_foldAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_foldAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Nat_foldAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Nat_foldAux___main___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Nat_foldAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Nat_foldAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Nat_foldAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_foldAux___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Nat_foldAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Nat_foldAux___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Nat_fold___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
lean::inc(x_2);
x_4 = l_Nat_foldAux___main___rarg(x_1, x_2, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Nat_fold(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_fold___rarg), 3, 0);
return x_2;
}
}
uint8 l_Nat_anyAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_3, x_6);
x_8 = lean::nat_sub(x_2, x_3);
lean::dec(x_3);
lean::inc(x_1);
x_9 = lean::apply_1(x_1, x_8);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
x_3 = x_7;
goto _start;
}
else
{
uint8 x_12; 
lean::dec(x_7);
lean::dec(x_1);
x_12 = 1;
return x_12;
}
}
else
{
uint8 x_13; 
lean::dec(x_3);
lean::dec(x_1);
x_13 = 0;
return x_13;
}
}
}
obj* l_Nat_anyAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Nat_anyAux___main(x_1, x_2, x_3);
lean::dec(x_2);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_Nat_anyAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_Nat_anyAux___main(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Nat_anyAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Nat_anyAux(x_1, x_2, x_3);
lean::dec(x_2);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_Nat_any(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
lean::inc(x_2);
x_3 = l_Nat_anyAux___main(x_1, x_2, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Nat_any___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Nat_any(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Nat_anyAux___main___at_Nat_all___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_3, x_6);
x_8 = lean::nat_sub(x_2, x_3);
lean::dec(x_3);
lean::inc(x_1);
x_9 = lean::apply_1(x_1, x_8);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
uint8 x_11; 
lean::dec(x_7);
lean::dec(x_1);
x_11 = 1;
return x_11;
}
else
{
x_3 = x_7;
goto _start;
}
}
else
{
uint8 x_13; 
lean::dec(x_3);
lean::dec(x_1);
x_13 = 0;
return x_13;
}
}
}
uint8 l_Nat_all(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
lean::inc(x_2);
x_3 = l_Nat_anyAux___main___at_Nat_all___spec__1(x_1, x_2, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
}
}
obj* l_Nat_anyAux___main___at_Nat_all___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Nat_anyAux___main___at_Nat_all___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Nat_all___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Nat_all(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Nat_repeatAux___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_2, x_6);
lean::dec(x_2);
lean::inc(x_1);
x_8 = lean::apply_1(x_1, x_3);
x_2 = x_7;
x_3 = x_8;
goto _start;
}
else
{
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
}
obj* l_Nat_repeatAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_repeatAux___main___rarg), 3, 0);
return x_2;
}
}
obj* l_Nat_repeatAux___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Nat_repeatAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Nat_repeatAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_repeatAux___rarg), 3, 0);
return x_2;
}
}
obj* l_Nat_repeat___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Nat_repeatAux___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_Nat_repeat(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_repeat___rarg), 3, 0);
return x_2;
}
}
obj* l_Nat_pow___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_2, x_5);
x_7 = l_Nat_pow___main(x_1, x_6);
lean::dec(x_6);
x_8 = lean::nat_mul(x_7, x_1);
lean::dec(x_7);
return x_8;
}
else
{
obj* x_9; 
x_9 = lean::mk_nat_obj(1u);
return x_9;
}
}
}
obj* l_Nat_pow___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_pow___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Nat_pow(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_pow___main(x_1, x_2);
return x_3;
}
}
obj* l_Nat_pow___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_pow(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Nat_HasPow() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_pow___boxed), 2, 0);
return x_1;
}
}
obj* l_Nat_decLe___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::nat_dec_le(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Nat_decLt___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::nat_dec_lt(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Nat_max(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
lean::inc(x_2);
return x_2;
}
}
}
obj* l_Nat_max___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_max(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Prod_foldI___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_2, 1);
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::nat_sub(x_4, x_5);
x_7 = l_Nat_foldAux___main___rarg(x_1, x_4, x_6, x_3);
return x_7;
}
}
obj* l_Prod_foldI(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Prod_foldI___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Prod_foldI___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Prod_foldI___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
uint8 l_Prod_anyI(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_2, 1);
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::nat_sub(x_3, x_4);
x_6 = l_Nat_anyAux___main(x_1, x_3, x_5);
return x_6;
}
}
obj* l_Prod_anyI___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Prod_anyI(x_1, x_2);
lean::dec(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Nat_anyAux___main___at_Prod_allI___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_3, x_6);
x_8 = lean::nat_sub(x_2, x_3);
lean::dec(x_3);
lean::inc(x_1);
x_9 = lean::apply_1(x_1, x_8);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
uint8 x_11; 
lean::dec(x_7);
lean::dec(x_1);
x_11 = 1;
return x_11;
}
else
{
x_3 = x_7;
goto _start;
}
}
else
{
uint8 x_13; 
lean::dec(x_3);
lean::dec(x_1);
x_13 = 0;
return x_13;
}
}
}
uint8 l_Prod_allI(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_2, 1);
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::nat_sub(x_3, x_4);
x_6 = l_Nat_anyAux___main___at_Prod_allI___spec__1(x_1, x_3, x_5);
if (x_6 == 0)
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8 x_8; 
x_8 = 0;
return x_8;
}
}
}
obj* l_Nat_anyAux___main___at_Prod_allI___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Nat_anyAux___main___at_Prod_allI___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* l_Prod_allI___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Prod_allI(x_1, x_2);
lean::dec(x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* initialize_init_core(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_nat_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_core(w);
if (io_result_is_error(w)) return w;
l_Nat_DecidableEq = _init_l_Nat_DecidableEq();
lean::mark_persistent(l_Nat_DecidableEq);
l_Nat_HasLessEq = _init_l_Nat_HasLessEq();
lean::mark_persistent(l_Nat_HasLessEq);
l_Nat_HasLess = _init_l_Nat_HasLess();
lean::mark_persistent(l_Nat_HasLess);
l_Nat_HasSub = _init_l_Nat_HasSub();
lean::mark_persistent(l_Nat_HasSub);
l_Nat_HasMul = _init_l_Nat_HasMul();
lean::mark_persistent(l_Nat_HasMul);
l_Nat_HasPow = _init_l_Nat_HasPow();
lean::mark_persistent(l_Nat_HasPow);
return w;
}
