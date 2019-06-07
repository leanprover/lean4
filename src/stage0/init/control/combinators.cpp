// Lean compiler output
// Module: init.control.combinators
// Imports: init.control.monad init.control.alternative init.data.list.basic
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
obj* l_List_mfoldl___main(obj*);
obj* l_Nat_mforAux___main(obj*);
obj* l_List_mmap(obj*);
obj* l_Nat_mforAux___boxed(obj*);
obj* l_List_mforall___main(obj*);
obj* l_mcond___boxed(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_List_mexists___main(obj*);
obj* l_unless___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mfilter___main___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfoldr___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Nat_mforAux___main___boxed(obj*);
obj* l_List_mexists___boxed(obj*);
obj* l_Nat_mforAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_mcond___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_mjoin___rarg___closed__1;
obj* l_mcond___rarg___lambda__1(obj*, obj*, uint8);
obj* l_Nat_mfold___rarg(obj*, obj*, obj*, obj*);
obj* l_List_mfilter___main___rarg(obj*, obj*, obj*, obj*);
obj* l_mjoin___boxed(obj*);
obj* l_Nat_mforAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mfilter___main___rarg___lambda__1(uint8, obj*, obj*, obj*);
obj* l_List_mmap___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfirst___main___boxed(obj*);
obj* l_id___rarg___boxed(obj*);
obj* l_when___boxed(obj*);
obj* l_List_mmap___main___boxed(obj*);
obj* l_List_mmap___boxed(obj*);
obj* l_List_mfor___main___boxed(obj*);
obj* l_Nat_mfoldAux___main(obj*, obj*);
obj* l_List_mfirst___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfoldr(obj*);
obj* l_List_mfilter___rarg(obj*, obj*, obj*, obj*);
obj* l_mcond___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_when___rarg(obj*, obj*, uint8, obj*);
obj* l_List_mfoldr___boxed(obj*);
obj* l_List_mforall___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Nat_mfoldAux___main___boxed(obj*, obj*);
obj* l_List_mmap___main___rarg___lambda__1(obj*, obj*);
obj* l_List_mfoldl___main___boxed(obj*);
obj* l_mwhen___rarg___lambda__1(obj*, obj*, uint8);
obj* l_List_mfoldr___main(obj*);
obj* l_List_mfoldl___main___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_List_mfirst___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mforall___main___boxed(obj*);
obj* l_List_mforall___main___rarg(obj*, obj*, obj*, obj*);
obj* l_unless___rarg(obj*, obj*, uint8, obj*);
obj* l_List_mfoldr___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Nat_mfoldAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Nat_mfor(obj*);
obj* l_List_mmap___main(obj*);
obj* l_List_mexists___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Nat_mfoldAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfilter___boxed(obj*);
obj* l_List_mmap___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_when___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mfoldl___boxed(obj*);
obj* l_List_mfoldl___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_mjoin___rarg(obj*, obj*, obj*);
obj* l_List_mfilter___main___boxed(obj*);
obj* l_mjoin(obj*);
obj* l_List_mfor___main(obj*);
obj* l_Nat_mforAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_mwhen___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_Nat_mfoldAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mforall(obj*);
obj* l_List_mfor___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Nat_mfold___boxed(obj*, obj*);
obj* l_List_mforall___main___rarg___lambda__1(obj*, obj*, obj*, uint8);
obj* l_Nat_mfold(obj*, obj*);
obj* l_Nat_mforAux___rarg(obj*, obj*, obj*, obj*);
obj* l_List_mfilter(obj*);
obj* l_mwhen___boxed(obj*);
obj* l_List_mfor___boxed(obj*);
obj* l_List_mfoldl___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Nat_mforAux(obj*);
obj* l_Nat_mfoldAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_unless___boxed(obj*);
obj* l_List_mfirst(obj*, obj*);
obj* l_List_mfoldr___main___boxed(obj*);
obj* l_List_mfilter___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mfilter___main(obj*);
obj* l_List_mexists___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_List_mforall___rarg(obj*, obj*, obj*, obj*);
obj* l_List_mmap___main___rarg___closed__1;
obj* l_List_mforall___boxed(obj*);
obj* l_List_mfoldl(obj*);
obj* l_List_mfor(obj*);
obj* l_Nat_mfor___boxed(obj*);
obj* l_List_mfirst___boxed(obj*, obj*);
obj* l_Nat_mfor___rarg(obj*, obj*, obj*);
obj* l_mcond(obj*);
obj* l_List_mfilter___main___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_Nat_mfor___rarg___boxed(obj*, obj*, obj*);
obj* l_Nat_mfoldAux___boxed(obj*, obj*);
obj* l_Nat_mfoldAux(obj*, obj*);
obj* l_unless(obj*);
obj* l_when(obj*);
obj* l_List_mexists___main___boxed(obj*);
obj* l_List_mexists(obj*);
obj* l_List_mfor___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_mwhen___rarg(obj*, obj*, obj*);
obj* l_List_mexists___rarg(obj*, obj*, obj*, obj*);
obj* l_mwhen(obj*);
obj* l_List_mfirst___main(obj*);
obj* l_List_mexists___main___rarg___lambda__1(obj*, obj*, obj*, uint8);
obj* _init_l_mjoin___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_mjoin___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_5 = l_mjoin___rarg___closed__1;
x_6 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_3, x_5);
return x_6;
}
}
obj* l_mjoin(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_mjoin___rarg), 3, 0);
return x_2;
}
}
obj* l_mjoin___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mjoin(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_when___rarg(obj* x_1, obj* x_2, uint8 x_3, obj* x_4) {
_start:
{
if (x_3 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
return x_7;
}
else
{
lean::dec(x_1);
lean::inc(x_4);
return x_4;
}
}
}
obj* l_when(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_when___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_when___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_3);
lean::dec(x_3);
x_6 = l_when___rarg(x_1, x_2, x_5, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_when___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_when(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_unless___rarg(obj* x_1, obj* x_2, uint8 x_3, obj* x_4) {
_start:
{
if (x_3 == 0)
{
lean::dec(x_1);
lean::inc(x_4);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
return x_7;
}
}
}
obj* l_unless(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_unless___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_unless___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_3);
lean::dec(x_3);
x_6 = l_unless___rarg(x_1, x_2, x_5, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_unless___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_unless(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_mcond___rarg___lambda__1(obj* x_1, obj* x_2, uint8 x_3) {
_start:
{
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
obj* l_mcond___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_mcond___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_4);
x_8 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_3, x_7);
return x_8;
}
}
obj* l_mcond(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_mcond___rarg), 5, 0);
return x_2;
}
}
obj* l_mcond___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
lean::dec(x_3);
x_5 = l_mcond___rarg___lambda__1(x_1, x_2, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_mcond___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mcond(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_mwhen___rarg___lambda__1(obj* x_1, obj* x_2, uint8 x_3) {
_start:
{
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::box(0);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
return x_7;
}
else
{
lean::dec(x_1);
lean::inc(x_2);
return x_2;
}
}
}
obj* l_mwhen___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_mwhen___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_3);
x_6 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_2, x_5);
return x_6;
}
}
obj* l_mwhen(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_mwhen___rarg), 3, 0);
return x_2;
}
}
obj* l_mwhen___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
lean::dec(x_3);
x_5 = l_mwhen___rarg___lambda__1(x_1, x_2, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_mwhen___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_mwhen(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Nat_mforAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_4, x_7);
x_9 = lean::cnstr_get(x_1, 4);
lean::inc(x_9);
x_10 = lean::nat_sub(x_3, x_8);
x_11 = lean::nat_sub(x_10, x_7);
lean::dec(x_10);
lean::inc(x_2);
x_12 = lean::apply_1(x_2, x_11);
x_13 = l_Nat_mforAux___main___rarg(x_1, x_2, x_3, x_8);
lean::dec(x_8);
x_14 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_2);
x_15 = lean::cnstr_get(x_1, 1);
lean::inc(x_15);
lean::dec(x_1);
x_16 = lean::box(0);
x_17 = lean::apply_2(x_15, lean::box(0), x_16);
return x_17;
}
}
}
obj* l_Nat_mforAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_mforAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Nat_mforAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Nat_mforAux___main___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Nat_mforAux___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Nat_mforAux___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Nat_mforAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Nat_mforAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Nat_mforAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_mforAux___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Nat_mforAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Nat_mforAux___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Nat_mforAux___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Nat_mforAux(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Nat_mfor___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Nat_mforAux___main___rarg(x_1, x_3, x_2, x_2);
return x_4;
}
}
obj* l_Nat_mfor(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_mfor___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Nat_mfor___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Nat_mfor___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Nat_mfor___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Nat_mfor(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Nat_mfoldAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_4, x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
x_11 = lean::nat_sub(x_3, x_9);
x_12 = lean::nat_sub(x_11, x_8);
lean::dec(x_11);
lean::inc(x_2);
x_13 = lean::apply_2(x_2, x_12, x_5);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_mfoldAux___main___rarg___boxed), 5, 4);
lean::closure_set(x_14, 0, x_1);
lean::closure_set(x_14, 1, x_2);
lean::closure_set(x_14, 2, x_3);
lean::closure_set(x_14, 3, x_9);
x_15 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_3);
lean::dec(x_2);
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
lean::dec(x_16);
x_18 = lean::apply_2(x_17, lean::box(0), x_5);
return x_18;
}
}
}
obj* l_Nat_mfoldAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_mfoldAux___main___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Nat_mfoldAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Nat_mfoldAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_Nat_mfoldAux___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_mfoldAux___main(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Nat_mfoldAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Nat_mfoldAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Nat_mfoldAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_mfoldAux___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_Nat_mfoldAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Nat_mfoldAux___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
return x_6;
}
}
obj* l_Nat_mfoldAux___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_mfoldAux(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Nat_mfold___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
lean::inc(x_4);
x_5 = l_Nat_mfoldAux___main___rarg(x_1, x_2, x_4, x_4, x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_Nat_mfold(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_mfold___rarg), 4, 0);
return x_3;
}
}
obj* l_Nat_mfold___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Nat_mfold(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_List_mmap___main___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_List_mmap___main___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___rarg___lambda__1), 2, 0);
return x_1;
}
}
obj* l_List_mmap___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::box(0);
x_8 = lean::apply_2(x_6, lean::box(0), x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_9 = lean::cnstr_get(x_5, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
lean::dec(x_12);
lean::inc(x_4);
x_14 = lean::apply_1(x_4, x_9);
x_15 = l_List_mmap___main___rarg___closed__1;
x_16 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_15, x_14);
x_17 = l_List_mmap___main___rarg(x_1, lean::box(0), lean::box(0), x_4, x_10);
x_18 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_16, x_17);
return x_18;
}
}
}
obj* l_List_mmap___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___main___rarg), 5, 0);
return x_2;
}
}
obj* l_List_mmap___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mmap___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mmap___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_List_mmap___main___rarg(x_1, lean::box(0), lean::box(0), x_4, x_5);
return x_6;
}
}
obj* l_List_mmap(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mmap___rarg), 5, 0);
return x_2;
}
}
obj* l_List_mmap___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mmap(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mfor___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::box(0);
x_8 = lean::apply_2(x_6, lean::box(0), x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = lean::cnstr_get(x_5, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_1, 4);
lean::inc(x_11);
lean::inc(x_4);
x_12 = lean::apply_1(x_4, x_9);
x_13 = l_List_mfor___main___rarg(x_1, lean::box(0), lean::box(0), x_4, x_10);
x_14 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
}
obj* l_List_mfor___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfor___main___rarg), 5, 0);
return x_2;
}
}
obj* l_List_mfor___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mfor___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mfor___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_List_mfor___main___rarg(x_1, lean::box(0), lean::box(0), x_4, x_5);
return x_6;
}
}
obj* l_List_mfor(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfor___rarg), 5, 0);
return x_2;
}
}
obj* l_List_mfor___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mfor(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mfilter___main___rarg___lambda__1(uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (x_1 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_3);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::apply_2(x_6, lean::box(0), x_4);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_4);
x_11 = lean::apply_2(x_9, lean::box(0), x_10);
return x_11;
}
}
}
obj* l_List_mfilter___main___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_1);
x_7 = l_List_mfilter___main___rarg(x_1, lean::box(0), x_2, x_3);
x_8 = lean::box(x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfilter___main___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_9, 0, x_8);
lean::closure_set(x_9, 1, x_1);
lean::closure_set(x_9, 2, x_4);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_9);
return x_10;
}
}
obj* l_List_mfilter___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::apply_2(x_6, lean::box(0), x_4);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::inc(x_3);
lean::inc(x_8);
x_11 = lean::apply_1(x_3, x_8);
lean::inc(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfilter___main___rarg___lambda__2___boxed), 6, 5);
lean::closure_set(x_12, 0, x_1);
lean::closure_set(x_12, 1, x_3);
lean::closure_set(x_12, 2, x_9);
lean::closure_set(x_12, 3, x_8);
lean::closure_set(x_12, 4, x_10);
x_13 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_11, x_12);
return x_13;
}
}
}
obj* l_List_mfilter___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfilter___main___rarg), 4, 0);
return x_2;
}
}
obj* l_List_mfilter___main___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
lean::dec(x_1);
x_6 = l_List_mfilter___main___rarg___lambda__1(x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* l_List_mfilter___main___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_6);
lean::dec(x_6);
x_8 = l_List_mfilter___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
obj* l_List_mfilter___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mfilter___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mfilter___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mfilter___main___rarg(x_1, lean::box(0), x_3, x_4);
return x_5;
}
}
obj* l_List_mfilter(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfilter___rarg), 4, 0);
return x_2;
}
}
obj* l_List_mfilter___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mfilter(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mfoldl___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mfoldl___main___rarg(x_1, lean::box(0), lean::box(0), x_2, x_4, x_3);
return x_5;
}
}
obj* l_List_mfoldl___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_4);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::apply_2(x_8, lean::box(0), x_5);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::dec(x_6);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::inc(x_4);
x_13 = lean::apply_2(x_4, x_5, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldl___main___rarg___lambda__1), 4, 3);
lean::closure_set(x_14, 0, x_1);
lean::closure_set(x_14, 1, x_4);
lean::closure_set(x_14, 2, x_11);
x_15 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
}
obj* l_List_mfoldl___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldl___main___rarg), 6, 0);
return x_2;
}
}
obj* l_List_mfoldl___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mfoldl___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mfoldl___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_List_mfoldl___main___rarg(x_1, lean::box(0), lean::box(0), x_4, x_5, x_6);
return x_7;
}
}
obj* l_List_mfoldl(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldl___rarg), 6, 0);
return x_2;
}
}
obj* l_List_mfoldl___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mfoldl(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mfoldr___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_4);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_9 = lean::apply_2(x_8, lean::box(0), x_5);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::dec(x_6);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::inc(x_4);
x_13 = l_List_mfoldr___main___rarg(x_1, lean::box(0), lean::box(0), x_4, x_5, x_11);
x_14 = lean::apply_1(x_4, x_10);
x_15 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
}
obj* l_List_mfoldr___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldr___main___rarg), 6, 0);
return x_2;
}
}
obj* l_List_mfoldr___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mfoldr___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mfoldr___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_List_mfoldr___main___rarg(x_1, lean::box(0), lean::box(0), x_4, x_5, x_6);
return x_7;
}
}
obj* l_List_mfoldr(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfoldr___rarg), 6, 0);
return x_2;
}
}
obj* l_List_mfoldr___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mfoldr(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mfirst___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::apply_1(x_6, lean::box(0));
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_5, 1);
lean::inc(x_9);
lean::dec(x_5);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
lean::inc(x_4);
x_11 = lean::apply_1(x_4, x_8);
x_12 = l_List_mfirst___main___rarg(x_1, lean::box(0), lean::box(0), x_4, x_9);
x_13 = lean::apply_3(x_10, lean::box(0), x_11, x_12);
return x_13;
}
}
}
obj* l_List_mfirst___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfirst___main___rarg), 5, 0);
return x_2;
}
}
obj* l_List_mfirst___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mfirst___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mfirst___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_List_mfirst___main___rarg(x_1, lean::box(0), lean::box(0), x_4, x_5);
return x_6;
}
}
obj* l_List_mfirst(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mfirst___rarg), 5, 0);
return x_3;
}
}
obj* l_List_mfirst___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_mfirst(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_List_mexists___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_List_mexists___main___rarg(x_1, lean::box(0), x_2, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_8 = lean::box(x_4);
x_9 = lean::apply_2(x_7, lean::box(0), x_8);
return x_9;
}
}
}
obj* l_List_mexists___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_7 = 0;
x_8 = lean::box(x_7);
x_9 = lean::apply_2(x_6, lean::box(0), x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::inc(x_3);
x_13 = lean::apply_1(x_3, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mexists___main___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_14, 0, x_1);
lean::closure_set(x_14, 1, x_3);
lean::closure_set(x_14, 2, x_11);
x_15 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
}
obj* l_List_mexists___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mexists___main___rarg), 4, 0);
return x_2;
}
}
obj* l_List_mexists___main___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
lean::dec(x_4);
x_6 = l_List_mexists___main___rarg___lambda__1(x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_List_mexists___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mexists___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mexists___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mexists___main___rarg(x_1, lean::box(0), x_3, x_4);
return x_5;
}
}
obj* l_List_mexists(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mexists___rarg), 4, 0);
return x_2;
}
}
obj* l_List_mexists___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mexists(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mforall___main___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_7 = lean::box(x_4);
x_8 = lean::apply_2(x_6, lean::box(0), x_7);
return x_8;
}
else
{
obj* x_9; 
x_9 = l_List_mforall___main___rarg(x_1, lean::box(0), x_2, x_3);
return x_9;
}
}
}
obj* l_List_mforall___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_7 = 1;
x_8 = lean::box(x_7);
x_9 = lean::apply_2(x_6, lean::box(0), x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::inc(x_3);
x_13 = lean::apply_1(x_3, x_10);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mforall___main___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_14, 0, x_1);
lean::closure_set(x_14, 1, x_3);
lean::closure_set(x_14, 2, x_11);
x_15 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
}
obj* l_List_mforall___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mforall___main___rarg), 4, 0);
return x_2;
}
}
obj* l_List_mforall___main___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
lean::dec(x_4);
x_6 = l_List_mforall___main___rarg___lambda__1(x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_List_mforall___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mforall___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_List_mforall___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_List_mforall___main___rarg(x_1, lean::box(0), x_3, x_4);
return x_5;
}
}
obj* l_List_mforall(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_List_mforall___rarg), 4, 0);
return x_2;
}
}
obj* l_List_mforall___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_List_mforall(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_control_monad(obj*);
obj* initialize_init_control_alternative(obj*);
obj* initialize_init_data_list_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_combinators(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_monad(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_alternative(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_list_basic(w);
if (io_result_is_error(w)) return w;
l_mjoin___rarg___closed__1 = _init_l_mjoin___rarg___closed__1();
lean::mark_persistent(l_mjoin___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name("mjoin"), 1, l_mjoin___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name("when"), 1, l_when___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name("unless"), 1, l_unless___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name("mcond"), 1, l_mcond___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name("mwhen"), 1, l_mwhen___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Nat"), "mforAux"), 1, l_Nat_mforAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Nat"), "mfor"), 1, l_Nat_mfor___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Nat"), "mfoldAux"), 2, l_Nat_mfoldAux___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("Nat"), "mfold"), 2, l_Nat_mfold___boxed);
l_List_mmap___main___rarg___closed__1 = _init_l_List_mmap___main___rarg___closed__1();
lean::mark_persistent(l_List_mmap___main___rarg___closed__1);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("List"), "mmap"), 1, l_List_mmap___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("List"), "mfor"), 1, l_List_mfor___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("List"), "mfilter"), 1, l_List_mfilter___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("List"), "mfoldl"), 1, l_List_mfoldl___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("List"), "mfoldr"), 1, l_List_mfoldr___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("List"), "mfirst"), 2, l_List_mfirst___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("List"), "mexists"), 1, l_List_mexists___boxed);
REGISTER_LEAN_FUNCTION(lean::mk_const_name(lean::mk_const_name("List"), "mforall"), 1, l_List_mforall___boxed);
return w;
}
