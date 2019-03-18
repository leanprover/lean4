// Lean compiler output
// Module: init.control.combinators
// Imports: init.control.monad init.control.alternative init.data.list.basic init.coe
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
obj* l_list_mfilter___main___rarg___lambda__1(uint8, obj*, obj*, obj*);
obj* l_list_mfirst___boxed(obj*, obj*);
obj* l_list_mfoldl___main___boxed(obj*);
obj* l_list_mforall___boxed(obj*);
obj* l_list_mmap(obj*);
obj* l_list_mforall___main___rarg(obj*, obj*, obj*, obj*);
obj* l_nat_mrepeat(obj*);
obj* l_list_mmap___main___boxed(obj*);
obj* l_list_mfor___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mfilter___main___rarg(obj*, obj*, obj*, obj*);
obj* l_mcond___boxed(obj*);
obj* l_list_mmap___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_unless___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mexists___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mfor(obj*);
obj* l_list_mfoldl___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mfoldl___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_mcond___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_mjoin___rarg___closed__1;
obj* l_list_mfilter___main(obj*);
obj* l_list_mfoldl___main___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_mcond___rarg___lambda__1(obj*, obj*, uint8);
obj* l_list_mexists___boxed(obj*);
obj* l_list_mfoldr___boxed(obj*);
obj* l_list_mforall___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mfoldr___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mfirst___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mforall___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_mjoin___boxed(obj*);
obj* l_list_mmap_x_27___main___boxed(obj*);
obj* l_list_mforall___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27(obj*);
obj* l_list_mforall(obj*);
obj* l_list_mmap_x_27___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mfoldl(obj*);
obj* l_id___rarg___boxed(obj*);
obj* l_when___boxed(obj*);
obj* l_list_mmap___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mfirst___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mfoldr(obj*);
obj* l_list_mmap___main(obj*);
obj* l_list_mfilter___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mforall___main(obj*);
obj* l_mcond___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_when___rarg(obj*, obj*, uint8, obj*);
obj* l_list_mfilter___main___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mfor___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___boxed(obj*);
obj* l_list_mforall___main___boxed(obj*);
obj* l_list_mfilter___main___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_list_mfilter___rarg(obj*, obj*, obj*, obj*);
obj* l_mwhen___rarg___lambda__1(obj*, obj*, uint8);
obj* l_list_mfoldr___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mexists___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mexists___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mforall___main___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mfoldr___main(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_list_mmap___main___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mfilter___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mfirst___main(obj*);
obj* l_nat_mrepeat___rarg(obj*, obj*, obj*);
obj* l_list_mfirst___main___boxed(obj*);
obj* l_list_mfilter___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_nat_repeat__core___main___at_nat_mrepeat___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mexists___main___boxed(obj*);
obj* l_unless___rarg(obj*, obj*, uint8, obj*);
obj* l_list_mmap_x_27___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mfoldl___main(obj*);
obj* l_list_mmap_x_27___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_when___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mfirst___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_mjoin___rarg(obj*, obj*, obj*);
obj* l_list_mfoldl___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_mcond___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mexists___main___rarg___lambda__1(obj*, obj*, obj*, uint8);
obj* l_mjoin(obj*);
obj* l_mwhen___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_mjoin___rarg___boxed(obj*, obj*, obj*);
obj* l_list_mfirst___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mfoldr___main___boxed(obj*);
obj* l_list_mfoldr___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mexists___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_nat_repeat__core___main___at_nat_mrepeat___spec__1(obj*);
obj* l_list_mfirst(obj*, obj*);
obj* l_list_mmap___main___rarg___lambda__1(obj*, obj*, obj*);
obj* l_nat_repeat__core___main___at_nat_mrepeat___spec__1___boxed(obj*);
obj* l_mwhen___boxed(obj*);
obj* l_list_mmap_x_27___main(obj*);
obj* l_list_mmap___boxed(obj*);
obj* l_list_mfoldr___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_nat_repeat__core___main___at_nat_mrepeat___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mfoldl___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_list_mfilter___boxed(obj*);
obj* l_unless___boxed(obj*);
obj* l_nat_mrepeat___boxed(obj*);
obj* l_list_mexists___main(obj*);
obj* l_list_mmap___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mfoldl___boxed(obj*);
obj* l_list_mexists___main___rarg(obj*, obj*, obj*, obj*);
obj* l_mcond(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_list_mforall___main___rarg___lambda__1(obj*, obj*, obj*, uint8);
obj* l_list_mfor___boxed(obj*);
obj* l_unless(obj*);
obj* l_when(obj*);
obj* l_list_mfilter___main___boxed(obj*);
obj* l_list_mexists(obj*);
obj* l_mwhen___rarg(obj*, obj*, obj*);
obj* l_list_mfilter(obj*);
obj* l_mwhen(obj*);
obj* l_nat_repeat__core___main___at_nat_mrepeat___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_17; obj* x_18; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_3, x_7);
x_9 = lean::nat_sub(x_2, x_3);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 4);
lean::inc(x_13);
lean::dec(x_11);
lean::inc(x_1);
x_17 = lean::apply_1(x_1, x_9);
x_18 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_4, x_17);
x_3 = x_8;
x_4 = x_18;
goto _start;
}
else
{
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
return x_4;
}
}
}
obj* l_nat_repeat__core___main___at_nat_mrepeat___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_repeat__core___main___at_nat_mrepeat___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_nat_mrepeat___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::box(0);
x_9 = lean::apply_2(x_5, lean::box(0), x_8);
lean::inc(x_1);
x_11 = l_nat_repeat__core___main___at_nat_mrepeat___spec__1___rarg(x_0, x_2, x_1, x_1, x_9);
lean::dec(x_1);
return x_11;
}
}
obj* l_nat_mrepeat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_mrepeat___rarg), 3, 0);
return x_1;
}
}
obj* l_nat_repeat__core___main___at_nat_mrepeat___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_nat_repeat__core___main___at_nat_mrepeat___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_nat_repeat__core___main___at_nat_mrepeat___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_nat_repeat__core___main___at_nat_mrepeat___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_nat_mrepeat___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_nat_mrepeat(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mmap___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_2);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_list_mmap___main___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_0);
x_6 = l_list_mmap___main___rarg(x_0, lean::box(0), lean::box(0), x_1, x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap___main___rarg___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_4);
x_8 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_6, x_7);
return x_8;
}
}
obj* l_list_mmap___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_19; obj* x_22; obj* x_24; obj* x_25; 
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_4, 1);
lean::inc(x_16);
lean::dec(x_4);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::inc(x_3);
x_22 = lean::apply_1(x_3, x_14);
lean::inc(x_19);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap___main___rarg___lambda__2), 5, 4);
lean::closure_set(x_24, 0, x_0);
lean::closure_set(x_24, 1, x_3);
lean::closure_set(x_24, 2, x_16);
lean::closure_set(x_24, 3, x_19);
x_25 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_22, x_24);
return x_25;
}
}
}
obj* l_list_mmap___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap___main___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_list_mmap___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mmap___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mmap___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mmap___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap___main___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4);
return x_5;
}
}
obj* l_list_mmap(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_list_mmap___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mmap___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mmap(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mmap_x_27___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_19; obj* x_21; obj* x_25; obj* x_26; obj* x_27; 
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_4, 1);
lean::inc(x_16);
lean::dec(x_4);
x_19 = lean::cnstr_get(x_0, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_19, 4);
lean::inc(x_21);
lean::dec(x_19);
lean::inc(x_3);
x_25 = lean::apply_1(x_3, x_14);
x_26 = l_list_mmap_x_27___main___rarg(x_0, lean::box(0), lean::box(0), x_3, x_16);
x_27 = lean::apply_4(x_21, lean::box(0), lean::box(0), x_25, x_26);
return x_27;
}
}
}
obj* l_list_mmap_x_27___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap_x_27___main___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_list_mmap_x_27___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap_x_27___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mmap_x_27___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mmap_x_27___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mmap_x_27___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap_x_27___main___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4);
return x_5;
}
}
obj* l_list_mmap_x_27(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap_x_27___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_list_mmap_x_27___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap_x_27___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mmap_x_27___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mmap_x_27(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mfor___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mmap_x_27___main___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4);
return x_5;
}
}
obj* l_list_mfor(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mfor___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_list_mfor___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mfor___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mfor___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mfor(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_mjoin___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
return x_0;
}
}
obj* l_mjoin___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_mjoin___rarg___closed__1;
x_7 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_2, x_6);
return x_7;
}
}
obj* l_mjoin(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_mjoin___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_mjoin___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_mjoin___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_mjoin___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mjoin(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mfilter___main___rarg___lambda__1(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (x_0 == 0)
{
obj* x_5; obj* x_8; obj* x_11; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_2(x_8, lean::box(0), x_3);
return x_11;
}
else
{
obj* x_12; obj* x_15; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_2);
lean::cnstr_set(x_18, 1, x_3);
x_19 = lean::apply_2(x_15, lean::box(0), x_18);
return x_19;
}
}
}
obj* l_list_mfilter___main___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_0);
x_7 = l_list_mfilter___main___rarg(x_0, lean::box(0), x_1, x_2);
x_8 = lean::box(x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mfilter___main___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_9, 0, x_8);
lean::closure_set(x_9, 1, x_0);
lean::closure_set(x_9, 2, x_3);
x_10 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_7, x_9);
return x_10;
}
}
obj* l_list_mfilter___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_8; obj* x_11; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_2(x_8, lean::box(0), x_3);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_17; obj* x_21; obj* x_23; obj* x_24; 
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_3, 1);
lean::inc(x_14);
lean::dec(x_3);
x_17 = lean::cnstr_get(x_0, 1);
lean::inc(x_17);
lean::inc(x_12);
lean::inc(x_2);
x_21 = lean::apply_1(x_2, x_12);
lean::inc(x_17);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mfilter___main___rarg___lambda__2___boxed), 6, 5);
lean::closure_set(x_23, 0, x_0);
lean::closure_set(x_23, 1, x_2);
lean::closure_set(x_23, 2, x_14);
lean::closure_set(x_23, 3, x_12);
lean::closure_set(x_23, 4, x_17);
x_24 = lean::apply_4(x_17, lean::box(0), lean::box(0), x_21, x_23);
return x_24;
}
}
}
obj* l_list_mfilter___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mfilter___main___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_list_mfilter___main___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_list_mfilter___main___rarg___lambda__1(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_list_mfilter___main___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = l_list_mfilter___main___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* l_list_mfilter___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mfilter___main___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mfilter___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mfilter___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mfilter___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mfilter___main___rarg(x_0, lean::box(0), x_2, x_3);
return x_4;
}
}
obj* l_list_mfilter(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mfilter___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_list_mfilter___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mfilter___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mfilter___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mfilter(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mfoldl___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mfoldl___main___rarg(x_0, lean::box(0), lean::box(0), x_1, x_3, x_2);
return x_4;
}
}
obj* l_list_mfoldl___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_10; obj* x_13; 
lean::dec(x_3);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::apply_2(x_10, lean::box(0), x_4);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
x_14 = lean::cnstr_get(x_5, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_5, 1);
lean::inc(x_16);
lean::dec(x_5);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::inc(x_3);
x_22 = lean::apply_2(x_3, x_4, x_14);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mfoldl___main___rarg___lambda__1), 4, 3);
lean::closure_set(x_23, 0, x_0);
lean::closure_set(x_23, 1, x_3);
lean::closure_set(x_23, 2, x_16);
x_24 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_22, x_23);
return x_24;
}
}
}
obj* l_list_mfoldl___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mfoldl___main___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_list_mfoldl___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_list_mfoldl___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_list_mfoldl___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mfoldl___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mfoldl___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_list_mfoldl___main___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4, x_5);
return x_6;
}
}
obj* l_list_mfoldl(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mfoldl___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_list_mfoldl___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_list_mfoldl___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_list_mfoldl___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mfoldl(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mfoldr___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_10; obj* x_13; 
lean::dec(x_3);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::apply_2(x_10, lean::box(0), x_4);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
x_14 = lean::cnstr_get(x_5, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_5, 1);
lean::inc(x_16);
lean::dec(x_5);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::inc(x_3);
x_22 = l_list_mfoldr___main___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4, x_16);
x_23 = lean::apply_1(x_3, x_14);
x_24 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_22, x_23);
return x_24;
}
}
}
obj* l_list_mfoldr___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mfoldr___main___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_list_mfoldr___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_list_mfoldr___main___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_list_mfoldr___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mfoldr___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mfoldr___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_list_mfoldr___main___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4, x_5);
return x_6;
}
}
obj* l_list_mfoldr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mfoldr___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_list_mfoldr___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_list_mfoldr___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_list_mfoldr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mfoldr(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mfirst___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; 
lean::dec(x_3);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::apply_1(x_6, lean::box(0));
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_15; obj* x_18; obj* x_19; obj* x_20; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_4, 1);
lean::inc(x_12);
lean::dec(x_4);
x_15 = lean::cnstr_get(x_0, 1);
lean::inc(x_15);
lean::inc(x_3);
x_18 = lean::apply_1(x_3, x_10);
x_19 = l_list_mfirst___main___rarg(x_0, lean::box(0), lean::box(0), x_3, x_12);
x_20 = lean::apply_3(x_15, lean::box(0), x_18, x_19);
return x_20;
}
}
}
obj* l_list_mfirst___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mfirst___main___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_list_mfirst___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mfirst___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mfirst___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mfirst___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mfirst___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mfirst___main___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4);
return x_5;
}
}
obj* l_list_mfirst(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mfirst___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_list_mfirst___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mfirst___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_list_mfirst___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_mfirst(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_mexists___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, uint8 x_3) {
_start:
{
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_list_mexists___main___rarg(x_0, lean::box(0), x_1, x_2);
return x_4;
}
else
{
obj* x_7; obj* x_10; uint8 x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = 1;
x_14 = lean::box(x_13);
x_15 = lean::apply_2(x_10, lean::box(0), x_14);
return x_15;
}
}
}
obj* l_list_mexists___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_8; uint8 x_11; obj* x_12; obj* x_13; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = 0;
x_12 = lean::box(x_11);
x_13 = lean::apply_2(x_8, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
x_14 = lean::cnstr_get(x_3, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_3, 1);
lean::inc(x_16);
lean::dec(x_3);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::inc(x_2);
x_22 = lean::apply_1(x_2, x_14);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mexists___main___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_23, 0, x_0);
lean::closure_set(x_23, 1, x_2);
lean::closure_set(x_23, 2, x_16);
x_24 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_22, x_23);
return x_24;
}
}
}
obj* l_list_mexists___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mexists___main___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_list_mexists___main___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
x_5 = l_list_mexists___main___rarg___lambda__1(x_0, x_1, x_2, x_4);
return x_5;
}
}
obj* l_list_mexists___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mexists___main___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mexists___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mexists___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mexists___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mexists___main___rarg(x_0, lean::box(0), x_2, x_3);
return x_4;
}
}
obj* l_list_mexists(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mexists___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_list_mexists___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mexists___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mexists___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mexists(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mforall___main___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, uint8 x_3) {
_start:
{
if (x_3 == 0)
{
obj* x_6; obj* x_9; uint8 x_12; obj* x_13; obj* x_14; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = 0;
x_13 = lean::box(x_12);
x_14 = lean::apply_2(x_9, lean::box(0), x_13);
return x_14;
}
else
{
obj* x_15; 
x_15 = l_list_mforall___main___rarg(x_0, lean::box(0), x_1, x_2);
return x_15;
}
}
}
obj* l_list_mforall___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_8; uint8 x_11; obj* x_12; obj* x_13; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = 1;
x_12 = lean::box(x_11);
x_13 = lean::apply_2(x_8, lean::box(0), x_12);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
x_14 = lean::cnstr_get(x_3, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_3, 1);
lean::inc(x_16);
lean::dec(x_3);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::inc(x_2);
x_22 = lean::apply_1(x_2, x_14);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mforall___main___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_23, 0, x_0);
lean::closure_set(x_23, 1, x_2);
lean::closure_set(x_23, 2, x_16);
x_24 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_22, x_23);
return x_24;
}
}
}
obj* l_list_mforall___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mforall___main___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_list_mforall___main___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
x_5 = l_list_mforall___main___rarg___lambda__1(x_0, x_1, x_2, x_4);
return x_5;
}
}
obj* l_list_mforall___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mforall___main___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mforall___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mforall___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mforall___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mforall___main___rarg(x_0, lean::box(0), x_2, x_3);
return x_4;
}
}
obj* l_list_mforall(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mforall___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_list_mforall___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mforall___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mforall___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_mforall(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_when___rarg(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
if (x_2 == 0)
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::box(0);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
else
{
lean::dec(x_0);
lean::inc(x_3);
return x_3;
}
}
}
obj* l_when(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_when___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_when___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = l_when___rarg(x_0, x_1, x_4, x_3);
lean::dec(x_1);
lean::dec(x_3);
return x_5;
}
}
obj* l_when___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_when(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_unless___rarg(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
if (x_2 == 0)
{
lean::dec(x_0);
lean::inc(x_3);
return x_3;
}
else
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = lean::apply_2(x_9, lean::box(0), x_12);
return x_13;
}
}
}
obj* l_unless(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_unless___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_unless___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = l_unless___rarg(x_0, x_1, x_4, x_3);
lean::dec(x_1);
lean::dec(x_3);
return x_5;
}
}
obj* l_unless___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_unless(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_mcond___rarg___lambda__1(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
if (x_2 == 0)
{
lean::inc(x_0);
return x_0;
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l_mcond___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_mcond___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_8, 0, x_4);
lean::closure_set(x_8, 1, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_2, x_8);
return x_9;
}
}
obj* l_mcond(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_mcond___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_mcond___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_mcond___rarg___lambda__1(x_0, x_1, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_mcond___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_mcond___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_mcond___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mcond(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_mwhen___rarg___lambda__1(obj* x_0, obj* x_1, uint8 x_2) {
_start:
{
if (x_2 == 0)
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
else
{
lean::dec(x_0);
lean::inc(x_1);
return x_1;
}
}
}
obj* l_mwhen___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_mwhen___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_2);
x_6 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_1, x_5);
return x_6;
}
}
obj* l_mwhen(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_mwhen___rarg), 3, 0);
return x_1;
}
}
obj* l_mwhen___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = l_mwhen___rarg___lambda__1(x_0, x_1, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_mwhen___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mwhen(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* initialize_init_control_monad(obj*);
obj* initialize_init_control_alternative(obj*);
obj* initialize_init_data_list_basic(obj*);
obj* initialize_init_coe(obj*);
static bool _G_initialized = false;
obj* initialize_init_control_combinators(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
w = initialize_init_control_monad(w);
w = initialize_init_control_alternative(w);
w = initialize_init_data_list_basic(w);
w = initialize_init_coe(w);
 l_mjoin___rarg___closed__1 = _init_l_mjoin___rarg___closed__1();
lean::mark_persistent(l_mjoin___rarg___closed__1);
return w;
}
