// Lean compiler output
// Module: init.control.combinators
// Imports: init.control.monad init.control.alternative init.data.list.basic init.coe
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* _l_s4_list_s6_mfoldl_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_list_s8_mmap_x27_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_list_s8_mmap_x27(obj*);
obj* _l_s4_list_s7_mfilter_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s3_nat_s6_repeat_s6___main_s4___at_s3_nat_s7_mrepeat_s9___spec__1_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_list_s6_mfoldr(obj*);
obj* _l_s4_list_s6_mfirst_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_list_s4_mmap_s6___main_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_list_s7_mforall_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s5_mcond(obj*);
obj* _l_s4_list_s7_mforall_s6___main_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s4_list_s7_mfilter_s6___main_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s5_mcond_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_list_s7_mexists_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_list_s4_mmap_s6___main_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_list_s6_mfoldl_s6___main(obj*);
obj* _l_s5_mwhen(obj*);
obj* _l_s4_list_s8_mmap_x27_s6___main(obj*);
obj* _l_s4_list_s7_mforall_s6___main(obj*);
obj* _l_s5_mwhen_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_list_s6_mfirst_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_list_s6_mfoldl_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_list_s4_mmap_s6___main(obj*);
obj* _l_s4_list_s6_mfoldl(obj*);
obj* _l_s4_list_s4_mmap(obj*);
obj* _l_s5_mjoin_s6___rarg_s11___closed__1;
obj* _l_s3_nat_s7_mrepeat_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_when(obj*);
obj* _l_s2_id_s6___rarg(obj*);
obj* _l_s4_list_s6_mfoldr_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_list_s7_mfilter_s6___main_s6___rarg_s11___lambda__1(unsigned char, obj*, obj*, obj*);
obj* _l_s4_when_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_list_s7_mfilter_s6___main_s6___rarg_s11___lambda__2_s7___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_list_s4_mmap_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_list_s4_mfor_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s5_mjoin_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_list_s4_mfor(obj*);
obj* _l_s4_list_s7_mexists_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_list_s7_mexists_s6___main(obj*);
obj* _l_s3_nat_s6_repeat_s6___main_s4___at_s3_nat_s7_mrepeat_s9___spec__1(obj*);
obj* _l_s4_list_s6_mfoldr_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_list_s7_mexists_s6___main_s6___rarg_s11___lambda__1(obj*, obj*, obj*, unsigned char);
obj* _l_s4_list_s7_mfilter(obj*);
obj* _l_s4_list_s4_mmap_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_list_s6_mfirst(obj*, obj*);
obj* _l_s4_list_s7_mforall_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_list_s6_mfirst_s6___main(obj*);
obj* _l_s5_mjoin(obj*);
obj* _l_s4_list_s7_mfilter_s6___main(obj*);
obj* _l_s4_list_s7_mexists(obj*);
obj* _l_s3_nat_s7_mrepeat(obj*);
obj* _l_s5_mwhen_s6___rarg_s11___lambda__1(obj*, obj*, unsigned char);
obj* _l_s4_list_s7_mfilter_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_list_s7_mforall(obj*);
obj* _l_s6_unless(obj*);
obj* _l_s4_list_s6_mfoldr_s6___main(obj*);
obj* _l_s4_list_s8_mmap_x27_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_list_s6_mfoldl_s6___main_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s5_mcond_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s5_mwhen_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_list_s7_mforall_s6___main_s6___rarg_s11___lambda__1(obj*, obj*, obj*, unsigned char);
obj* _l_s4_list_s7_mfilter_s6___main_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*, unsigned char);
obj* _l_s4_list_s7_mexists_s6___main_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s6_unless_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s5_mcond_s6___rarg_s11___lambda__1(obj*, obj*, unsigned char);
obj* _l_s3_nat_s7_mrepeat_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = _l_s3_nat_s6_repeat_s6___main_s4___at_s3_nat_s7_mrepeat_s9___spec__1_s6___rarg(x_0, x_2, x_1);
return x_3;
}
}
obj* _l_s3_nat_s7_mrepeat(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_nat_s7_mrepeat_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s3_nat_s6_repeat_s6___main_s4___at_s3_nat_s7_mrepeat_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_8; obj* x_14; obj* x_15; obj* x_18; obj* x_21; obj* x_22; 
lean::dec(x_4);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_7);
lean::dec(x_2);
lean::inc(x_8);
lean::inc(x_1);
lean::inc(x_0);
x_14 = _l_s3_nat_s6_repeat_s6___main_s4___at_s3_nat_s7_mrepeat_s9___spec__1_s6___rarg(x_0, x_1, x_8);
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
lean::dec(x_0);
x_18 = lean::cnstr_get(x_15, 4);
lean::inc(x_18);
lean::dec(x_15);
x_21 = lean::apply_1(x_1, x_8);
x_22 = lean::apply_4(x_18, lean::box(0), lean::box(0), x_14, x_21);
return x_22;
}
else
{
obj* x_26; obj* x_29; unsigned char x_32; obj* x_33; obj* x_34; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_0, 0);
lean::inc(x_26);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
x_32 = 0;
x_33 = lean::box(x_32);
x_34 = lean::apply_2(x_29, lean::box(0), x_33);
return x_34;
}
}
}
obj* _l_s3_nat_s6_repeat_s6___main_s4___at_s3_nat_s7_mrepeat_s9___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s3_nat_s6_repeat_s6___main_s4___at_s3_nat_s7_mrepeat_s9___spec__1_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s4_list_s4_mmap_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::alloc_cnstr(0, 0, 0);
;
x_16 = lean::apply_2(x_12, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_17; obj* x_19; obj* x_22; obj* x_25; obj* x_27; obj* x_28; 
x_17 = lean::cnstr_get(x_4, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_4, 1);
lean::inc(x_19);
lean::dec(x_4);
x_22 = lean::cnstr_get(x_0, 1);
lean::inc(x_22);
lean::inc(x_3);
x_25 = lean::apply_1(x_3, x_17);
lean::inc(x_22);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s4_mmap_s6___main_s6___rarg_s11___lambda__2), 5, 4);
lean::closure_set(x_27, 0, x_0);
lean::closure_set(x_27, 1, x_3);
lean::closure_set(x_27, 2, x_19);
lean::closure_set(x_27, 3, x_22);
x_28 = lean::apply_4(x_22, lean::box(0), lean::box(0), x_25, x_27);
return x_28;
}
}
}
obj* _l_s4_list_s4_mmap_s6___main_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
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
obj* _l_s4_list_s4_mmap_s6___main_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_0);
x_6 = _l_s4_list_s4_mmap_s6___main_s6___rarg(x_0, lean::box(0), lean::box(0), x_1, x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s4_mmap_s6___main_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_4);
x_8 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_6, x_7);
return x_8;
}
}
obj* _l_s4_list_s4_mmap_s6___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s4_mmap_s6___main_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s4_list_s4_mmap_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = _l_s4_list_s4_mmap_s6___main_s6___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4);
return x_7;
}
}
obj* _l_s4_list_s4_mmap(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s4_mmap_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; unsigned char x_15; obj* x_16; obj* x_17; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = 0;
x_16 = lean::box(x_15);
x_17 = lean::apply_2(x_12, lean::box(0), x_16);
return x_17;
}
else
{
obj* x_18; obj* x_20; obj* x_23; obj* x_25; obj* x_29; obj* x_30; obj* x_31; 
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_4, 1);
lean::inc(x_20);
lean::dec(x_4);
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_23, 4);
lean::inc(x_25);
lean::dec(x_23);
lean::inc(x_3);
x_29 = lean::apply_1(x_3, x_18);
x_30 = _l_s4_list_s8_mmap_x27_s6___main_s6___rarg(x_0, lean::box(0), lean::box(0), x_3, x_20);
x_31 = lean::apply_4(x_25, lean::box(0), lean::box(0), x_29, x_30);
return x_31;
}
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s8_mmap_x27_s6___main_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s4_list_s8_mmap_x27_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = _l_s4_list_s8_mmap_x27_s6___main_s6___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4);
return x_7;
}
}
obj* _l_s4_list_s8_mmap_x27(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s8_mmap_x27_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s4_list_s4_mfor_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = _l_s4_list_s8_mmap_x27_s6___main_s6___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4);
return x_7;
}
}
obj* _l_s4_list_s4_mfor(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s4_mfor_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s5_mjoin_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_7; obj* x_9; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_7);
x_9 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_2, x_7);
return x_9;
}
}
obj* _init__l_s5_mjoin_s6___rarg_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s6___rarg), 1, 0);
return x_0;
}
}
obj* _l_s5_mjoin(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_mjoin_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s4_list_s7_mfilter_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_9; obj* x_12; 
lean::dec(x_2);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::apply_2(x_9, lean::box(0), x_3);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_18; obj* x_22; obj* x_24; obj* x_25; 
x_13 = lean::cnstr_get(x_3, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_3, 1);
lean::inc(x_15);
lean::dec(x_3);
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
lean::inc(x_13);
lean::inc(x_2);
x_22 = lean::apply_1(x_2, x_13);
lean::inc(x_18);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s7_mfilter_s6___main_s6___rarg_s11___lambda__2_s7___boxed), 6, 5);
lean::closure_set(x_24, 0, x_0);
lean::closure_set(x_24, 1, x_2);
lean::closure_set(x_24, 2, x_15);
lean::closure_set(x_24, 3, x_13);
lean::closure_set(x_24, 4, x_18);
x_25 = lean::apply_4(x_18, lean::box(0), lean::box(0), x_22, x_24);
return x_25;
}
}
}
obj* _l_s4_list_s7_mfilter_s6___main_s6___rarg_s11___lambda__1(unsigned char x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* _l_s4_list_s7_mfilter_s6___main_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, unsigned char x_5) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_0);
x_7 = _l_s4_list_s7_mfilter_s6___main_s6___rarg(x_0, lean::box(0), x_1, x_2);
x_8 = lean::box(x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s7_mfilter_s6___main_s6___rarg_s11___lambda__1_s7___boxed), 4, 3);
lean::closure_set(x_9, 0, x_8);
lean::closure_set(x_9, 1, x_0);
lean::closure_set(x_9, 2, x_3);
x_10 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_7, x_9);
return x_10;
}
}
obj* _l_s4_list_s7_mfilter_s6___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s7_mfilter_s6___main_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_list_s7_mfilter_s6___main_s6___rarg_s11___lambda__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned char x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = _l_s4_list_s7_mfilter_s6___main_s6___rarg_s11___lambda__1(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* _l_s4_list_s7_mfilter_s6___main_s6___rarg_s11___lambda__2_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
unsigned char x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = _l_s4_list_s7_mfilter_s6___main_s6___rarg_s11___lambda__2(x_0, x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* _l_s4_list_s7_mfilter_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_1);
x_5 = _l_s4_list_s7_mfilter_s6___main_s6___rarg(x_0, lean::box(0), x_2, x_3);
return x_5;
}
}
obj* _l_s4_list_s7_mfilter(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s7_mfilter_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_list_s6_mfoldl_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_5) == 0)
{
obj* x_10; obj* x_13; obj* x_16; 
lean::dec(x_5);
lean::dec(x_3);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::apply_2(x_13, lean::box(0), x_4);
return x_16;
}
else
{
obj* x_17; obj* x_19; obj* x_22; obj* x_25; obj* x_26; obj* x_27; 
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = lean::cnstr_get(x_0, 1);
lean::inc(x_22);
lean::inc(x_3);
x_25 = lean::apply_2(x_3, x_4, x_17);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s6_mfoldl_s6___main_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_26, 0, x_0);
lean::closure_set(x_26, 1, x_3);
lean::closure_set(x_26, 2, x_19);
x_27 = lean::apply_4(x_22, lean::box(0), lean::box(0), x_25, x_26);
return x_27;
}
}
}
obj* _l_s4_list_s6_mfoldl_s6___main_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = _l_s4_list_s6_mfoldl_s6___main_s6___rarg(x_0, lean::box(0), lean::box(0), x_1, x_3, x_2);
return x_4;
}
}
obj* _l_s4_list_s6_mfoldl_s6___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s6_mfoldl_s6___main_s6___rarg), 6, 0);
return x_2;
}
}
obj* _l_s4_list_s6_mfoldl_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_8; 
lean::dec(x_2);
lean::dec(x_1);
x_8 = _l_s4_list_s6_mfoldl_s6___main_s6___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4, x_5);
return x_8;
}
}
obj* _l_s4_list_s6_mfoldl(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s6_mfoldl_s6___rarg), 6, 0);
return x_2;
}
}
obj* _l_s4_list_s6_mfoldr_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_5) == 0)
{
obj* x_10; obj* x_13; obj* x_16; 
lean::dec(x_5);
lean::dec(x_3);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::apply_2(x_13, lean::box(0), x_4);
return x_16;
}
else
{
obj* x_17; obj* x_19; obj* x_22; obj* x_25; obj* x_26; obj* x_27; 
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = lean::cnstr_get(x_0, 1);
lean::inc(x_22);
lean::inc(x_3);
x_25 = _l_s4_list_s6_mfoldr_s6___main_s6___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4, x_19);
x_26 = lean::apply_1(x_3, x_17);
x_27 = lean::apply_4(x_22, lean::box(0), lean::box(0), x_25, x_26);
return x_27;
}
}
}
obj* _l_s4_list_s6_mfoldr_s6___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s6_mfoldr_s6___main_s6___rarg), 6, 0);
return x_2;
}
}
obj* _l_s4_list_s6_mfoldr_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_8; 
lean::dec(x_2);
lean::dec(x_1);
x_8 = _l_s4_list_s6_mfoldr_s6___main_s6___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4, x_5);
return x_8;
}
}
obj* _l_s4_list_s6_mfoldr(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s6_mfoldr_s6___rarg), 6, 0);
return x_2;
}
}
obj* _l_s4_list_s6_mfirst_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
lean::dec(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_12; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::apply_1(x_9, lean::box(0));
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_18; obj* x_21; obj* x_22; obj* x_23; 
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_4, 1);
lean::inc(x_15);
lean::dec(x_4);
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
lean::inc(x_3);
x_21 = lean::apply_1(x_3, x_13);
x_22 = _l_s4_list_s6_mfirst_s6___main_s6___rarg(x_0, lean::box(0), lean::box(0), x_3, x_15);
x_23 = lean::apply_3(x_18, lean::box(0), x_21, x_22);
return x_23;
}
}
}
obj* _l_s4_list_s6_mfirst_s6___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s6_mfirst_s6___main_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s4_list_s6_mfirst_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = _l_s4_list_s6_mfirst_s6___main_s6___rarg(x_0, lean::box(0), lean::box(0), x_3, x_4);
return x_7;
}
}
obj* _l_s4_list_s6_mfirst(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s6_mfirst_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_list_s7_mexists_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; obj* x_10; unsigned char x_13; obj* x_14; obj* x_15; 
lean::dec(x_2);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = 0;
x_14 = lean::box(x_13);
x_15 = lean::apply_2(x_10, lean::box(0), x_14);
return x_15;
}
else
{
obj* x_16; obj* x_18; obj* x_21; obj* x_24; obj* x_25; obj* x_26; 
x_16 = lean::cnstr_get(x_3, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_3, 1);
lean::inc(x_18);
lean::dec(x_3);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::inc(x_2);
x_24 = lean::apply_1(x_2, x_16);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s7_mexists_s6___main_s6___rarg_s11___lambda__1_s7___boxed), 4, 3);
lean::closure_set(x_25, 0, x_0);
lean::closure_set(x_25, 1, x_2);
lean::closure_set(x_25, 2, x_18);
x_26 = lean::apply_4(x_21, lean::box(0), lean::box(0), x_24, x_25);
return x_26;
}
}
}
obj* _l_s4_list_s7_mexists_s6___main_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, unsigned char x_3) {
_start:
{
if (x_3 == 0)
{
obj* x_4; 
x_4 = _l_s4_list_s7_mexists_s6___main_s6___rarg(x_0, lean::box(0), x_1, x_2);
return x_4;
}
else
{
obj* x_7; obj* x_10; unsigned char x_13; obj* x_14; obj* x_15; 
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
obj* _l_s4_list_s7_mexists_s6___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s7_mexists_s6___main_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_list_s7_mexists_s6___main_s6___rarg_s11___lambda__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned char x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
x_5 = _l_s4_list_s7_mexists_s6___main_s6___rarg_s11___lambda__1(x_0, x_1, x_2, x_4);
return x_5;
}
}
obj* _l_s4_list_s7_mexists_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_1);
x_5 = _l_s4_list_s7_mexists_s6___main_s6___rarg(x_0, lean::box(0), x_2, x_3);
return x_5;
}
}
obj* _l_s4_list_s7_mexists(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s7_mexists_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_list_s7_mforall_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; obj* x_10; unsigned char x_13; obj* x_14; obj* x_15; 
lean::dec(x_2);
lean::dec(x_3);
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
else
{
obj* x_16; obj* x_18; obj* x_21; obj* x_24; obj* x_25; obj* x_26; 
x_16 = lean::cnstr_get(x_3, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_3, 1);
lean::inc(x_18);
lean::dec(x_3);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
lean::inc(x_2);
x_24 = lean::apply_1(x_2, x_16);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s7_mforall_s6___main_s6___rarg_s11___lambda__1_s7___boxed), 4, 3);
lean::closure_set(x_25, 0, x_0);
lean::closure_set(x_25, 1, x_2);
lean::closure_set(x_25, 2, x_18);
x_26 = lean::apply_4(x_21, lean::box(0), lean::box(0), x_24, x_25);
return x_26;
}
}
}
obj* _l_s4_list_s7_mforall_s6___main_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, unsigned char x_3) {
_start:
{
if (x_3 == 0)
{
obj* x_6; obj* x_9; unsigned char x_12; obj* x_13; obj* x_14; 
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
x_15 = _l_s4_list_s7_mforall_s6___main_s6___rarg(x_0, lean::box(0), x_1, x_2);
return x_15;
}
}
}
obj* _l_s4_list_s7_mforall_s6___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s7_mforall_s6___main_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_list_s7_mforall_s6___main_s6___rarg_s11___lambda__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned char x_4; obj* x_5; 
x_4 = lean::unbox(x_3);
x_5 = _l_s4_list_s7_mforall_s6___main_s6___rarg_s11___lambda__1(x_0, x_1, x_2, x_4);
return x_5;
}
}
obj* _l_s4_list_s7_mforall_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_1);
x_5 = _l_s4_list_s7_mforall_s6___main_s6___rarg(x_0, lean::box(0), x_2, x_3);
return x_5;
}
}
obj* _l_s4_list_s7_mforall(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s7_mforall_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_when_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_10; unsigned char x_13; obj* x_14; obj* x_15; 
lean::dec(x_2);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = 0;
x_14 = lean::box(x_13);
x_15 = lean::apply_2(x_10, lean::box(0), x_14);
return x_15;
}
else
{
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
}
obj* _l_s4_when(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_when_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s6_unless_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_9; obj* x_12; unsigned char x_15; obj* x_16; obj* x_17; 
lean::dec(x_2);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = 0;
x_16 = lean::box(x_15);
x_17 = lean::apply_2(x_12, lean::box(0), x_16);
return x_17;
}
}
}
obj* _l_s6_unless(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_unless_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s5_mcond_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_mcond_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_3);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_2, x_9);
return x_10;
}
}
obj* _l_s5_mcond_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, unsigned char x_2) {
_start:
{
if (x_2 == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
obj* _l_s5_mcond(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_mcond_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s5_mcond_s6___rarg_s11___lambda__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = _l_s5_mcond_s6___rarg_s11___lambda__1(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s5_mwhen_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_mwhen_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_2);
x_6 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_1, x_5);
return x_6;
}
}
obj* _l_s5_mwhen_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, unsigned char x_2) {
_start:
{
if (x_2 == 0)
{
obj* x_4; obj* x_7; unsigned char x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = 0;
x_11 = lean::box(x_10);
x_12 = lean::apply_2(x_7, lean::box(0), x_11);
return x_12;
}
else
{
lean::dec(x_0);
return x_1;
}
}
}
obj* _l_s5_mwhen(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_mwhen_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s5_mwhen_s6___rarg_s11___lambda__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = _l_s5_mwhen_s6___rarg_s11___lambda__1(x_0, x_1, x_3);
return x_4;
}
}
void _l_initialize__l_s4_init_s7_control_s5_monad();
void _l_initialize__l_s4_init_s7_control_s11_alternative();
void _l_initialize__l_s4_init_s4_data_s4_list_s5_basic();
void _l_initialize__l_s4_init_s3_coe();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s7_control_s11_combinators() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s7_control_s5_monad();
 _l_initialize__l_s4_init_s7_control_s11_alternative();
 _l_initialize__l_s4_init_s4_data_s4_list_s5_basic();
 _l_initialize__l_s4_init_s3_coe();
 _l_s5_mjoin_s6___rarg_s11___closed__1 = _init__l_s5_mjoin_s6___rarg_s11___closed__1();
}
