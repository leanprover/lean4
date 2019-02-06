// Lean compiler output
// Module: init.lean.ir.elim_phi
// Imports: init.lean.ir.instances init.control.state init.lean.disjoint_set
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_mk__hashmap__imp___rarg(obj*);
obj* l_hashmap__imp_fold__buckets___rarg(obj*, obj*, obj*);
obj* l_lean_ir_elim__phi(obj*);
obj* l___private_3363165505__find__aux___main___at_lean_ir_merge___spec__3(obj*, obj*, obj*);
obj* l_lean_ir_header_replace__vars(obj*, obj*);
obj* l_lean_mk__disjoint__set___at_lean_ir_elim__phi__m_run___spec__1;
obj* l_lean_ir_elim__phi__m_run___rarg___closed__1;
obj* l_lean_ir_arg_replace__vars(obj*, obj*);
obj* l_d__hashmap_find___at_lean_ir_merge___spec__4(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_group__vars___main___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_elim__phi__aux(obj*, obj*);
obj* l_lean_ir_instr_replace__vars(obj*, obj*);
obj* l_list_mmap___main___at_lean_ir_instr_replace__vars___main___spec__1(obj*, obj*);
obj* l_list_mmap___main___at_lean_ir_instr_replace__vars___main___spec__2(obj*, obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_lean_ir_elim__phi__m;
obj* l_mk__array___rarg(obj*, obj*);
obj* l_list_mmap___main___at_lean_ir_header_replace__vars___spec__1(obj*, obj*);
obj* l_list_mmap___main___at_lean_ir_block_replace__vars___spec__1(obj*, obj*);
obj* l_array_uread___rarg(obj*, usize, obj*);
obj* l_lean_ir_decl_replace__vars(obj*, obj*);
obj* l_lean_ir_find(obj*, obj*);
obj* l_lean_ir_elim__phi__m_run___rarg(obj*);
obj* l_lean_ir_instr_replace__vars___main(obj*, obj*);
obj* l_mk__d__hashmap___at_lean_ir_elim__phi__m_run___spec__2(obj*);
obj* l_hashmap__imp_find__aux___main___at_lean_ir_merge___spec__10(obj*, obj*);
uint8 l_hashmap__imp_contains__aux___at_lean_ir_merge___spec__9(obj*, obj*);
obj* l_hashmap__imp_find__aux___main___at_lean_ir_merge___spec__6(obj*, obj*);
obj* l_list_mmap___main___at_lean_ir_decl_replace__vars___main___spec__1(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_group__vars___main___spec__2(obj*, obj*);
obj* l_lean_ir_block_replace__vars(obj*, obj*);
obj* l_hashmap__imp_insert___at_lean_ir_merge___spec__8___closed__1;
obj* l_d__hashmap_insert___at_lean_ir_merge___spec__7(obj*, obj*, obj*);
obj* l_lean_disjoint__set_merge___main___at_lean_ir_merge___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_merge(obj*, obj*, obj*);
obj* l_lean_ir_group__vars(obj*, obj*);
obj* l_array_uwrite___rarg(obj*, usize, obj*, obj*);
obj* l_list_mmap___main___at_lean_ir_instr_replace__vars___main___spec__3(obj*, obj*);
obj* l_lean_ir_elim__phi__m_run(obj*);
obj* l_lean_disjoint__set_find___main___at_lean_ir_find___spec__1(obj*, obj*);
obj* l_lean_ir_group__vars___main(obj*, obj*);
obj* l_lean_ir_terminator_replace__vars(obj*, obj*);
obj* l_hashmap__imp_replace__aux___main___at_lean_ir_merge___spec__11(obj*, obj*, obj*);
obj* l_lean_name_hash___boxed(obj*);
obj* l_hashmap__imp_find___at_lean_ir_merge___spec__5(obj*, obj*);
obj* l_lean_ir_terminator_replace__vars___main(obj*, obj*);
obj* l_d__hashmap_size___at_lean_ir_merge___spec__2(obj*);
obj* l_hashmap__imp_contains__aux___at_lean_ir_merge___spec__9___boxed(obj*, obj*);
obj* l_lean_ir_decl_replace__vars___main(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_group__vars___main___spec__3(obj*, obj*);
obj* l_hashmap__imp_insert___at_lean_ir_merge___spec__8(obj*, obj*, obj*);
obj* l_hashmap__imp_reinsert__aux___rarg(obj*, obj*, obj*, obj*);
obj* _init_l_lean_ir_elim__phi__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_ir_elim__phi__m_run___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; 
x_1 = l_lean_ir_elim__phi__m_run___rarg___closed__1;
lean::inc(x_1);
x_3 = lean::apply_1(x_0, x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
obj* _init_l_lean_ir_elim__phi__m_run___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = l_lean_mk__disjoint__set___at_lean_ir_elim__phi__m_run___spec__1;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_ir_elim__phi__m_run(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_elim__phi__m_run___rarg), 1, 0);
return x_2;
}
}
obj* l_mk__d__hashmap___at_lean_ir_elim__phi__m_run___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mk__hashmap__imp___rarg(x_0);
return x_1;
}
}
obj* _init_l_lean_mk__disjoint__set___at_lean_ir_elim__phi__m_run___spec__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(8u);
x_1 = l_mk__hashmap__imp___rarg(x_0);
return x_1;
}
}
obj* l_lean_ir_merge(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_disjoint__set_merge___main___at_lean_ir_merge___spec__1(x_2, x_0, x_1);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* l_d__hashmap_size___at_lean_ir_merge___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_hashmap__imp_find__aux___main___at_lean_ir_merge___spec__6(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; uint8 x_15; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::name_dec_eq(x_10, x_0);
lean::dec(x_10);
if (x_15 == 0)
{
lean::dec(x_12);
x_1 = x_7;
goto _start;
}
else
{
obj* x_21; 
lean::dec(x_7);
lean::dec(x_0);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_12);
return x_21;
}
}
}
}
obj* l_hashmap__imp_find___at_lean_ir_merge___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; usize x_7; usize x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::name_hash_usize(x_1);
x_8 = lean::usize_modn(x_7, x_5);
lean::dec(x_5);
x_10 = l_array_uread___rarg(x_2, x_8, lean::box(0));
x_11 = l_hashmap__imp_find__aux___main___at_lean_ir_merge___spec__6(x_1, x_10);
return x_11;
}
}
obj* l_d__hashmap_find___at_lean_ir_merge___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_hashmap__imp_find___at_lean_ir_merge___spec__5(x_0, x_1);
return x_2;
}
}
obj* l___private_3363165505__find__aux___main___at_lean_ir_merge___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_7; 
lean::inc(x_1);
lean::inc(x_2);
x_7 = l_hashmap__imp_find___at_lean_ir_merge___spec__5(x_2, x_1);
if (lean::obj_tag(x_7) == 0)
{
obj* x_11; 
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_2);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_3);
return x_11;
}
else
{
obj* x_13; obj* x_16; uint8 x_18; 
lean::dec(x_3);
x_13 = lean::cnstr_get(x_7, 0);
lean::inc(x_13);
lean::dec(x_7);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
x_18 = lean::name_dec_eq(x_16, x_1);
lean::dec(x_1);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_13);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_sub(x_0, x_21);
lean::dec(x_21);
lean::dec(x_0);
x_0 = x_22;
x_1 = x_16;
goto _start;
}
else
{
lean::dec(x_16);
lean::dec(x_0);
lean::dec(x_2);
return x_13;
}
}
}
else
{
obj* x_31; 
lean::dec(x_0);
lean::dec(x_2);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_1);
lean::cnstr_set(x_31, 1, x_3);
return x_31;
}
}
}
obj* l_hashmap__imp_find__aux___main___at_lean_ir_merge___spec__10(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; uint8 x_15; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::name_dec_eq(x_10, x_0);
lean::dec(x_10);
if (x_15 == 0)
{
lean::dec(x_12);
x_1 = x_7;
goto _start;
}
else
{
obj* x_21; 
lean::dec(x_7);
lean::dec(x_0);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_12);
return x_21;
}
}
}
}
uint8 l_hashmap__imp_contains__aux___at_lean_ir_merge___spec__9(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = l_hashmap__imp_find__aux___main___at_lean_ir_merge___spec__10(x_0, x_1);
x_3 = l_option_is__some___main___rarg(x_2);
return x_3;
}
}
obj* l_hashmap__imp_replace__aux___main___at_lean_ir_merge___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; uint8 x_12; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_9 = x_2;
}
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::name_dec_eq(x_10, x_0);
lean::dec(x_10);
if (x_12 == 0)
{
obj* x_14; obj* x_15; 
x_14 = l_hashmap__imp_replace__aux___main___at_lean_ir_merge___spec__11(x_0, x_1, x_7);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_5);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_5);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_0);
lean::cnstr_set(x_17, 1, x_1);
if (lean::is_scalar(x_9)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_9;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_7);
return x_18;
}
}
}
}
obj* l_hashmap__imp_insert___at_lean_ir_merge___spec__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; usize x_10; usize x_11; obj* x_13; uint8 x_16; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_10 = lean::name_hash_usize(x_1);
x_11 = lean::usize_modn(x_10, x_8);
lean::inc(x_5);
x_13 = l_array_uread___rarg(x_5, x_11, lean::box(0));
lean::inc(x_13);
lean::inc(x_1);
x_16 = l_hashmap__imp_contains__aux___at_lean_ir_merge___spec__9(x_1, x_13);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_add(x_3, x_17);
lean::dec(x_17);
lean::dec(x_3);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_2);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_13);
x_23 = l_array_uwrite___rarg(x_5, x_11, x_22, lean::box(0));
x_24 = lean::nat_dec_le(x_18, x_8);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_34; 
x_25 = lean::mk_nat_obj(2u);
x_26 = lean::nat_mul(x_8, x_25);
lean::dec(x_25);
lean::dec(x_8);
x_29 = lean::box(0);
x_30 = l_mk__array___rarg(x_26, x_29);
x_31 = l_hashmap__imp_insert___at_lean_ir_merge___spec__8___closed__1;
lean::inc(x_31);
x_33 = l_hashmap__imp_fold__buckets___rarg(x_23, x_30, x_31);
if (lean::is_scalar(x_7)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_7;
}
lean::cnstr_set(x_34, 0, x_18);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
else
{
obj* x_36; 
lean::dec(x_8);
if (lean::is_scalar(x_7)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_7;
}
lean::cnstr_set(x_36, 0, x_18);
lean::cnstr_set(x_36, 1, x_23);
return x_36;
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_8);
x_38 = l_hashmap__imp_replace__aux___main___at_lean_ir_merge___spec__11(x_1, x_2, x_13);
x_39 = l_array_uwrite___rarg(x_5, x_11, x_38, lean::box(0));
if (lean::is_scalar(x_7)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_7;
}
lean::cnstr_set(x_40, 0, x_3);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
}
}
obj* _init_l_hashmap__imp_insert___at_lean_ir_merge___spec__8___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_name_hash___boxed), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_hashmap__imp_reinsert__aux___rarg), 4, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_d__hashmap_insert___at_lean_ir_merge___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_hashmap__imp_insert___at_lean_ir_merge___spec__8(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_disjoint__set_merge___main___at_lean_ir_merge___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_8; obj* x_11; obj* x_12; obj* x_14; uint8 x_16; 
lean::inc(x_0);
x_4 = l_d__hashmap_size___at_lean_ir_merge___spec__2(x_0);
lean::inc(x_0);
lean::inc(x_1);
lean::inc(x_4);
x_8 = l___private_3363165505__find__aux___main___at_lean_ir_merge___spec__3(x_4, x_1, x_0);
lean::inc(x_0);
lean::inc(x_2);
x_11 = l___private_3363165505__find__aux___main___at_lean_ir_merge___spec__3(x_4, x_2, x_0);
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
x_16 = lean::name_dec_eq(x_12, x_14);
lean::dec(x_14);
lean::dec(x_12);
if (x_16 == 0)
{
obj* x_19; obj* x_22; uint8 x_25; 
x_19 = lean::cnstr_get(x_8, 1);
lean::inc(x_19);
lean::dec(x_8);
x_22 = lean::cnstr_get(x_11, 1);
lean::inc(x_22);
lean::dec(x_11);
x_25 = lean::nat_dec_lt(x_19, x_22);
if (x_25 == 0)
{
uint8 x_26; 
x_26 = lean::nat_dec_eq(x_19, x_22);
lean::dec(x_19);
if (x_26 == 0)
{
obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_22);
x_29 = lean::mk_nat_obj(0u);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_29);
x_31 = l_hashmap__imp_insert___at_lean_ir_merge___spec__8(x_0, x_2, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_41; obj* x_42; 
x_32 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_2);
lean::cnstr_set(x_34, 1, x_32);
x_35 = l_hashmap__imp_insert___at_lean_ir_merge___spec__8(x_0, x_1, x_34);
x_36 = lean::mk_nat_obj(1u);
x_37 = lean::nat_add(x_22, x_36);
lean::dec(x_36);
lean::dec(x_22);
lean::inc(x_2);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_2);
lean::cnstr_set(x_41, 1, x_37);
x_42 = l_hashmap__imp_insert___at_lean_ir_merge___spec__8(x_35, x_2, x_41);
return x_42;
}
}
else
{
obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_19);
lean::dec(x_22);
x_45 = lean::mk_nat_obj(0u);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_2);
lean::cnstr_set(x_46, 1, x_45);
x_47 = l_hashmap__imp_insert___at_lean_ir_merge___spec__8(x_0, x_1, x_46);
return x_47;
}
}
else
{
lean::dec(x_11);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_2);
return x_0;
}
}
}
obj* l_hashmap__imp_contains__aux___at_lean_ir_merge___spec__9___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_hashmap__imp_contains__aux___at_lean_ir_merge___spec__9(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_lean_ir_find(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; 
lean::inc(x_1);
x_3 = l_lean_disjoint__set_find___main___at_lean_ir_find___spec__1(x_1, x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
}
obj* l_lean_disjoint__set_find___main___at_lean_ir_find___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
lean::inc(x_0);
x_3 = l_d__hashmap_size___at_lean_ir_merge___spec__2(x_0);
x_4 = l___private_3363165505__find__aux___main___at_lean_ir_merge___spec__3(x_3, x_1, x_0);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_ir_group__vars___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
lean::dec(x_0);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_8; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_list_mmap_x_27___main___at_lean_ir_group__vars___main___spec__3(x_5, x_1);
return x_8;
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_group__vars___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_15; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
x_14 = l_lean_ir_merge(x_12, x_7, x_2);
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
lean::dec(x_14);
x_1 = x_9;
x_2 = x_15;
goto _start;
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_group__vars___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
lean::dec(x_0);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = l_list_mmap_x_27___main___at_lean_ir_group__vars___main___spec__1(x_5, x_10, x_1);
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
lean::dec(x_12);
x_0 = x_7;
x_1 = x_13;
goto _start;
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_group__vars___main___spec__3(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
lean::dec(x_0);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_13; obj* x_14; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
x_13 = l_list_mmap_x_27___main___at_lean_ir_group__vars___main___spec__2(x_10, x_1);
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
lean::dec(x_13);
x_0 = x_7;
x_1 = x_14;
goto _start;
}
}
}
obj* l_lean_ir_group__vars(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_group__vars___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_ir_instr_replace__vars___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; uint8 x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_22; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_lean_ir_find(x_2, x_1);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
x_14 = l_lean_ir_find(x_5, x_11);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
if (lean::is_scalar(x_7)) {
 x_20 = lean::alloc_cnstr(0, 2, 1);
} else {
 x_20 = x_7;
}
lean::cnstr_set(x_20, 0, x_9);
lean::cnstr_set(x_20, 1, x_15);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_4);
x_21 = x_20;
if (lean::is_scalar(x_13)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_13;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_17);
return x_22;
}
case 1:
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_26 = lean::cnstr_get(x_0, 1);
lean::inc(x_26);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_28 = x_0;
}
x_29 = l_lean_ir_find(x_23, x_1);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
if (lean::is_shared(x_29)) {
 lean::dec(x_29);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_29, 0);
 lean::cnstr_release(x_29, 1);
 x_34 = x_29;
}
if (lean::is_scalar(x_28)) {
 x_35 = lean::alloc_cnstr(1, 2, 1);
} else {
 x_35 = x_28;
}
lean::cnstr_set(x_35, 0, x_30);
lean::cnstr_set(x_35, 1, x_26);
lean::cnstr_set_scalar(x_35, sizeof(void*)*2, x_25);
x_36 = x_35;
if (lean::is_scalar(x_34)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_34;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_32);
return x_37;
}
case 2:
{
obj* x_38; uint8 x_40; uint8 x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_38 = lean::cnstr_get(x_0, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_41 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2 + 1);
x_42 = lean::cnstr_get(x_0, 1);
lean::inc(x_42);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_44 = x_0;
}
x_45 = l_lean_ir_find(x_38, x_1);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
if (lean::is_shared(x_45)) {
 lean::dec(x_45);
 x_50 = lean::box(0);
} else {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_50 = x_45;
}
x_51 = l_lean_ir_find(x_42, x_48);
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
lean::dec(x_51);
if (lean::is_scalar(x_44)) {
 x_57 = lean::alloc_cnstr(2, 2, 2);
} else {
 x_57 = x_44;
}
lean::cnstr_set(x_57, 0, x_46);
lean::cnstr_set(x_57, 1, x_52);
lean::cnstr_set_scalar(x_57, sizeof(void*)*2, x_40);
x_58 = x_57;
lean::cnstr_set_scalar(x_58, sizeof(void*)*2 + 1, x_41);
x_59 = x_58;
if (lean::is_scalar(x_50)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_50;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_54);
return x_60;
}
case 3:
{
obj* x_61; uint8 x_63; uint8 x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_79; obj* x_82; obj* x_83; obj* x_85; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_61 = lean::cnstr_get(x_0, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_64 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3 + 1);
x_65 = lean::cnstr_get(x_0, 1);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_0, 2);
lean::inc(x_67);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_69 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 x_69 = x_0;
}
x_70 = l_lean_ir_find(x_61, x_1);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_75 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 lean::cnstr_release(x_70, 1);
 x_75 = x_70;
}
x_76 = l_lean_ir_find(x_65, x_73);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
x_82 = l_lean_ir_find(x_67, x_79);
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
if (lean::is_scalar(x_69)) {
 x_88 = lean::alloc_cnstr(3, 3, 2);
} else {
 x_88 = x_69;
}
lean::cnstr_set(x_88, 0, x_71);
lean::cnstr_set(x_88, 1, x_77);
lean::cnstr_set(x_88, 2, x_83);
lean::cnstr_set_scalar(x_88, sizeof(void*)*3, x_63);
x_89 = x_88;
lean::cnstr_set_scalar(x_89, sizeof(void*)*3 + 1, x_64);
x_90 = x_89;
if (lean::is_scalar(x_75)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_75;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_85);
return x_91;
}
case 4:
{
uint8 x_92; obj* x_93; obj* x_95; obj* x_96; obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_92 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
x_93 = lean::cnstr_get(x_0, 0);
lean::inc(x_93);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_95 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_95 = x_0;
}
x_96 = l_lean_ir_find(x_93, x_1);
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_96, 1);
lean::inc(x_99);
if (lean::is_shared(x_96)) {
 lean::dec(x_96);
 x_101 = lean::box(0);
} else {
 lean::cnstr_release(x_96, 0);
 lean::cnstr_release(x_96, 1);
 x_101 = x_96;
}
if (lean::is_scalar(x_95)) {
 x_102 = lean::alloc_cnstr(4, 1, 1);
} else {
 x_102 = x_95;
}
lean::cnstr_set(x_102, 0, x_97);
lean::cnstr_set_scalar(x_102, sizeof(void*)*1, x_92);
x_103 = x_102;
if (lean::is_scalar(x_101)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_101;
}
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_99);
return x_104;
}
case 5:
{
obj* x_105; obj* x_107; obj* x_109; obj* x_111; obj* x_112; obj* x_113; obj* x_115; obj* x_117; obj* x_118; obj* x_119; obj* x_121; obj* x_124; obj* x_125; 
x_105 = lean::cnstr_get(x_0, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_0, 1);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_0, 2);
lean::inc(x_109);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_111 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 x_111 = x_0;
}
x_112 = l_lean_ir_find(x_105, x_1);
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_112, 1);
lean::inc(x_115);
if (lean::is_shared(x_112)) {
 lean::dec(x_112);
 x_117 = lean::box(0);
} else {
 lean::cnstr_release(x_112, 0);
 lean::cnstr_release(x_112, 1);
 x_117 = x_112;
}
x_118 = l_list_mmap___main___at_lean_ir_instr_replace__vars___main___spec__1(x_109, x_115);
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_118, 1);
lean::inc(x_121);
lean::dec(x_118);
if (lean::is_scalar(x_111)) {
 x_124 = lean::alloc_cnstr(5, 3, 0);
} else {
 x_124 = x_111;
}
lean::cnstr_set(x_124, 0, x_113);
lean::cnstr_set(x_124, 1, x_107);
lean::cnstr_set(x_124, 2, x_119);
if (lean::is_scalar(x_117)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_117;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_121);
return x_125;
}
case 6:
{
obj* x_126; uint16 x_128; uint16 x_129; usize x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_135; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_126 = lean::cnstr_get(x_0, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
x_129 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2 + 2);
x_130 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*1);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_131 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_131 = x_0;
}
x_132 = l_lean_ir_find(x_126, x_1);
x_133 = lean::cnstr_get(x_132, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_132, 1);
lean::inc(x_135);
if (lean::is_shared(x_132)) {
 lean::dec(x_132);
 x_137 = lean::box(0);
} else {
 lean::cnstr_release(x_132, 0);
 lean::cnstr_release(x_132, 1);
 x_137 = x_132;
}
if (lean::is_scalar(x_131)) {
 x_138 = lean::alloc_cnstr(6, 1, sizeof(size_t)*1 + 4);
} else {
 x_138 = x_131;
}
lean::cnstr_set(x_138, 0, x_133);
lean::cnstr_set_scalar(x_138, sizeof(void*)*2, x_128);
x_139 = x_138;
lean::cnstr_set_scalar(x_139, sizeof(void*)*2 + 2, x_129);
x_140 = x_139;
lean::cnstr_set_scalar(x_140, sizeof(void*)*1, x_130);
x_141 = x_140;
if (lean::is_scalar(x_137)) {
 x_142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_142 = x_137;
}
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_135);
return x_142;
}
case 7:
{
obj* x_143; uint16 x_145; obj* x_146; obj* x_148; obj* x_149; obj* x_150; obj* x_152; obj* x_154; obj* x_155; obj* x_156; obj* x_158; obj* x_161; obj* x_162; obj* x_163; 
x_143 = lean::cnstr_get(x_0, 0);
lean::inc(x_143);
x_145 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
x_146 = lean::cnstr_get(x_0, 1);
lean::inc(x_146);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_148 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_148 = x_0;
}
x_149 = l_lean_ir_find(x_143, x_1);
x_150 = lean::cnstr_get(x_149, 0);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_149, 1);
lean::inc(x_152);
if (lean::is_shared(x_149)) {
 lean::dec(x_149);
 x_154 = lean::box(0);
} else {
 lean::cnstr_release(x_149, 0);
 lean::cnstr_release(x_149, 1);
 x_154 = x_149;
}
x_155 = l_lean_ir_find(x_146, x_152);
x_156 = lean::cnstr_get(x_155, 0);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_155, 1);
lean::inc(x_158);
lean::dec(x_155);
if (lean::is_scalar(x_148)) {
 x_161 = lean::alloc_cnstr(7, 2, 2);
} else {
 x_161 = x_148;
}
lean::cnstr_set(x_161, 0, x_150);
lean::cnstr_set(x_161, 1, x_156);
lean::cnstr_set_scalar(x_161, sizeof(void*)*2, x_145);
x_162 = x_161;
if (lean::is_scalar(x_154)) {
 x_163 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_163 = x_154;
}
lean::cnstr_set(x_163, 0, x_162);
lean::cnstr_set(x_163, 1, x_158);
return x_163;
}
case 8:
{
obj* x_164; obj* x_166; uint16 x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_173; obj* x_175; obj* x_176; obj* x_177; obj* x_179; obj* x_182; obj* x_183; obj* x_184; 
x_164 = lean::cnstr_get(x_0, 0);
lean::inc(x_164);
x_166 = lean::cnstr_get(x_0, 1);
lean::inc(x_166);
x_168 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_169 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_169 = x_0;
}
x_170 = l_lean_ir_find(x_164, x_1);
x_171 = lean::cnstr_get(x_170, 0);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_170, 1);
lean::inc(x_173);
if (lean::is_shared(x_170)) {
 lean::dec(x_170);
 x_175 = lean::box(0);
} else {
 lean::cnstr_release(x_170, 0);
 lean::cnstr_release(x_170, 1);
 x_175 = x_170;
}
x_176 = l_lean_ir_find(x_166, x_173);
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_176, 1);
lean::inc(x_179);
lean::dec(x_176);
if (lean::is_scalar(x_169)) {
 x_182 = lean::alloc_cnstr(8, 2, 2);
} else {
 x_182 = x_169;
}
lean::cnstr_set(x_182, 0, x_171);
lean::cnstr_set(x_182, 1, x_177);
lean::cnstr_set_scalar(x_182, sizeof(void*)*2, x_168);
x_183 = x_182;
if (lean::is_scalar(x_175)) {
 x_184 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_184 = x_175;
}
lean::cnstr_set(x_184, 0, x_183);
lean::cnstr_set(x_184, 1, x_179);
return x_184;
}
case 9:
{
obj* x_185; usize x_187; obj* x_188; obj* x_190; obj* x_191; obj* x_192; obj* x_194; obj* x_196; obj* x_197; obj* x_198; obj* x_200; obj* x_203; obj* x_204; obj* x_205; 
x_185 = lean::cnstr_get(x_0, 0);
lean::inc(x_185);
x_187 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
x_188 = lean::cnstr_get(x_0, 1);
lean::inc(x_188);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_190 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_190 = x_0;
}
x_191 = l_lean_ir_find(x_185, x_1);
x_192 = lean::cnstr_get(x_191, 0);
lean::inc(x_192);
x_194 = lean::cnstr_get(x_191, 1);
lean::inc(x_194);
if (lean::is_shared(x_191)) {
 lean::dec(x_191);
 x_196 = lean::box(0);
} else {
 lean::cnstr_release(x_191, 0);
 lean::cnstr_release(x_191, 1);
 x_196 = x_191;
}
x_197 = l_lean_ir_find(x_188, x_194);
x_198 = lean::cnstr_get(x_197, 0);
lean::inc(x_198);
x_200 = lean::cnstr_get(x_197, 1);
lean::inc(x_200);
lean::dec(x_197);
if (lean::is_scalar(x_190)) {
 x_203 = lean::alloc_cnstr(9, 2, sizeof(size_t)*1);
} else {
 x_203 = x_190;
}
lean::cnstr_set(x_203, 0, x_192);
lean::cnstr_set(x_203, 1, x_198);
lean::cnstr_set_scalar(x_203, sizeof(void*)*2, x_187);
x_204 = x_203;
if (lean::is_scalar(x_196)) {
 x_205 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_205 = x_196;
}
lean::cnstr_set(x_205, 0, x_204);
lean::cnstr_set(x_205, 1, x_200);
return x_205;
}
case 10:
{
obj* x_206; uint8 x_208; obj* x_209; usize x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_216; obj* x_218; obj* x_219; obj* x_220; obj* x_222; obj* x_225; obj* x_226; obj* x_227; obj* x_228; 
x_206 = lean::cnstr_get(x_0, 0);
lean::inc(x_206);
x_208 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_209 = lean::cnstr_get(x_0, 1);
lean::inc(x_209);
x_211 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_212 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_212 = x_0;
}
x_213 = l_lean_ir_find(x_206, x_1);
x_214 = lean::cnstr_get(x_213, 0);
lean::inc(x_214);
x_216 = lean::cnstr_get(x_213, 1);
lean::inc(x_216);
if (lean::is_shared(x_213)) {
 lean::dec(x_213);
 x_218 = lean::box(0);
} else {
 lean::cnstr_release(x_213, 0);
 lean::cnstr_release(x_213, 1);
 x_218 = x_213;
}
x_219 = l_lean_ir_find(x_209, x_216);
x_220 = lean::cnstr_get(x_219, 0);
lean::inc(x_220);
x_222 = lean::cnstr_get(x_219, 1);
lean::inc(x_222);
lean::dec(x_219);
if (lean::is_scalar(x_212)) {
 x_225 = lean::alloc_cnstr(10, 2, sizeof(size_t)*1 + 1);
} else {
 x_225 = x_212;
}
lean::cnstr_set(x_225, 0, x_214);
lean::cnstr_set(x_225, 1, x_220);
lean::cnstr_set_scalar(x_225, sizeof(void*)*3, x_208);
x_226 = x_225;
lean::cnstr_set_scalar(x_226, sizeof(void*)*2, x_211);
x_227 = x_226;
if (lean::is_scalar(x_218)) {
 x_228 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_228 = x_218;
}
lean::cnstr_set(x_228, 0, x_227);
lean::cnstr_set(x_228, 1, x_222);
return x_228;
}
case 11:
{
obj* x_229; obj* x_231; obj* x_233; obj* x_235; obj* x_236; obj* x_237; obj* x_239; obj* x_241; obj* x_242; obj* x_243; obj* x_245; obj* x_248; obj* x_249; 
x_229 = lean::cnstr_get(x_0, 0);
lean::inc(x_229);
x_231 = lean::cnstr_get(x_0, 1);
lean::inc(x_231);
x_233 = lean::cnstr_get(x_0, 2);
lean::inc(x_233);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_235 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 x_235 = x_0;
}
x_236 = l_lean_ir_find(x_229, x_1);
x_237 = lean::cnstr_get(x_236, 0);
lean::inc(x_237);
x_239 = lean::cnstr_get(x_236, 1);
lean::inc(x_239);
if (lean::is_shared(x_236)) {
 lean::dec(x_236);
 x_241 = lean::box(0);
} else {
 lean::cnstr_release(x_236, 0);
 lean::cnstr_release(x_236, 1);
 x_241 = x_236;
}
x_242 = l_list_mmap___main___at_lean_ir_instr_replace__vars___main___spec__2(x_233, x_239);
x_243 = lean::cnstr_get(x_242, 0);
lean::inc(x_243);
x_245 = lean::cnstr_get(x_242, 1);
lean::inc(x_245);
lean::dec(x_242);
if (lean::is_scalar(x_235)) {
 x_248 = lean::alloc_cnstr(11, 3, 0);
} else {
 x_248 = x_235;
}
lean::cnstr_set(x_248, 0, x_237);
lean::cnstr_set(x_248, 1, x_231);
lean::cnstr_set(x_248, 2, x_243);
if (lean::is_scalar(x_241)) {
 x_249 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_249 = x_241;
}
lean::cnstr_set(x_249, 0, x_248);
lean::cnstr_set(x_249, 1, x_245);
return x_249;
}
case 12:
{
obj* x_250; obj* x_252; obj* x_254; obj* x_255; obj* x_256; obj* x_258; obj* x_260; obj* x_261; obj* x_262; obj* x_264; obj* x_267; obj* x_268; 
x_250 = lean::cnstr_get(x_0, 0);
lean::inc(x_250);
x_252 = lean::cnstr_get(x_0, 1);
lean::inc(x_252);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_254 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_254 = x_0;
}
x_255 = l_lean_ir_find(x_250, x_1);
x_256 = lean::cnstr_get(x_255, 0);
lean::inc(x_256);
x_258 = lean::cnstr_get(x_255, 1);
lean::inc(x_258);
if (lean::is_shared(x_255)) {
 lean::dec(x_255);
 x_260 = lean::box(0);
} else {
 lean::cnstr_release(x_255, 0);
 lean::cnstr_release(x_255, 1);
 x_260 = x_255;
}
x_261 = l_list_mmap___main___at_lean_ir_instr_replace__vars___main___spec__3(x_252, x_258);
x_262 = lean::cnstr_get(x_261, 0);
lean::inc(x_262);
x_264 = lean::cnstr_get(x_261, 1);
lean::inc(x_264);
lean::dec(x_261);
if (lean::is_scalar(x_254)) {
 x_267 = lean::alloc_cnstr(12, 2, 0);
} else {
 x_267 = x_254;
}
lean::cnstr_set(x_267, 0, x_256);
lean::cnstr_set(x_267, 1, x_262);
if (lean::is_scalar(x_260)) {
 x_268 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_268 = x_260;
}
lean::cnstr_set(x_268, 0, x_267);
lean::cnstr_set(x_268, 1, x_264);
return x_268;
}
case 13:
{
obj* x_269; obj* x_271; obj* x_273; obj* x_275; obj* x_276; obj* x_277; obj* x_279; obj* x_281; obj* x_282; obj* x_283; obj* x_285; obj* x_288; obj* x_289; obj* x_291; obj* x_294; obj* x_295; 
x_269 = lean::cnstr_get(x_0, 0);
lean::inc(x_269);
x_271 = lean::cnstr_get(x_0, 1);
lean::inc(x_271);
x_273 = lean::cnstr_get(x_0, 2);
lean::inc(x_273);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_275 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 x_275 = x_0;
}
x_276 = l_lean_ir_find(x_269, x_1);
x_277 = lean::cnstr_get(x_276, 0);
lean::inc(x_277);
x_279 = lean::cnstr_get(x_276, 1);
lean::inc(x_279);
if (lean::is_shared(x_276)) {
 lean::dec(x_276);
 x_281 = lean::box(0);
} else {
 lean::cnstr_release(x_276, 0);
 lean::cnstr_release(x_276, 1);
 x_281 = x_276;
}
x_282 = l_lean_ir_find(x_271, x_279);
x_283 = lean::cnstr_get(x_282, 0);
lean::inc(x_283);
x_285 = lean::cnstr_get(x_282, 1);
lean::inc(x_285);
lean::dec(x_282);
x_288 = l_lean_ir_find(x_273, x_285);
x_289 = lean::cnstr_get(x_288, 0);
lean::inc(x_289);
x_291 = lean::cnstr_get(x_288, 1);
lean::inc(x_291);
lean::dec(x_288);
if (lean::is_scalar(x_275)) {
 x_294 = lean::alloc_cnstr(13, 3, 0);
} else {
 x_294 = x_275;
}
lean::cnstr_set(x_294, 0, x_277);
lean::cnstr_set(x_294, 1, x_283);
lean::cnstr_set(x_294, 2, x_289);
if (lean::is_scalar(x_281)) {
 x_295 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_295 = x_281;
}
lean::cnstr_set(x_295, 0, x_294);
lean::cnstr_set(x_295, 1, x_291);
return x_295;
}
case 14:
{
obj* x_296; uint8 x_298; obj* x_299; obj* x_301; obj* x_303; obj* x_304; obj* x_305; obj* x_307; obj* x_309; obj* x_310; obj* x_311; obj* x_313; obj* x_316; obj* x_317; obj* x_319; obj* x_322; obj* x_323; obj* x_324; 
x_296 = lean::cnstr_get(x_0, 0);
lean::inc(x_296);
x_298 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_299 = lean::cnstr_get(x_0, 1);
lean::inc(x_299);
x_301 = lean::cnstr_get(x_0, 2);
lean::inc(x_301);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_303 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 x_303 = x_0;
}
x_304 = l_lean_ir_find(x_296, x_1);
x_305 = lean::cnstr_get(x_304, 0);
lean::inc(x_305);
x_307 = lean::cnstr_get(x_304, 1);
lean::inc(x_307);
if (lean::is_shared(x_304)) {
 lean::dec(x_304);
 x_309 = lean::box(0);
} else {
 lean::cnstr_release(x_304, 0);
 lean::cnstr_release(x_304, 1);
 x_309 = x_304;
}
x_310 = l_lean_ir_find(x_299, x_307);
x_311 = lean::cnstr_get(x_310, 0);
lean::inc(x_311);
x_313 = lean::cnstr_get(x_310, 1);
lean::inc(x_313);
lean::dec(x_310);
x_316 = l_lean_ir_find(x_301, x_313);
x_317 = lean::cnstr_get(x_316, 0);
lean::inc(x_317);
x_319 = lean::cnstr_get(x_316, 1);
lean::inc(x_319);
lean::dec(x_316);
if (lean::is_scalar(x_303)) {
 x_322 = lean::alloc_cnstr(14, 3, 1);
} else {
 x_322 = x_303;
}
lean::cnstr_set(x_322, 0, x_305);
lean::cnstr_set(x_322, 1, x_311);
lean::cnstr_set(x_322, 2, x_317);
lean::cnstr_set_scalar(x_322, sizeof(void*)*3, x_298);
x_323 = x_322;
if (lean::is_scalar(x_309)) {
 x_324 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_324 = x_309;
}
lean::cnstr_set(x_324, 0, x_323);
lean::cnstr_set(x_324, 1, x_319);
return x_324;
}
default:
{
obj* x_325; obj* x_327; obj* x_329; obj* x_331; obj* x_332; obj* x_333; obj* x_335; obj* x_337; obj* x_338; obj* x_339; obj* x_341; obj* x_344; obj* x_345; obj* x_347; obj* x_350; obj* x_351; 
x_325 = lean::cnstr_get(x_0, 0);
lean::inc(x_325);
x_327 = lean::cnstr_get(x_0, 1);
lean::inc(x_327);
x_329 = lean::cnstr_get(x_0, 2);
lean::inc(x_329);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_331 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 x_331 = x_0;
}
x_332 = l_lean_ir_find(x_325, x_1);
x_333 = lean::cnstr_get(x_332, 0);
lean::inc(x_333);
x_335 = lean::cnstr_get(x_332, 1);
lean::inc(x_335);
if (lean::is_shared(x_332)) {
 lean::dec(x_332);
 x_337 = lean::box(0);
} else {
 lean::cnstr_release(x_332, 0);
 lean::cnstr_release(x_332, 1);
 x_337 = x_332;
}
x_338 = l_lean_ir_find(x_327, x_335);
x_339 = lean::cnstr_get(x_338, 0);
lean::inc(x_339);
x_341 = lean::cnstr_get(x_338, 1);
lean::inc(x_341);
lean::dec(x_338);
x_344 = l_lean_ir_find(x_329, x_341);
x_345 = lean::cnstr_get(x_344, 0);
lean::inc(x_345);
x_347 = lean::cnstr_get(x_344, 1);
lean::inc(x_347);
lean::dec(x_344);
if (lean::is_scalar(x_331)) {
 x_350 = lean::alloc_cnstr(15, 3, 0);
} else {
 x_350 = x_331;
}
lean::cnstr_set(x_350, 0, x_333);
lean::cnstr_set(x_350, 1, x_339);
lean::cnstr_set(x_350, 2, x_345);
if (lean::is_scalar(x_337)) {
 x_351 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_351 = x_337;
}
lean::cnstr_set(x_351, 0, x_350);
lean::cnstr_set(x_351, 1, x_347);
return x_351;
}
}
}
}
obj* l_list_mmap___main___at_lean_ir_instr_replace__vars___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
lean::dec(x_0);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_23; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_9 = x_0;
}
x_10 = l_lean_ir_find(x_5, x_1);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
}
x_16 = l_list_mmap___main___at_lean_ir_instr_replace__vars___main___spec__1(x_7, x_13);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
if (lean::is_scalar(x_9)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_9;
}
lean::cnstr_set(x_22, 0, x_11);
lean::cnstr_set(x_22, 1, x_17);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
}
}
obj* l_list_mmap___main___at_lean_ir_instr_replace__vars___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
lean::dec(x_0);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_23; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_9 = x_0;
}
x_10 = l_lean_ir_find(x_5, x_1);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
}
x_16 = l_list_mmap___main___at_lean_ir_instr_replace__vars___main___spec__2(x_7, x_13);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
if (lean::is_scalar(x_9)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_9;
}
lean::cnstr_set(x_22, 0, x_11);
lean::cnstr_set(x_22, 1, x_17);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
}
}
obj* l_list_mmap___main___at_lean_ir_instr_replace__vars___main___spec__3(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
lean::dec(x_0);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_23; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_9 = x_0;
}
x_10 = l_lean_ir_find(x_5, x_1);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
}
x_16 = l_list_mmap___main___at_lean_ir_instr_replace__vars___main___spec__3(x_7, x_13);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
if (lean::is_scalar(x_9)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_9;
}
lean::cnstr_set(x_22, 0, x_11);
lean::cnstr_set(x_22, 1, x_17);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
}
}
obj* l_lean_ir_instr_replace__vars(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_instr_replace__vars___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_ir_terminator_replace__vars___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_4 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_4 = x_0;
}
x_5 = l_lean_ir_find(x_2, x_1);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
}
if (lean::is_scalar(x_4)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_4;
}
lean::cnstr_set(x_11, 0, x_6);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
case 1:
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 1);
lean::inc(x_15);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_17 = x_0;
}
x_18 = l_lean_ir_find(x_13, x_1);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 x_23 = x_18;
}
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_19);
lean::cnstr_set(x_24, 1, x_15);
if (lean::is_scalar(x_23)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_23;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_21);
return x_25;
}
default:
{
obj* x_26; 
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_0);
lean::cnstr_set(x_26, 1, x_1);
return x_26;
}
}
}
}
obj* l_lean_ir_terminator_replace__vars(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_terminator_replace__vars___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_ir_arg_replace__vars(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; uint8 x_10; obj* x_12; obj* x_13; obj* x_14; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = l_lean_ir_find(x_2, x_1);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
}
x_10 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
lean::dec(x_0);
x_12 = lean::alloc_cnstr(0, 1, 1);
lean::cnstr_set(x_12, 0, x_5);
lean::cnstr_set_scalar(x_12, sizeof(void*)*1, x_10);
x_13 = x_12;
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_9;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
}
obj* l_lean_ir_header_replace__vars(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; uint8 x_14; obj* x_16; obj* x_17; obj* x_18; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = l_list_mmap___main___at_lean_ir_header_replace__vars___spec__1(x_2, x_1);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
}
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 2);
lean::inc(x_12);
x_14 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
lean::dec(x_0);
x_16 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_16, 0, x_10);
lean::cnstr_set(x_16, 1, x_5);
lean::cnstr_set(x_16, 2, x_12);
lean::cnstr_set_scalar(x_16, sizeof(void*)*3, x_14);
x_17 = x_16;
if (lean::is_scalar(x_9)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_9;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_7);
return x_18;
}
}
obj* l_list_mmap___main___at_lean_ir_header_replace__vars___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
lean::dec(x_0);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_23; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_9 = x_0;
}
x_10 = l_lean_ir_arg_replace__vars(x_5, x_1);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
}
x_16 = l_list_mmap___main___at_lean_ir_header_replace__vars___spec__1(x_7, x_13);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
if (lean::is_scalar(x_9)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_9;
}
lean::cnstr_set(x_22, 0, x_11);
lean::cnstr_set(x_22, 1, x_17);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
}
}
obj* l_lean_ir_block_replace__vars(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_18; obj* x_21; obj* x_22; obj* x_23; 
x_2 = lean::cnstr_get(x_0, 2);
lean::inc(x_2);
x_4 = l_list_mmap___main___at_lean_ir_block_replace__vars___spec__1(x_2, x_1);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
}
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
x_12 = l_lean_ir_terminator_replace__vars___main(x_10, x_7);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
lean::dec(x_0);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_22, 0, x_18);
lean::cnstr_set(x_22, 1, x_21);
lean::cnstr_set(x_22, 2, x_5);
lean::cnstr_set(x_22, 3, x_13);
if (lean::is_scalar(x_9)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_9;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_15);
return x_23;
}
}
obj* l_list_mmap___main___at_lean_ir_block_replace__vars___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
lean::dec(x_0);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_23; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_9 = x_0;
}
x_10 = l_lean_ir_instr_replace__vars___main(x_5, x_1);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
}
x_16 = l_list_mmap___main___at_lean_ir_block_replace__vars___spec__1(x_7, x_13);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
if (lean::is_scalar(x_9)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_9;
}
lean::cnstr_set(x_22, 0, x_11);
lean::cnstr_set(x_22, 1, x_17);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
}
}
obj* l_lean_ir_decl_replace__vars___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_21; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_7 = x_0;
}
x_8 = l_lean_ir_header_replace__vars(x_3, x_1);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
x_14 = l_list_mmap___main___at_lean_ir_decl_replace__vars___main___spec__1(x_5, x_11);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
if (lean::is_scalar(x_7)) {
 x_20 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_20 = x_7;
}
lean::cnstr_set(x_20, 0, x_9);
lean::cnstr_set(x_20, 1, x_15);
if (lean::is_scalar(x_13)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_13;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_17);
return x_21;
}
}
}
obj* l_list_mmap___main___at_lean_ir_decl_replace__vars___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
lean::dec(x_0);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_23; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_9 = x_0;
}
x_10 = l_lean_ir_block_replace__vars(x_5, x_1);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
}
x_16 = l_list_mmap___main___at_lean_ir_decl_replace__vars___main___spec__1(x_7, x_13);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
if (lean::is_scalar(x_9)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_9;
}
lean::cnstr_set(x_22, 0, x_11);
lean::cnstr_set(x_22, 1, x_17);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
}
}
obj* l_lean_ir_decl_replace__vars(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_decl_replace__vars___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_ir_elim__phi__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
lean::inc(x_0);
x_3 = l_lean_ir_group__vars___main(x_0, x_1);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = l_lean_ir_decl_replace__vars___main(x_0, x_4);
return x_7;
}
}
obj* l_lean_ir_elim__phi(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_elim__phi__aux), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = l_lean_ir_elim__phi__m_run___rarg(x_1);
return x_2;
}
}
void initialize_init_lean_ir_instances();
void initialize_init_control_state();
void initialize_init_lean_disjoint__set();
static bool _G_initialized = false;
void initialize_init_lean_ir_elim__phi() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_ir_instances();
 initialize_init_control_state();
 initialize_init_lean_disjoint__set();
 l_lean_ir_elim__phi__m = _init_l_lean_ir_elim__phi__m();
 l_lean_ir_elim__phi__m_run___rarg___closed__1 = _init_l_lean_ir_elim__phi__m_run___rarg___closed__1();
 l_lean_mk__disjoint__set___at_lean_ir_elim__phi__m_run___spec__1 = _init_l_lean_mk__disjoint__set___at_lean_ir_elim__phi__m_run___spec__1();
 l_hashmap__imp_insert___at_lean_ir_merge___spec__8___closed__1 = _init_l_hashmap__imp_insert___at_lean_ir_merge___spec__8___closed__1();
}
