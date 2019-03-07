// Lean compiler output
// Module: init.lean.compiler.ir
// Imports: init.default init.lean.name init.lean.kvmap
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
uint8 l_lean_ir_alts_is__pure(obj*);
uint8 l_lean_ir_ctor__info_beq___main(obj*, obj*);
obj* l_lean_ir_jpid;
obj* l_lean_ir_args_alpha__eqv___boxed(obj*, obj*, obj*);
obj* l_lean_ir_ctor__info_beq___main___boxed(obj*, obj*);
obj* l_lean_ir_expr_alpha__eqv___boxed(obj*, obj*, obj*);
obj* l_lean_ir_args_alpha__eqv___main___boxed(obj*, obj*, obj*);
obj* l_lean_ir_varid_has__aeqv;
uint8 l_lean_ir_litval_beq(obj*, obj*);
obj* l_lean_ir_arg_has__aeqv;
obj* l_lean_ir_litval_beq___boxed(obj*, obj*);
uint8 l_lean_ir_expr_is__pure___main(obj*);
uint8 l_lean_ir_expr_is__pure(obj*);
uint8 l_lean_ir_type_beq___main(uint8, uint8);
obj* l_lean_ir_args_has__aeqv;
obj* l_lean_ir_alts_is__pure___boxed(obj*);
obj* l_lean_ir_type_has__beq;
obj* l_lean_ir_arg_alpha__eqv___main___boxed(obj*, obj*, obj*);
uint8 l_lean_ir_fnbody_is__pure(obj*);
obj* l_lean_ir_ctor__info_beq___boxed(obj*, obj*);
obj* l_lean_ir_litval_has__beq;
obj* l_lean_ir_alt_is__pure___main___boxed(obj*);
obj* l_lean_ir_fnbody_is__pure___main___boxed(obj*);
uint8 l_lean_ir_expr_alpha__eqv___main(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_ir_varid_alpha__eqv___spec__1___boxed(obj*, obj*);
obj* l_lean_ir_ctor__info_has__beq;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_lean_ir_args_alpha__eqv___main(obj*, obj*, obj*);
uint8 l_lean_ir_alts_is__pure___main(obj*);
obj* l_lean_ir_type_beq___boxed(obj*, obj*);
uint8 l_lean_ir_fnbody_is__pure___main(obj*);
uint8 l_lean_ir_litval_beq___main(obj*, obj*);
obj* l_lean_ir_fnbody_is__pure___boxed(obj*);
obj* l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(obj*, obj*);
obj* l_lean_ir_litval_beq___main___boxed(obj*, obj*);
uint8 l_lean_ir_expr_alpha__eqv(obj*, obj*, obj*);
obj* l_lean_ir_varid_alpha__eqv___boxed(obj*, obj*, obj*);
obj* l_lean_ir_arg_alpha__eqv___boxed(obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
uint8 l_lean_ir_varid_alpha__eqv(obj*, obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_lean_ir_expr_alpha__eqv___main___boxed(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_ir_varid_alpha__eqv___spec__1(obj*, obj*);
obj* l_lean_ir_fid;
obj* l_lean_ir_type_beq___main___boxed(obj*, obj*);
obj* l_lean_ir_varid;
obj* l_lean_ir_alt_is__pure___boxed(obj*);
uint8 l_lean_ir_type_beq(uint8, uint8);
uint8 l_lean_ir_ctor__info_beq(obj*, obj*);
uint8 l_lean_ir_alt_is__pure(obj*);
uint8 l_lean_ir_arg_alpha__eqv___main(obj*, obj*, obj*);
obj* l_lean_ir_expr_is__pure___main___boxed(obj*);
uint8 l_lean_ir_args_alpha__eqv(obj*, obj*, obj*);
obj* l_lean_ir_alts_is__pure___main___boxed(obj*);
uint8 l_lean_ir_arg_alpha__eqv(obj*, obj*, obj*);
uint8 l_lean_ir_alt_is__pure___main(obj*);
obj* l_lean_ir_expr_is__pure___boxed(obj*);
obj* _init_l_lean_ir_varid() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_fid() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_ir_jpid() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint8 l_lean_ir_type_beq___main(uint8 x_0, uint8 x_1) {
_start:
{
switch (x_0) {
case 0:
{
switch (x_1) {
case 0:
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
default:
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
}
case 1:
{
switch (x_1) {
case 1:
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
default:
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
}
}
case 2:
{
switch (x_1) {
case 2:
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
default:
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
}
case 3:
{
switch (x_1) {
case 3:
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
default:
{
uint8 x_9; 
x_9 = 0;
return x_9;
}
}
}
case 4:
{
switch (x_1) {
case 4:
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
default:
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
}
}
case 5:
{
switch (x_1) {
case 5:
{
uint8 x_12; 
x_12 = 1;
return x_12;
}
default:
{
uint8 x_13; 
x_13 = 0;
return x_13;
}
}
}
case 6:
{
switch (x_1) {
case 6:
{
uint8 x_14; 
x_14 = 1;
return x_14;
}
default:
{
uint8 x_15; 
x_15 = 0;
return x_15;
}
}
}
case 7:
{
switch (x_1) {
case 7:
{
uint8 x_16; 
x_16 = 1;
return x_16;
}
default:
{
uint8 x_17; 
x_17 = 0;
return x_17;
}
}
}
default:
{
switch (x_1) {
case 8:
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
default:
{
uint8 x_19; 
x_19 = 0;
return x_19;
}
}
}
}
}
}
obj* l_lean_ir_type_beq___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_lean_ir_type_beq___main(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_lean_ir_type_beq(uint8 x_0, uint8 x_1) {
_start:
{
uint8 x_2; 
x_2 = l_lean_ir_type_beq___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_ir_type_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_lean_ir_type_beq(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _init_l_lean_ir_type_has__beq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_type_beq___boxed), 2, 0);
return x_0;
}
}
uint8 l_lean_ir_litval_beq___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_8; 
x_8 = 0;
return x_8;
}
else
{
obj* x_9; obj* x_10; uint8 x_11; 
x_9 = lean::cnstr_get(x_0, 0);
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::string_dec_eq(x_9, x_10);
if (x_11 == 0)
{
uint8 x_12; 
x_12 = 0;
return x_12;
}
else
{
uint8 x_13; 
x_13 = 1;
return x_13;
}
}
}
}
}
obj* l_lean_ir_litval_beq___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_ir_litval_beq___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_lean_ir_litval_beq(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_lean_ir_litval_beq___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_ir_litval_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_ir_litval_beq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_lean_ir_litval_has__beq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_litval_beq___boxed), 2, 0);
return x_0;
}
}
uint8 l_lean_ir_ctor__info_beq___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::cnstr_get(x_0, 2);
x_5 = lean::cnstr_get(x_0, 3);
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::cnstr_get(x_1, 2);
x_9 = lean::cnstr_get(x_1, 3);
x_10 = lean_name_dec_eq(x_2, x_6);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8 x_12; 
x_12 = lean::nat_dec_eq(x_3, x_7);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = 0;
return x_13;
}
else
{
uint8 x_14; 
x_14 = lean::nat_dec_eq(x_4, x_8);
if (x_14 == 0)
{
uint8 x_15; 
x_15 = 0;
return x_15;
}
else
{
uint8 x_16; 
x_16 = lean::nat_dec_eq(x_5, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
}
}
}
}
}
obj* l_lean_ir_ctor__info_beq___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_ir_ctor__info_beq___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_lean_ir_ctor__info_beq(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_lean_ir_ctor__info_beq___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_ir_ctor__info_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_lean_ir_ctor__info_beq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_lean_ir_ctor__info_has__beq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_ctor__info_beq___boxed), 2, 0);
return x_0;
}
}
uint8 l_lean_ir_expr_is__pure___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
case 2:
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
case 9:
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
case 10:
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
case 12:
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
case 13:
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
default:
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* l_lean_ir_expr_is__pure___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_expr_is__pure___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_lean_ir_expr_is__pure(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_lean_ir_expr_is__pure___main(x_0);
return x_1;
}
}
obj* l_lean_ir_expr_is__pure___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_expr_is__pure(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_lean_ir_fnbody_is__pure___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::cnstr_get(x_0, 1);
x_2 = lean::cnstr_get(x_0, 2);
x_3 = l_lean_ir_expr_is__pure___main(x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
x_0 = x_2;
goto _start;
}
}
case 1:
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::cnstr_get(x_0, 2);
x_6 = lean::cnstr_get(x_0, 3);
x_7 = l_lean_ir_expr_is__pure___main(x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
x_0 = x_6;
goto _start;
}
}
case 3:
{
obj* x_9; 
x_9 = lean::cnstr_get(x_0, 3);
x_0 = x_9;
goto _start;
}
case 4:
{
obj* x_11; 
x_11 = lean::cnstr_get(x_0, 4);
x_0 = x_11;
goto _start;
}
case 10:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_0, 1);
x_0 = x_13;
goto _start;
}
case 11:
{
obj* x_15; uint8 x_16; 
x_15 = lean::cnstr_get(x_0, 1);
x_16 = l_lean_ir_alts_is__pure___main(x_15);
return x_16;
}
case 12:
{
uint8 x_17; 
x_17 = 1;
return x_17;
}
case 13:
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
case 14:
{
uint8 x_19; 
x_19 = 1;
return x_19;
}
default:
{
uint8 x_20; 
x_20 = 0;
return x_20;
}
}
}
}
uint8 l_lean_ir_alts_is__pure___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
else
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = l_lean_ir_alt_is__pure___main(x_2);
if (x_4 == 0)
{
return x_4;
}
else
{
x_0 = x_3;
goto _start;
}
}
}
}
uint8 l_lean_ir_alt_is__pure___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; uint8 x_2; 
x_1 = lean::cnstr_get(x_0, 1);
x_2 = l_lean_ir_fnbody_is__pure___main(x_1);
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
}
obj* l_lean_ir_fnbody_is__pure___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_fnbody_is__pure___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_ir_alts_is__pure___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_alts_is__pure___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_ir_alt_is__pure___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_alt_is__pure___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_lean_ir_fnbody_is__pure(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_lean_ir_fnbody_is__pure___main(x_0);
return x_1;
}
}
obj* l_lean_ir_fnbody_is__pure___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_fnbody_is__pure(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_lean_ir_alts_is__pure(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_lean_ir_alts_is__pure___main(x_0);
return x_1;
}
}
obj* l_lean_ir_alts_is__pure___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_alts_is__pure(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_lean_ir_alt_is__pure(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_lean_ir_alt_is__pure___main(x_0);
return x_1;
}
}
obj* l_lean_ir_alt_is__pure___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_lean_ir_alt_is__pure(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_ir_varid_alpha__eqv___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_1);
return x_2;
}
}
uint8 l_lean_ir_varid_alpha__eqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean_name_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_1);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
else
{
obj* x_6; uint8 x_9; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_9 = lean_name_dec_eq(x_6, x_2);
lean::dec(x_6);
if (x_9 == 0)
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8 x_12; 
x_12 = 1;
return x_12;
}
}
}
else
{
uint8 x_14; 
lean::dec(x_0);
x_14 = 1;
return x_14;
}
}
}
obj* l_rbmap_find___main___at_lean_ir_varid_alpha__eqv___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_ir_varid_alpha__eqv___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_ir_varid_alpha__eqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_lean_ir_varid_alpha__eqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_lean_ir_varid_has__aeqv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_varid_alpha__eqv___boxed), 3, 0);
return x_0;
}
}
uint8 l_lean_ir_arg_alpha__eqv___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_2, 0);
x_5 = l_lean_ir_varid_alpha__eqv(x_0, x_3, x_4);
return x_5;
}
else
{
uint8 x_7; 
lean::dec(x_0);
x_7 = 0;
return x_7;
}
}
else
{
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_9; 
x_9 = 0;
return x_9;
}
else
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
}
}
obj* l_lean_ir_arg_alpha__eqv___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_lean_ir_arg_alpha__eqv___main(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
uint8 l_lean_ir_arg_alpha__eqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_lean_ir_arg_alpha__eqv___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_ir_arg_alpha__eqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_lean_ir_arg_alpha__eqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_lean_ir_arg_has__aeqv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_arg_alpha__eqv___boxed), 3, 0);
return x_0;
}
}
uint8 l_lean_ir_args_alpha__eqv___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
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
else
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_7; 
lean::dec(x_0);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_13; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
x_10 = lean::cnstr_get(x_2, 0);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_13 = l_lean_ir_arg_alpha__eqv___main(x_0, x_8, x_10);
if (x_13 == 0)
{
lean::dec(x_0);
return x_13;
}
else
{
x_1 = x_9;
x_2 = x_11;
goto _start;
}
}
}
}
}
obj* l_lean_ir_args_alpha__eqv___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_lean_ir_args_alpha__eqv___main(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
uint8 l_lean_ir_args_alpha__eqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_lean_ir_args_alpha__eqv___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_ir_args_alpha__eqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_lean_ir_args_alpha__eqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_lean_ir_args_has__aeqv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_args_alpha__eqv___boxed), 3, 0);
return x_0;
}
}
uint8 l_lean_ir_expr_alpha__eqv___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_lean_ir_ctor__info_beq___main(x_3, x_5);
if (x_7 == 0)
{
lean::dec(x_0);
return x_7;
}
else
{
uint8 x_9; 
x_9 = l_lean_ir_args_alpha__eqv___main(x_0, x_4, x_6);
return x_9;
}
}
default:
{
uint8 x_11; 
lean::dec(x_0);
x_11 = 0;
return x_11;
}
}
}
case 1:
{
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_12; obj* x_13; uint8 x_14; 
x_12 = lean::cnstr_get(x_1, 0);
x_13 = lean::cnstr_get(x_2, 0);
x_14 = l_lean_ir_varid_alpha__eqv(x_0, x_12, x_13);
return x_14;
}
default:
{
uint8 x_16; 
lean::dec(x_0);
x_16 = 0;
return x_16;
}
}
}
case 2:
{
switch (lean::obj_tag(x_2)) {
case 2:
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; uint8 x_24; 
x_17 = lean::cnstr_get(x_1, 0);
x_18 = lean::cnstr_get(x_1, 1);
x_19 = lean::cnstr_get(x_1, 2);
x_20 = lean::cnstr_get(x_2, 0);
x_21 = lean::cnstr_get(x_2, 1);
x_22 = lean::cnstr_get(x_2, 2);
lean::inc(x_0);
x_24 = l_lean_ir_varid_alpha__eqv(x_0, x_17, x_20);
if (x_24 == 0)
{
if (x_24 == 0)
{
lean::dec(x_0);
return x_24;
}
else
{
uint8 x_26; 
x_26 = l_lean_ir_args_alpha__eqv___main(x_0, x_19, x_22);
return x_26;
}
}
else
{
uint8 x_27; 
x_27 = l_lean_ir_ctor__info_beq___main(x_18, x_21);
if (x_27 == 0)
{
lean::dec(x_0);
return x_27;
}
else
{
uint8 x_29; 
x_29 = l_lean_ir_args_alpha__eqv___main(x_0, x_19, x_22);
return x_29;
}
}
}
default:
{
uint8 x_31; 
lean::dec(x_0);
x_31 = 0;
return x_31;
}
}
}
case 3:
{
switch (lean::obj_tag(x_2)) {
case 3:
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; uint8 x_36; 
x_32 = lean::cnstr_get(x_1, 0);
x_33 = lean::cnstr_get(x_1, 1);
x_34 = lean::cnstr_get(x_2, 0);
x_35 = lean::cnstr_get(x_2, 1);
x_36 = lean::nat_dec_eq(x_32, x_34);
if (x_36 == 0)
{
uint8 x_38; 
lean::dec(x_0);
x_38 = 0;
return x_38;
}
else
{
uint8 x_39; 
x_39 = l_lean_ir_varid_alpha__eqv(x_0, x_33, x_35);
return x_39;
}
}
default:
{
uint8 x_41; 
lean::dec(x_0);
x_41 = 0;
return x_41;
}
}
}
case 4:
{
switch (lean::obj_tag(x_2)) {
case 4:
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; uint8 x_46; 
x_42 = lean::cnstr_get(x_1, 0);
x_43 = lean::cnstr_get(x_1, 1);
x_44 = lean::cnstr_get(x_2, 0);
x_45 = lean::cnstr_get(x_2, 1);
x_46 = lean::nat_dec_eq(x_42, x_44);
if (x_46 == 0)
{
uint8 x_48; 
lean::dec(x_0);
x_48 = 0;
return x_48;
}
else
{
uint8 x_49; 
x_49 = l_lean_ir_varid_alpha__eqv(x_0, x_43, x_45);
return x_49;
}
}
default:
{
uint8 x_51; 
lean::dec(x_0);
x_51 = 0;
return x_51;
}
}
}
case 5:
{
switch (lean::obj_tag(x_2)) {
case 5:
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; uint8 x_56; 
x_52 = lean::cnstr_get(x_1, 0);
x_53 = lean::cnstr_get(x_1, 1);
x_54 = lean::cnstr_get(x_2, 0);
x_55 = lean::cnstr_get(x_2, 1);
x_56 = lean::nat_dec_eq(x_52, x_54);
if (x_56 == 0)
{
uint8 x_58; 
lean::dec(x_0);
x_58 = 0;
return x_58;
}
else
{
uint8 x_59; 
x_59 = l_lean_ir_varid_alpha__eqv(x_0, x_53, x_55);
return x_59;
}
}
default:
{
uint8 x_61; 
lean::dec(x_0);
x_61 = 0;
return x_61;
}
}
}
case 6:
{
switch (lean::obj_tag(x_2)) {
case 6:
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; uint8 x_66; 
x_62 = lean::cnstr_get(x_1, 0);
x_63 = lean::cnstr_get(x_1, 1);
x_64 = lean::cnstr_get(x_2, 0);
x_65 = lean::cnstr_get(x_2, 1);
x_66 = lean_name_dec_eq(x_62, x_64);
if (x_66 == 0)
{
uint8 x_68; 
lean::dec(x_0);
x_68 = 0;
return x_68;
}
else
{
uint8 x_69; 
x_69 = l_lean_ir_args_alpha__eqv___main(x_0, x_63, x_65);
return x_69;
}
}
default:
{
uint8 x_71; 
lean::dec(x_0);
x_71 = 0;
return x_71;
}
}
}
case 7:
{
switch (lean::obj_tag(x_2)) {
case 7:
{
obj* x_72; obj* x_73; obj* x_74; uint8 x_75; 
x_72 = lean::cnstr_get(x_1, 0);
x_73 = lean::cnstr_get(x_2, 0);
x_74 = lean::cnstr_get(x_2, 1);
x_75 = lean_name_dec_eq(x_72, x_73);
if (x_75 == 0)
{
uint8 x_77; 
lean::dec(x_0);
x_77 = 0;
return x_77;
}
else
{
uint8 x_78; 
x_78 = l_lean_ir_args_alpha__eqv___main(x_0, x_74, x_74);
return x_78;
}
}
default:
{
uint8 x_80; 
lean::dec(x_0);
x_80 = 0;
return x_80;
}
}
}
case 8:
{
switch (lean::obj_tag(x_2)) {
case 8:
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; uint8 x_86; 
x_81 = lean::cnstr_get(x_1, 0);
x_82 = lean::cnstr_get(x_1, 1);
x_83 = lean::cnstr_get(x_2, 0);
x_84 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_86 = l_lean_ir_varid_alpha__eqv(x_0, x_81, x_83);
if (x_86 == 0)
{
lean::dec(x_0);
return x_86;
}
else
{
uint8 x_88; 
x_88 = l_lean_ir_args_alpha__eqv___main(x_0, x_82, x_84);
return x_88;
}
}
default:
{
uint8 x_90; 
lean::dec(x_0);
x_90 = 0;
return x_90;
}
}
}
case 9:
{
uint8 x_91; 
x_91 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
switch (lean::obj_tag(x_2)) {
case 9:
{
obj* x_92; uint8 x_93; obj* x_94; uint8 x_95; 
x_92 = lean::cnstr_get(x_1, 0);
x_93 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
x_94 = lean::cnstr_get(x_2, 0);
x_95 = l_lean_ir_type_beq___main(x_91, x_93);
if (x_95 == 0)
{
lean::dec(x_0);
return x_95;
}
else
{
uint8 x_97; 
x_97 = l_lean_ir_varid_alpha__eqv(x_0, x_92, x_94);
return x_97;
}
}
default:
{
uint8 x_99; 
lean::dec(x_0);
x_99 = 0;
return x_99;
}
}
}
case 10:
{
switch (lean::obj_tag(x_2)) {
case 10:
{
obj* x_100; obj* x_101; uint8 x_102; 
x_100 = lean::cnstr_get(x_1, 0);
x_101 = lean::cnstr_get(x_2, 0);
x_102 = l_lean_ir_varid_alpha__eqv(x_0, x_100, x_101);
return x_102;
}
default:
{
uint8 x_104; 
lean::dec(x_0);
x_104 = 0;
return x_104;
}
}
}
case 11:
{
lean::dec(x_0);
switch (lean::obj_tag(x_2)) {
case 11:
{
obj* x_106; obj* x_107; uint8 x_108; 
x_106 = lean::cnstr_get(x_1, 0);
x_107 = lean::cnstr_get(x_2, 0);
x_108 = l_lean_ir_litval_beq___main(x_106, x_107);
return x_108;
}
default:
{
uint8 x_109; 
x_109 = 0;
return x_109;
}
}
}
case 12:
{
switch (lean::obj_tag(x_2)) {
case 12:
{
obj* x_110; obj* x_111; uint8 x_112; 
x_110 = lean::cnstr_get(x_1, 0);
x_111 = lean::cnstr_get(x_2, 0);
x_112 = l_lean_ir_varid_alpha__eqv(x_0, x_110, x_111);
return x_112;
}
default:
{
uint8 x_114; 
lean::dec(x_0);
x_114 = 0;
return x_114;
}
}
}
default:
{
switch (lean::obj_tag(x_2)) {
case 13:
{
obj* x_115; obj* x_116; uint8 x_117; 
x_115 = lean::cnstr_get(x_1, 0);
x_116 = lean::cnstr_get(x_2, 0);
x_117 = l_lean_ir_varid_alpha__eqv(x_0, x_115, x_116);
return x_117;
}
default:
{
uint8 x_119; 
lean::dec(x_0);
x_119 = 0;
return x_119;
}
}
}
}
}
}
obj* l_lean_ir_expr_alpha__eqv___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_lean_ir_expr_alpha__eqv___main(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
uint8 l_lean_ir_expr_alpha__eqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_lean_ir_expr_alpha__eqv___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_ir_expr_alpha__eqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_lean_ir_expr_alpha__eqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
void initialize_init_default();
void initialize_init_lean_name();
void initialize_init_lean_kvmap();
static bool _G_initialized = false;
void initialize_init_lean_compiler_ir() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_default();
 initialize_init_lean_name();
 initialize_init_lean_kvmap();
 l_lean_ir_varid = _init_l_lean_ir_varid();
 l_lean_ir_fid = _init_l_lean_ir_fid();
 l_lean_ir_jpid = _init_l_lean_ir_jpid();
 l_lean_ir_type_has__beq = _init_l_lean_ir_type_has__beq();
lean::mark_persistent(l_lean_ir_type_has__beq);
 l_lean_ir_litval_has__beq = _init_l_lean_ir_litval_has__beq();
lean::mark_persistent(l_lean_ir_litval_has__beq);
 l_lean_ir_ctor__info_has__beq = _init_l_lean_ir_ctor__info_has__beq();
lean::mark_persistent(l_lean_ir_ctor__info_has__beq);
 l_lean_ir_varid_has__aeqv = _init_l_lean_ir_varid_has__aeqv();
lean::mark_persistent(l_lean_ir_varid_has__aeqv);
 l_lean_ir_arg_has__aeqv = _init_l_lean_ir_arg_has__aeqv();
lean::mark_persistent(l_lean_ir_arg_has__aeqv);
 l_lean_ir_args_has__aeqv = _init_l_lean_ir_args_has__aeqv();
lean::mark_persistent(l_lean_ir_args_has__aeqv);
}
