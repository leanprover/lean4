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
obj* l_lean_ir_alts_is__pure(obj*);
uint8 l_lean_ir_ctor__info_beq___main(obj*, obj*);
obj* l_lean_ir_jpid;
obj* l_lean_ir_args_alpha__eqv___boxed(obj*, obj*, obj*);
obj* l_lean_ir_ctor__info_beq___main___boxed(obj*, obj*);
obj* l_lean_ir_expr_alpha__eqv___boxed(obj*, obj*, obj*);
obj* l_lean_ir_args_alpha__eqv___main___boxed(obj*, obj*, obj*);
uint8 l_lean_ir_expr_is__pure___main(obj*);
uint8 l_lean_ir_expr_is__pure(obj*);
obj* l_lean_ir_alts_is__pure___boxed(obj*);
obj* l_lean_ir_arg_alpha__eqv___main___boxed(obj*, obj*, obj*);
obj* l_lean_ir_fnbody_is__pure(obj*);
obj* l_lean_ir_ctor__info_beq___boxed(obj*, obj*);
obj* l_lean_ir_alt_is__pure___main___boxed(obj*);
obj* l_lean_ir_fnbody_is__pure___main___boxed(obj*);
obj* l_lean_ir_expr_alpha__eqv___main(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_ir_varid_alpha__eqv___spec__1___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_ir_args_alpha__eqv___main(obj*, obj*, obj*);
obj* l_lean_ir_alts_is__pure___main(obj*);
obj* l_lean_ir_fnbody_is__pure___main(obj*);
obj* l_lean_ir_fnbody_is__pure___boxed(obj*);
obj* l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(obj*, obj*);
obj* l_lean_ir_expr_alpha__eqv(obj*, obj*, obj*);
obj* l_lean_ir_varid_alpha__eqv___boxed(obj*, obj*, obj*);
obj* l_lean_ir_arg_alpha__eqv___boxed(obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
uint8 l_lean_ir_varid_alpha__eqv(obj*, obj*, obj*);
obj* l_lean_ir_expr_alpha__eqv___main___boxed(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_ir_varid_alpha__eqv___spec__1(obj*, obj*);
obj* l_lean_ir_fid;
obj* l_lean_ir_varid;
obj* l_lean_ir_alt_is__pure___boxed(obj*);
uint8 l_lean_ir_ctor__info_beq(obj*, obj*);
obj* l_lean_ir_alt_is__pure(obj*);
uint8 l_lean_ir_arg_alpha__eqv___main(obj*, obj*, obj*);
obj* l_lean_ir_expr_is__pure___main___boxed(obj*);
obj* l_lean_ir_args_alpha__eqv(obj*, obj*, obj*);
obj* l_lean_ir_alts_is__pure___main___boxed(obj*);
uint8 l_lean_ir_arg_alpha__eqv(obj*, obj*, obj*);
obj* l_lean_ir_alt_is__pure___main(obj*);
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
obj* l_lean_ir_fnbody_is__pure___main(obj* x_0) {
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
obj* x_4; 
x_4 = lean::box(x_3);
return x_4;
}
else
{
x_0 = x_2;
goto _start;
}
}
case 1:
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_0, 2);
x_7 = lean::cnstr_get(x_0, 3);
x_8 = l_lean_ir_expr_is__pure___main(x_6);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::box(x_8);
return x_9;
}
else
{
x_0 = x_7;
goto _start;
}
}
case 3:
{
obj* x_11; 
x_11 = lean::cnstr_get(x_0, 3);
x_0 = x_11;
goto _start;
}
case 4:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_0, 4);
x_0 = x_13;
goto _start;
}
case 10:
{
obj* x_15; 
x_15 = lean::cnstr_get(x_0, 1);
x_0 = x_15;
goto _start;
}
case 11:
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_0, 1);
x_18 = l_lean_ir_alts_is__pure___main(x_17);
return x_18;
}
case 12:
{
uint8 x_19; obj* x_20; 
x_19 = 1;
x_20 = lean::box(x_19);
return x_20;
}
case 13:
{
uint8 x_21; obj* x_22; 
x_21 = 1;
x_22 = lean::box(x_21);
return x_22;
}
case 14:
{
uint8 x_23; obj* x_24; 
x_23 = 1;
x_24 = lean::box(x_23);
return x_24;
}
default:
{
uint8 x_25; obj* x_26; 
x_25 = 0;
x_26 = lean::box(x_25);
return x_26;
}
}
}
}
obj* l_lean_ir_alts_is__pure___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; obj* x_2; 
x_1 = 1;
x_2 = lean::box(x_1);
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = l_lean_ir_alt_is__pure___main(x_3);
x_6 = lean::unbox(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
x_0 = x_4;
goto _start;
}
}
}
}
obj* l_lean_ir_alt_is__pure___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_2; 
x_1 = lean::cnstr_get(x_0, 1);
x_2 = l_lean_ir_fnbody_is__pure___main(x_1);
return x_2;
}
else
{
uint8 x_3; obj* x_4; 
x_3 = 0;
x_4 = lean::box(x_3);
return x_4;
}
}
}
obj* l_lean_ir_fnbody_is__pure___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_fnbody_is__pure___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_alts_is__pure___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_alts_is__pure___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_alt_is__pure___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_alt_is__pure___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_fnbody_is__pure(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_fnbody_is__pure___main(x_0);
return x_1;
}
}
obj* l_lean_ir_fnbody_is__pure___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_fnbody_is__pure(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_alts_is__pure(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_alts_is__pure___main(x_0);
return x_1;
}
}
obj* l_lean_ir_alts_is__pure___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_alts_is__pure(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_alt_is__pure(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_alt_is__pure___main(x_0);
return x_1;
}
}
obj* l_lean_ir_alt_is__pure___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_alt_is__pure(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_lean_ir_args_alpha__eqv___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_4; obj* x_5; 
x_4 = 1;
x_5 = lean::box(x_4);
return x_5;
}
else
{
uint8 x_6; obj* x_7; 
x_6 = 0;
x_7 = lean::box(x_6);
return x_7;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_9; obj* x_10; 
lean::dec(x_0);
x_9 = 0;
x_10 = lean::box(x_9);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; uint8 x_16; 
x_11 = lean::cnstr_get(x_1, 0);
x_12 = lean::cnstr_get(x_1, 1);
x_13 = lean::cnstr_get(x_2, 0);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_16 = l_lean_ir_arg_alpha__eqv___main(x_0, x_11, x_13);
if (x_16 == 0)
{
obj* x_18; 
lean::dec(x_0);
x_18 = lean::box(x_16);
return x_18;
}
else
{
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
}
}
obj* l_lean_ir_args_alpha__eqv___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_args_alpha__eqv___main(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_ir_args_alpha__eqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_args_alpha__eqv___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_ir_args_alpha__eqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_args_alpha__eqv(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_ir_expr_alpha__eqv___main(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_9; 
lean::dec(x_0);
x_9 = lean::box(x_7);
return x_9;
}
else
{
obj* x_10; 
x_10 = l_lean_ir_args_alpha__eqv___main(x_0, x_4, x_6);
return x_10;
}
}
default:
{
uint8 x_12; obj* x_13; 
lean::dec(x_0);
x_12 = 0;
x_13 = lean::box(x_12);
return x_13;
}
}
}
case 1:
{
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_14; obj* x_15; uint8 x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_1, 0);
x_15 = lean::cnstr_get(x_2, 0);
x_16 = l_lean_ir_varid_alpha__eqv(x_0, x_14, x_15);
x_17 = lean::box(x_16);
return x_17;
}
default:
{
uint8 x_19; obj* x_20; 
lean::dec(x_0);
x_19 = 0;
x_20 = lean::box(x_19);
return x_20;
}
}
}
case 2:
{
switch (lean::obj_tag(x_2)) {
case 2:
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; uint8 x_28; 
x_21 = lean::cnstr_get(x_1, 0);
x_22 = lean::cnstr_get(x_1, 1);
x_23 = lean::cnstr_get(x_1, 2);
x_24 = lean::cnstr_get(x_2, 0);
x_25 = lean::cnstr_get(x_2, 1);
x_26 = lean::cnstr_get(x_2, 2);
lean::inc(x_0);
x_28 = l_lean_ir_varid_alpha__eqv(x_0, x_21, x_24);
if (x_28 == 0)
{
if (x_28 == 0)
{
obj* x_30; 
lean::dec(x_0);
x_30 = lean::box(x_28);
return x_30;
}
else
{
obj* x_31; 
x_31 = l_lean_ir_args_alpha__eqv___main(x_0, x_23, x_26);
return x_31;
}
}
else
{
uint8 x_32; 
x_32 = l_lean_ir_ctor__info_beq___main(x_22, x_25);
if (x_32 == 0)
{
obj* x_34; 
lean::dec(x_0);
x_34 = lean::box(x_32);
return x_34;
}
else
{
obj* x_35; 
x_35 = l_lean_ir_args_alpha__eqv___main(x_0, x_23, x_26);
return x_35;
}
}
}
default:
{
uint8 x_37; obj* x_38; 
lean::dec(x_0);
x_37 = 0;
x_38 = lean::box(x_37);
return x_38;
}
}
}
default:
{
uint8 x_40; obj* x_41; 
lean::dec(x_0);
x_40 = 0;
x_41 = lean::box(x_40);
return x_41;
}
}
}
}
obj* l_lean_ir_expr_alpha__eqv___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_expr_alpha__eqv___main(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_ir_expr_alpha__eqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_expr_alpha__eqv___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_ir_expr_alpha__eqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_expr_alpha__eqv(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
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
lean::mark_persistent(l_lean_ir_varid);
 l_lean_ir_fid = _init_l_lean_ir_fid();
lean::mark_persistent(l_lean_ir_fid);
 l_lean_ir_jpid = _init_l_lean_ir_jpid();
lean::mark_persistent(l_lean_ir_jpid);
}
