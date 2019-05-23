// Lean compiler output
// Module: init.lean.compiler.ir.simpcase
// Imports: init.lean.compiler.ir.basic
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
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_simpCase(obj*);
obj* l_Lean_IR_ensureHasDefault(obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_ensureHasDefault___spec__1(obj*, obj*);
obj* l_Lean_IR_FnBody_simpCase___main(obj*);
obj* l_Array_back___at_Lean_IR_ensureHasDefault___spec__2___boxed(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2___closed__1;
obj* l___private_init_lean_compiler_ir_simpcase_1__maxOccs(obj*);
obj* l___private_init_lean_compiler_ir_simpcase_2__addDefault(obj*);
obj* l_Lean_IR_reshape(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__2(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_FnBody_flatten(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_2__addDefault___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_2__addDefault___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_Lean_IR_altInh;
uint8 l_Lean_IR_Alt_isDefault___main(obj*);
obj* l_Lean_IR_Decl_simpCase(obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_ensureHasDefault___spec__1___boxed(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2(obj*, obj*);
obj* l_Array_shrink___main___rarg(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
uint8 l_Lean_IR_FnBody_beq(obj*, obj*);
obj* l___private_init_lean_compiler_ir_simpcase_3__mkSimpCase(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_simpcase_1__maxOccs___boxed(obj*);
obj* l_Lean_IR_Decl_simpCase___main(obj*);
obj* l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_3__mkSimpCase___spec__1(obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_ensureHasDefault___spec__2(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__1(obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_ensureHasDefault___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_0);
x_3 = lean::nat_dec_lt(x_1, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
uint8 x_6; 
lean::dec(x_1);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_fget(x_0, x_1);
x_8 = l_Lean_IR_Alt_isDefault___main(x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_1, x_10);
lean::dec(x_1);
x_1 = x_11;
goto _start;
}
else
{
lean::dec(x_1);
return x_8;
}
}
}
}
obj* l_Array_back___at_Lean_IR_ensureHasDefault___spec__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_1 = lean::array_get_size(x_0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean::nat_sub(x_1, x_2);
lean::dec(x_1);
x_5 = l_Lean_IR_altInh;
x_6 = lean::array_get(x_5, x_0, x_3);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_IR_ensureHasDefault(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Array_anyMAux___main___at_Lean_IR_ensureHasDefault___spec__1(x_0, x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::array_get_size(x_0);
x_4 = lean::mk_nat_obj(2ul);
x_5 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_3);
if (x_5 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
x_7 = l_Array_back___at_Lean_IR_ensureHasDefault___spec__2(x_0);
x_8 = lean::array_pop(x_0);
x_9 = l_Lean_IR_AltCore_body___main(x_7);
lean::dec(x_7);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_9);
x_12 = lean::array_push(x_8, x_11);
return x_12;
}
else
{
return x_0;
}
}
else
{
return x_0;
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_ensureHasDefault___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Array_anyMAux___main___at_Lean_IR_ensureHasDefault___spec__1(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Array_back___at_Lean_IR_ensureHasDefault___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_back___at_Lean_IR_ensureHasDefault___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
else
{
obj* x_10; obj* x_11; uint8 x_14; obj* x_15; obj* x_16; 
x_10 = lean::array_fget(x_2, x_3);
x_11 = l_Lean_IR_AltCore_body___main(x_10);
lean::dec(x_10);
lean::inc(x_1);
x_14 = l_Lean_IR_FnBody_beq(x_11, x_1);
x_15 = lean::mk_nat_obj(1ul);
x_16 = lean::nat_add(x_3, x_15);
lean::dec(x_3);
if (x_14 == 0)
{
x_3 = x_16;
goto _start;
}
else
{
obj* x_19; 
x_19 = lean::nat_add(x_4, x_15);
lean::dec(x_4);
x_3 = x_16;
x_4 = x_19;
goto _start;
}
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_15; uint8 x_17; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l_Lean_IR_AltCore_body___main(x_8);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_2, x_10);
lean::dec(x_2);
lean::inc(x_11);
x_14 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__1(x_0, x_9, x_0, x_11, x_10);
x_15 = lean::cnstr_get(x_3, 1);
lean::inc(x_15);
x_17 = lean::nat_dec_lt(x_15, x_14);
lean::dec(x_15);
if (x_17 == 0)
{
lean::dec(x_14);
lean::dec(x_8);
x_2 = x_11;
goto _start;
}
else
{
obj* x_23; 
lean::dec(x_3);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_8);
lean::cnstr_set(x_23, 1, x_14);
x_2 = x_11;
x_3 = x_23;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_simpcase_1__maxOccs(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = l_Lean_IR_altInh;
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::array_get(x_1, x_0, x_2);
x_4 = lean::mk_nat_obj(1ul);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__2(x_0, x_0, x_4, x_5);
return x_6;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_simpcase_1__maxOccs___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_simpcase_1__maxOccs(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_2__addDefault___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; 
lean::dec(x_2);
x_8 = l_Array_shrink___main___rarg(x_1, x_3);
lean::dec(x_3);
return x_8;
}
else
{
obj* x_10; obj* x_11; obj* x_13; uint8 x_14; 
x_10 = lean::array_fget(x_1, x_2);
x_11 = l_Lean_IR_AltCore_body___main(x_10);
lean::dec(x_10);
x_13 = l_Lean_IR_AltCore_body___main(x_0);
x_14 = l_Lean_IR_FnBody_beq(x_11, x_13);
if (x_14 == 0)
{
uint8 x_15; 
x_15 = lean::nat_dec_lt(x_3, x_2);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_19; 
x_16 = lean::mk_nat_obj(1ul);
x_17 = lean::nat_add(x_2, x_16);
lean::dec(x_2);
x_19 = lean::nat_add(x_3, x_16);
lean::dec(x_3);
x_2 = x_17;
x_3 = x_19;
goto _start;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_26; 
x_22 = lean::array_fswap(x_1, x_2, x_3);
x_23 = lean::mk_nat_obj(1ul);
x_24 = lean::nat_add(x_2, x_23);
lean::dec(x_2);
x_26 = lean::nat_add(x_3, x_23);
lean::dec(x_3);
x_1 = x_22;
x_2 = x_24;
x_3 = x_26;
goto _start;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = lean::mk_nat_obj(1ul);
x_30 = lean::nat_add(x_2, x_29);
lean::dec(x_2);
x_2 = x_30;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_simpcase_2__addDefault(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::array_get_size(x_0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean::nat_dec_le(x_1, x_2);
lean::dec(x_1);
if (x_3 == 0)
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0ul);
x_6 = l_Array_anyMAux___main___at_Lean_IR_ensureHasDefault___spec__1(x_0, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; uint8 x_13; 
x_7 = l___private_init_lean_compiler_ir_simpcase_1__maxOccs(x_0);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::nat_dec_eq(x_10, x_2);
lean::dec(x_10);
if (x_13 == 0)
{
obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_15 = l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_2__addDefault___spec__1(x_8, x_0, x_5, x_5);
x_16 = l_Lean_IR_AltCore_body___main(x_8);
lean::dec(x_8);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_16);
x_19 = lean::array_push(x_15, x_18);
return x_19;
}
else
{
lean::dec(x_8);
return x_0;
}
}
else
{
return x_0;
}
}
else
{
return x_0;
}
}
}
obj* l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_2__addDefault___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_2__addDefault___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_3__mkSimpCase___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_0);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_7; 
lean::dec(x_1);
x_7 = l_Array_shrink___main___rarg(x_0, x_2);
lean::dec(x_2);
return x_7;
}
else
{
obj* x_9; obj* x_10; obj* x_12; uint8 x_13; 
x_9 = lean::array_fget(x_0, x_1);
x_10 = l_Lean_IR_AltCore_body___main(x_9);
lean::dec(x_9);
x_12 = lean::box(13);
x_13 = l_Lean_IR_FnBody_beq(x_10, x_12);
if (x_13 == 0)
{
uint8 x_14; 
x_14 = lean::nat_dec_lt(x_2, x_1);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_18; 
x_15 = lean::mk_nat_obj(1ul);
x_16 = lean::nat_add(x_1, x_15);
lean::dec(x_1);
x_18 = lean::nat_add(x_2, x_15);
lean::dec(x_2);
x_1 = x_16;
x_2 = x_18;
goto _start;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_25; 
x_21 = lean::array_fswap(x_0, x_1, x_2);
x_22 = lean::mk_nat_obj(1ul);
x_23 = lean::nat_add(x_1, x_22);
lean::dec(x_1);
x_25 = lean::nat_add(x_2, x_22);
lean::dec(x_2);
x_0 = x_21;
x_1 = x_23;
x_2 = x_25;
goto _start;
}
}
else
{
obj* x_28; obj* x_29; 
x_28 = lean::mk_nat_obj(1ul);
x_29 = lean::nat_add(x_1, x_28);
lean::dec(x_1);
x_1 = x_29;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_simpcase_3__mkSimpCase(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_3__mkSimpCase___spec__1(x_2, x_3, x_3);
x_5 = l___private_init_lean_compiler_ir_simpcase_2__addDefault(x_4);
x_6 = lean::array_get_size(x_5);
x_7 = lean::nat_dec_eq(x_6, x_3);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(1ul);
x_9 = lean::nat_dec_eq(x_6, x_8);
lean::dec(x_6);
if (x_9 == 0)
{
obj* x_11; 
x_11 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_1);
lean::cnstr_set(x_11, 2, x_5);
return x_11;
}
else
{
obj* x_14; obj* x_15; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_14 = l_Lean_IR_altInh;
x_15 = lean::array_get(x_14, x_5, x_3);
lean::dec(x_5);
x_17 = l_Lean_IR_AltCore_body___main(x_15);
lean::dec(x_15);
return x_17;
}
}
else
{
obj* x_23; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_6);
lean::dec(x_0);
x_23 = lean::box(13);
return x_23;
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::nat_dec_lt(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = lean::box(13);
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_0, x_9);
switch (lean::obj_tag(x_6)) {
case 1:
{
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_11 = lean::cnstr_get(x_6, 0);
x_13 = lean::cnstr_get(x_6, 1);
x_15 = lean::cnstr_get(x_6, 2);
x_17 = lean::cnstr_get(x_6, 3);
if (lean::is_exclusive(x_6)) {
 x_19 = x_6;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_6);
 x_19 = lean::box(0);
}
x_20 = l_Lean_IR_FnBody_simpCase___main(x_15);
if (lean::is_scalar(x_19)) {
 x_21 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_21 = x_19;
}
lean::cnstr_set(x_21, 0, x_11);
lean::cnstr_set(x_21, 1, x_13);
lean::cnstr_set(x_21, 2, x_20);
lean::cnstr_set(x_21, 3, x_17);
x_22 = lean::array_fset(x_8, x_0, x_21);
lean::dec(x_0);
x_0 = x_10;
x_1 = x_22;
goto _start;
}
default:
{
obj* x_25; 
x_25 = lean::array_fset(x_8, x_0, x_6);
lean::dec(x_0);
x_0 = x_10;
x_1 = x_25;
goto _start;
}
}
}
}
}
obj* _init_l_Array_hmmapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(13);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::nat_dec_lt(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_0, x_9);
if (lean::obj_tag(x_6) == 0)
{
obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_11 = lean::cnstr_get(x_6, 0);
x_13 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 x_15 = x_6;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_6);
 x_15 = lean::box(0);
}
x_16 = l_Lean_IR_FnBody_simpCase___main(x_13);
if (lean::is_scalar(x_15)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_15;
}
lean::cnstr_set(x_17, 0, x_11);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::array_fset(x_8, x_0, x_17);
lean::dec(x_0);
x_0 = x_10;
x_1 = x_18;
goto _start;
}
else
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_21 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_23 = x_6;
} else {
 lean::inc(x_21);
 lean::dec(x_6);
 x_23 = lean::box(0);
}
x_24 = l_Lean_IR_FnBody_simpCase___main(x_21);
if (lean::is_scalar(x_23)) {
 x_25 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_25 = x_23;
}
lean::cnstr_set(x_25, 0, x_24);
x_26 = lean::array_fset(x_8, x_0, x_25);
lean::dec(x_0);
x_0 = x_10;
x_1 = x_26;
goto _start;
}
}
}
}
obj* l_Lean_IR_FnBody_simpCase___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_1 = l_Lean_IR_FnBody_flatten(x_0);
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::mk_nat_obj(0ul);
x_8 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__1(x_7, x_2);
switch (lean::obj_tag(x_4)) {
case 10:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_4, 2);
lean::inc(x_13);
lean::dec(x_4);
x_16 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2(x_7, x_13);
x_17 = l___private_init_lean_compiler_ir_simpcase_3__mkSimpCase(x_9, x_11, x_16);
x_18 = l_Lean_IR_reshape(x_8, x_17);
return x_18;
}
default:
{
obj* x_19; 
x_19 = l_Lean_IR_reshape(x_8, x_4);
return x_19;
}
}
}
}
obj* l_Lean_IR_FnBody_simpCase(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_FnBody_simpCase___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_Decl_simpCase___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_3; uint8 x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_8 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = l_Lean_IR_FnBody_simpCase___main(x_6);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_3);
lean::cnstr_set(x_10, 2, x_9);
lean::cnstr_set_scalar(x_10, sizeof(void*)*3, x_5);
x_11 = x_10;
return x_11;
}
else
{
return x_0;
}
}
}
obj* l_Lean_IR_Decl_simpCase(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Decl_simpCase___main(x_0);
return x_1;
}
}
obj* initialize_init_lean_compiler_ir_basic(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_simpcase(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
 l_Array_hmmapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2___closed__1 = _init_l_Array_hmmapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2___closed__1);
return w;
}
