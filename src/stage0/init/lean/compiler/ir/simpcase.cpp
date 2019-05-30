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
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_simpCase(obj*);
obj* l_Lean_IR_ensureHasDefault(obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_ensureHasDefault___spec__1(obj*, obj*);
obj* l_Lean_IR_FnBody_simpCase___main(obj*);
obj* l_Array_fswap(obj*, obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_ensureHasDefault___spec__2___boxed(obj*);
obj* l___private_init_lean_compiler_ir_simpcase_1__maxOccs(obj*);
obj* l___private_init_lean_compiler_ir_simpcase_2__addDefault(obj*);
obj* l_Lean_IR_reshape(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__2(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Array_ummapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__1(obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_flatten(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_2__addDefault___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_push(obj*, obj*, obj*);
obj* l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_2__addDefault___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_Lean_IR_altInh;
uint8 l_Lean_IR_Alt_isDefault___main(obj*);
obj* l_Lean_IR_Decl_simpCase(obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_ensureHasDefault___spec__1___boxed(obj*, obj*);
obj* l_Array_ummapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2(obj*, obj*);
obj* l_Array_shrink___main___rarg(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Array_pop(obj*, obj*);
uint8 l_Lean_IR_FnBody_beq(obj*, obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_simpcase_3__mkSimpCase(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_simpcase_1__maxOccs___boxed(obj*);
obj* l_Lean_IR_Decl_simpCase___main(obj*);
obj* l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_3__mkSimpCase___spec__1(obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_ensureHasDefault___spec__2(obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_ensureHasDefault___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_5; 
lean::dec(x_2);
x_5 = 0;
return x_5;
}
else
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_fget(x_1, x_2);
x_7 = l_Lean_IR_Alt_isDefault___main(x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_2, x_8);
lean::dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean::dec(x_2);
return x_7;
}
}
}
}
obj* l_Array_back___at_Lean_IR_ensureHasDefault___spec__2(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_sub(x_2, x_3);
lean::dec(x_2);
x_5 = l_Lean_IR_altInh;
x_6 = lean::array_get(x_5, x_1, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_IR_ensureHasDefault(obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l_Array_anyMAux___main___at_Lean_IR_ensureHasDefault___spec__1(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; uint8 x_6; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::mk_nat_obj(2u);
x_6 = lean::nat_dec_lt(x_4, x_5);
lean::dec(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = l_Array_back___at_Lean_IR_ensureHasDefault___spec__2(x_1);
x_8 = lean::array_pop(x_1);
x_9 = l_Lean_IR_AltCore_body___main(x_7);
lean::dec(x_7);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
x_11 = lean::array_push(x_8, x_10);
return x_11;
}
else
{
return x_1;
}
}
else
{
return x_1;
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_ensureHasDefault___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyMAux___main___at_Lean_IR_ensureHasDefault___spec__1(x_1, x_2);
lean::dec(x_1);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Array_back___at_Lean_IR_ensureHasDefault___spec__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_back___at_Lean_IR_ensureHasDefault___spec__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_2);
return x_5;
}
else
{
obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = l_Lean_IR_AltCore_body___main(x_8);
lean::dec(x_8);
lean::inc(x_2);
x_10 = l_Lean_IR_FnBody_beq(x_9, x_2);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_4, x_11);
lean::dec(x_4);
if (x_10 == 0)
{
x_4 = x_12;
goto _start;
}
else
{
obj* x_14; 
x_14 = lean::nat_add(x_5, x_11);
lean::dec(x_5);
x_4 = x_12;
x_5 = x_14;
goto _start;
}
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = l_Lean_IR_AltCore_body___main(x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_3, x_9);
lean::dec(x_3);
lean::inc(x_10);
x_11 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__1(x_1, x_8, x_1, x_10, x_9);
x_12 = lean::cnstr_get(x_4, 1);
lean::inc(x_12);
x_13 = lean::nat_dec_lt(x_12, x_11);
lean::dec(x_12);
if (x_13 == 0)
{
lean::dec(x_11);
lean::dec(x_7);
x_3 = x_10;
goto _start;
}
else
{
obj* x_15; 
lean::dec(x_4);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_7);
lean::cnstr_set(x_15, 1, x_11);
x_3 = x_10;
x_4 = x_15;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_simpcase_1__maxOccs(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = l_Lean_IR_altInh;
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::array_get(x_2, x_1, x_3);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__2(x_1, x_1, x_5, x_6);
return x_7;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_simpcase_1__maxOccs___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_simpcase_1__maxOccs___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_simpcase_1__maxOccs(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_2__addDefault___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_7; 
lean::dec(x_3);
x_7 = l_Array_shrink___main___rarg(x_2, x_4);
lean::dec(x_4);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_8 = lean::array_fget(x_2, x_3);
x_9 = l_Lean_IR_AltCore_body___main(x_8);
lean::dec(x_8);
x_10 = l_Lean_IR_AltCore_body___main(x_1);
x_11 = l_Lean_IR_FnBody_beq(x_9, x_10);
if (x_11 == 0)
{
uint8 x_12; 
x_12 = lean::nat_dec_lt(x_4, x_3);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_15 = lean::nat_add(x_4, x_13);
lean::dec(x_4);
x_3 = x_14;
x_4 = x_15;
goto _start;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::array_fswap(x_2, x_3, x_4);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_3, x_18);
lean::dec(x_3);
x_20 = lean::nat_add(x_4, x_18);
lean::dec(x_4);
x_2 = x_17;
x_3 = x_19;
x_4 = x_20;
goto _start;
}
}
else
{
obj* x_22; obj* x_23; 
x_22 = lean::mk_nat_obj(1u);
x_23 = lean::nat_add(x_3, x_22);
lean::dec(x_3);
x_3 = x_23;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_simpcase_2__addDefault(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_dec_le(x_2, x_3);
lean::dec(x_2);
if (x_4 == 0)
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_anyMAux___main___at_Lean_IR_ensureHasDefault___spec__1(x_1, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_7 = l___private_init_lean_compiler_ir_simpcase_1__maxOccs(x_1);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::nat_dec_eq(x_9, x_3);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_2__addDefault___spec__1(x_8, x_1, x_5, x_5);
x_12 = l_Lean_IR_AltCore_body___main(x_8);
lean::dec(x_8);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::array_push(x_11, x_13);
return x_14;
}
else
{
lean::dec(x_8);
return x_1;
}
}
else
{
return x_1;
}
}
else
{
return x_1;
}
}
}
obj* l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_2__addDefault___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_2__addDefault___spec__1(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_3__mkSimpCase___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = l_Array_shrink___main___rarg(x_1, x_3);
lean::dec(x_3);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_7 = lean::array_fget(x_1, x_2);
x_8 = l_Lean_IR_AltCore_body___main(x_7);
lean::dec(x_7);
x_9 = lean::box(13);
x_10 = l_Lean_IR_FnBody_beq(x_8, x_9);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = lean::nat_dec_lt(x_3, x_2);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_2, x_12);
lean::dec(x_2);
x_14 = lean::nat_add(x_3, x_12);
lean::dec(x_3);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::array_fswap(x_1, x_2, x_3);
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_add(x_2, x_17);
lean::dec(x_2);
x_19 = lean::nat_add(x_3, x_17);
lean::dec(x_3);
x_1 = x_16;
x_2 = x_18;
x_3 = x_19;
goto _start;
}
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_add(x_2, x_21);
lean::dec(x_2);
x_2 = x_22;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_simpcase_3__mkSimpCase(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_filterAux___main___at___private_init_lean_compiler_ir_simpcase_3__mkSimpCase___spec__1(x_3, x_4, x_4);
x_6 = l___private_init_lean_compiler_ir_simpcase_2__addDefault(x_5);
x_7 = lean::array_get_size(x_6);
x_8 = lean::nat_dec_eq(x_7, x_4);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_dec_eq(x_7, x_9);
lean::dec(x_7);
if (x_10 == 0)
{
obj* x_11; 
x_11 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_2);
lean::cnstr_set(x_11, 2, x_6);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_2);
lean::dec(x_1);
x_12 = l_Lean_IR_altInh;
x_13 = lean::array_get(x_12, x_6, x_4);
lean::dec(x_6);
x_14 = l_Lean_IR_AltCore_body___main(x_13);
lean::dec(x_13);
return x_14;
}
}
else
{
obj* x_15; 
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_1);
x_15 = lean::box(13);
return x_15;
}
}
}
obj* l_Array_ummapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_7 = lean::array_fget(x_2, x_1);
x_8 = lean::box(0);
lean::inc(x_7);
x_9 = x_8;
x_10 = lean::array_fset(x_2, x_1, x_9);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_1, x_11);
if (lean::obj_tag(x_7) == 1)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_7, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_7, 1);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_7, 2);
lean::inc(x_20);
x_21 = lean::cnstr_get(x_7, 3);
lean::inc(x_21);
x_22 = l_Lean_IR_FnBody_simpCase___main(x_20);
x_23 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_23, 0, x_18);
lean::cnstr_set(x_23, 1, x_19);
lean::cnstr_set(x_23, 2, x_22);
lean::cnstr_set(x_23, 3, x_21);
x_13 = x_23;
goto block_17;
}
else
{
lean::inc(x_7);
x_13 = x_7;
goto block_17;
}
block_17:
{
obj* x_14; obj* x_15; 
x_14 = x_13;
x_15 = lean::array_fset(x_10, x_1, x_14);
lean::dec(x_1);
x_1 = x_12;
x_2 = x_15;
goto _start;
}
}
}
}
obj* l_Array_ummapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::array_fget(x_2, x_1);
x_8 = lean::box(0);
lean::inc(x_7);
x_9 = x_8;
x_10 = lean::array_fset(x_2, x_1, x_9);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_1, x_11);
if (lean::obj_tag(x_7) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_7, 0);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
x_15 = l_Lean_IR_FnBody_simpCase___main(x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_15);
x_17 = x_16;
x_18 = lean::array_fset(x_10, x_1, x_17);
lean::dec(x_1);
x_1 = x_12;
x_2 = x_18;
goto _start;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_7, 0);
lean::inc(x_20);
x_21 = l_Lean_IR_FnBody_simpCase___main(x_20);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = x_22;
x_24 = lean::array_fset(x_10, x_1, x_23);
lean::dec(x_1);
x_1 = x_12;
x_2 = x_24;
goto _start;
}
}
}
}
obj* l_Lean_IR_FnBody_simpCase___main(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_Lean_IR_FnBody_flatten(x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_ummapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__1(x_5, x_3);
if (lean::obj_tag(x_4) == 10)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
lean::dec(x_4);
x_10 = l_Array_ummapAux___main___at_Lean_IR_FnBody_simpCase___main___spec__2(x_5, x_9);
x_11 = l___private_init_lean_compiler_ir_simpcase_3__mkSimpCase(x_7, x_8, x_10);
x_12 = l_Lean_IR_reshape(x_6, x_11);
return x_12;
}
else
{
obj* x_13; 
x_13 = l_Lean_IR_reshape(x_6, x_4);
return x_13;
}
}
}
obj* l_Lean_IR_FnBody_simpCase(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_FnBody_simpCase___main(x_1);
return x_2;
}
}
obj* l_Lean_IR_Decl_simpCase___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = !lean::is_exclusive(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 2);
x_4 = l_Lean_IR_FnBody_simpCase___main(x_3);
lean::cnstr_set(x_1, 2, x_4);
return x_1;
}
else
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
lean::inc(x_6);
lean::inc(x_5);
lean::dec(x_1);
x_9 = l_Lean_IR_FnBody_simpCase___main(x_8);
x_10 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_6);
lean::cnstr_set(x_10, 2, x_9);
lean::cnstr_set_scalar(x_10, sizeof(void*)*3, x_7);
return x_10;
}
}
else
{
return x_1;
}
}
}
obj* l_Lean_IR_Decl_simpCase(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Decl_simpCase___main(x_1);
return x_2;
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
return w;
}
