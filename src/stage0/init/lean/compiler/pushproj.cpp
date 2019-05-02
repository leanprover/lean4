// Lean compiler output
// Module: init.lean.compiler.pushproj
// Imports: init.default init.lean.compiler.ir
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
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_collectFreeVars(obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
extern obj* l_Lean_IR_vsetInh;
obj* l_Lean_IR_Decl_pushProj(obj*);
obj* l_RBNode_ins___main___at___private_init_lean_compiler_ir_2__collectIndex___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_pushProjs___main___closed__1;
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__4___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Decl_pushProj___main(obj*);
obj* l_Lean_IR_FnBody_freeVars(obj*);
obj* l_Lean_IR_reshape(obj*, obj*);
uint8 l_Array_anyAux___main___at_Lean_IR_pushProjs___main___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_pushProj(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_RBNode_findCore___main___at___private_init_lean_compiler_ir_2__collectIndex___spec__1(obj*, obj*);
obj* l_Lean_IR_FnBody_flatten(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
uint8 l_Array_isEmpty___rarg(obj*);
uint8 l_RBNode_isRed___main___rarg(obj*);
obj* l_Lean_IR_pushProjs(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_pushProj___main(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__3(obj*, obj*);
obj* l_Nat_decLt___boxed(obj*, obj*);
obj* l_Array_reverseAux___main___rarg(obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Lean_IR_pushProjs___main(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_pushProjs___main___spec__1(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__1(obj*, obj*);
obj* l_Lean_IR_FnBody_setBody___main(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__4(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2(obj*, obj*, obj*, obj*);
obj* l_Array_anyAux___main___at_Lean_IR_pushProjs___main___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_pushProjs___main___spec__1___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3___closed__1;
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_append___spec__1___rarg(obj*, obj*, obj*, obj*);
extern obj* l_Lean_IR_Inhabited;
obj* l_Array_back___at_Lean_IR_pushProjs___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_1 = lean::array_get_size(x_0);
x_2 = lean::mk_nat_obj(1ul);
x_3 = lean::nat_sub(x_1, x_2);
lean::dec(x_1);
x_5 = l_Lean_IR_Inhabited;
x_6 = lean::array_get(x_5, x_0, x_3);
lean::dec(x_3);
return x_6;
}
}
uint8 l_Array_anyAux___main___at_Lean_IR_pushProjs___main___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_8; 
lean::dec(x_3);
x_8 = 0;
return x_8;
}
else
{
obj* x_9; obj* x_10; 
x_9 = lean::array_fget(x_2, x_3);
x_10 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_2__collectIndex___spec__1(x_9, x_1);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_12; 
lean::dec(x_3);
x_12 = 1;
return x_12;
}
else
{
obj* x_14; obj* x_15; 
lean::dec(x_10);
x_14 = lean::mk_nat_obj(1ul);
x_15 = lean::nat_add(x_3, x_14);
lean::dec(x_3);
x_3 = x_15;
goto _start;
}
}
}
}
obj* _init_l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(12);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_5);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::array_fget(x_5, x_4);
x_12 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3___closed__1;
x_13 = lean::array_fset(x_5, x_4, x_12);
x_14 = lean::mk_nat_obj(1ul);
x_15 = lean::nat_add(x_4, x_14);
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_16 = lean::cnstr_get(x_11, 0);
x_18 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 lean::cnstr_set(x_11, 1, lean::box(0));
 x_20 = x_11;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_11);
 x_20 = lean::box(0);
}
x_21 = l_Lean_IR_vsetInh;
x_22 = lean::array_get(x_21, x_0, x_4);
x_23 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_2__collectIndex___spec__1(x_22, x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; 
if (lean::is_scalar(x_20)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_20;
}
lean::cnstr_set(x_24, 0, x_16);
lean::cnstr_set(x_24, 1, x_18);
x_25 = lean::array_fset(x_13, x_4, x_24);
lean::dec(x_4);
x_4 = x_15;
x_5 = x_25;
goto _start;
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_23);
lean::inc(x_1);
x_30 = l_Lean_IR_FnBody_setBody___main(x_1, x_18);
if (lean::is_scalar(x_20)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_20;
}
lean::cnstr_set(x_31, 0, x_16);
lean::cnstr_set(x_31, 1, x_30);
x_32 = lean::array_fset(x_13, x_4, x_31);
lean::dec(x_4);
x_4 = x_15;
x_5 = x_32;
goto _start;
}
}
else
{
obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_35 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 x_37 = x_11;
} else {
 lean::inc(x_35);
 lean::dec(x_11);
 x_37 = lean::box(0);
}
x_38 = l_Lean_IR_vsetInh;
x_39 = lean::array_get(x_38, x_0, x_4);
x_40 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_2__collectIndex___spec__1(x_39, x_3);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_42; 
if (lean::is_scalar(x_37)) {
 x_41 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_41 = x_37;
}
lean::cnstr_set(x_41, 0, x_35);
x_42 = lean::array_fset(x_13, x_4, x_41);
lean::dec(x_4);
x_4 = x_15;
x_5 = x_42;
goto _start;
}
else
{
obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_40);
lean::inc(x_1);
x_47 = l_Lean_IR_FnBody_setBody___main(x_1, x_35);
if (lean::is_scalar(x_37)) {
 x_48 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_48 = x_37;
}
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::array_fset(x_13, x_4, x_48);
lean::dec(x_4);
x_4 = x_15;
x_5 = x_49;
goto _start;
}
}
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_0);
return x_4;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
x_10 = lean::array_fget(x_4, x_3);
x_11 = lean::box(0);
x_12 = lean::array_fset(x_4, x_3, x_11);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
lean::inc(x_10);
x_16 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_2__collectIndex___spec__1(x_10, x_2);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; 
x_17 = lean::array_fset(x_12, x_3, x_10);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_17;
goto _start;
}
else
{
obj* x_22; obj* x_23; 
lean::dec(x_16);
lean::inc(x_0);
x_22 = l_Lean_IR_FnBody_collectFreeVars(x_0, x_10);
x_23 = lean::array_fset(x_12, x_3, x_22);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_23;
goto _start;
}
}
}
}
obj* _init_l_Lean_IR_pushProjs___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Nat_decLt___boxed), 2, 0);
return x_0;
}
}
obj* l_Lean_IR_pushProjs___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_Array_isEmpty___rarg(x_0);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = l_Array_back___at_Lean_IR_pushProjs___main___spec__1(x_0);
x_7 = lean::array_pop(x_0);
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
switch (lean::obj_tag(x_8)) {
case 3:
{
obj* x_11; obj* x_14; 
lean::dec(x_8);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::inc(x_4);
x_14 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_2__collectIndex___spec__1(x_4, x_11);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; uint8 x_17; 
x_15 = l_Lean_IR_pushProjs___main___closed__1;
x_16 = lean::mk_nat_obj(0ul);
x_17 = l_Array_anyAux___main___at_Lean_IR_pushProjs___main___spec__2(x_15, x_11, x_2, x_16);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_11);
lean::inc(x_6);
x_20 = lean::array_push(x_3, x_6);
x_21 = l_Lean_IR_FnBody_collectFreeVars(x_6, x_4);
x_0 = x_7;
x_3 = x_20;
x_4 = x_21;
goto _start;
}
else
{
obj* x_24; obj* x_25; 
lean::inc(x_6);
x_24 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3(x_2, x_6, x_15, x_11, x_16, x_1);
x_25 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__4(x_6, x_15, x_11, x_16, x_2);
lean::dec(x_11);
x_0 = x_7;
x_1 = x_24;
x_2 = x_25;
goto _start;
}
}
else
{
obj* x_31; obj* x_32; 
lean::dec(x_14);
lean::dec(x_11);
lean::inc(x_6);
x_31 = lean::array_push(x_3, x_6);
x_32 = l_Lean_IR_FnBody_collectFreeVars(x_6, x_4);
x_0 = x_7;
x_3 = x_31;
x_4 = x_32;
goto _start;
}
}
case 4:
{
obj* x_36; obj* x_37; 
lean::dec(x_8);
lean::inc(x_6);
x_36 = lean::array_push(x_3, x_6);
x_37 = l_Lean_IR_FnBody_collectFreeVars(x_6, x_4);
x_0 = x_7;
x_3 = x_36;
x_4 = x_37;
goto _start;
}
case 5:
{
obj* x_41; obj* x_42; 
lean::dec(x_8);
lean::inc(x_6);
x_41 = lean::array_push(x_3, x_6);
x_42 = l_Lean_IR_FnBody_collectFreeVars(x_6, x_4);
x_0 = x_7;
x_3 = x_41;
x_4 = x_42;
goto _start;
}
default:
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_52; 
lean::dec(x_4);
lean::dec(x_8);
lean::dec(x_2);
x_47 = lean::array_push(x_7, x_6);
x_48 = lean::mk_nat_obj(0ul);
x_49 = l_Array_reverseAux___main___rarg(x_3, x_48);
x_50 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_49, x_49, x_48, x_47);
lean::dec(x_49);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_50);
lean::cnstr_set(x_52, 1, x_1);
return x_52;
}
}
}
default:
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_4);
lean::dec(x_2);
x_55 = lean::array_push(x_7, x_6);
x_56 = lean::mk_nat_obj(0ul);
x_57 = l_Array_reverseAux___main___rarg(x_3, x_56);
x_58 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_57, x_57, x_56, x_55);
lean::dec(x_57);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_1);
return x_60;
}
}
}
else
{
obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_2);
x_64 = lean::mk_nat_obj(0ul);
x_65 = l_Array_reverseAux___main___rarg(x_3, x_64);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_1);
return x_66;
}
}
}
obj* l_Array_back___at_Lean_IR_pushProjs___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_back___at_Lean_IR_pushProjs___main___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_anyAux___main___at_Lean_IR_pushProjs___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = l_Array_anyAux___main___at_Lean_IR_pushProjs___main___spec__2(x_0, x_1, x_2, x_3);
x_5 = lean::box(x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_6;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__4(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_IR_pushProjs(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_pushProjs___main(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__1(obj* x_0, obj* x_1) {
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
x_7 = lean::box(12);
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_0, x_9);
switch (lean::obj_tag(x_6)) {
case 1:
{
obj* x_11; obj* x_13; uint8 x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_11 = lean::cnstr_get(x_6, 0);
x_13 = lean::cnstr_get(x_6, 1);
x_15 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*4);
x_16 = lean::cnstr_get(x_6, 2);
x_18 = lean::cnstr_get(x_6, 3);
if (lean::is_exclusive(x_6)) {
 x_20 = x_6;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_6);
 x_20 = lean::box(0);
}
x_21 = l_Lean_IR_FnBody_pushProj___main(x_16);
if (lean::is_scalar(x_20)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_20;
}
lean::cnstr_set(x_22, 0, x_11);
lean::cnstr_set(x_22, 1, x_13);
lean::cnstr_set(x_22, 2, x_21);
lean::cnstr_set(x_22, 3, x_18);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_15);
x_23 = x_22;
x_24 = lean::array_fset(x_8, x_0, x_23);
lean::dec(x_0);
x_0 = x_10;
x_1 = x_24;
goto _start;
}
default:
{
obj* x_27; 
x_27 = lean::array_fset(x_8, x_0, x_6);
lean::dec(x_0);
x_0 = x_10;
x_1 = x_27;
goto _start;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l_Lean_IR_AltCore_body___main(x_8);
lean::dec(x_8);
x_11 = l_Lean_IR_FnBody_freeVars(x_9);
x_12 = lean::array_push(x_3, x_11);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_2, x_13);
lean::dec(x_2);
x_2 = x_14;
x_3 = x_12;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__3(obj* x_0, obj* x_1) {
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
x_7 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3___closed__1;
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
x_16 = l_Lean_IR_FnBody_pushProj___main(x_13);
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
x_24 = l_Lean_IR_FnBody_pushProj___main(x_21);
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
obj* l_Lean_IR_FnBody_pushProj___main(obj* x_0) {
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
x_8 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__1(x_7, x_2);
switch (lean::obj_tag(x_4)) {
case 9:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; uint8 x_21; 
x_9 = lean::cnstr_get(x_4, 0);
x_11 = lean::cnstr_get(x_4, 1);
x_13 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 lean::cnstr_set(x_4, 2, lean::box(0));
 x_15 = x_4;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_4);
 x_15 = lean::box(0);
}
x_16 = lean::array_get_size(x_13);
x_17 = lean::mk_empty_array(x_16);
lean::dec(x_16);
x_19 = l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2(x_13, x_13, x_7, x_17);
x_20 = lean::box(0);
x_21 = l_RBNode_isRed___main___rarg(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_32; obj* x_33; obj* x_34; 
x_22 = lean::box(0);
lean::inc(x_11);
x_24 = l_RBNode_ins___main___at___private_init_lean_compiler_ir_2__collectIndex___spec__2(x_20, x_11, x_22);
x_25 = l_Array_empty___closed__1;
x_26 = l_Lean_IR_pushProjs___main(x_8, x_13, x_19, x_25, x_24);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
x_32 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__3(x_7, x_29);
if (lean::is_scalar(x_15)) {
 x_33 = lean::alloc_cnstr(9, 3, 0);
} else {
 x_33 = x_15;
}
lean::cnstr_set(x_33, 0, x_9);
lean::cnstr_set(x_33, 1, x_11);
lean::cnstr_set(x_33, 2, x_32);
x_34 = l_Lean_IR_reshape(x_27, x_33);
return x_34;
}
else
{
obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_46; obj* x_47; obj* x_48; 
x_35 = lean::box(0);
lean::inc(x_11);
x_37 = l_RBNode_ins___main___at___private_init_lean_compiler_ir_2__collectIndex___spec__2(x_20, x_11, x_35);
x_38 = l_RBNode_setBlack___main___rarg(x_37);
x_39 = l_Array_empty___closed__1;
x_40 = l_Lean_IR_pushProjs___main(x_8, x_13, x_19, x_39, x_38);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
x_46 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__3(x_7, x_43);
if (lean::is_scalar(x_15)) {
 x_47 = lean::alloc_cnstr(9, 3, 0);
} else {
 x_47 = x_15;
}
lean::cnstr_set(x_47, 0, x_9);
lean::cnstr_set(x_47, 1, x_11);
lean::cnstr_set(x_47, 2, x_46);
x_48 = l_Lean_IR_reshape(x_41, x_47);
return x_48;
}
}
default:
{
obj* x_49; 
x_49 = l_Lean_IR_reshape(x_8, x_4);
return x_49;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_FnBody_pushProj(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_FnBody_pushProj___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_Decl_pushProj___main(obj* x_0) {
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
x_9 = l_Lean_IR_FnBody_pushProj___main(x_6);
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
obj* l_Lean_IR_Decl_pushProj(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Decl_pushProj___main(x_0);
return x_1;
}
}
obj* initialize_init_default(obj*);
obj* initialize_init_lean_compiler_ir(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_pushproj(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir(w);
if (io_result_is_error(w)) return w;
 l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3___closed__1 = _init_l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3___closed__1);
 l_Lean_IR_pushProjs___main___closed__1 = _init_l_Lean_IR_pushProjs___main___closed__1();
lean::mark_persistent(l_Lean_IR_pushProjs___main___closed__1);
return w;
}
