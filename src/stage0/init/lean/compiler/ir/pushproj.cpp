// Lean compiler output
// Module: init.lean.compiler.ir.pushproj
// Imports: init.lean.compiler.ir.basic init.lean.compiler.ir.freevars
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
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
extern obj* l_Lean_IR_vsetInh;
obj* l_Lean_IR_Decl_pushProj(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_freeIndices(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2___closed__1;
obj* l_Lean_IR_Decl_pushProj___main(obj*);
obj* l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(obj*, obj*);
obj* l_RBNode_insert___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_reshape(obj*, obj*);
obj* l_Lean_IR_FnBody_pushProj(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_FnBody_flatten(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
uint8 l_Array_isEmpty___rarg(obj*);
obj* l_Lean_IR_pushProjs(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_pushProj___main(obj*);
obj* l_Lean_IR_FnBody_collectFreeIndices(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__3(obj*, obj*);
obj* l_Array_reverseAux___main___rarg(obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Lean_IR_pushProjs___main(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_pushProjs___main___spec__1(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__1(obj*, obj*);
obj* l_Lean_IR_FnBody_setBody___main(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2(obj*, obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_pushProjs___main___spec__1___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3___boxed(obj*, obj*, obj*, obj*);
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
obj* _init_l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(13);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
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
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::array_fget(x_4, x_3);
x_11 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2___closed__1;
x_12 = lean::array_fset(x_4, x_3, x_11);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_10, 0);
x_17 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 lean::cnstr_set(x_10, 1, lean::box(0));
 x_19 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_10);
 x_19 = lean::box(0);
}
x_20 = l_Lean_IR_vsetInh;
x_21 = lean::array_get(x_20, x_0, x_3);
x_22 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_21, x_2);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; 
if (lean::is_scalar(x_19)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_19;
}
lean::cnstr_set(x_23, 0, x_15);
lean::cnstr_set(x_23, 1, x_17);
x_24 = lean::array_fset(x_12, x_3, x_23);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_24;
goto _start;
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_22);
lean::inc(x_1);
x_29 = l_Lean_IR_FnBody_setBody___main(x_1, x_17);
if (lean::is_scalar(x_19)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_19;
}
lean::cnstr_set(x_30, 0, x_15);
lean::cnstr_set(x_30, 1, x_29);
x_31 = lean::array_fset(x_12, x_3, x_30);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_31;
goto _start;
}
}
else
{
obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_34 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 x_36 = x_10;
} else {
 lean::inc(x_34);
 lean::dec(x_10);
 x_36 = lean::box(0);
}
x_37 = l_Lean_IR_vsetInh;
x_38 = lean::array_get(x_37, x_0, x_3);
x_39 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_38, x_2);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_41; 
if (lean::is_scalar(x_36)) {
 x_40 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_40 = x_36;
}
lean::cnstr_set(x_40, 0, x_34);
x_41 = lean::array_fset(x_12, x_3, x_40);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_41;
goto _start;
}
else
{
obj* x_46; obj* x_47; obj* x_48; 
lean::dec(x_39);
lean::inc(x_1);
x_46 = l_Lean_IR_FnBody_setBody___main(x_1, x_34);
if (lean::is_scalar(x_36)) {
 x_47 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_47 = x_36;
}
lean::cnstr_set(x_47, 0, x_46);
x_48 = lean::array_fset(x_12, x_3, x_47);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_48;
goto _start;
}
}
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; 
x_9 = lean::array_fget(x_3, x_2);
x_10 = lean::box(0);
x_11 = lean::array_fset(x_3, x_2, x_10);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
lean::inc(x_9);
x_15 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_9, x_1);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; 
x_16 = lean::array_fset(x_11, x_2, x_9);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_16;
goto _start;
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_15);
lean::inc(x_0);
x_21 = l_Lean_IR_FnBody_collectFreeIndices(x_0, x_9);
x_22 = lean::array_fset(x_11, x_2, x_21);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_22;
goto _start;
}
}
}
}
obj* l_Lean_IR_pushProjs___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_Array_isEmpty___rarg(x_0);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; uint8 x_13; obj* x_14; 
x_6 = l_Array_back___at_Lean_IR_pushProjs___main___spec__1(x_0);
x_7 = lean::array_pop(x_0);
switch (lean::obj_tag(x_6)) {
case 0:
{
uint8 x_16; obj* x_17; 
x_16 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*3);
x_17 = lean::cnstr_get(x_6, 1);
lean::inc(x_17);
switch (lean::obj_tag(x_17)) {
case 3:
{
obj* x_19; 
x_19 = lean::cnstr_get(x_6, 0);
lean::inc(x_19);
x_12 = x_19;
x_13 = x_16;
x_14 = x_17;
goto lbl_15;
}
case 4:
{
obj* x_21; 
x_21 = lean::cnstr_get(x_6, 0);
lean::inc(x_21);
x_12 = x_21;
x_13 = x_16;
x_14 = x_17;
goto lbl_15;
}
case 5:
{
obj* x_23; 
x_23 = lean::cnstr_get(x_6, 0);
lean::inc(x_23);
x_12 = x_23;
x_13 = x_16;
x_14 = x_17;
goto lbl_15;
}
case 12:
{
obj* x_26; 
lean::dec(x_17);
x_26 = lean::box(0);
x_10 = x_26;
goto lbl_11;
}
case 13:
{
obj* x_28; 
lean::dec(x_17);
x_28 = lean::box(0);
x_10 = x_28;
goto lbl_11;
}
default:
{
obj* x_32; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_17);
x_32 = lean::box(0);
x_8 = x_32;
goto lbl_9;
}
}
}
default:
{
obj* x_35; 
lean::dec(x_4);
lean::dec(x_2);
x_35 = lean::box(0);
x_8 = x_35;
goto lbl_9;
}
}
lbl_9:
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_42; 
lean::dec(x_8);
x_37 = lean::array_push(x_7, x_6);
x_38 = lean::mk_nat_obj(0ul);
x_39 = l_Array_reverseAux___main___rarg(x_3, x_38);
x_40 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_39, x_39, x_38, x_37);
lean::dec(x_39);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_1);
return x_42;
}
lbl_11:
{
obj* x_45; obj* x_46; 
lean::dec(x_10);
lean::inc(x_6);
x_45 = lean::array_push(x_3, x_6);
x_46 = l_Lean_IR_FnBody_collectFreeIndices(x_6, x_4);
x_0 = x_7;
x_3 = x_45;
x_4 = x_46;
goto _start;
}
lbl_15:
{
obj* x_50; 
lean::dec(x_14);
lean::inc(x_4);
x_50 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_4, x_12);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_53; obj* x_54; 
x_51 = lean::mk_nat_obj(0ul);
lean::inc(x_6);
x_53 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2(x_2, x_6, x_12, x_51, x_1);
x_54 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3(x_6, x_12, x_51, x_2);
lean::dec(x_12);
x_0 = x_7;
x_1 = x_53;
x_2 = x_54;
goto _start;
}
else
{
obj* x_59; 
lean::dec(x_50);
lean::dec(x_12);
x_59 = lean::box(0);
x_10 = x_59;
goto lbl_11;
}
}
}
else
{
obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_2);
x_63 = lean::mk_nat_obj(0ul);
x_64 = l_Array_reverseAux___main___rarg(x_3, x_63);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_1);
return x_65;
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
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
x_20 = l_Lean_IR_FnBody_pushProj___main(x_15);
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
x_11 = l_Lean_IR_FnBody_freeIndices(x_9);
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
x_7 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2___closed__1;
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
case 10:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_31; obj* x_32; obj* x_33; 
x_9 = lean::cnstr_get(x_4, 0);
x_11 = lean::cnstr_get(x_4, 1);
x_13 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
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
x_21 = lean::box(0);
lean::inc(x_11);
x_23 = l_RBNode_insert___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__2(x_20, x_11, x_21);
x_24 = l_Array_empty___closed__1;
x_25 = l_Lean_IR_pushProjs___main(x_8, x_13, x_19, x_24, x_23);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_31 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__3(x_7, x_28);
if (lean::is_scalar(x_15)) {
 x_32 = lean::alloc_cnstr(10, 3, 0);
} else {
 x_32 = x_15;
}
lean::cnstr_set(x_32, 0, x_9);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_31);
x_33 = l_Lean_IR_reshape(x_26, x_32);
return x_33;
}
default:
{
obj* x_34; 
x_34 = l_Lean_IR_reshape(x_8, x_4);
return x_34;
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
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_lean_compiler_ir_freevars(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_pushproj(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_freevars(w);
if (io_result_is_error(w)) return w;
 l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2___closed__1 = _init_l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2___closed__1);
return w;
}
