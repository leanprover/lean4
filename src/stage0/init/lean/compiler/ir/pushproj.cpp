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
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Lean_IR_Decl_pushProj___main(obj*);
obj* l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(obj*, obj*);
obj* l_RBNode_insert___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_reshape(obj*, obj*);
obj* l_Lean_IR_FnBody_pushProj(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Array_fget(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_flatten(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
uint8 l_Array_isEmpty___rarg(obj*);
obj* l_Array_push(obj*, obj*, obj*);
obj* l_Lean_IR_pushProjs(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_pushProj___main(obj*);
obj* l_Lean_IR_FnBody_collectFreeIndices(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__3(obj*, obj*);
obj* l_Array_reverseAux___main___rarg(obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Array_pop(obj*, obj*);
obj* l_Lean_IR_pushProjs___main(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_pushProjs___main___spec__1(obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__1(obj*, obj*);
obj* l_Lean_IR_FnBody_setBody___main(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2(obj*, obj*, obj*, obj*);
obj* l_Array_back___at_Lean_IR_pushProjs___main___spec__1___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Array_append___spec__1___rarg(obj*, obj*, obj*, obj*);
extern obj* l_Lean_IR_Inhabited;
obj* l_Array_back___at_Lean_IR_pushProjs___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean::nat_sub(x_2, x_3);
lean::dec(x_2);
x_5 = l_Lean_IR_Inhabited;
x_6 = lean::array_get(x_5, x_1, x_4);
lean::dec(x_4);
return x_6;
}
}
obj* _init_l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(13);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_5);
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::array_fget(x_5, x_4);
x_9 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2___closed__1;
x_10 = lean::array_fset(x_5, x_4, x_9);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_4, x_11);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_8);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_8, 1);
x_15 = l_Lean_IR_vsetInh;
x_16 = lean::array_get(x_15, x_1, x_4);
x_17 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_16, x_3);
lean::dec(x_16);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; 
lean::dec(x_17);
x_18 = lean::array_fset(x_10, x_4, x_8);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_18;
goto _start;
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_17);
lean::inc(x_2);
x_20 = l_Lean_IR_FnBody_setBody___main(x_2, x_14);
lean::cnstr_set(x_8, 1, x_20);
x_21 = lean::array_fset(x_10, x_4, x_8);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_21;
goto _start;
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_8, 0);
x_24 = lean::cnstr_get(x_8, 1);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_8);
x_25 = l_Lean_IR_vsetInh;
x_26 = lean::array_get(x_25, x_1, x_4);
x_27 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_26, x_3);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_27);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_23);
lean::cnstr_set(x_28, 1, x_24);
x_29 = lean::array_fset(x_10, x_4, x_28);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_29;
goto _start;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_27);
lean::inc(x_2);
x_31 = l_Lean_IR_FnBody_setBody___main(x_2, x_24);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_23);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::array_fset(x_10, x_4, x_32);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_33;
goto _start;
}
}
}
else
{
uint8 x_35; 
x_35 = !lean::is_exclusive(x_8);
if (x_35 == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_36 = lean::cnstr_get(x_8, 0);
x_37 = l_Lean_IR_vsetInh;
x_38 = lean::array_get(x_37, x_1, x_4);
x_39 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_38, x_3);
lean::dec(x_38);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_41; 
lean::dec(x_39);
x_40 = lean::array_fset(x_10, x_4, x_8);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_40;
goto _start;
}
else
{
obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_39);
lean::inc(x_2);
x_42 = l_Lean_IR_FnBody_setBody___main(x_2, x_36);
lean::cnstr_set(x_8, 0, x_42);
x_43 = lean::array_fset(x_10, x_4, x_8);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_43;
goto _start;
}
}
else
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_45 = lean::cnstr_get(x_8, 0);
lean::inc(x_45);
lean::dec(x_8);
x_46 = l_Lean_IR_vsetInh;
x_47 = lean::array_get(x_46, x_1, x_4);
x_48 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_47, x_3);
lean::dec(x_47);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_48);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_45);
x_50 = lean::array_fset(x_10, x_4, x_49);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_50;
goto _start;
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_48);
lean::inc(x_2);
x_52 = l_Lean_IR_FnBody_setBody___main(x_2, x_45);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
x_54 = lean::array_fset(x_10, x_4, x_53);
lean::dec(x_4);
x_4 = x_12;
x_5 = x_54;
goto _start;
}
}
}
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_4);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::array_fget(x_4, x_3);
x_8 = lean::box(0);
x_9 = lean::array_fset(x_4, x_3, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_add(x_3, x_10);
x_12 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_7, x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_12);
x_13 = lean::array_fset(x_9, x_3, x_7);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_13;
goto _start;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_12);
lean::inc(x_1);
x_15 = l_Lean_IR_FnBody_collectFreeIndices(x_1, x_7);
x_16 = lean::array_fset(x_9, x_3, x_15);
lean::dec(x_3);
x_3 = x_11;
x_4 = x_16;
goto _start;
}
}
}
}
obj* l_Lean_IR_pushProjs___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = l_Array_isEmpty___rarg(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_16; obj* x_21; uint8 x_22; obj* x_23; 
x_7 = l_Array_back___at_Lean_IR_pushProjs___main___spec__1(x_1);
x_8 = lean::array_pop(x_1);
if (lean::obj_tag(x_7) == 0)
{
obj* x_31; 
x_31 = lean::cnstr_get(x_7, 1);
lean::inc(x_31);
switch (lean::obj_tag(x_31)) {
case 3:
{
obj* x_32; uint8 x_33; 
x_32 = lean::cnstr_get(x_7, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*3);
x_21 = x_32;
x_22 = x_33;
x_23 = x_31;
goto block_30;
}
case 4:
{
obj* x_34; uint8 x_35; 
x_34 = lean::cnstr_get(x_7, 0);
lean::inc(x_34);
x_35 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*3);
x_21 = x_34;
x_22 = x_35;
x_23 = x_31;
goto block_30;
}
case 5:
{
obj* x_36; uint8 x_37; 
x_36 = lean::cnstr_get(x_7, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*3);
x_21 = x_36;
x_22 = x_37;
x_23 = x_31;
goto block_30;
}
case 12:
{
obj* x_38; 
lean::dec(x_31);
x_38 = lean::box(0);
x_16 = x_38;
goto block_20;
}
case 13:
{
obj* x_39; 
lean::dec(x_31);
x_39 = lean::box(0);
x_16 = x_39;
goto block_20;
}
default: 
{
obj* x_40; 
lean::dec(x_31);
lean::dec(x_5);
lean::dec(x_3);
x_40 = lean::box(0);
x_9 = x_40;
goto block_15;
}
}
}
else
{
obj* x_41; 
lean::dec(x_5);
lean::dec(x_3);
x_41 = lean::box(0);
x_9 = x_41;
goto block_15;
}
block_15:
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_9);
x_10 = lean::array_push(x_8, x_7);
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Array_reverseAux___main___rarg(x_4, x_11);
x_13 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_12, x_12, x_11, x_10);
lean::dec(x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_2);
return x_14;
}
block_20:
{
obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_16);
lean::inc(x_7);
x_17 = lean::array_push(x_4, x_7);
x_18 = l_Lean_IR_FnBody_collectFreeIndices(x_7, x_5);
x_1 = x_8;
x_4 = x_17;
x_5 = x_18;
goto _start;
}
block_30:
{
obj* x_24; 
lean::dec(x_23);
x_24 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__1(x_5, x_21);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_24);
x_25 = lean::mk_nat_obj(0u);
lean::inc(x_7);
x_26 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2(x_3, x_7, x_21, x_25, x_2);
x_27 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3(x_7, x_21, x_25, x_3);
lean::dec(x_21);
x_1 = x_8;
x_2 = x_26;
x_3 = x_27;
goto _start;
}
else
{
obj* x_29; 
lean::dec(x_24);
lean::dec(x_21);
x_29 = lean::box(0);
x_16 = x_29;
goto block_20;
}
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_1);
x_42 = lean::mk_nat_obj(0u);
x_43 = l_Array_reverseAux___main___rarg(x_4, x_42);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_2);
return x_44;
}
}
}
obj* l_Array_back___at_Lean_IR_pushProjs___main___spec__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Array_back___at_Lean_IR_pushProjs___main___spec__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__3(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_IR_pushProjs(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_IR_pushProjs___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::array_fget(x_2, x_1);
x_6 = lean::box(13);
x_7 = lean::array_fset(x_2, x_1, x_6);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_1, x_8);
if (lean::obj_tag(x_5) == 1)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_5);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_5, 2);
x_12 = l_Lean_IR_FnBody_pushProj___main(x_11);
lean::cnstr_set(x_5, 2, x_12);
x_13 = lean::array_fset(x_7, x_1, x_5);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_13;
goto _start;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_5, 0);
x_16 = lean::cnstr_get(x_5, 1);
x_17 = lean::cnstr_get(x_5, 2);
x_18 = lean::cnstr_get(x_5, 3);
lean::inc(x_18);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_5);
x_19 = l_Lean_IR_FnBody_pushProj___main(x_17);
x_20 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_20, 0, x_15);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_19);
lean::cnstr_set(x_20, 3, x_18);
x_21 = lean::array_fset(x_7, x_1, x_20);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_21;
goto _start;
}
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::array_fset(x_7, x_1, x_5);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_23;
goto _start;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = l_Lean_IR_AltCore_body___main(x_7);
lean::dec(x_7);
x_9 = l_Lean_IR_FnBody_freeIndices(x_8);
x_10 = lean::array_push(x_4, x_9);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_3, x_11);
lean::dec(x_3);
x_3 = x_12;
x_4 = x_10;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::array_fget(x_2, x_1);
x_6 = l_Array_hmmapAux___main___at_Lean_IR_pushProjs___main___spec__2___closed__1;
x_7 = lean::array_fset(x_2, x_1, x_6);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_1, x_8);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_5);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_5, 1);
x_12 = l_Lean_IR_FnBody_pushProj___main(x_11);
lean::cnstr_set(x_5, 1, x_12);
x_13 = lean::array_fset(x_7, x_1, x_5);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_13;
goto _start;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_15 = lean::cnstr_get(x_5, 0);
x_16 = lean::cnstr_get(x_5, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_5);
x_17 = l_Lean_IR_FnBody_pushProj___main(x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::array_fset(x_7, x_1, x_18);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_19;
goto _start;
}
}
else
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_5);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_5, 0);
x_23 = l_Lean_IR_FnBody_pushProj___main(x_22);
lean::cnstr_set(x_5, 0, x_23);
x_24 = lean::array_fset(x_7, x_1, x_5);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_24;
goto _start;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_5, 0);
lean::inc(x_26);
lean::dec(x_5);
x_27 = l_Lean_IR_FnBody_pushProj___main(x_26);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::array_fset(x_7, x_1, x_28);
lean::dec(x_1);
x_1 = x_9;
x_2 = x_29;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_FnBody_pushProj___main(obj* x_1) {
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
x_6 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__1(x_5, x_3);
if (lean::obj_tag(x_4) == 10)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_8 = lean::cnstr_get(x_4, 1);
x_9 = lean::cnstr_get(x_4, 2);
x_10 = lean::array_get_size(x_9);
x_11 = lean::mk_empty_array(x_10);
lean::dec(x_10);
x_12 = l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2(x_9, x_9, x_5, x_11);
x_13 = lean::box(0);
x_14 = lean::box(0);
lean::inc(x_8);
x_15 = l_RBNode_insert___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__2(x_13, x_8, x_14);
x_16 = l_Array_empty___closed__1;
x_17 = l_Lean_IR_pushProjs___main(x_6, x_9, x_12, x_16, x_15);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_17, 1);
lean::inc(x_19);
lean::dec(x_17);
x_20 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__3(x_5, x_19);
lean::cnstr_set(x_4, 2, x_20);
x_21 = l_Lean_IR_reshape(x_18, x_4);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_22 = lean::cnstr_get(x_4, 0);
x_23 = lean::cnstr_get(x_4, 1);
x_24 = lean::cnstr_get(x_4, 2);
lean::inc(x_24);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_4);
x_25 = lean::array_get_size(x_24);
x_26 = lean::mk_empty_array(x_25);
lean::dec(x_25);
x_27 = l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2(x_24, x_24, x_5, x_26);
x_28 = lean::box(0);
x_29 = lean::box(0);
lean::inc(x_23);
x_30 = l_RBNode_insert___at___private_init_lean_compiler_ir_freevars_14__collectIndex___spec__2(x_28, x_23, x_29);
x_31 = l_Array_empty___closed__1;
x_32 = l_Lean_IR_pushProjs___main(x_6, x_24, x_27, x_31, x_30);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_34 = lean::cnstr_get(x_32, 1);
lean::inc(x_34);
lean::dec(x_32);
x_35 = l_Array_hmmapAux___main___at_Lean_IR_FnBody_pushProj___main___spec__3(x_5, x_34);
x_36 = lean::alloc_cnstr(10, 3, 0);
lean::cnstr_set(x_36, 0, x_22);
lean::cnstr_set(x_36, 1, x_23);
lean::cnstr_set(x_36, 2, x_35);
x_37 = l_Lean_IR_reshape(x_33, x_36);
return x_37;
}
}
else
{
obj* x_38; 
x_38 = l_Lean_IR_reshape(x_6, x_4);
return x_38;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_FnBody_pushProj___main___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_IR_FnBody_pushProj(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_FnBody_pushProj___main(x_1);
return x_2;
}
}
obj* l_Lean_IR_Decl_pushProj___main(obj* x_1) {
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
x_4 = l_Lean_IR_FnBody_pushProj___main(x_3);
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
x_9 = l_Lean_IR_FnBody_pushProj___main(x_8);
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
obj* l_Lean_IR_Decl_pushProj(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Decl_pushProj___main(x_1);
return x_2;
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
