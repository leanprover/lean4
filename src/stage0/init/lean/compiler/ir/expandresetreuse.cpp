// Lean compiler output
// Module: init.lean.compiler.ir.expandresetreuse
// Imports: init.control.state init.control.reader init.lean.compiler.ir.compilerm
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
obj* l_Lean_IR_Decl_expandResetReuse(obj*);
extern obj* l_Array_empty___closed__1;
obj* l_Lean_IR_ExpandResetReuse_searchAndExpand___main(obj*, obj*);
obj* l_Lean_IR_Decl_expandResetReuse___main(obj*);
obj* l_Lean_IR_ExpandResetReuse_expand(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_reshape(obj*, obj*);
uint8 l_Lean_IR_ExpandResetReuse_consumed(obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_consumed___boxed(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
uint8 l_Lean_IR_FnBody_isTerminal___main(obj*);
obj* l_Lean_IR_ExpandResetReuse_searchAndExpand(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1___closed__1;
namespace lean {
obj* nat_add(obj*, obj*);
}
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
uint8 l_Lean_IR_ExpandResetReuse_consumed___main(obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_ExpandResetReuse_consumed___main___boxed(obj*, obj*);
obj* l_Lean_IR_FnBody_body___main(obj*);
obj* l_Lean_IR_push(obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1(obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_7; 
lean::dec(x_2);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; obj* x_9; uint8 x_11; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l_Lean_IR_AltCore_body___main(x_8);
lean::dec(x_8);
x_11 = l_Lean_IR_ExpandResetReuse_consumed___main(x_0, x_9);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
lean::dec(x_2);
x_2 = x_13;
goto _start;
}
else
{
lean::dec(x_2);
return x_11;
}
}
}
}
uint8 l_Lean_IR_ExpandResetReuse_consumed___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
switch (lean::obj_tag(x_4)) {
case 2:
{
obj* x_6; obj* x_9; uint8 x_12; 
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::nat_dec_eq(x_0, x_9);
lean::dec(x_9);
if (x_12 == 0)
{
x_1 = x_6;
goto _start;
}
else
{
uint8 x_16; 
lean::dec(x_6);
x_16 = 1;
return x_16;
}
}
default:
{
obj* x_18; 
lean::dec(x_4);
x_18 = lean::cnstr_get(x_1, 2);
lean::inc(x_18);
lean::dec(x_1);
x_1 = x_18;
goto _start;
}
}
}
case 7:
{
obj* x_22; obj* x_24; uint8 x_27; 
x_22 = lean::cnstr_get(x_1, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_1, 2);
lean::inc(x_24);
lean::dec(x_1);
x_27 = lean::nat_dec_eq(x_0, x_22);
lean::dec(x_22);
if (x_27 == 0)
{
x_1 = x_24;
goto _start;
}
else
{
uint8 x_31; 
lean::dec(x_24);
x_31 = 1;
return x_31;
}
}
case 10:
{
obj* x_32; obj* x_35; uint8 x_36; 
x_32 = lean::cnstr_get(x_1, 2);
lean::inc(x_32);
lean::dec(x_1);
x_35 = lean::mk_nat_obj(0ul);
x_36 = l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(x_0, x_32, x_35);
lean::dec(x_32);
return x_36;
}
default:
{
obj* x_38; 
x_38 = lean::box(0);
x_2 = x_38;
goto lbl_3;
}
}
lbl_3:
{
uint8 x_40; 
lean::dec(x_2);
x_40 = l_Lean_IR_FnBody_isTerminal___main(x_1);
if (x_40 == 0)
{
obj* x_41; 
x_41 = l_Lean_IR_FnBody_body___main(x_1);
lean::dec(x_1);
x_1 = x_41;
goto _start;
}
else
{
uint8 x_45; 
lean::dec(x_1);
x_45 = 0;
return x_45;
}
}
}
}
obj* l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_ExpandResetReuse_consumed___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_ExpandResetReuse_consumed___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
return x_3;
}
}
uint8 l_Lean_IR_ExpandResetReuse_consumed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_consumed___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_ExpandResetReuse_consumed___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_ExpandResetReuse_consumed(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_ExpandResetReuse_expand(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
x_6 = 7;
x_7 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_7, 0, x_1);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set_scalar(x_7, sizeof(void*)*3, x_6);
x_8 = x_7;
x_9 = l_Lean_IR_reshape(x_0, x_8);
return x_9;
}
}
obj* _init_l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(13);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1(obj* x_0, obj* x_1) {
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
x_7 = l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = lean::mk_nat_obj(1ul);
x_10 = lean::nat_add(x_0, x_9);
if (lean::obj_tag(x_6) == 0)
{
obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
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
x_16 = l_Array_empty___closed__1;
x_17 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_13, x_16);
if (lean::is_scalar(x_15)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_15;
}
lean::cnstr_set(x_18, 0, x_11);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::array_fset(x_8, x_0, x_18);
lean::dec(x_0);
x_0 = x_10;
x_1 = x_19;
goto _start;
}
else
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_22 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_24 = x_6;
} else {
 lean::inc(x_22);
 lean::dec(x_6);
 x_24 = lean::box(0);
}
x_25 = l_Array_empty___closed__1;
x_26 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_22, x_25);
if (lean::is_scalar(x_24)) {
 x_27 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_27 = x_24;
}
lean::cnstr_set(x_27, 0, x_26);
x_28 = lean::array_fset(x_8, x_0, x_27);
lean::dec(x_0);
x_0 = x_10;
x_1 = x_28;
goto _start;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_searchAndExpand___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
switch (lean::obj_tag(x_4)) {
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; uint8 x_16; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_4, 1);
lean::inc(x_12);
lean::dec(x_4);
lean::inc(x_8);
x_16 = l_Lean_IR_ExpandResetReuse_consumed___main(x_6, x_8);
if (x_16 == 0)
{
obj* x_20; 
lean::dec(x_10);
lean::dec(x_6);
lean::dec(x_12);
x_20 = l_Lean_IR_push(x_1, x_0);
x_0 = x_8;
x_1 = x_20;
goto _start;
}
else
{
obj* x_23; 
lean::dec(x_0);
x_23 = l_Lean_IR_ExpandResetReuse_expand(x_1, x_6, x_10, x_12, x_8);
return x_23;
}
}
default:
{
obj* x_25; 
lean::dec(x_4);
x_25 = lean::box(0);
x_2 = x_25;
goto lbl_3;
}
}
}
case 10:
{
obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_26 = lean::cnstr_get(x_0, 0);
x_28 = lean::cnstr_get(x_0, 1);
x_30 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_32 = x_0;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_0);
 x_32 = lean::box(0);
}
x_33 = lean::mk_nat_obj(0ul);
x_34 = l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1(x_33, x_30);
if (lean::is_scalar(x_32)) {
 x_35 = lean::alloc_cnstr(10, 3, 0);
} else {
 x_35 = x_32;
}
lean::cnstr_set(x_35, 0, x_26);
lean::cnstr_set(x_35, 1, x_28);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_Lean_IR_reshape(x_1, x_35);
return x_36;
}
default:
{
obj* x_37; 
x_37 = lean::box(0);
x_2 = x_37;
goto lbl_3;
}
}
lbl_3:
{
uint8 x_39; 
lean::dec(x_2);
x_39 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_39 == 0)
{
obj* x_40; obj* x_41; 
x_40 = l_Lean_IR_FnBody_body___main(x_0);
x_41 = l_Lean_IR_push(x_1, x_0);
x_0 = x_40;
x_1 = x_41;
goto _start;
}
else
{
obj* x_43; 
x_43 = l_Lean_IR_reshape(x_1, x_0);
return x_43;
}
}
}
}
obj* l_Lean_IR_ExpandResetReuse_searchAndExpand(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_Decl_expandResetReuse___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_3; uint8 x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
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
x_9 = l_Array_empty___closed__1;
x_10 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_6, x_9);
if (lean::is_scalar(x_8)) {
 x_11 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_11 = x_8;
}
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_3);
lean::cnstr_set(x_11, 2, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*3, x_5);
x_12 = x_11;
return x_12;
}
else
{
return x_0;
}
}
}
obj* l_Lean_IR_Decl_expandResetReuse(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Decl_expandResetReuse___main(x_0);
return x_1;
}
}
obj* initialize_init_control_state(obj*);
obj* initialize_init_control_reader(obj*);
obj* initialize_init_lean_compiler_ir_compilerm(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_expandresetreuse(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_control_state(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (io_result_is_error(w)) return w;
 l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1___closed__1 = _init_l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1___closed__1);
return w;
}
