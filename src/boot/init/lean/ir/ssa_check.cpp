// Lean compiler output
// Module: init.lean.ir.ssa_check
// Imports: init.lean.ir.instances init.lean.ir.format
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
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_lean_ir_check__blockids___closed__1;
extern obj* l_lean_ir_mk__var__set;
obj* l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(obj*, obj*);
obj* l_lean_ir_terminator_check__blockids(obj*, obj*);
obj* l_rbtree_seteq___at_lean_ir_phis_check__predecessors___spec__1(obj*, obj*);
obj* l_lean_ir_var_define(obj*, obj*, obj*);
extern obj* l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
obj* l_rbmap_find__core___main___at_lean_ir_var_defined___spec__2(obj*, obj*);
obj* l_lean_ir_terminator_to__format___main(obj*);
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_ir_var_declare(obj*, obj*, obj*);
obj* l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_instr_to__format___main(obj*);
obj* l_lean_ir_blockid_defined___closed__1;
obj* l_lean_ir_ssa__valid__m;
obj* l_list_mmap_x_27___main___at_lean_ir_decl_check__blockids___main___spec__1(obj*, obj*);
obj* l_lean_ir_block_declare___closed__1;
obj* l_lean_ir_terminator_valid__ssa(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_ir_phi_valid__ssa(obj*, obj*, obj*);
obj* l_lean_ir_ssa__valid__m_run___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__3(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__2(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(obj*, obj*, obj*);
obj* l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(obj*);
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(obj*, obj*);
obj* l_lean_ir_decl_valid__ssa___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_ir_ssa__pre__m;
obj* l_lean_ir_var_defined___closed__1;
obj* l_lean_ir_block_declare___closed__2;
obj* l_lean_ir_ssa__valid__m_run(obj*);
obj* l_rbnode_find__core___main___at_lean_ir_phi_predecessors___spec__3(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_var_declare___spec__3(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_blockid_defined(obj*, obj*);
obj* l_reader__t_bind___at_lean_ir_decl_valid__ssa___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_ir_var_declare___spec__1(obj*, obj*);
uint8 l_option_to__bool___main___rarg(obj*);
obj* l_state__t_bind___at_lean_ir_check__blockids___spec__2(obj*, obj*);
obj* l_lean_ir_decl_check__blockids(obj*, obj*);
obj* l_rbnode_mk__insert__result___main___rarg(uint8, obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_rbtree_find___at_lean_ir_var_defined___spec__1(obj*, obj*);
obj* l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__1(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(obj*, obj*, obj*);
obj* l_rbtree_subset___at_lean_ir_phis_check__predecessors___spec__2(obj*, obj*);
extern obj* l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
obj* l_lean_ir_decl_header___main(obj*);
obj* l_lean_ir_phi_predecessors(obj*, obj*, obj*);
obj* l_lean_ir_decl_declare__vars___main___closed__1;
obj* l_rbnode_find__core___main___at_lean_ir_var_defined___spec__3(obj*, obj*);
obj* l_lean_ir_phis_check__predecessors(obj*, obj*, obj*);
obj* l_reader__t_bind___at_lean_ir_decl_valid__ssa___spec__3(obj*, obj*);
obj* l_rbmap_find__core___main___at_lean_ir_phi_predecessors___spec__2(obj*, obj*);
obj* l_lean_ir_phi_to__format___main(obj*);
obj* l_lean_ir_var_defined(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_check__blockids___main___spec__2(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_phi_predecessors___spec__4(obj*, obj*, obj*);
obj* l_lean_ir_blockid__check__m;
obj* l_lean_ir_check__blockids(obj*);
obj* l_lean_ir_block_declare(obj*, obj*);
extern obj* l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
obj* l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__2(obj*, obj*, obj*);
obj* l_state__t_bind___at_lean_ir_check__blockids___spec__2___rarg(obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___closed__1;
obj* l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__2(obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_check__blockids___spec__1(obj*, obj*);
obj* l_lean_ir_phi_declare(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__1(obj*, obj*);
obj* l_lean_ir_block_check__blockids(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4(obj*, obj*, obj*, obj*);
extern obj* l_lean_ir_mk__var2blockid;
obj* l_lean_ir_blockid__check__m_run(obj*);
obj* l_lean_ir_instr_declare__vars___main(obj*, obj*, obj*);
obj* l_lean_ir_var_declare___closed__1;
obj* l_lean_ir_block_declare__vars(obj*, obj*);
obj* l_lean_ir_decl_check__blockids___main(obj*, obj*);
obj* l_lean_ir_blockid__check__m_run___rarg(obj*);
obj* l_lean_ir_check__blockids___lambda__1(obj*, obj*);
obj* l_lean_ir_instr_valid__ssa(obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1;
extern obj* l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
obj* l_lean_ir_decl_valid__ssa(obj*);
extern obj* l_lean_ir_mk__blockid__set;
obj* l_rbnode_ins___main___at_lean_ir_var_define___spec__3(obj*, obj*, obj*);
obj* l_lean_ir_arg_define(obj*, obj*, obj*);
obj* l_lean_ir_var_declare___closed__2;
obj* l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(obj*);
obj* l_lean_ir_decl_declare__vars(obj*, obj*);
obj* l_lean_ir_arg_declare(obj*, obj*, obj*);
uint8 l_rbnode_get__color___main___rarg(obj*);
obj* l_rbnode_insert___at_lean_ir_var_declare___spec__4(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2(obj*);
obj* l_lean_ir_instr_declare__vars(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_var_define___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_decl_declare__vars___main(obj*, obj*);
extern obj* l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
obj* l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__1(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__1(obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2(obj*, obj*);
obj* l_lean_ir_decl_var2blockid(obj*);
obj* l_rbnode_insert___at_lean_ir_var_define___spec__2(obj*, obj*, obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__4(obj*, obj*, obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5(obj*, obj*, obj*);
obj* l_lean_ir_block_valid__ssa__core(obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_check__blockids___spec__1___rarg(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_terminator_check__blockids___spec__1(obj*, obj*);
extern obj* l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
obj* l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__2;
obj* _init_l_lean_ir_ssa__pre__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_16; uint8 x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; uint8 x_22; 
lean::dec(x_5);
lean::inc(x_1);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_1);
lean::dec(x_11);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_9);
return x_26;
}
else
{
lean::dec(x_9);
x_0 = x_11;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
x_0 = x_5;
goto _start;
}
}
default:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_44; uint8 x_45; 
x_33 = lean::cnstr_get(x_0, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 2);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_0, 3);
lean::inc(x_39);
lean::dec(x_0);
lean::inc(x_35);
lean::inc(x_1);
x_44 = l_lean_name_quick__lt___main(x_1, x_35);
x_45 = lean::unbox(x_44);
lean::dec(x_44);
if (x_45 == 0)
{
obj* x_49; uint8 x_50; 
lean::dec(x_33);
lean::inc(x_1);
x_49 = l_lean_name_quick__lt___main(x_35, x_1);
x_50 = lean::unbox(x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_54; 
lean::dec(x_1);
lean::dec(x_39);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_37);
return x_54;
}
else
{
lean::dec(x_37);
x_0 = x_39;
goto _start;
}
}
else
{
lean::dec(x_35);
lean::dec(x_37);
lean::dec(x_39);
x_0 = x_33;
goto _start;
}
}
}
}
}
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg), 2, 0);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_ir_var_declare___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; uint8 x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_9);
lean::dec(x_7);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_13;
 lean::cnstr_set_tag(x_13, 1);
}
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_11);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
x_27 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_13;
 lean::cnstr_set_tag(x_13, 1);
}
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_7);
lean::cnstr_set(x_28, 2, x_9);
lean::cnstr_set(x_28, 3, x_27);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_13;
 lean::cnstr_set_tag(x_13, 1);
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; uint8 x_43; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
lean::inc(x_33);
lean::inc(x_1);
x_42 = l_lean_name_quick__lt___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; uint8 x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = l_lean_name_quick__lt___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_33);
lean::dec(x_35);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_39;
 lean::cnstr_set_tag(x_39, 2);
}
lean::cnstr_set(x_52, 0, x_31);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_37);
return x_52;
}
else
{
uint8 x_54; 
lean::inc(x_37);
x_54 = l_rbnode_get__color___main___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_37, x_1, x_2);
x_57 = l_rbnode_balance2__node___main___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_39;
 lean::cnstr_set_tag(x_39, 2);
}
lean::cnstr_set(x_59, 0, x_31);
lean::cnstr_set(x_59, 1, x_33);
lean::cnstr_set(x_59, 2, x_35);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
else
{
uint8 x_61; 
lean::inc(x_31);
x_61 = l_rbnode_get__color___main___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_31, x_1, x_2);
x_64 = l_rbnode_balance1__node___main___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_39;
 lean::cnstr_set_tag(x_39, 2);
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_35);
lean::cnstr_set(x_66, 3, x_37);
return x_66;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_var_declare___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_ir_var_declare___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_var_declare___spec__4(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_ir_var_declare(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; uint8 x_6; 
lean::inc(x_0);
lean::inc(x_2);
x_5 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(x_2, x_0);
x_6 = l_option_is__some___main___rarg(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; 
x_7 = l_rbnode_insert___at_lean_ir_var_declare___spec__4(x_2, x_0, x_1);
x_8 = l_lean_ir_var_declare___closed__1;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_7);
return x_10;
}
else
{
obj* x_12; uint8 x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_1);
x_12 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_13 = 0;
x_14 = l_lean_ir_var_declare___closed__2;
lean::inc(x_14);
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_12);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_13);
x_17 = x_16;
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_2);
return x_19;
}
}
}
obj* _init_l_lean_ir_var_declare___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_var_declare___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("already defined ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_instr_declare__vars___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_ir_var_declare(x_3, x_1, x_2);
return x_6;
}
case 1:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_var_declare(x_7, x_1, x_2);
return x_10;
}
case 2:
{
obj* x_11; obj* x_14; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = l_lean_ir_var_declare(x_11, x_1, x_2);
return x_14;
}
case 3:
{
obj* x_15; obj* x_18; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
lean::dec(x_0);
x_18 = l_lean_ir_var_declare(x_15, x_1, x_2);
return x_18;
}
case 4:
{
obj* x_21; obj* x_23; 
lean::dec(x_1);
lean::dec(x_0);
x_21 = l_lean_ir_var_declare___closed__1;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_2);
return x_23;
}
case 5:
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_0, 0);
lean::inc(x_24);
lean::dec(x_0);
x_27 = l_lean_ir_var_declare(x_24, x_1, x_2);
return x_27;
}
case 6:
{
obj* x_28; obj* x_31; 
x_28 = lean::cnstr_get(x_0, 0);
lean::inc(x_28);
lean::dec(x_0);
x_31 = l_lean_ir_var_declare(x_28, x_1, x_2);
return x_31;
}
case 7:
{
obj* x_34; obj* x_36; 
lean::dec(x_1);
lean::dec(x_0);
x_34 = l_lean_ir_var_declare___closed__1;
lean::inc(x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_2);
return x_36;
}
case 8:
{
obj* x_37; obj* x_40; 
x_37 = lean::cnstr_get(x_0, 0);
lean::inc(x_37);
lean::dec(x_0);
x_40 = l_lean_ir_var_declare(x_37, x_1, x_2);
return x_40;
}
case 9:
{
obj* x_43; obj* x_45; 
lean::dec(x_1);
lean::dec(x_0);
x_43 = l_lean_ir_var_declare___closed__1;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_2);
return x_45;
}
case 10:
{
obj* x_46; obj* x_49; 
x_46 = lean::cnstr_get(x_0, 0);
lean::inc(x_46);
lean::dec(x_0);
x_49 = l_lean_ir_var_declare(x_46, x_1, x_2);
return x_49;
}
case 11:
{
obj* x_50; obj* x_53; 
x_50 = lean::cnstr_get(x_0, 0);
lean::inc(x_50);
lean::dec(x_0);
x_53 = l_lean_ir_var_declare(x_50, x_1, x_2);
return x_53;
}
case 12:
{
obj* x_54; obj* x_57; 
x_54 = lean::cnstr_get(x_0, 0);
lean::inc(x_54);
lean::dec(x_0);
x_57 = l_lean_ir_var_declare(x_54, x_1, x_2);
return x_57;
}
case 13:
{
obj* x_58; obj* x_61; 
x_58 = lean::cnstr_get(x_0, 0);
lean::inc(x_58);
lean::dec(x_0);
x_61 = l_lean_ir_var_declare(x_58, x_1, x_2);
return x_61;
}
case 14:
{
obj* x_62; obj* x_65; 
x_62 = lean::cnstr_get(x_0, 0);
lean::inc(x_62);
lean::dec(x_0);
x_65 = l_lean_ir_var_declare(x_62, x_1, x_2);
return x_65;
}
default:
{
obj* x_68; obj* x_70; 
lean::dec(x_1);
lean::dec(x_0);
x_68 = l_lean_ir_var_declare___closed__1;
lean::inc(x_68);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_2);
return x_70;
}
}
}
}
obj* l_lean_ir_instr_declare__vars(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_instr_declare__vars___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_ir_phi_declare(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = l_lean_ir_var_declare(x_3, x_1, x_2);
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
if (lean::obj_tag(x_6) == 0)
{
obj* x_11; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_13 = x_6;
}
x_14 = l_lean_ir_phi_to__format___main(x_0);
x_15 = 0;
x_16 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_16);
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_14);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_15);
x_19 = x_18;
x_20 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_20);
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_20);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_15);
x_23 = x_22;
x_24 = lean::box(1);
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_15);
x_26 = x_25;
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_11);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_15);
x_28 = x_27;
if (lean::is_scalar(x_13)) {
 x_29 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_29 = x_13;
 lean::cnstr_set_tag(x_13, 0);
}
lean::cnstr_set(x_29, 0, x_28);
if (lean::is_scalar(x_10)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_10;
 lean::cnstr_set_tag(x_10, 0);
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_8);
return x_30;
}
else
{
obj* x_32; 
lean::dec(x_0);
if (lean::is_scalar(x_10)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_10;
 lean::cnstr_set_tag(x_10, 0);
}
lean::cnstr_set(x_32, 0, x_6);
lean::cnstr_set(x_32, 1, x_8);
return x_32;
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_var_declare___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = l_lean_ir_phi_declare(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
 lean::cnstr_set_tag(x_24, 0);
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
 lean::cnstr_set_tag(x_19, 0);
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_var_declare___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = l_lean_ir_instr_declare__vars___main(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
 lean::cnstr_set_tag(x_24, 0);
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
 lean::cnstr_set_tag(x_19, 0);
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_lean_ir_block_declare__vars(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_12; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::inc(x_4);
x_7 = l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__1(x_2, x_4, x_1);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_12 = x_7;
}
if (lean::obj_tag(x_8) == 0)
{
obj* x_14; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_0);
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_16 = x_8;
}
x_17 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_4);
x_18 = 0;
x_19 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_19);
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_18);
x_22 = x_21;
x_23 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_23);
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_23);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_18);
x_26 = x_25;
x_27 = lean::box(1);
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_18);
x_29 = x_28;
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_14);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_18);
x_31 = x_30;
if (lean::is_scalar(x_16)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_16;
 lean::cnstr_set_tag(x_16, 0);
}
lean::cnstr_set(x_32, 0, x_31);
if (lean::is_scalar(x_12)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_12;
 lean::cnstr_set_tag(x_12, 0);
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_10);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_39; obj* x_40; obj* x_42; 
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_34 = x_8;
}
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
lean::dec(x_0);
lean::inc(x_4);
x_39 = l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__2(x_35, x_4, x_10);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
if (lean::obj_tag(x_40) == 0)
{
obj* x_45; obj* x_48; uint8 x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_45 = lean::cnstr_get(x_40, 0);
lean::inc(x_45);
lean::dec(x_40);
x_48 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_4);
x_49 = 0;
x_50 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_50);
x_52 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_52, 0, x_50);
lean::cnstr_set(x_52, 1, x_48);
lean::cnstr_set_scalar(x_52, sizeof(void*)*2, x_49);
x_53 = x_52;
x_54 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_54);
x_56 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_56, 0, x_53);
lean::cnstr_set(x_56, 1, x_54);
lean::cnstr_set_scalar(x_56, sizeof(void*)*2, x_49);
x_57 = x_56;
x_58 = lean::box(1);
x_59 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_58);
lean::cnstr_set_scalar(x_59, sizeof(void*)*2, x_49);
x_60 = x_59;
x_61 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_45);
lean::cnstr_set_scalar(x_61, sizeof(void*)*2, x_49);
x_62 = x_61;
if (lean::is_scalar(x_34)) {
 x_63 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_63 = x_34;
 lean::cnstr_set_tag(x_34, 0);
}
lean::cnstr_set(x_63, 0, x_62);
if (lean::is_scalar(x_12)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_12;
 lean::cnstr_set_tag(x_12, 0);
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_42);
return x_64;
}
else
{
obj* x_67; 
lean::dec(x_4);
lean::dec(x_34);
if (lean::is_scalar(x_12)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_12;
 lean::cnstr_set_tag(x_12, 0);
}
lean::cnstr_set(x_67, 0, x_40);
lean::cnstr_set(x_67, 1, x_42);
return x_67;
}
}
}
}
obj* l_lean_ir_arg_declare(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_ir_var_declare(x_3, x_1, x_2);
return x_6;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; 
lean::dec(x_0);
x_3 = l_lean_ir_var_declare___closed__1;
lean::inc(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_14; obj* x_16; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = l_lean_ir_block_declare__vars(x_6, x_1);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
if (lean::obj_tag(x_12) == 0)
{
obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_8);
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_20 = x_12;
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
 lean::cnstr_set_tag(x_20, 0);
}
lean::cnstr_set(x_21, 0, x_18);
if (lean::is_scalar(x_16)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_16;
 lean::cnstr_set_tag(x_16, 0);
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_14);
return x_22;
}
else
{
lean::dec(x_12);
lean::dec(x_16);
x_0 = x_8;
x_1 = x_14;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_var_declare___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = l_lean_ir_arg_declare(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
 lean::cnstr_set_tag(x_24, 0);
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
 lean::cnstr_set_tag(x_19, 0);
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_lean_ir_decl_declare__vars___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; 
lean::dec(x_0);
x_3 = l_lean_ir_var_declare___closed__1;
lean::inc(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
else
{
obj* x_6; obj* x_8; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; obj* x_15; 
lean::dec(x_6);
lean::dec(x_8);
x_13 = l_lean_ir_decl_declare__vars___main___closed__1;
lean::inc(x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_1);
return x_15;
}
else
{
obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_31; 
x_16 = lean::cnstr_get(x_8, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_8, 1);
lean::inc(x_18);
lean::dec(x_8);
x_24 = lean::cnstr_get(x_6, 1);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_16, 0);
lean::inc(x_26);
x_28 = l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__2(x_24, x_26, x_1);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
if (lean::obj_tag(x_29) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_16);
x_35 = lean::cnstr_get(x_29, 0);
lean::inc(x_35);
if (lean::is_shared(x_29)) {
 lean::dec(x_29);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_29, 0);
 x_37 = x_29;
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_37;
 lean::cnstr_set_tag(x_37, 0);
}
lean::cnstr_set(x_38, 0, x_35);
x_21 = x_38;
x_22 = x_31;
goto lbl_23;
}
else
{
obj* x_40; obj* x_41; obj* x_43; 
lean::dec(x_29);
x_40 = l_lean_ir_block_declare__vars(x_16, x_31);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
x_21 = x_41;
x_22 = x_43;
goto lbl_23;
}
lbl_23:
{
if (lean::obj_tag(x_21) == 0)
{
obj* x_47; obj* x_49; obj* x_50; obj* x_53; uint8 x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_18);
x_47 = lean::cnstr_get(x_21, 0);
lean::inc(x_47);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_49 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_49 = x_21;
}
x_50 = lean::cnstr_get(x_6, 0);
lean::inc(x_50);
lean::dec(x_6);
x_53 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_50);
x_54 = 0;
x_55 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_55);
x_57 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_53);
lean::cnstr_set_scalar(x_57, sizeof(void*)*2, x_54);
x_58 = x_57;
x_59 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_59);
x_61 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_61, 0, x_58);
lean::cnstr_set(x_61, 1, x_59);
lean::cnstr_set_scalar(x_61, sizeof(void*)*2, x_54);
x_62 = x_61;
x_63 = lean::box(1);
x_64 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set(x_64, 1, x_63);
lean::cnstr_set_scalar(x_64, sizeof(void*)*2, x_54);
x_65 = x_64;
x_66 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_47);
lean::cnstr_set_scalar(x_66, sizeof(void*)*2, x_54);
x_67 = x_66;
if (lean::is_scalar(x_49)) {
 x_68 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_68 = x_49;
 lean::cnstr_set_tag(x_49, 0);
}
lean::cnstr_set(x_68, 0, x_67);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_22);
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_76; 
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_70 = x_21;
}
x_71 = l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__1(x_18, x_22);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
if (lean::is_shared(x_71)) {
 lean::dec(x_71);
 x_76 = lean::box(0);
} else {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 x_76 = x_71;
}
if (lean::obj_tag(x_72) == 0)
{
obj* x_77; obj* x_80; obj* x_83; uint8 x_84; obj* x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_77 = lean::cnstr_get(x_72, 0);
lean::inc(x_77);
lean::dec(x_72);
x_80 = lean::cnstr_get(x_6, 0);
lean::inc(x_80);
lean::dec(x_6);
x_83 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_80);
x_84 = 0;
x_85 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_85);
x_87 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set(x_87, 1, x_83);
lean::cnstr_set_scalar(x_87, sizeof(void*)*2, x_84);
x_88 = x_87;
x_89 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_89);
x_91 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_91, 0, x_88);
lean::cnstr_set(x_91, 1, x_89);
lean::cnstr_set_scalar(x_91, sizeof(void*)*2, x_84);
x_92 = x_91;
x_93 = lean::box(1);
x_94 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set(x_94, 1, x_93);
lean::cnstr_set_scalar(x_94, sizeof(void*)*2, x_84);
x_95 = x_94;
x_96 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_77);
lean::cnstr_set_scalar(x_96, sizeof(void*)*2, x_84);
x_97 = x_96;
if (lean::is_scalar(x_70)) {
 x_98 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_98 = x_70;
 lean::cnstr_set_tag(x_70, 0);
}
lean::cnstr_set(x_98, 0, x_97);
if (lean::is_scalar(x_76)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_76;
 lean::cnstr_set_tag(x_76, 0);
}
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_74);
return x_99;
}
else
{
obj* x_102; 
lean::dec(x_6);
lean::dec(x_70);
if (lean::is_scalar(x_76)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_76;
 lean::cnstr_set_tag(x_76, 0);
}
lean::cnstr_set(x_102, 0, x_72);
lean::cnstr_set(x_102, 1, x_74);
return x_102;
}
}
}
}
}
}
}
obj* _init_l_lean_ir_decl_declare__vars___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("declaration must have at least one basic block");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_ir_decl_declare__vars(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_decl_declare__vars___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_ir_decl_var2blockid(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_6; 
x_1 = l_lean_ir_mk__var2blockid;
lean::inc(x_1);
x_3 = l_lean_ir_decl_declare__vars___main(x_0, x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_6);
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_12 = x_4;
}
if (lean::is_scalar(x_12)) {
 x_13 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_13 = x_12;
 lean::cnstr_set_tag(x_12, 0);
}
lean::cnstr_set(x_13, 0, x_10);
return x_13;
}
else
{
obj* x_14; obj* x_15; 
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_14 = x_4;
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_15 = x_14;
 lean::cnstr_set_tag(x_14, 1);
}
lean::cnstr_set(x_15, 0, x_6);
return x_15;
}
}
}
obj* _init_l_lean_ir_ssa__valid__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_ir_ssa__valid__m_run___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; 
x_2 = l_lean_ir_mk__var__set;
lean::inc(x_2);
x_4 = lean::apply_2(x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_ir_ssa__valid__m_run(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_ssa__valid__m_run___rarg), 2, 0);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_ir_var_define___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; uint8 x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_9);
lean::dec(x_7);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_13;
 lean::cnstr_set_tag(x_13, 1);
}
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_11);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
x_27 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_13;
 lean::cnstr_set_tag(x_13, 1);
}
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_7);
lean::cnstr_set(x_28, 2, x_9);
lean::cnstr_set(x_28, 3, x_27);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_13;
 lean::cnstr_set_tag(x_13, 1);
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; uint8 x_43; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
lean::inc(x_33);
lean::inc(x_1);
x_42 = l_lean_name_quick__lt___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; uint8 x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = l_lean_name_quick__lt___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_33);
lean::dec(x_35);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_39;
 lean::cnstr_set_tag(x_39, 2);
}
lean::cnstr_set(x_52, 0, x_31);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_37);
return x_52;
}
else
{
uint8 x_54; 
lean::inc(x_37);
x_54 = l_rbnode_get__color___main___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_37, x_1, x_2);
x_57 = l_rbnode_balance2__node___main___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_39;
 lean::cnstr_set_tag(x_39, 2);
}
lean::cnstr_set(x_59, 0, x_31);
lean::cnstr_set(x_59, 1, x_33);
lean::cnstr_set(x_59, 2, x_35);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
else
{
uint8 x_61; 
lean::inc(x_31);
x_61 = l_rbnode_get__color___main___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_31, x_1, x_2);
x_64 = l_rbnode_balance1__node___main___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_39;
 lean::cnstr_set_tag(x_39, 2);
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_35);
lean::cnstr_set(x_66, 3, x_37);
return x_66;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_var_define___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_ir_var_define___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_var_define___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_ir_var_define(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; 
lean::dec(x_1);
x_4 = lean::box(0);
x_5 = l_rbnode_insert___at_lean_ir_var_define___spec__2(x_2, x_0, x_4);
x_6 = l_lean_ir_var_declare___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
}
obj* l_lean_ir_arg_define(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_ir_var_define(x_3, x_1, x_2);
return x_6;
}
}
obj* l_rbnode_find__core___main___at_lean_ir_var_defined___spec__3(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_16; uint8 x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_22; uint8 x_23; 
lean::dec(x_5);
lean::inc(x_1);
lean::inc(x_7);
x_22 = l_lean_name_quick__lt___main(x_7, x_1);
x_23 = lean::unbox(x_22);
lean::dec(x_22);
if (x_23 == 0)
{
obj* x_27; obj* x_28; 
lean::dec(x_1);
lean::dec(x_11);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_7);
lean::cnstr_set(x_27, 1, x_9);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
else
{
lean::dec(x_9);
lean::dec(x_7);
x_0 = x_11;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
x_0 = x_5;
goto _start;
}
}
default:
{
obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_47; uint8 x_48; 
x_36 = lean::cnstr_get(x_0, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_0, 1);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_0, 2);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_0, 3);
lean::inc(x_42);
lean::dec(x_0);
lean::inc(x_38);
lean::inc(x_1);
x_47 = l_lean_name_quick__lt___main(x_1, x_38);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_53; uint8 x_54; 
lean::dec(x_36);
lean::inc(x_1);
lean::inc(x_38);
x_53 = l_lean_name_quick__lt___main(x_38, x_1);
x_54 = lean::unbox(x_53);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_58; obj* x_59; 
lean::dec(x_1);
lean::dec(x_42);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_38);
lean::cnstr_set(x_58, 1, x_40);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
else
{
lean::dec(x_38);
lean::dec(x_40);
x_0 = x_42;
goto _start;
}
}
else
{
lean::dec(x_38);
lean::dec(x_40);
lean::dec(x_42);
x_0 = x_36;
goto _start;
}
}
}
}
}
obj* l_rbmap_find__core___main___at_lean_ir_var_defined___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find__core___main___at_lean_ir_var_defined___spec__3(x_0, x_1);
return x_2;
}
}
obj* l_rbtree_find___at_lean_ir_var_defined___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find__core___main___at_lean_ir_var_defined___spec__3(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_8; obj* x_11; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_7 = x_2;
}
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_7;
 lean::cnstr_set_tag(x_7, 1);
}
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
}
}
obj* l_lean_ir_var_defined(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; uint8 x_7; 
lean::dec(x_1);
lean::inc(x_0);
lean::inc(x_2);
x_6 = l_rbtree_find___at_lean_ir_var_defined___spec__1(x_2, x_0);
x_7 = l_option_is__some___main___rarg(x_6);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_8 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_9 = 0;
x_10 = l_lean_ir_var_defined___closed__1;
lean::inc(x_10);
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_8);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_9);
x_13 = x_12;
x_14 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_14);
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_9);
x_17 = x_16;
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_2);
return x_19;
}
else
{
obj* x_21; obj* x_23; 
lean::dec(x_0);
x_21 = l_lean_ir_var_declare___closed__1;
lean::inc(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_2);
return x_23;
}
}
}
obj* _init_l_lean_ir_var_defined___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("undefined '");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = l_lean_ir_var_declare___closed__1;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_17; uint8 x_18; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
lean::inc(x_10);
lean::inc(x_0);
x_17 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(x_0, x_10);
x_18 = l_option_is__some___main___rarg(x_17);
if (x_18 == 0)
{
obj* x_22; uint8 x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_2);
x_22 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_10);
x_23 = 0;
x_24 = l_lean_ir_var_defined___closed__1;
lean::inc(x_24);
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_22);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_23);
x_27 = x_26;
x_28 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_27);
lean::cnstr_set(x_30, 1, x_28);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_23);
x_31 = x_30;
x_32 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_3);
return x_33;
}
else
{
lean::dec(x_10);
x_1 = x_12;
goto _start;
}
}
}
}
obj* l_lean_ir_phi_valid__ssa(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_7; obj* x_8; obj* x_10; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_1);
x_7 = l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1(x_1, x_3, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_12 = x_7;
}
if (lean::obj_tag(x_8) == 0)
{
obj* x_14; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_16 = x_8;
}
x_17 = l_lean_ir_phi_to__format___main(x_0);
x_18 = 0;
x_19 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_19);
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_18);
x_22 = x_21;
x_23 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_23);
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_23);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_18);
x_26 = x_25;
x_27 = lean::box(1);
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_18);
x_29 = x_28;
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_14);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_18);
x_31 = x_30;
if (lean::is_scalar(x_16)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_16;
 lean::cnstr_set_tag(x_16, 0);
}
lean::cnstr_set(x_32, 0, x_31);
if (lean::is_scalar(x_12)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_12;
 lean::cnstr_set_tag(x_12, 0);
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_10);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_40; 
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_34 = x_8;
}
x_35 = lean::cnstr_get(x_0, 0);
lean::inc(x_35);
x_37 = l_lean_ir_var_define(x_35, x_1, x_10);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_43; obj* x_46; uint8 x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_43 = lean::cnstr_get(x_38, 0);
lean::inc(x_43);
lean::dec(x_38);
x_46 = l_lean_ir_phi_to__format___main(x_0);
x_47 = 0;
x_48 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_48);
x_50 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_46);
lean::cnstr_set_scalar(x_50, sizeof(void*)*2, x_47);
x_51 = x_50;
x_52 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_52);
x_54 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_54, 0, x_51);
lean::cnstr_set(x_54, 1, x_52);
lean::cnstr_set_scalar(x_54, sizeof(void*)*2, x_47);
x_55 = x_54;
x_56 = lean::box(1);
x_57 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
lean::cnstr_set_scalar(x_57, sizeof(void*)*2, x_47);
x_58 = x_57;
x_59 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_43);
lean::cnstr_set_scalar(x_59, sizeof(void*)*2, x_47);
x_60 = x_59;
if (lean::is_scalar(x_34)) {
 x_61 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_61 = x_34;
 lean::cnstr_set_tag(x_34, 0);
}
lean::cnstr_set(x_61, 0, x_60);
if (lean::is_scalar(x_12)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_12;
 lean::cnstr_set_tag(x_12, 0);
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_40);
return x_62;
}
else
{
obj* x_65; 
lean::dec(x_0);
lean::dec(x_34);
if (lean::is_scalar(x_12)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_12;
 lean::cnstr_set_tag(x_12, 0);
}
lean::cnstr_set(x_65, 0, x_38);
lean::cnstr_set(x_65, 1, x_40);
return x_65;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_var_declare___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = l_lean_ir_var_defined(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
 lean::cnstr_set_tag(x_24, 0);
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
 lean::cnstr_set_tag(x_19, 0);
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_var_declare___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = l_lean_ir_var_defined(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
 lean::cnstr_set_tag(x_24, 0);
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
 lean::cnstr_set_tag(x_19, 0);
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_var_declare___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = l_lean_ir_var_defined(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
 lean::cnstr_set_tag(x_24, 0);
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
 lean::cnstr_set_tag(x_19, 0);
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_lean_ir_instr_valid__ssa(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::inc(x_1);
x_10 = l_lean_ir_var_define(x_5, x_1, x_2);
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
if (lean::obj_tag(x_11) == 0)
{
obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_7);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_20 = x_11;
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
 lean::cnstr_set_tag(x_20, 0);
}
lean::cnstr_set(x_21, 0, x_18);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_15;
 lean::cnstr_set_tag(x_15, 0);
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_13);
x_3 = x_22;
goto lbl_4;
}
else
{
obj* x_25; 
lean::dec(x_15);
lean::dec(x_11);
x_25 = l_lean_ir_var_defined(x_7, x_1, x_13);
x_3 = x_25;
goto lbl_4;
}
}
case 1:
{
obj* x_26; obj* x_28; 
x_26 = lean::cnstr_get(x_0, 0);
lean::inc(x_26);
x_28 = l_lean_ir_var_define(x_26, x_1, x_2);
x_3 = x_28;
goto lbl_4;
}
case 2:
{
obj* x_29; obj* x_31; obj* x_34; obj* x_35; obj* x_37; obj* x_39; 
x_29 = lean::cnstr_get(x_0, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_0, 1);
lean::inc(x_31);
lean::inc(x_1);
x_34 = l_lean_ir_var_define(x_29, x_1, x_2);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
if (lean::is_shared(x_34)) {
 lean::dec(x_34);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_release(x_34, 1);
 x_39 = x_34;
}
if (lean::obj_tag(x_35) == 0)
{
obj* x_42; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_1);
lean::dec(x_31);
x_42 = lean::cnstr_get(x_35, 0);
lean::inc(x_42);
if (lean::is_shared(x_35)) {
 lean::dec(x_35);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_35, 0);
 x_44 = x_35;
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_44;
 lean::cnstr_set_tag(x_44, 0);
}
lean::cnstr_set(x_45, 0, x_42);
if (lean::is_scalar(x_39)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_39;
 lean::cnstr_set_tag(x_39, 0);
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_37);
x_3 = x_46;
goto lbl_4;
}
else
{
obj* x_49; 
lean::dec(x_35);
lean::dec(x_39);
x_49 = l_lean_ir_var_defined(x_31, x_1, x_37);
x_3 = x_49;
goto lbl_4;
}
}
case 3:
{
obj* x_50; obj* x_52; obj* x_54; obj* x_57; obj* x_58; obj* x_60; obj* x_62; 
x_50 = lean::cnstr_get(x_0, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_0, 1);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_0, 2);
lean::inc(x_54);
lean::inc(x_1);
x_57 = l_lean_ir_var_define(x_50, x_1, x_2);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
if (lean::is_shared(x_57)) {
 lean::dec(x_57);
 x_62 = lean::box(0);
} else {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_62 = x_57;
}
if (lean::obj_tag(x_58) == 0)
{
obj* x_66; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_1);
lean::dec(x_54);
lean::dec(x_52);
x_66 = lean::cnstr_get(x_58, 0);
lean::inc(x_66);
if (lean::is_shared(x_58)) {
 lean::dec(x_58);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_58, 0);
 x_68 = x_58;
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_68;
 lean::cnstr_set_tag(x_68, 0);
}
lean::cnstr_set(x_69, 0, x_66);
if (lean::is_scalar(x_62)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_62;
 lean::cnstr_set_tag(x_62, 0);
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_60);
x_3 = x_70;
goto lbl_4;
}
else
{
obj* x_71; obj* x_73; obj* x_74; obj* x_76; 
if (lean::is_shared(x_58)) {
 lean::dec(x_58);
 x_71 = lean::box(0);
} else {
 lean::cnstr_release(x_58, 0);
 x_71 = x_58;
}
lean::inc(x_1);
x_73 = l_lean_ir_var_defined(x_52, x_1, x_60);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_81; obj* x_84; obj* x_85; 
lean::dec(x_1);
lean::dec(x_54);
x_81 = lean::cnstr_get(x_74, 0);
lean::inc(x_81);
lean::dec(x_74);
if (lean::is_scalar(x_71)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_71;
 lean::cnstr_set_tag(x_71, 0);
}
lean::cnstr_set(x_84, 0, x_81);
if (lean::is_scalar(x_62)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_62;
 lean::cnstr_set_tag(x_62, 0);
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_76);
x_3 = x_85;
goto lbl_4;
}
else
{
obj* x_89; 
lean::dec(x_74);
lean::dec(x_62);
lean::dec(x_71);
x_89 = l_lean_ir_var_defined(x_54, x_1, x_76);
x_3 = x_89;
goto lbl_4;
}
}
}
case 4:
{
obj* x_90; obj* x_92; 
x_90 = lean::cnstr_get(x_0, 0);
lean::inc(x_90);
x_92 = l_lean_ir_var_defined(x_90, x_1, x_2);
x_3 = x_92;
goto lbl_4;
}
case 5:
{
obj* x_93; obj* x_95; obj* x_98; obj* x_99; obj* x_101; obj* x_103; 
x_93 = lean::cnstr_get(x_0, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_0, 2);
lean::inc(x_95);
lean::inc(x_1);
x_98 = l_lean_ir_var_define(x_93, x_1, x_2);
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_98, 1);
lean::inc(x_101);
if (lean::is_shared(x_98)) {
 lean::dec(x_98);
 x_103 = lean::box(0);
} else {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 x_103 = x_98;
}
if (lean::obj_tag(x_99) == 0)
{
obj* x_106; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_1);
lean::dec(x_95);
x_106 = lean::cnstr_get(x_99, 0);
lean::inc(x_106);
if (lean::is_shared(x_99)) {
 lean::dec(x_99);
 x_108 = lean::box(0);
} else {
 lean::cnstr_release(x_99, 0);
 x_108 = x_99;
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_109 = x_108;
 lean::cnstr_set_tag(x_108, 0);
}
lean::cnstr_set(x_109, 0, x_106);
if (lean::is_scalar(x_103)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_103;
 lean::cnstr_set_tag(x_103, 0);
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_101);
x_3 = x_110;
goto lbl_4;
}
else
{
obj* x_113; 
lean::dec(x_99);
lean::dec(x_103);
x_113 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__1(x_95, x_1, x_101);
x_3 = x_113;
goto lbl_4;
}
}
case 6:
{
obj* x_114; obj* x_116; 
x_114 = lean::cnstr_get(x_0, 0);
lean::inc(x_114);
x_116 = l_lean_ir_var_define(x_114, x_1, x_2);
x_3 = x_116;
goto lbl_4;
}
case 7:
{
obj* x_117; obj* x_119; obj* x_122; obj* x_123; obj* x_125; obj* x_127; 
x_117 = lean::cnstr_get(x_0, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_0, 1);
lean::inc(x_119);
lean::inc(x_1);
x_122 = l_lean_ir_var_defined(x_117, x_1, x_2);
x_123 = lean::cnstr_get(x_122, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_122, 1);
lean::inc(x_125);
if (lean::is_shared(x_122)) {
 lean::dec(x_122);
 x_127 = lean::box(0);
} else {
 lean::cnstr_release(x_122, 0);
 lean::cnstr_release(x_122, 1);
 x_127 = x_122;
}
if (lean::obj_tag(x_123) == 0)
{
obj* x_130; obj* x_132; obj* x_133; obj* x_134; 
lean::dec(x_1);
lean::dec(x_119);
x_130 = lean::cnstr_get(x_123, 0);
lean::inc(x_130);
if (lean::is_shared(x_123)) {
 lean::dec(x_123);
 x_132 = lean::box(0);
} else {
 lean::cnstr_release(x_123, 0);
 x_132 = x_123;
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_133 = x_132;
 lean::cnstr_set_tag(x_132, 0);
}
lean::cnstr_set(x_133, 0, x_130);
if (lean::is_scalar(x_127)) {
 x_134 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_134 = x_127;
 lean::cnstr_set_tag(x_127, 0);
}
lean::cnstr_set(x_134, 0, x_133);
lean::cnstr_set(x_134, 1, x_125);
x_3 = x_134;
goto lbl_4;
}
else
{
obj* x_137; 
lean::dec(x_123);
lean::dec(x_127);
x_137 = l_lean_ir_var_defined(x_119, x_1, x_125);
x_3 = x_137;
goto lbl_4;
}
}
case 8:
{
obj* x_138; obj* x_140; obj* x_143; obj* x_144; obj* x_146; obj* x_148; 
x_138 = lean::cnstr_get(x_0, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_0, 1);
lean::inc(x_140);
lean::inc(x_1);
x_143 = l_lean_ir_var_define(x_138, x_1, x_2);
x_144 = lean::cnstr_get(x_143, 0);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_143, 1);
lean::inc(x_146);
if (lean::is_shared(x_143)) {
 lean::dec(x_143);
 x_148 = lean::box(0);
} else {
 lean::cnstr_release(x_143, 0);
 lean::cnstr_release(x_143, 1);
 x_148 = x_143;
}
if (lean::obj_tag(x_144) == 0)
{
obj* x_151; obj* x_153; obj* x_154; obj* x_155; 
lean::dec(x_1);
lean::dec(x_140);
x_151 = lean::cnstr_get(x_144, 0);
lean::inc(x_151);
if (lean::is_shared(x_144)) {
 lean::dec(x_144);
 x_153 = lean::box(0);
} else {
 lean::cnstr_release(x_144, 0);
 x_153 = x_144;
}
if (lean::is_scalar(x_153)) {
 x_154 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_154 = x_153;
 lean::cnstr_set_tag(x_153, 0);
}
lean::cnstr_set(x_154, 0, x_151);
if (lean::is_scalar(x_148)) {
 x_155 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_155 = x_148;
 lean::cnstr_set_tag(x_148, 0);
}
lean::cnstr_set(x_155, 0, x_154);
lean::cnstr_set(x_155, 1, x_146);
x_3 = x_155;
goto lbl_4;
}
else
{
obj* x_158; 
lean::dec(x_148);
lean::dec(x_144);
x_158 = l_lean_ir_var_defined(x_140, x_1, x_146);
x_3 = x_158;
goto lbl_4;
}
}
case 9:
{
obj* x_159; obj* x_161; obj* x_164; obj* x_165; obj* x_167; obj* x_169; 
x_159 = lean::cnstr_get(x_0, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_0, 1);
lean::inc(x_161);
lean::inc(x_1);
x_164 = l_lean_ir_var_defined(x_159, x_1, x_2);
x_165 = lean::cnstr_get(x_164, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_164, 1);
lean::inc(x_167);
if (lean::is_shared(x_164)) {
 lean::dec(x_164);
 x_169 = lean::box(0);
} else {
 lean::cnstr_release(x_164, 0);
 lean::cnstr_release(x_164, 1);
 x_169 = x_164;
}
if (lean::obj_tag(x_165) == 0)
{
obj* x_172; obj* x_174; obj* x_175; obj* x_176; 
lean::dec(x_1);
lean::dec(x_161);
x_172 = lean::cnstr_get(x_165, 0);
lean::inc(x_172);
if (lean::is_shared(x_165)) {
 lean::dec(x_165);
 x_174 = lean::box(0);
} else {
 lean::cnstr_release(x_165, 0);
 x_174 = x_165;
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_175 = x_174;
 lean::cnstr_set_tag(x_174, 0);
}
lean::cnstr_set(x_175, 0, x_172);
if (lean::is_scalar(x_169)) {
 x_176 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_176 = x_169;
 lean::cnstr_set_tag(x_169, 0);
}
lean::cnstr_set(x_176, 0, x_175);
lean::cnstr_set(x_176, 1, x_167);
x_3 = x_176;
goto lbl_4;
}
else
{
obj* x_179; 
lean::dec(x_165);
lean::dec(x_169);
x_179 = l_lean_ir_var_defined(x_161, x_1, x_167);
x_3 = x_179;
goto lbl_4;
}
}
case 10:
{
obj* x_180; obj* x_182; obj* x_185; obj* x_186; obj* x_188; obj* x_190; 
x_180 = lean::cnstr_get(x_0, 0);
lean::inc(x_180);
x_182 = lean::cnstr_get(x_0, 1);
lean::inc(x_182);
lean::inc(x_1);
x_185 = l_lean_ir_var_define(x_180, x_1, x_2);
x_186 = lean::cnstr_get(x_185, 0);
lean::inc(x_186);
x_188 = lean::cnstr_get(x_185, 1);
lean::inc(x_188);
if (lean::is_shared(x_185)) {
 lean::dec(x_185);
 x_190 = lean::box(0);
} else {
 lean::cnstr_release(x_185, 0);
 lean::cnstr_release(x_185, 1);
 x_190 = x_185;
}
if (lean::obj_tag(x_186) == 0)
{
obj* x_193; obj* x_195; obj* x_196; obj* x_197; 
lean::dec(x_182);
lean::dec(x_1);
x_193 = lean::cnstr_get(x_186, 0);
lean::inc(x_193);
if (lean::is_shared(x_186)) {
 lean::dec(x_186);
 x_195 = lean::box(0);
} else {
 lean::cnstr_release(x_186, 0);
 x_195 = x_186;
}
if (lean::is_scalar(x_195)) {
 x_196 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_196 = x_195;
 lean::cnstr_set_tag(x_195, 0);
}
lean::cnstr_set(x_196, 0, x_193);
if (lean::is_scalar(x_190)) {
 x_197 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_197 = x_190;
 lean::cnstr_set_tag(x_190, 0);
}
lean::cnstr_set(x_197, 0, x_196);
lean::cnstr_set(x_197, 1, x_188);
x_3 = x_197;
goto lbl_4;
}
else
{
obj* x_200; 
lean::dec(x_190);
lean::dec(x_186);
x_200 = l_lean_ir_var_defined(x_182, x_1, x_188);
x_3 = x_200;
goto lbl_4;
}
}
case 11:
{
obj* x_201; obj* x_203; obj* x_206; obj* x_207; obj* x_209; obj* x_211; 
x_201 = lean::cnstr_get(x_0, 0);
lean::inc(x_201);
x_203 = lean::cnstr_get(x_0, 2);
lean::inc(x_203);
lean::inc(x_1);
x_206 = l_lean_ir_var_define(x_201, x_1, x_2);
x_207 = lean::cnstr_get(x_206, 0);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_206, 1);
lean::inc(x_209);
if (lean::is_shared(x_206)) {
 lean::dec(x_206);
 x_211 = lean::box(0);
} else {
 lean::cnstr_release(x_206, 0);
 lean::cnstr_release(x_206, 1);
 x_211 = x_206;
}
if (lean::obj_tag(x_207) == 0)
{
obj* x_214; obj* x_216; obj* x_217; obj* x_218; 
lean::dec(x_203);
lean::dec(x_1);
x_214 = lean::cnstr_get(x_207, 0);
lean::inc(x_214);
if (lean::is_shared(x_207)) {
 lean::dec(x_207);
 x_216 = lean::box(0);
} else {
 lean::cnstr_release(x_207, 0);
 x_216 = x_207;
}
if (lean::is_scalar(x_216)) {
 x_217 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_217 = x_216;
 lean::cnstr_set_tag(x_216, 0);
}
lean::cnstr_set(x_217, 0, x_214);
if (lean::is_scalar(x_211)) {
 x_218 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_218 = x_211;
 lean::cnstr_set_tag(x_211, 0);
}
lean::cnstr_set(x_218, 0, x_217);
lean::cnstr_set(x_218, 1, x_209);
x_3 = x_218;
goto lbl_4;
}
else
{
obj* x_221; 
lean::dec(x_211);
lean::dec(x_207);
x_221 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__2(x_203, x_1, x_209);
x_3 = x_221;
goto lbl_4;
}
}
case 12:
{
obj* x_222; obj* x_224; obj* x_227; obj* x_228; obj* x_230; obj* x_232; 
x_222 = lean::cnstr_get(x_0, 0);
lean::inc(x_222);
x_224 = lean::cnstr_get(x_0, 1);
lean::inc(x_224);
lean::inc(x_1);
x_227 = l_lean_ir_var_define(x_222, x_1, x_2);
x_228 = lean::cnstr_get(x_227, 0);
lean::inc(x_228);
x_230 = lean::cnstr_get(x_227, 1);
lean::inc(x_230);
if (lean::is_shared(x_227)) {
 lean::dec(x_227);
 x_232 = lean::box(0);
} else {
 lean::cnstr_release(x_227, 0);
 lean::cnstr_release(x_227, 1);
 x_232 = x_227;
}
if (lean::obj_tag(x_228) == 0)
{
obj* x_235; obj* x_237; obj* x_238; obj* x_239; 
lean::dec(x_224);
lean::dec(x_1);
x_235 = lean::cnstr_get(x_228, 0);
lean::inc(x_235);
if (lean::is_shared(x_228)) {
 lean::dec(x_228);
 x_237 = lean::box(0);
} else {
 lean::cnstr_release(x_228, 0);
 x_237 = x_228;
}
if (lean::is_scalar(x_237)) {
 x_238 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_238 = x_237;
 lean::cnstr_set_tag(x_237, 0);
}
lean::cnstr_set(x_238, 0, x_235);
if (lean::is_scalar(x_232)) {
 x_239 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_239 = x_232;
 lean::cnstr_set_tag(x_232, 0);
}
lean::cnstr_set(x_239, 0, x_238);
lean::cnstr_set(x_239, 1, x_230);
x_3 = x_239;
goto lbl_4;
}
else
{
obj* x_242; 
lean::dec(x_228);
lean::dec(x_232);
x_242 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__3(x_224, x_1, x_230);
x_3 = x_242;
goto lbl_4;
}
}
case 13:
{
obj* x_243; obj* x_245; obj* x_247; obj* x_250; obj* x_251; obj* x_253; obj* x_255; 
x_243 = lean::cnstr_get(x_0, 0);
lean::inc(x_243);
x_245 = lean::cnstr_get(x_0, 1);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_0, 2);
lean::inc(x_247);
lean::inc(x_1);
x_250 = l_lean_ir_var_define(x_243, x_1, x_2);
x_251 = lean::cnstr_get(x_250, 0);
lean::inc(x_251);
x_253 = lean::cnstr_get(x_250, 1);
lean::inc(x_253);
if (lean::is_shared(x_250)) {
 lean::dec(x_250);
 x_255 = lean::box(0);
} else {
 lean::cnstr_release(x_250, 0);
 lean::cnstr_release(x_250, 1);
 x_255 = x_250;
}
if (lean::obj_tag(x_251) == 0)
{
obj* x_259; obj* x_261; obj* x_262; obj* x_263; 
lean::dec(x_247);
lean::dec(x_245);
lean::dec(x_1);
x_259 = lean::cnstr_get(x_251, 0);
lean::inc(x_259);
if (lean::is_shared(x_251)) {
 lean::dec(x_251);
 x_261 = lean::box(0);
} else {
 lean::cnstr_release(x_251, 0);
 x_261 = x_251;
}
if (lean::is_scalar(x_261)) {
 x_262 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_262 = x_261;
 lean::cnstr_set_tag(x_261, 0);
}
lean::cnstr_set(x_262, 0, x_259);
if (lean::is_scalar(x_255)) {
 x_263 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_263 = x_255;
 lean::cnstr_set_tag(x_255, 0);
}
lean::cnstr_set(x_263, 0, x_262);
lean::cnstr_set(x_263, 1, x_253);
x_3 = x_263;
goto lbl_4;
}
else
{
obj* x_264; obj* x_266; obj* x_267; obj* x_269; 
if (lean::is_shared(x_251)) {
 lean::dec(x_251);
 x_264 = lean::box(0);
} else {
 lean::cnstr_release(x_251, 0);
 x_264 = x_251;
}
lean::inc(x_1);
x_266 = l_lean_ir_var_defined(x_245, x_1, x_253);
x_267 = lean::cnstr_get(x_266, 0);
lean::inc(x_267);
x_269 = lean::cnstr_get(x_266, 1);
lean::inc(x_269);
lean::dec(x_266);
if (lean::obj_tag(x_267) == 0)
{
obj* x_274; obj* x_277; obj* x_278; 
lean::dec(x_247);
lean::dec(x_1);
x_274 = lean::cnstr_get(x_267, 0);
lean::inc(x_274);
lean::dec(x_267);
if (lean::is_scalar(x_264)) {
 x_277 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_277 = x_264;
 lean::cnstr_set_tag(x_264, 0);
}
lean::cnstr_set(x_277, 0, x_274);
if (lean::is_scalar(x_255)) {
 x_278 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_278 = x_255;
 lean::cnstr_set_tag(x_255, 0);
}
lean::cnstr_set(x_278, 0, x_277);
lean::cnstr_set(x_278, 1, x_269);
x_3 = x_278;
goto lbl_4;
}
else
{
obj* x_282; 
lean::dec(x_264);
lean::dec(x_255);
lean::dec(x_267);
x_282 = l_lean_ir_var_defined(x_247, x_1, x_269);
x_3 = x_282;
goto lbl_4;
}
}
}
case 14:
{
obj* x_283; obj* x_285; obj* x_287; obj* x_290; obj* x_291; obj* x_293; obj* x_295; 
x_283 = lean::cnstr_get(x_0, 0);
lean::inc(x_283);
x_285 = lean::cnstr_get(x_0, 1);
lean::inc(x_285);
x_287 = lean::cnstr_get(x_0, 2);
lean::inc(x_287);
lean::inc(x_1);
x_290 = l_lean_ir_var_define(x_283, x_1, x_2);
x_291 = lean::cnstr_get(x_290, 0);
lean::inc(x_291);
x_293 = lean::cnstr_get(x_290, 1);
lean::inc(x_293);
if (lean::is_shared(x_290)) {
 lean::dec(x_290);
 x_295 = lean::box(0);
} else {
 lean::cnstr_release(x_290, 0);
 lean::cnstr_release(x_290, 1);
 x_295 = x_290;
}
if (lean::obj_tag(x_291) == 0)
{
obj* x_299; obj* x_301; obj* x_302; obj* x_303; 
lean::dec(x_1);
lean::dec(x_287);
lean::dec(x_285);
x_299 = lean::cnstr_get(x_291, 0);
lean::inc(x_299);
if (lean::is_shared(x_291)) {
 lean::dec(x_291);
 x_301 = lean::box(0);
} else {
 lean::cnstr_release(x_291, 0);
 x_301 = x_291;
}
if (lean::is_scalar(x_301)) {
 x_302 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_302 = x_301;
 lean::cnstr_set_tag(x_301, 0);
}
lean::cnstr_set(x_302, 0, x_299);
if (lean::is_scalar(x_295)) {
 x_303 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_303 = x_295;
 lean::cnstr_set_tag(x_295, 0);
}
lean::cnstr_set(x_303, 0, x_302);
lean::cnstr_set(x_303, 1, x_293);
x_3 = x_303;
goto lbl_4;
}
else
{
obj* x_304; obj* x_306; obj* x_307; obj* x_309; 
if (lean::is_shared(x_291)) {
 lean::dec(x_291);
 x_304 = lean::box(0);
} else {
 lean::cnstr_release(x_291, 0);
 x_304 = x_291;
}
lean::inc(x_1);
x_306 = l_lean_ir_var_defined(x_285, x_1, x_293);
x_307 = lean::cnstr_get(x_306, 0);
lean::inc(x_307);
x_309 = lean::cnstr_get(x_306, 1);
lean::inc(x_309);
lean::dec(x_306);
if (lean::obj_tag(x_307) == 0)
{
obj* x_314; obj* x_317; obj* x_318; 
lean::dec(x_1);
lean::dec(x_287);
x_314 = lean::cnstr_get(x_307, 0);
lean::inc(x_314);
lean::dec(x_307);
if (lean::is_scalar(x_304)) {
 x_317 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_317 = x_304;
 lean::cnstr_set_tag(x_304, 0);
}
lean::cnstr_set(x_317, 0, x_314);
if (lean::is_scalar(x_295)) {
 x_318 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_318 = x_295;
 lean::cnstr_set_tag(x_295, 0);
}
lean::cnstr_set(x_318, 0, x_317);
lean::cnstr_set(x_318, 1, x_309);
x_3 = x_318;
goto lbl_4;
}
else
{
obj* x_322; 
lean::dec(x_304);
lean::dec(x_307);
lean::dec(x_295);
x_322 = l_lean_ir_var_defined(x_287, x_1, x_309);
x_3 = x_322;
goto lbl_4;
}
}
}
default:
{
obj* x_323; obj* x_325; obj* x_327; obj* x_330; obj* x_331; obj* x_333; obj* x_335; 
x_323 = lean::cnstr_get(x_0, 0);
lean::inc(x_323);
x_325 = lean::cnstr_get(x_0, 1);
lean::inc(x_325);
x_327 = lean::cnstr_get(x_0, 2);
lean::inc(x_327);
lean::inc(x_1);
x_330 = l_lean_ir_var_defined(x_323, x_1, x_2);
x_331 = lean::cnstr_get(x_330, 0);
lean::inc(x_331);
x_333 = lean::cnstr_get(x_330, 1);
lean::inc(x_333);
if (lean::is_shared(x_330)) {
 lean::dec(x_330);
 x_335 = lean::box(0);
} else {
 lean::cnstr_release(x_330, 0);
 lean::cnstr_release(x_330, 1);
 x_335 = x_330;
}
if (lean::obj_tag(x_331) == 0)
{
obj* x_339; obj* x_341; obj* x_342; obj* x_343; 
lean::dec(x_327);
lean::dec(x_1);
lean::dec(x_325);
x_339 = lean::cnstr_get(x_331, 0);
lean::inc(x_339);
if (lean::is_shared(x_331)) {
 lean::dec(x_331);
 x_341 = lean::box(0);
} else {
 lean::cnstr_release(x_331, 0);
 x_341 = x_331;
}
if (lean::is_scalar(x_341)) {
 x_342 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_342 = x_341;
 lean::cnstr_set_tag(x_341, 0);
}
lean::cnstr_set(x_342, 0, x_339);
if (lean::is_scalar(x_335)) {
 x_343 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_343 = x_335;
 lean::cnstr_set_tag(x_335, 0);
}
lean::cnstr_set(x_343, 0, x_342);
lean::cnstr_set(x_343, 1, x_333);
x_3 = x_343;
goto lbl_4;
}
else
{
obj* x_344; obj* x_346; obj* x_347; obj* x_349; 
if (lean::is_shared(x_331)) {
 lean::dec(x_331);
 x_344 = lean::box(0);
} else {
 lean::cnstr_release(x_331, 0);
 x_344 = x_331;
}
lean::inc(x_1);
x_346 = l_lean_ir_var_defined(x_325, x_1, x_333);
x_347 = lean::cnstr_get(x_346, 0);
lean::inc(x_347);
x_349 = lean::cnstr_get(x_346, 1);
lean::inc(x_349);
lean::dec(x_346);
if (lean::obj_tag(x_347) == 0)
{
obj* x_354; obj* x_357; obj* x_358; 
lean::dec(x_327);
lean::dec(x_1);
x_354 = lean::cnstr_get(x_347, 0);
lean::inc(x_354);
lean::dec(x_347);
if (lean::is_scalar(x_344)) {
 x_357 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_357 = x_344;
 lean::cnstr_set_tag(x_344, 0);
}
lean::cnstr_set(x_357, 0, x_354);
if (lean::is_scalar(x_335)) {
 x_358 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_358 = x_335;
 lean::cnstr_set_tag(x_335, 0);
}
lean::cnstr_set(x_358, 0, x_357);
lean::cnstr_set(x_358, 1, x_349);
x_3 = x_358;
goto lbl_4;
}
else
{
obj* x_362; 
lean::dec(x_335);
lean::dec(x_344);
lean::dec(x_347);
x_362 = l_lean_ir_var_defined(x_327, x_1, x_349);
x_3 = x_362;
goto lbl_4;
}
}
}
}
lbl_4:
{
obj* x_363; obj* x_365; obj* x_367; 
x_363 = lean::cnstr_get(x_3, 0);
lean::inc(x_363);
x_365 = lean::cnstr_get(x_3, 1);
lean::inc(x_365);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_367 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_367 = x_3;
}
if (lean::obj_tag(x_363) == 0)
{
obj* x_368; obj* x_370; obj* x_371; uint8 x_372; obj* x_373; obj* x_375; obj* x_376; obj* x_377; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; obj* x_387; 
x_368 = lean::cnstr_get(x_363, 0);
lean::inc(x_368);
if (lean::is_shared(x_363)) {
 lean::dec(x_363);
 x_370 = lean::box(0);
} else {
 lean::cnstr_release(x_363, 0);
 x_370 = x_363;
}
x_371 = l_lean_ir_instr_to__format___main(x_0);
x_372 = 0;
x_373 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_373);
x_375 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_375, 0, x_373);
lean::cnstr_set(x_375, 1, x_371);
lean::cnstr_set_scalar(x_375, sizeof(void*)*2, x_372);
x_376 = x_375;
x_377 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_377);
x_379 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_379, 0, x_376);
lean::cnstr_set(x_379, 1, x_377);
lean::cnstr_set_scalar(x_379, sizeof(void*)*2, x_372);
x_380 = x_379;
x_381 = lean::box(1);
x_382 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_382, 0, x_380);
lean::cnstr_set(x_382, 1, x_381);
lean::cnstr_set_scalar(x_382, sizeof(void*)*2, x_372);
x_383 = x_382;
x_384 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_384, 0, x_383);
lean::cnstr_set(x_384, 1, x_368);
lean::cnstr_set_scalar(x_384, sizeof(void*)*2, x_372);
x_385 = x_384;
if (lean::is_scalar(x_370)) {
 x_386 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_386 = x_370;
 lean::cnstr_set_tag(x_370, 0);
}
lean::cnstr_set(x_386, 0, x_385);
if (lean::is_scalar(x_367)) {
 x_387 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_387 = x_367;
 lean::cnstr_set_tag(x_367, 0);
}
lean::cnstr_set(x_387, 0, x_386);
lean::cnstr_set(x_387, 1, x_365);
return x_387;
}
else
{
obj* x_389; 
lean::dec(x_0);
if (lean::is_scalar(x_367)) {
 x_389 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_389 = x_367;
 lean::cnstr_set_tag(x_367, 0);
}
lean::cnstr_set(x_389, 0, x_363);
lean::cnstr_set(x_389, 1, x_365);
return x_389;
}
}
}
}
obj* l_lean_ir_terminator_valid__ssa(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = l_lean_ir_var_defined(x_6, x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_3 = x_9;
x_4 = x_11;
goto lbl_5;
}
case 1:
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
x_16 = l_lean_ir_var_defined(x_14, x_1, x_2);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_3 = x_17;
x_4 = x_19;
goto lbl_5;
}
default:
{
obj* x_23; 
lean::dec(x_1);
x_23 = l_lean_ir_var_declare___closed__1;
lean::inc(x_23);
x_3 = x_23;
x_4 = x_2;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_25; obj* x_27; obj* x_28; uint8 x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_25 = lean::cnstr_get(x_3, 0);
lean::inc(x_25);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_27 = x_3;
}
x_28 = l_lean_ir_terminator_to__format___main(x_0);
x_29 = 0;
x_30 = l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_30);
x_32 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_28);
lean::cnstr_set_scalar(x_32, sizeof(void*)*2, x_29);
x_33 = x_32;
x_34 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_34);
x_36 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_36, 0, x_33);
lean::cnstr_set(x_36, 1, x_34);
lean::cnstr_set_scalar(x_36, sizeof(void*)*2, x_29);
x_37 = x_36;
x_38 = lean::box(1);
x_39 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
lean::cnstr_set_scalar(x_39, sizeof(void*)*2, x_29);
x_40 = x_39;
x_41 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_25);
lean::cnstr_set_scalar(x_41, sizeof(void*)*2, x_29);
x_42 = x_41;
if (lean::is_scalar(x_27)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_27;
 lean::cnstr_set_tag(x_27, 0);
}
lean::cnstr_set(x_43, 0, x_42);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_4);
return x_44;
}
else
{
obj* x_46; 
lean::dec(x_0);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_3);
lean::cnstr_set(x_46, 1, x_4);
return x_46;
}
}
}
}
obj* l_rbnode_find__core___main___at_lean_ir_phi_predecessors___spec__3(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_16; uint8 x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_22; uint8 x_23; 
lean::dec(x_5);
lean::inc(x_1);
lean::inc(x_7);
x_22 = l_lean_name_quick__lt___main(x_7, x_1);
x_23 = lean::unbox(x_22);
lean::dec(x_22);
if (x_23 == 0)
{
obj* x_27; obj* x_28; 
lean::dec(x_1);
lean::dec(x_11);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_7);
lean::cnstr_set(x_27, 1, x_9);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
else
{
lean::dec(x_9);
lean::dec(x_7);
x_0 = x_11;
goto _start;
}
}
else
{
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_11);
x_0 = x_5;
goto _start;
}
}
default:
{
obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_47; uint8 x_48; 
x_36 = lean::cnstr_get(x_0, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_0, 1);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_0, 2);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_0, 3);
lean::inc(x_42);
lean::dec(x_0);
lean::inc(x_38);
lean::inc(x_1);
x_47 = l_lean_name_quick__lt___main(x_1, x_38);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_53; uint8 x_54; 
lean::dec(x_36);
lean::inc(x_1);
lean::inc(x_38);
x_53 = l_lean_name_quick__lt___main(x_38, x_1);
x_54 = lean::unbox(x_53);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_58; obj* x_59; 
lean::dec(x_1);
lean::dec(x_42);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_38);
lean::cnstr_set(x_58, 1, x_40);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_58);
return x_59;
}
else
{
lean::dec(x_38);
lean::dec(x_40);
x_0 = x_42;
goto _start;
}
}
else
{
lean::dec(x_38);
lean::dec(x_40);
lean::dec(x_42);
x_0 = x_36;
goto _start;
}
}
}
}
}
obj* l_rbmap_find__core___main___at_lean_ir_phi_predecessors___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find__core___main___at_lean_ir_phi_predecessors___spec__3(x_0, x_1);
return x_2;
}
}
obj* l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find__core___main___at_lean_ir_phi_predecessors___spec__3(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_8; obj* x_11; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_7 = x_2;
}
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_11 = x_7;
 lean::cnstr_set_tag(x_7, 1);
}
lean::cnstr_set(x_11, 0, x_8);
return x_11;
}
}
}
obj* l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; uint8 x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_9);
lean::dec(x_7);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_13;
 lean::cnstr_set_tag(x_13, 1);
}
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_11);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
x_27 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_13;
 lean::cnstr_set_tag(x_13, 1);
}
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_7);
lean::cnstr_set(x_28, 2, x_9);
lean::cnstr_set(x_28, 3, x_27);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_13;
 lean::cnstr_set_tag(x_13, 1);
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; uint8 x_43; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
lean::inc(x_33);
lean::inc(x_1);
x_42 = l_lean_name_quick__lt___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; uint8 x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = l_lean_name_quick__lt___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_33);
lean::dec(x_35);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_39;
 lean::cnstr_set_tag(x_39, 2);
}
lean::cnstr_set(x_52, 0, x_31);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_37);
return x_52;
}
else
{
uint8 x_54; 
lean::inc(x_37);
x_54 = l_rbnode_get__color___main___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_37, x_1, x_2);
x_57 = l_rbnode_balance2__node___main___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_39;
 lean::cnstr_set_tag(x_39, 2);
}
lean::cnstr_set(x_59, 0, x_31);
lean::cnstr_set(x_59, 1, x_33);
lean::cnstr_set(x_59, 2, x_35);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
else
{
uint8 x_61; 
lean::inc(x_31);
x_61 = l_rbnode_get__color___main___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_31, x_1, x_2);
x_64 = l_rbnode_balance1__node___main___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_39;
 lean::cnstr_set_tag(x_39, 2);
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_35);
lean::cnstr_set(x_66, 3, x_37);
return x_66;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_ir_phi_predecessors___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_1);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_17; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::dec(x_2);
lean::inc(x_10);
lean::inc(x_3);
x_17 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(x_3, x_10);
if (lean::obj_tag(x_17) == 0)
{
obj* x_22; uint8 x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_17);
lean::dec(x_12);
lean::dec(x_1);
lean::dec(x_3);
x_22 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_10);
x_23 = 0;
x_24 = l_lean_ir_var_defined___closed__1;
lean::inc(x_24);
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_22);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_23);
x_27 = x_26;
x_28 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_27);
lean::cnstr_set(x_30, 1, x_28);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_23);
x_31 = x_30;
x_32 = l_lean_ir_phi_to__format___main(x_0);
x_33 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
lean::cnstr_set_scalar(x_33, sizeof(void*)*2, x_23);
x_34 = x_33;
x_35 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_35);
x_37 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_37, 0, x_34);
lean::cnstr_set(x_37, 1, x_35);
lean::cnstr_set_scalar(x_37, sizeof(void*)*2, x_23);
x_38 = x_37;
x_39 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_4);
return x_40;
}
else
{
obj* x_42; obj* x_47; uint8 x_48; 
lean::dec(x_10);
x_42 = lean::cnstr_get(x_17, 0);
lean::inc(x_42);
lean::dec(x_17);
lean::inc(x_42);
lean::inc(x_1);
x_47 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_1, x_42);
x_48 = l_option_is__some___main___rarg(x_47);
if (x_48 == 0)
{
obj* x_49; obj* x_50; 
x_49 = lean::box(0);
x_50 = l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5(x_1, x_42, x_49);
x_1 = x_50;
x_2 = x_12;
goto _start;
}
else
{
obj* x_56; uint8 x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_12);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_42);
x_56 = l_lean_ir_phi_to__format___main(x_0);
x_57 = 0;
x_58 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__2;
lean::inc(x_58);
x_60 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_56);
lean::cnstr_set_scalar(x_60, sizeof(void*)*2, x_57);
x_61 = x_60;
x_62 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_62);
x_64 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_64, 0, x_61);
lean::cnstr_set(x_64, 1, x_62);
lean::cnstr_set_scalar(x_64, sizeof(void*)*2, x_57);
x_65 = x_64;
x_66 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_4);
return x_67;
}
}
}
}
}
obj* _init_l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("' at '");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("multiple predecessors at '");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_phi_predecessors(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = l_lean_ir_mk__blockid__set;
lean::inc(x_5);
x_7 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7(x_0, x_5, x_3, x_1, x_2);
return x_7;
}
}
obj* l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_4; obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = 1;
x_5 = lean::box(x_4);
return x_5;
}
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_14; uint8 x_15; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 3);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_0);
x_14 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_0, x_8);
x_15 = l_option_to__bool___main___rarg(x_14);
if (x_15 == 0)
{
lean::dec(x_6);
if (x_15 == 0)
{
obj* x_19; 
lean::dec(x_10);
lean::dec(x_0);
x_19 = lean::box(x_15);
return x_19;
}
else
{
x_1 = x_10;
goto _start;
}
}
else
{
obj* x_22; uint8 x_23; 
lean::inc(x_0);
x_22 = l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(x_0, x_6);
x_23 = lean::unbox(x_22);
if (x_23 == 0)
{
lean::dec(x_10);
lean::dec(x_0);
return x_22;
}
else
{
lean::dec(x_22);
x_1 = x_10;
goto _start;
}
}
}
default:
{
obj* x_28; obj* x_30; obj* x_32; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_1, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_1, 1);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_1, 3);
lean::inc(x_32);
lean::dec(x_1);
lean::inc(x_0);
x_36 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_0, x_30);
x_37 = l_option_to__bool___main___rarg(x_36);
if (x_37 == 0)
{
lean::dec(x_28);
if (x_37 == 0)
{
obj* x_41; 
lean::dec(x_0);
lean::dec(x_32);
x_41 = lean::box(x_37);
return x_41;
}
else
{
x_1 = x_32;
goto _start;
}
}
else
{
obj* x_44; uint8 x_45; 
lean::inc(x_0);
x_44 = l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(x_0, x_28);
x_45 = lean::unbox(x_44);
if (x_45 == 0)
{
lean::dec(x_0);
lean::dec(x_32);
return x_44;
}
else
{
lean::dec(x_44);
x_1 = x_32;
goto _start;
}
}
}
}
}
}
obj* l_rbtree_subset___at_lean_ir_phis_check__predecessors___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(x_1, x_0);
return x_2;
}
}
obj* l_rbtree_seteq___at_lean_ir_phis_check__predecessors___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; uint8 x_5; 
lean::inc(x_0);
lean::inc(x_1);
x_4 = l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(x_1, x_0);
x_5 = lean::unbox(x_4);
if (x_5 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_4;
}
else
{
obj* x_9; 
lean::dec(x_4);
x_9 = l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(x_0, x_1);
return x_9;
}
}
}
obj* l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_18; obj* x_19; obj* x_21; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_2);
lean::inc(x_8);
x_18 = l_lean_ir_phi_predecessors(x_8, x_2, x_3);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_0);
x_25 = lean::cnstr_get(x_19, 0);
lean::inc(x_25);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_27 = x_19;
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
 lean::cnstr_set_tag(x_27, 0);
}
lean::cnstr_set(x_28, 0, x_25);
x_13 = x_28;
x_14 = x_21;
goto lbl_15;
}
else
{
obj* x_29; obj* x_31; 
x_29 = lean::cnstr_get(x_19, 0);
lean::inc(x_29);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_31 = x_19;
}
if (lean::obj_tag(x_0) == 0)
{
obj* x_33; obj* x_34; 
lean::dec(x_0);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_29);
if (lean::is_scalar(x_31)) {
 x_34 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_34 = x_31;
 lean::cnstr_set_tag(x_31, 1);
}
lean::cnstr_set(x_34, 0, x_33);
x_13 = x_34;
x_14 = x_21;
goto lbl_15;
}
else
{
obj* x_35; obj* x_37; uint8 x_38; 
x_35 = lean::cnstr_get(x_0, 0);
lean::inc(x_35);
x_37 = l_rbtree_seteq___at_lean_ir_phis_check__predecessors___spec__1(x_35, x_29);
x_38 = lean::unbox(x_37);
lean::dec(x_37);
if (x_38 == 0)
{
obj* x_41; obj* x_43; uint8 x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_0);
x_41 = lean::cnstr_get(x_8, 0);
lean::inc(x_41);
x_43 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_41);
x_44 = 0;
x_45 = l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___closed__1;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_43);
lean::cnstr_set_scalar(x_47, sizeof(void*)*2, x_44);
x_48 = x_47;
x_49 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1;
lean::inc(x_49);
x_51 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set(x_51, 1, x_49);
lean::cnstr_set_scalar(x_51, sizeof(void*)*2, x_44);
x_52 = x_51;
lean::inc(x_8);
x_54 = l_lean_ir_phi_to__format___main(x_8);
x_55 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*2, x_44);
x_56 = x_55;
x_57 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_57);
lean::cnstr_set_scalar(x_59, sizeof(void*)*2, x_44);
x_60 = x_59;
if (lean::is_scalar(x_31)) {
 x_61 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_61 = x_31;
 lean::cnstr_set_tag(x_31, 0);
}
lean::cnstr_set(x_61, 0, x_60);
x_13 = x_61;
x_14 = x_21;
goto lbl_15;
}
else
{
obj* x_62; 
if (lean::is_scalar(x_31)) {
 x_62 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_62 = x_31;
 lean::cnstr_set_tag(x_31, 1);
}
lean::cnstr_set(x_62, 0, x_0);
x_13 = x_62;
x_14 = x_21;
goto lbl_15;
}
}
}
lbl_15:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_65; obj* x_67; obj* x_68; uint8 x_69; obj* x_70; obj* x_72; obj* x_73; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_10);
lean::dec(x_2);
x_65 = lean::cnstr_get(x_13, 0);
lean::inc(x_65);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_67 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_67 = x_13;
}
x_68 = l_lean_ir_phi_to__format___main(x_8);
x_69 = 0;
x_70 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_70);
x_72 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_72, 0, x_70);
lean::cnstr_set(x_72, 1, x_68);
lean::cnstr_set_scalar(x_72, sizeof(void*)*2, x_69);
x_73 = x_72;
x_74 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_74);
x_76 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_74);
lean::cnstr_set_scalar(x_76, sizeof(void*)*2, x_69);
x_77 = x_76;
x_78 = lean::box(1);
x_79 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_78);
lean::cnstr_set_scalar(x_79, sizeof(void*)*2, x_69);
x_80 = x_79;
x_81 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_65);
lean::cnstr_set_scalar(x_81, sizeof(void*)*2, x_69);
x_82 = x_81;
if (lean::is_scalar(x_67)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_67;
 lean::cnstr_set_tag(x_67, 0);
}
lean::cnstr_set(x_83, 0, x_82);
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_14);
return x_84;
}
else
{
lean::dec(x_8);
if (lean::obj_tag(x_13) == 0)
{
obj* x_88; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_10);
lean::dec(x_2);
x_88 = lean::cnstr_get(x_13, 0);
lean::inc(x_88);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_90 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_90 = x_13;
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_91 = x_90;
 lean::cnstr_set_tag(x_90, 0);
}
lean::cnstr_set(x_91, 0, x_88);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_14);
return x_92;
}
else
{
obj* x_93; 
x_93 = lean::cnstr_get(x_13, 0);
lean::inc(x_93);
lean::dec(x_13);
x_0 = x_93;
x_1 = x_10;
x_3 = x_14;
goto _start;
}
}
}
}
}
}
obj* _init_l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("missing predecessor '");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_phis_check__predecessors(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_3 = lean::box(0);
x_4 = l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4(x_3, x_0, x_1, x_2);
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
if (lean::obj_tag(x_5) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_12 = x_5;
}
if (lean::is_scalar(x_12)) {
 x_13 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_13 = x_12;
 lean::cnstr_set_tag(x_12, 0);
}
lean::cnstr_set(x_13, 0, x_10);
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_9;
 lean::cnstr_set_tag(x_9, 0);
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
else
{
obj* x_16; obj* x_18; 
lean::dec(x_5);
x_16 = l_lean_ir_var_declare___closed__1;
lean::inc(x_16);
if (lean::is_scalar(x_9)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_9;
 lean::cnstr_set_tag(x_9, 0);
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_7);
return x_18;
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_var_declare___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = l_lean_ir_phi_valid__ssa(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
 lean::cnstr_set_tag(x_24, 0);
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
 lean::cnstr_set_tag(x_19, 0);
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_var_declare___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = l_lean_ir_instr_valid__ssa(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
 lean::cnstr_set_tag(x_24, 0);
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
 lean::cnstr_set_tag(x_19, 0);
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_lean_ir_block_valid__ssa__core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_10; obj* x_11; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::inc(x_1);
lean::inc(x_6);
x_10 = l_lean_ir_phis_check__predecessors(x_6, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_6);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_20 = x_11;
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
 lean::cnstr_set_tag(x_20, 0);
}
lean::cnstr_set(x_21, 0, x_18);
x_3 = x_21;
x_4 = x_13;
goto lbl_5;
}
else
{
obj* x_22; obj* x_24; obj* x_25; obj* x_27; 
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_22 = x_11;
}
lean::inc(x_1);
x_24 = l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__1(x_6, x_1, x_13);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_31; obj* x_34; 
lean::dec(x_1);
x_31 = lean::cnstr_get(x_25, 0);
lean::inc(x_31);
lean::dec(x_25);
if (lean::is_scalar(x_22)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_22;
 lean::cnstr_set_tag(x_22, 0);
}
lean::cnstr_set(x_34, 0, x_31);
x_3 = x_34;
x_4 = x_27;
goto lbl_5;
}
else
{
obj* x_36; obj* x_39; obj* x_40; obj* x_42; 
lean::dec(x_25);
x_36 = lean::cnstr_get(x_0, 2);
lean::inc(x_36);
lean::inc(x_1);
x_39 = l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__2(x_36, x_1, x_27);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
if (lean::obj_tag(x_40) == 0)
{
obj* x_46; obj* x_49; 
lean::dec(x_1);
x_46 = lean::cnstr_get(x_40, 0);
lean::inc(x_46);
lean::dec(x_40);
if (lean::is_scalar(x_22)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_22;
 lean::cnstr_set_tag(x_22, 0);
}
lean::cnstr_set(x_49, 0, x_46);
x_3 = x_49;
x_4 = x_42;
goto lbl_5;
}
else
{
obj* x_52; obj* x_54; obj* x_55; obj* x_57; 
lean::dec(x_22);
lean::dec(x_40);
x_52 = lean::cnstr_get(x_0, 3);
lean::inc(x_52);
x_54 = l_lean_ir_terminator_valid__ssa(x_52, x_1, x_42);
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
x_3 = x_55;
x_4 = x_57;
goto lbl_5;
}
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_60; obj* x_62; obj* x_63; obj* x_66; uint8 x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_60 = lean::cnstr_get(x_3, 0);
lean::inc(x_60);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_62 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_62 = x_3;
}
x_63 = lean::cnstr_get(x_0, 0);
lean::inc(x_63);
lean::dec(x_0);
x_66 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_63);
x_67 = 0;
x_68 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_68);
x_70 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_66);
lean::cnstr_set_scalar(x_70, sizeof(void*)*2, x_67);
x_71 = x_70;
x_72 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_72);
x_74 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_74, 0, x_71);
lean::cnstr_set(x_74, 1, x_72);
lean::cnstr_set_scalar(x_74, sizeof(void*)*2, x_67);
x_75 = x_74;
x_76 = lean::box(1);
x_77 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_77, 0, x_75);
lean::cnstr_set(x_77, 1, x_76);
lean::cnstr_set_scalar(x_77, sizeof(void*)*2, x_67);
x_78 = x_77;
x_79 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_60);
lean::cnstr_set_scalar(x_79, sizeof(void*)*2, x_67);
x_80 = x_79;
if (lean::is_scalar(x_62)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_62;
 lean::cnstr_set_tag(x_62, 0);
}
lean::cnstr_set(x_81, 0, x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_4);
return x_82;
}
else
{
obj* x_84; 
lean::dec(x_0);
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_3);
lean::cnstr_set(x_84, 1, x_4);
return x_84;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_var_declare___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = l_lean_ir_arg_define(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
 lean::cnstr_set_tag(x_24, 0);
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
 lean::cnstr_set_tag(x_19, 0);
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_8 = x_1;
}
if (lean::is_scalar(x_8)) {
 x_9 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_9 = x_8;
 lean::cnstr_set_tag(x_8, 0);
}
lean::cnstr_set(x_9, 0, x_6);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
else
{
obj* x_11; obj* x_14; 
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_14 = lean::apply_3(x_0, x_11, x_2, x_3);
return x_14;
}
}
}
obj* l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2___rarg), 4, 0);
return x_4;
}
}
obj* l_reader__t_bind___at_lean_ir_decl_valid__ssa___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_11; 
lean::inc(x_2);
x_5 = lean::apply_2(x_0, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_3(x_1, x_6, x_2, x_8);
return x_11;
}
}
obj* l_reader__t_bind___at_lean_ir_decl_valid__ssa___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_ir_decl_valid__ssa___spec__3___rarg), 4, 0);
return x_4;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_var_declare___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = l_lean_ir_block_valid__ssa__core(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
 lean::cnstr_set_tag(x_24, 0);
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
 lean::cnstr_set_tag(x_19, 0);
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_lean_ir_decl_valid__ssa(obj* x_0) {
_start:
{
obj* x_1; obj* x_4; 
lean::inc(x_0);
x_4 = l_lean_ir_decl_var2blockid(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_1 = x_5;
goto lbl_2;
}
else
{
obj* x_8; obj* x_10; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
}
if (lean::obj_tag(x_0) == 0)
{
obj* x_12; 
lean::dec(x_0);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_10;
 lean::cnstr_set_tag(x_10, 1);
}
lean::cnstr_set(x_12, 0, x_8);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_17; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_13, 1);
lean::inc(x_17);
lean::dec(x_13);
if (lean::obj_tag(x_15) == 0)
{
obj* x_23; 
lean::dec(x_17);
lean::dec(x_15);
lean::dec(x_0);
if (lean::is_scalar(x_10)) {
 x_23 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_23 = x_10;
 lean::cnstr_set_tag(x_10, 1);
}
lean::cnstr_set(x_23, 0, x_8);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_34; 
x_24 = lean::cnstr_get(x_15, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_15, 1);
lean::inc(x_26);
lean::dec(x_15);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__1), 3, 1);
lean::closure_set(x_29, 0, x_17);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_decl_valid__ssa___lambda__1), 4, 1);
lean::closure_set(x_30, 0, x_24);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2___rarg), 4, 1);
lean::closure_set(x_31, 0, x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_ir_decl_valid__ssa___spec__3___rarg), 4, 2);
lean::closure_set(x_32, 0, x_29);
lean::closure_set(x_32, 1, x_31);
lean::inc(x_8);
x_34 = l_lean_ir_ssa__valid__m_run___rarg(x_32, x_8);
if (lean::obj_tag(x_34) == 0)
{
obj* x_38; 
lean::dec(x_26);
lean::dec(x_10);
lean::dec(x_8);
x_38 = lean::cnstr_get(x_34, 0);
lean::inc(x_38);
lean::dec(x_34);
x_1 = x_38;
goto lbl_2;
}
else
{
obj* x_42; obj* x_44; 
lean::dec(x_34);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__4), 3, 1);
lean::closure_set(x_42, 0, x_26);
lean::inc(x_8);
x_44 = l_lean_ir_ssa__valid__m_run___rarg(x_42, x_8);
if (lean::obj_tag(x_44) == 0)
{
obj* x_47; 
lean::dec(x_10);
lean::dec(x_8);
x_47 = lean::cnstr_get(x_44, 0);
lean::inc(x_47);
lean::dec(x_44);
x_1 = x_47;
goto lbl_2;
}
else
{
obj* x_52; 
lean::dec(x_0);
lean::dec(x_44);
if (lean::is_scalar(x_10)) {
 x_52 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_52 = x_10;
 lean::cnstr_set_tag(x_10, 1);
}
lean::cnstr_set(x_52, 0, x_8);
return x_52;
}
}
}
}
}
lbl_2:
{
obj* x_53; obj* x_54; obj* x_57; uint8 x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_53 = l_lean_ir_decl_header___main(x_0);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
lean::dec(x_53);
x_57 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_54);
x_58 = 0;
x_59 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_59);
x_61 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_57);
lean::cnstr_set_scalar(x_61, sizeof(void*)*2, x_58);
x_62 = x_61;
x_63 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_63);
x_65 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_65, 0, x_62);
lean::cnstr_set(x_65, 1, x_63);
lean::cnstr_set_scalar(x_65, sizeof(void*)*2, x_58);
x_66 = x_65;
x_67 = lean::box(1);
x_68 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set(x_68, 1, x_67);
lean::cnstr_set_scalar(x_68, sizeof(void*)*2, x_58);
x_69 = x_68;
x_70 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_1);
lean::cnstr_set_scalar(x_70, sizeof(void*)*2, x_58);
x_71 = x_70;
x_72 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
return x_72;
}
}
}
obj* l_lean_ir_decl_valid__ssa___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_1);
x_5 = l_lean_ir_block_valid__ssa__core(x_0, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_ir_blockid__check__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_ir_blockid__check__m_run___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; 
x_1 = l_lean_ir_mk__blockid__set;
lean::inc(x_1);
x_3 = lean::apply_1(x_0, x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_ir_blockid__check__m_run(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_blockid__check__m_run___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_ir_block_declare(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_7; uint8 x_8; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
lean::inc(x_2);
lean::inc(x_1);
x_7 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_1, x_2);
x_8 = l_option_is__some___main___rarg(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_13; 
x_9 = lean::box(0);
x_10 = l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5(x_1, x_2, x_9);
x_11 = l_lean_ir_var_declare___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_10);
return x_13;
}
else
{
obj* x_14; uint8 x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_14 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_2);
x_15 = 0;
x_16 = l_lean_ir_block_declare___closed__1;
lean::inc(x_16);
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_14);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_15);
x_19 = x_18;
x_20 = l_lean_ir_block_declare___closed__2;
lean::inc(x_20);
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_20);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_15);
x_23 = x_22;
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_1);
return x_25;
}
}
}
obj* _init_l_lean_ir_block_declare___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("block label '");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_block_declare___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("' has been used more than once");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_blockid_defined(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; uint8 x_5; 
lean::inc(x_0);
lean::inc(x_1);
x_4 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_1, x_0);
x_5 = l_option_is__some___main___rarg(x_4);
if (x_5 == 0)
{
obj* x_6; uint8 x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_6 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_0);
x_7 = 0;
x_8 = l_lean_ir_blockid_defined___closed__1;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_6);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_7);
x_11 = x_10;
x_12 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_12);
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_12);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_7);
x_15 = x_14;
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_1);
return x_17;
}
else
{
obj* x_19; obj* x_21; 
lean::dec(x_0);
x_19 = l_lean_ir_var_declare___closed__1;
lean::inc(x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_1);
return x_21;
}
}
}
obj* _init_l_lean_ir_blockid_defined___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("unknown basic block '");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_terminator_check__blockids___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; 
lean::dec(x_0);
x_3 = l_lean_ir_var_declare___closed__1;
lean::inc(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_14; obj* x_16; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = l_lean_ir_blockid_defined(x_6, x_1);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
if (lean::obj_tag(x_12) == 0)
{
obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_8);
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_20 = x_12;
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
 lean::cnstr_set_tag(x_20, 0);
}
lean::cnstr_set(x_21, 0, x_18);
if (lean::is_scalar(x_16)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_16;
 lean::cnstr_set_tag(x_16, 0);
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_14);
return x_22;
}
else
{
lean::dec(x_12);
lean::dec(x_16);
x_0 = x_8;
x_1 = x_14;
goto _start;
}
}
}
}
obj* l_lean_ir_terminator_check__blockids(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_5; 
x_5 = l_lean_ir_var_declare___closed__1;
lean::inc(x_5);
x_2 = x_5;
x_3 = x_1;
goto lbl_4;
}
case 1:
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = l_list_mmap_x_27___main___at_lean_ir_terminator_check__blockids___spec__1(x_7, x_1);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_2 = x_10;
x_3 = x_12;
goto lbl_4;
}
default:
{
obj* x_15; obj* x_17; obj* x_18; obj* x_20; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
x_17 = l_lean_ir_blockid_defined(x_15, x_1);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
x_2 = x_18;
x_3 = x_20;
goto lbl_4;
}
}
lbl_4:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_23; obj* x_25; obj* x_26; uint8 x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_23 = lean::cnstr_get(x_2, 0);
lean::inc(x_23);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_25 = x_2;
}
x_26 = l_lean_ir_terminator_to__format___main(x_0);
x_27 = 0;
x_28 = l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_26);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_27);
x_31 = x_30;
x_32 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_32);
x_34 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_34, 0, x_31);
lean::cnstr_set(x_34, 1, x_32);
lean::cnstr_set_scalar(x_34, sizeof(void*)*2, x_27);
x_35 = x_34;
x_36 = lean::box(1);
x_37 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_36);
lean::cnstr_set_scalar(x_37, sizeof(void*)*2, x_27);
x_38 = x_37;
x_39 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_23);
lean::cnstr_set_scalar(x_39, sizeof(void*)*2, x_27);
x_40 = x_39;
if (lean::is_scalar(x_25)) {
 x_41 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_41 = x_25;
 lean::cnstr_set_tag(x_25, 0);
}
lean::cnstr_set(x_41, 0, x_40);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_3);
return x_42;
}
else
{
obj* x_44; 
lean::dec(x_0);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_2);
lean::cnstr_set(x_44, 1, x_3);
return x_44;
}
}
}
}
obj* l_lean_ir_block_check__blockids(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 3);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_ir_terminator_check__blockids(x_2, x_1);
return x_5;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_check__blockids___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; 
lean::dec(x_0);
x_3 = l_lean_ir_var_declare___closed__1;
lean::inc(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_14; obj* x_16; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = l_lean_ir_block_declare(x_6, x_1);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
if (lean::obj_tag(x_12) == 0)
{
obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_8);
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_20 = x_12;
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
 lean::cnstr_set_tag(x_20, 0);
}
lean::cnstr_set(x_21, 0, x_18);
if (lean::is_scalar(x_16)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_16;
 lean::cnstr_set_tag(x_16, 0);
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_14);
return x_22;
}
else
{
lean::dec(x_12);
lean::dec(x_16);
x_0 = x_8;
x_1 = x_14;
goto _start;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_check__blockids___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; 
lean::dec(x_0);
x_3 = l_lean_ir_var_declare___closed__1;
lean::inc(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_14; obj* x_16; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = l_lean_ir_block_check__blockids(x_6, x_1);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
if (lean::obj_tag(x_12) == 0)
{
obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_8);
x_18 = lean::cnstr_get(x_12, 0);
lean::inc(x_18);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_20 = x_12;
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
 lean::cnstr_set_tag(x_20, 0);
}
lean::cnstr_set(x_21, 0, x_18);
if (lean::is_scalar(x_16)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_16;
 lean::cnstr_set_tag(x_16, 0);
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_14);
return x_22;
}
else
{
lean::dec(x_12);
lean::dec(x_16);
x_0 = x_8;
x_1 = x_14;
goto _start;
}
}
}
}
obj* l_lean_ir_decl_check__blockids___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; 
lean::dec(x_0);
x_3 = l_lean_ir_var_declare___closed__1;
lean::inc(x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_8);
x_12 = l_list_mmap_x_27___main___at_lean_ir_decl_check__blockids___main___spec__1(x_8, x_1);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 x_17 = x_12;
}
if (lean::obj_tag(x_13) == 0)
{
obj* x_19; obj* x_21; obj* x_22; obj* x_25; uint8 x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_8);
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_21 = x_13;
}
x_22 = lean::cnstr_get(x_6, 0);
lean::inc(x_22);
lean::dec(x_6);
x_25 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_22);
x_26 = 0;
x_27 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_27);
x_29 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_26);
x_30 = x_29;
x_31 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_31);
x_33 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_33, 0, x_30);
lean::cnstr_set(x_33, 1, x_31);
lean::cnstr_set_scalar(x_33, sizeof(void*)*2, x_26);
x_34 = x_33;
x_35 = lean::box(1);
x_36 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
lean::cnstr_set_scalar(x_36, sizeof(void*)*2, x_26);
x_37 = x_36;
x_38 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_19);
lean::cnstr_set_scalar(x_38, sizeof(void*)*2, x_26);
x_39 = x_38;
if (lean::is_scalar(x_21)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_21;
 lean::cnstr_set_tag(x_21, 0);
}
lean::cnstr_set(x_40, 0, x_39);
if (lean::is_scalar(x_17)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_17;
 lean::cnstr_set_tag(x_17, 0);
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_15);
return x_41;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_46; 
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_42 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_42 = x_13;
}
x_43 = l_list_mmap_x_27___main___at_lean_ir_decl_check__blockids___main___spec__2(x_8, x_15);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_49; obj* x_52; obj* x_55; uint8 x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_49 = lean::cnstr_get(x_44, 0);
lean::inc(x_49);
lean::dec(x_44);
x_52 = lean::cnstr_get(x_6, 0);
lean::inc(x_52);
lean::dec(x_6);
x_55 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_52);
x_56 = 0;
x_57 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*2, x_56);
x_60 = x_59;
x_61 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_61);
x_63 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_63, 0, x_60);
lean::cnstr_set(x_63, 1, x_61);
lean::cnstr_set_scalar(x_63, sizeof(void*)*2, x_56);
x_64 = x_63;
x_65 = lean::box(1);
x_66 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_66, 0, x_64);
lean::cnstr_set(x_66, 1, x_65);
lean::cnstr_set_scalar(x_66, sizeof(void*)*2, x_56);
x_67 = x_66;
x_68 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_49);
lean::cnstr_set_scalar(x_68, sizeof(void*)*2, x_56);
x_69 = x_68;
if (lean::is_scalar(x_42)) {
 x_70 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_70 = x_42;
 lean::cnstr_set_tag(x_42, 0);
}
lean::cnstr_set(x_70, 0, x_69);
if (lean::is_scalar(x_17)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_17;
 lean::cnstr_set_tag(x_17, 0);
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_46);
return x_71;
}
else
{
obj* x_74; 
lean::dec(x_6);
lean::dec(x_42);
if (lean::is_scalar(x_17)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_17;
 lean::cnstr_set_tag(x_17, 0);
}
lean::cnstr_set(x_74, 0, x_44);
lean::cnstr_set(x_74, 1, x_46);
return x_74;
}
}
}
}
}
obj* l_lean_ir_decl_check__blockids(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_decl_check__blockids___main(x_0, x_1);
return x_2;
}
}
obj* l_except__t_bind__cont___at_lean_ir_check__blockids___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_0);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
}
if (lean::is_scalar(x_6)) {
 x_7 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_7 = x_6;
 lean::cnstr_set_tag(x_6, 0);
}
lean::cnstr_set(x_7, 0, x_4);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_2);
return x_8;
}
else
{
obj* x_9; obj* x_12; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::apply_2(x_0, x_9, x_2);
return x_12;
}
}
}
obj* l_except__t_bind__cont___at_lean_ir_check__blockids___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_check__blockids___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_state__t_bind___at_lean_ir_check__blockids___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_9; 
x_3 = lean::apply_1(x_0, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::apply_2(x_1, x_4, x_6);
return x_9;
}
}
obj* l_state__t_bind___at_lean_ir_check__blockids___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_bind___at_lean_ir_check__blockids___spec__2___rarg), 3, 0);
return x_4;
}
}
obj* l_lean_ir_check__blockids(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_decl_check__blockids), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = l_lean_ir_check__blockids___closed__1;
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_bind___at_lean_ir_check__blockids___spec__2___rarg), 3, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
x_5 = l_lean_ir_blockid__check__m_run___rarg(x_4);
return x_5;
}
}
obj* _init_l_lean_ir_check__blockids___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_check__blockids___lambda__1), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_check__blockids___spec__1___rarg), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_check__blockids___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
lean::inc(x_1);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_1);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
void initialize_init_lean_ir_instances();
void initialize_init_lean_ir_format();
static bool _G_initialized = false;
void initialize_init_lean_ir_ssa__check() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_ir_instances();
 initialize_init_lean_ir_format();
 l_lean_ir_ssa__pre__m = _init_l_lean_ir_ssa__pre__m();
 l_lean_ir_var_declare___closed__1 = _init_l_lean_ir_var_declare___closed__1();
 l_lean_ir_var_declare___closed__2 = _init_l_lean_ir_var_declare___closed__2();
 l_lean_ir_decl_declare__vars___main___closed__1 = _init_l_lean_ir_decl_declare__vars___main___closed__1();
 l_lean_ir_ssa__valid__m = _init_l_lean_ir_ssa__valid__m();
 l_lean_ir_var_defined___closed__1 = _init_l_lean_ir_var_defined___closed__1();
 l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1 = _init_l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1();
 l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__2 = _init_l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__2();
 l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___closed__1 = _init_l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___closed__1();
 l_lean_ir_blockid__check__m = _init_l_lean_ir_blockid__check__m();
 l_lean_ir_block_declare___closed__1 = _init_l_lean_ir_block_declare___closed__1();
 l_lean_ir_block_declare___closed__2 = _init_l_lean_ir_block_declare___closed__2();
 l_lean_ir_blockid_defined___closed__1 = _init_l_lean_ir_blockid_defined___closed__1();
 l_lean_ir_check__blockids___closed__1 = _init_l_lean_ir_check__blockids___closed__1();
}
