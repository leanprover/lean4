// Lean compiler output
// Module: init.lean.ir.ssa_check
// Imports: init.lean.ir.instances init.lean.ir.format
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
obj* l_lean_ir_check__blockids___closed__1;
extern obj* l_lean_ir_mk__var__set;
obj* l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(obj*, obj*);
obj* l_lean_ir_terminator_check__blockids(obj*, obj*);
obj* l_rbtree_seteq___at_lean_ir_phis_check__predecessors___spec__1(obj*, obj*);
obj* l_lean_ir_var_define(obj*, obj*, obj*);
extern obj* l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
obj* l_lean_ir_var_define___boxed(obj*, obj*, obj*);
obj* l_rbmap_find__core___main___at_lean_ir_var_defined___spec__2(obj*, obj*);
obj* l_lean_ir_terminator_to__format___main(obj*);
obj* l_lean_ir_arg_define___boxed(obj*, obj*, obj*);
obj* l_rbtree_subset___at_lean_ir_phis_check__predecessors___spec__2___boxed(obj*, obj*);
obj* l_reader__t_bind___at_lean_ir_decl_valid__ssa___spec__3___boxed(obj*, obj*);
obj* l_lean_ir_var_declare(obj*, obj*, obj*);
obj* l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_instr_to__format___main(obj*);
obj* l_rbnode_ins___main___at_lean_ir_var_define___spec__3___boxed(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_ir_blockid_defined___closed__1;
obj* l_lean_ir_ssa__valid__m;
obj* l_lean_ir_instr_declare__vars___main___boxed(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_check__blockids___main___spec__1(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_block_declare___closed__1;
obj* l_lean_ir_terminator_valid__ssa(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_ir_phi_valid__ssa(obj*, obj*, obj*);
obj* l_lean_ir_ssa__valid__m_run___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__2___boxed(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__3(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__2(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6___boxed(obj*, obj*, obj*);
obj* l_rbmap_find__core___main___at_lean_ir_var_defined___spec__2___boxed(obj*, obj*);
obj* l_lean_ir_phi_valid__ssa___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_var_declare___spec__5___boxed(obj*, obj*, obj*);
obj* l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(obj*);
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_ir_decl_valid__ssa___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_ir_instr_valid__ssa___boxed(obj*, obj*, obj*);
obj* l_rbtree_find___at_lean_ir_var_defined___spec__1___boxed(obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2___boxed(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_ir_ssa__pre__m;
obj* l_lean_ir_var_defined___closed__1;
obj* l_lean_ir_block_declare___closed__2;
obj* l_lean_ir_ssa__valid__m_run(obj*);
obj* l_rbnode_find__core___main___at_lean_ir_phi_predecessors___spec__3(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_var_declare___spec__3(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_blockid_defined(obj*, obj*);
obj* l_reader__t_bind___at_lean_ir_decl_valid__ssa___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5___boxed(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_ir_var_declare___spec__1(obj*, obj*);
uint8 l_option_to__bool___main___rarg(obj*);
obj* l_state__t_bind___at_lean_ir_check__blockids___spec__2(obj*, obj*);
obj* l_lean_ir_decl_check__blockids(obj*, obj*);
obj* l_lean_ir_phi_declare___boxed(obj*, obj*, obj*);
uint8 l_option_is__some___main___rarg(obj*);
obj* l_lean_ir_var_declare___boxed(obj*, obj*, obj*);
obj* l_lean_ir_block_valid__ssa__core___boxed(obj*, obj*, obj*);
obj* l_rbtree_find___at_lean_ir_var_defined___spec__1(obj*, obj*);
obj* l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(obj*);
obj* l_rbmap_find___main___at_lean_ir_var_declare___spec__1___boxed(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__1(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(obj*, obj*, obj*);
obj* l_rbtree_subset___at_lean_ir_phis_check__predecessors___spec__2(obj*, obj*);
extern obj* l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
obj* l_lean_ir_instr_declare__vars___boxed(obj*, obj*, obj*);
obj* l_lean_ir_decl_header___main(obj*);
obj* l_lean_ir_phi_predecessors(obj*, obj*, obj*);
obj* l_lean_ir_phis_check__predecessors___boxed(obj*, obj*, obj*);
obj* l_lean_ir_decl_declare__vars___main___closed__1;
obj* l_rbnode_find__core___main___at_lean_ir_var_defined___spec__3(obj*, obj*);
obj* l_lean_ir_phis_check__predecessors(obj*, obj*, obj*);
obj* l_reader__t_bind___at_lean_ir_decl_valid__ssa___spec__3(obj*, obj*);
obj* l_rbmap_find__core___main___at_lean_ir_phi_predecessors___spec__2(obj*, obj*);
obj* l_rbnode_insert___at_lean_ir_var_declare___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_ir_phi_to__format___main(obj*);
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2___boxed(obj*);
obj* l_lean_ir_terminator_valid__ssa___boxed(obj*, obj*, obj*);
obj* l_rbnode_find__core___main___at_lean_ir_phi_predecessors___spec__3___boxed(obj*, obj*);
obj* l_lean_ir_var_defined(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_check__blockids___main___spec__2(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_phi_predecessors___spec__4(obj*, obj*, obj*);
obj* l_lean_ir_blockid__check__m;
obj* l_lean_ir_check__blockids(obj*);
obj* l_rbnode_insert___at_lean_ir_var_define___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_ir_block_declare(obj*, obj*);
extern obj* l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
obj* l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__2(obj*, obj*, obj*);
obj* l_rbnode_find__core___main___at_lean_ir_var_defined___spec__3___boxed(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_state__t_bind___at_lean_ir_check__blockids___spec__2___rarg(obj*, obj*, obj*);
obj* l_lean_ir_arg_declare___boxed(obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___closed__1;
obj* l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_check__blockids___lambda__1___boxed(obj*, obj*);
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_check__blockids___spec__1(obj*, obj*);
obj* l_lean_ir_phi_declare(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__1(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_phi_predecessors___spec__4___boxed(obj*, obj*, obj*);
obj* l_lean_ir_block_check__blockids(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4(obj*, obj*, obj*, obj*);
extern obj* l_lean_ir_mk__var2blockid;
obj* l_lean_ir_phi_predecessors___boxed(obj*, obj*, obj*);
obj* l_lean_ir_blockid__check__m_run(obj*);
obj* l_lean_ir_instr_declare__vars___main(obj*, obj*, obj*);
obj* l_lean_ir_var_declare___closed__1;
obj* l_lean_ir_block_declare__vars(obj*, obj*);
obj* l_rbtree_find___at_lean_ir_phi_predecessors___spec__1___boxed(obj*, obj*);
obj* l_lean_ir_decl_check__blockids___main(obj*, obj*);
obj* l_lean_ir_blockid__check__m_run___rarg(obj*);
obj* l_lean_ir_check__blockids___lambda__1(obj*, obj*);
obj* l_lean_ir_instr_valid__ssa(obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_check__blockids___spec__1___boxed(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1;
obj* l_rbmap_insert___main___at_lean_ir_var_declare___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_ir_blockid__check__m_run___boxed(obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__2___boxed(obj*, obj*, obj*);
extern obj* l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
obj* l_lean_ir_decl_valid__ssa(obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__1___boxed(obj*, obj*, obj*);
extern obj* l_lean_ir_mk__blockid__set;
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_var_define___spec__3(obj*, obj*, obj*);
obj* l_lean_ir_arg_define(obj*, obj*, obj*);
obj* l_lean_ir_var_declare___closed__2;
obj* l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(obj*);
obj* l_rbmap_insert___main___at_lean_ir_var_define___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_ir_decl_declare__vars(obj*, obj*);
obj* l_rbnode_balance1___main___rarg(obj*, obj*);
obj* l_lean_ir_arg_declare(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_ir_var_declare___spec__4(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2(obj*);
obj* l_lean_ir_blockid_defined___boxed(obj*, obj*);
obj* l_lean_ir_decl_valid__ssa___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_instr_declare__vars(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__1___boxed(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_var_define___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_decl_declare__vars___main(obj*, obj*);
extern obj* l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
obj* l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3___boxed(obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__2___boxed(obj*, obj*, obj*);
obj* l_rbtree_seteq___at_lean_ir_phis_check__predecessors___spec__1___boxed(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__1(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__1(obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2(obj*, obj*);
obj* l_lean_ir_decl_var2blockid(obj*);
obj* l_rbnode_insert___at_lean_ir_var_define___spec__2(obj*, obj*, obj*);
obj* l_state__t_bind___at_lean_ir_check__blockids___spec__2___boxed(obj*, obj*);
obj* l_lean_ir_ssa__valid__m_run___boxed(obj*);
obj* l_lean_ir_var_defined___boxed(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__4(obj*, obj*, obj*);
uint8 l_rbnode_is__red___main___rarg(obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7(obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5(obj*, obj*, obj*);
obj* l_rbmap_find__core___main___at_lean_ir_phi_predecessors___spec__2___boxed(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_ir_block_valid__ssa__core(obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_check__blockids___spec__1___rarg(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_terminator_check__blockids___spec__1(obj*, obj*);
obj* l_rbnode_set__black___main___rarg(obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
obj* l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__2;
obj* _init_l_lean_ir_ssa__pre__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
x_6 = lean::cnstr_get(x_0, 3);
x_7 = l_lean_name_quick__lt___main(x_1, x_4);
x_8 = lean::unbox(x_7);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = l_lean_name_quick__lt___main(x_4, x_1);
x_10 = lean::unbox(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::inc(x_5);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_5);
return x_12;
}
else
{
x_0 = x_6;
goto _start;
}
}
else
{
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg___boxed), 2, 0);
return x_1;
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
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_6; obj* x_7; 
x_3 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_var_declare___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
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
obj* l_lean_ir_var_declare(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(x_2, x_0);
x_4 = l_option_is__some___main___rarg(x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = l_rbnode_insert___at_lean_ir_var_declare___spec__4(x_2, x_0, x_1);
lean::dec(x_0);
x_8 = l_lean_ir_var_declare___closed__1;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_6);
return x_9;
}
else
{
obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_11 = 0;
x_12 = l_lean_ir_var_declare___closed__2;
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_10);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_11);
x_14 = x_13;
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_2);
return x_16;
}
}
}
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_ir_var_declare___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_ir_var_declare___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_ir_var_declare___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_ir_var_declare___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_var_declare___spec__4(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_ir_var_declare___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_ir_var_declare___spec__3(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_ir_var_declare___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_var_declare(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_ir_instr_declare__vars___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 4:
{
obj* x_4; obj* x_5; 
lean::dec(x_0);
x_4 = l_lean_ir_var_declare___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
case 7:
{
obj* x_7; obj* x_8; 
lean::dec(x_0);
x_7 = l_lean_ir_var_declare___closed__1;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_2);
return x_8;
}
case 9:
{
obj* x_10; obj* x_11; 
lean::dec(x_0);
x_10 = l_lean_ir_var_declare___closed__1;
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_2);
return x_11;
}
case 15:
{
obj* x_13; obj* x_14; 
lean::dec(x_0);
x_13 = l_lean_ir_var_declare___closed__1;
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_2);
return x_14;
}
default:
{
obj* x_15; obj* x_18; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
lean::dec(x_0);
x_18 = l_lean_ir_var_declare(x_15, x_1, x_2);
return x_18;
}
}
}
}
obj* l_lean_ir_instr_declare__vars___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_instr_declare__vars___main(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* l_lean_ir_instr_declare__vars___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_instr_declare__vars(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_ir_phi_declare(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = l_lean_ir_var_declare(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_8 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_10 = x_5;
} else {
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_13 = x_6;
} else {
 lean::inc(x_11);
 lean::dec(x_6);
 x_13 = lean::box(0);
}
x_14 = l_lean_ir_phi_to__format___main(x_0);
x_15 = 0;
x_16 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_14);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_15);
x_18 = x_17;
x_19 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_15);
x_21 = x_20;
x_22 = lean::box(1);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_15);
x_24 = x_23;
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_11);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_15);
x_26 = x_25;
if (lean::is_scalar(x_13)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_13;
}
lean::cnstr_set(x_27, 0, x_26);
if (lean::is_scalar(x_10)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_10;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_8);
return x_28;
}
else
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_0);
x_30 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_32 = x_5;
} else {
 lean::inc(x_30);
 lean::dec(x_5);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_6);
lean::cnstr_set(x_33, 1, x_30);
return x_33;
}
}
}
obj* l_lean_ir_phi_declare___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_phi_declare(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_var_declare___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_phi_declare(x_5, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_14 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_16 = x_10;
} else {
 lean::inc(x_14);
 lean::dec(x_10);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_19 = x_11;
} else {
 lean::inc(x_17);
 lean::dec(x_11);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
return x_21;
}
else
{
obj* x_23; 
lean::dec(x_11);
x_23 = lean::cnstr_get(x_10, 1);
lean::inc(x_23);
lean::dec(x_10);
x_0 = x_7;
x_2 = x_23;
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
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_var_declare___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_instr_declare__vars___main(x_5, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_14 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_16 = x_10;
} else {
 lean::inc(x_14);
 lean::dec(x_10);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_19 = x_11;
} else {
 lean::inc(x_17);
 lean::dec(x_11);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
return x_21;
}
else
{
obj* x_23; 
lean::dec(x_11);
x_23 = lean::cnstr_get(x_10, 1);
lean::inc(x_23);
lean::dec(x_10);
x_0 = x_7;
x_2 = x_23;
goto _start;
}
}
}
}
obj* l_lean_ir_block_declare__vars(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__1(x_2, x_4, x_1);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_0);
x_10 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_12 = x_6;
} else {
 lean::inc(x_10);
 lean::dec(x_6);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_15 = x_7;
} else {
 lean::inc(x_13);
 lean::dec(x_7);
 x_15 = lean::box(0);
}
x_16 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_4);
x_17 = 0;
x_18 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_16);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_17);
x_20 = x_19;
x_21 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_17);
x_23 = x_22;
x_24 = lean::box(1);
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_17);
x_26 = x_25;
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_13);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_17);
x_28 = x_27;
if (lean::is_scalar(x_15)) {
 x_29 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_29 = x_15;
}
lean::cnstr_set(x_29, 0, x_28);
if (lean::is_scalar(x_12)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_12;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_10);
return x_30;
}
else
{
obj* x_32; obj* x_35; obj* x_38; obj* x_39; 
lean::dec(x_7);
x_32 = lean::cnstr_get(x_6, 1);
lean::inc(x_32);
lean::dec(x_6);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
lean::dec(x_0);
x_38 = l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__2(x_35, x_4, x_32);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
if (lean::obj_tag(x_39) == 0)
{
obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_47; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_41 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_43 = x_38;
} else {
 lean::inc(x_41);
 lean::dec(x_38);
 x_43 = lean::box(0);
}
x_44 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_46 = x_39;
} else {
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
x_47 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_4);
x_48 = 0;
x_49 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
x_50 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_47);
lean::cnstr_set_scalar(x_50, sizeof(void*)*2, x_48);
x_51 = x_50;
x_52 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_53 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_52);
lean::cnstr_set_scalar(x_53, sizeof(void*)*2, x_48);
x_54 = x_53;
x_55 = lean::box(1);
x_56 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
lean::cnstr_set_scalar(x_56, sizeof(void*)*2, x_48);
x_57 = x_56;
x_58 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_44);
lean::cnstr_set_scalar(x_58, sizeof(void*)*2, x_48);
x_59 = x_58;
if (lean::is_scalar(x_46)) {
 x_60 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_60 = x_46;
}
lean::cnstr_set(x_60, 0, x_59);
if (lean::is_scalar(x_43)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_43;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_41);
return x_61;
}
else
{
obj* x_63; obj* x_65; obj* x_66; 
lean::dec(x_4);
x_63 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_65 = x_38;
} else {
 lean::inc(x_63);
 lean::dec(x_38);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_39);
lean::cnstr_set(x_66, 1, x_63);
return x_66;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__2(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* l_lean_ir_arg_declare___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_arg_declare(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_3; 
x_2 = l_lean_ir_var_declare___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_lean_ir_block_declare__vars(x_4, x_1);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_6);
x_13 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_15 = x_9;
} else {
 lean::inc(x_13);
 lean::dec(x_9);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_18 = x_10;
} else {
 lean::inc(x_16);
 lean::dec(x_10);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_13);
return x_20;
}
else
{
obj* x_22; 
lean::dec(x_10);
x_22 = lean::cnstr_get(x_9, 1);
lean::inc(x_22);
lean::dec(x_9);
x_0 = x_6;
x_1 = x_22;
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
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_var_declare___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_arg_declare(x_5, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_14 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_16 = x_10;
} else {
 lean::inc(x_14);
 lean::dec(x_10);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_19 = x_11;
} else {
 lean::inc(x_17);
 lean::dec(x_11);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
return x_21;
}
else
{
obj* x_23; 
lean::dec(x_11);
x_23 = lean::cnstr_get(x_10, 1);
lean::inc(x_23);
lean::dec(x_10);
x_0 = x_7;
x_2 = x_23;
goto _start;
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
obj* l_lean_ir_decl_declare__vars___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
lean::dec(x_0);
x_3 = l_lean_ir_var_declare___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_0);
x_8 = l_lean_ir_decl_declare__vars___main___closed__1;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_1);
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_27; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_5, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_5, 1);
lean::inc(x_15);
lean::dec(x_5);
x_21 = lean::cnstr_get(x_10, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_13, 0);
lean::inc(x_23);
x_25 = l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__2(x_21, x_23, x_1);
lean::dec(x_23);
x_27 = lean::cnstr_get(x_25, 0);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_30; obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_13);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_35 = x_27;
} else {
 lean::inc(x_33);
 lean::dec(x_27);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
x_18 = x_36;
x_19 = x_30;
goto lbl_20;
}
else
{
obj* x_38; obj* x_41; obj* x_42; obj* x_44; 
lean::dec(x_27);
x_38 = lean::cnstr_get(x_25, 1);
lean::inc(x_38);
lean::dec(x_25);
x_41 = l_lean_ir_block_declare__vars(x_13, x_38);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
x_18 = x_42;
x_19 = x_44;
goto lbl_20;
}
lbl_20:
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_48; obj* x_50; obj* x_51; obj* x_54; uint8 x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_15);
x_48 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_50 = x_18;
} else {
 lean::inc(x_48);
 lean::dec(x_18);
 x_50 = lean::box(0);
}
x_51 = lean::cnstr_get(x_10, 0);
lean::inc(x_51);
lean::dec(x_10);
x_54 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_51);
x_55 = 0;
x_56 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
x_57 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_54);
lean::cnstr_set_scalar(x_57, sizeof(void*)*2, x_55);
x_58 = x_57;
x_59 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_60 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set(x_60, 1, x_59);
lean::cnstr_set_scalar(x_60, sizeof(void*)*2, x_55);
x_61 = x_60;
x_62 = lean::box(1);
x_63 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set(x_63, 1, x_62);
lean::cnstr_set_scalar(x_63, sizeof(void*)*2, x_55);
x_64 = x_63;
x_65 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_48);
lean::cnstr_set_scalar(x_65, sizeof(void*)*2, x_55);
x_66 = x_65;
if (lean::is_scalar(x_50)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_50;
}
lean::cnstr_set(x_67, 0, x_66);
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_19);
return x_68;
}
else
{
obj* x_70; obj* x_71; 
lean::dec(x_18);
x_70 = l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__1(x_15, x_19);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
if (lean::obj_tag(x_71) == 0)
{
obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_82; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_73 = lean::cnstr_get(x_70, 1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 x_75 = x_70;
} else {
 lean::inc(x_73);
 lean::dec(x_70);
 x_75 = lean::box(0);
}
x_76 = lean::cnstr_get(x_71, 0);
if (lean::is_exclusive(x_71)) {
 x_78 = x_71;
} else {
 lean::inc(x_76);
 lean::dec(x_71);
 x_78 = lean::box(0);
}
x_79 = lean::cnstr_get(x_10, 0);
lean::inc(x_79);
lean::dec(x_10);
x_82 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_79);
x_83 = 0;
x_84 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
x_85 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_82);
lean::cnstr_set_scalar(x_85, sizeof(void*)*2, x_83);
x_86 = x_85;
x_87 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_88 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_87);
lean::cnstr_set_scalar(x_88, sizeof(void*)*2, x_83);
x_89 = x_88;
x_90 = lean::box(1);
x_91 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_91, 0, x_89);
lean::cnstr_set(x_91, 1, x_90);
lean::cnstr_set_scalar(x_91, sizeof(void*)*2, x_83);
x_92 = x_91;
x_93 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_76);
lean::cnstr_set_scalar(x_93, sizeof(void*)*2, x_83);
x_94 = x_93;
if (lean::is_scalar(x_78)) {
 x_95 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_95 = x_78;
}
lean::cnstr_set(x_95, 0, x_94);
if (lean::is_scalar(x_75)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_75;
}
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_73);
return x_96;
}
else
{
obj* x_98; obj* x_100; obj* x_101; 
lean::dec(x_10);
x_98 = lean::cnstr_get(x_70, 1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 x_100 = x_70;
} else {
 lean::inc(x_98);
 lean::dec(x_70);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_71);
lean::cnstr_set(x_101, 1, x_98);
return x_101;
}
}
}
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__2(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_lean_ir_mk__var2blockid;
x_2 = l_lean_ir_decl_declare__vars___main(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_8; obj* x_9; 
lean::dec(x_2);
x_6 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_8 = x_3;
} else {
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
if (lean::is_scalar(x_8)) {
 x_9 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_9 = x_8;
}
lean::cnstr_set(x_9, 0, x_6);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_14; 
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_10 = x_3;
} else {
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::dec(x_2);
if (lean::is_scalar(x_10)) {
 x_14 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_14 = x_10;
}
lean::cnstr_set(x_14, 0, x_11);
return x_14;
}
}
}
obj* _init_l_lean_ir_ssa__valid__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_lean_ir_ssa__valid__m_run___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_lean_ir_mk__var__set;
x_3 = lean::apply_2(x_0, x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_ir_ssa__valid__m_run(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_ssa__valid__m_run___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_ir_ssa__valid__m_run___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_ssa__valid__m_run(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_ir_var_define___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_6; obj* x_7; 
x_3 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_var_define___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
x_4 = l_rbnode_insert___at_lean_ir_var_define___spec__2(x_2, x_0, x_3);
x_5 = l_lean_ir_var_declare___closed__1;
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_4);
return x_6;
}
}
obj* l_rbnode_ins___main___at_lean_ir_var_define___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_ir_var_define___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_var_define___spec__2(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_ir_var_define___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_ir_var_define___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_ir_var_define___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_var_define(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_ir_arg_define(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = l_lean_ir_var_define(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_ir_arg_define___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_arg_define(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_rbnode_find__core___main___at_lean_ir_var_defined___spec__3(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
x_6 = lean::cnstr_get(x_0, 3);
x_7 = l_lean_name_quick__lt___main(x_1, x_4);
x_8 = lean::unbox(x_7);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = l_lean_name_quick__lt___main(x_4, x_1);
x_10 = lean::unbox(x_9);
if (x_10 == 0)
{
obj* x_13; obj* x_14; 
lean::inc(x_5);
lean::inc(x_4);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_4);
lean::cnstr_set(x_13, 1, x_5);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
else
{
x_0 = x_6;
goto _start;
}
}
else
{
x_0 = x_3;
goto _start;
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
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
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
obj* l_lean_ir_var_defined(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = l_rbtree_find___at_lean_ir_var_defined___spec__1(x_2, x_0);
x_4 = l_option_is__some___main___rarg(x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
x_6 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_7 = 0;
x_8 = l_lean_ir_var_defined___closed__1;
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_6);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_7);
x_10 = x_9;
x_11 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_7);
x_13 = x_12;
x_14 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::inc(x_2);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_2);
return x_16;
}
else
{
obj* x_18; obj* x_20; 
lean::dec(x_0);
x_18 = l_lean_ir_var_declare___closed__1;
lean::inc(x_2);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_2);
return x_20;
}
}
}
obj* l_rbnode_find__core___main___at_lean_ir_var_defined___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find__core___main___at_lean_ir_var_defined___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find__core___main___at_lean_ir_var_defined___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find__core___main___at_lean_ir_var_defined___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbtree_find___at_lean_ir_var_defined___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbtree_find___at_lean_ir_var_defined___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_ir_var_defined___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_var_defined(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_6; 
x_4 = l_lean_ir_var_declare___closed__1;
lean::inc(x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; uint8 x_13; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_12 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(x_0, x_7);
x_13 = l_option_is__some___main___rarg(x_12);
lean::dec(x_12);
if (x_13 == 0)
{
obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; 
lean::dec(x_9);
x_16 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_7);
x_17 = 0;
x_18 = l_lean_ir_var_defined___closed__1;
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_16);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_17);
x_20 = x_19;
x_21 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_17);
x_23 = x_22;
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::inc(x_3);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_3);
return x_26;
}
else
{
lean::dec(x_7);
x_1 = x_9;
goto _start;
}
}
}
}
obj* l_lean_ir_phi_valid__ssa(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1(x_1, x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_8 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_10 = x_5;
} else {
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_13 = x_6;
} else {
 lean::inc(x_11);
 lean::dec(x_6);
 x_13 = lean::box(0);
}
x_14 = l_lean_ir_phi_to__format___main(x_0);
x_15 = 0;
x_16 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
x_17 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_14);
lean::cnstr_set_scalar(x_17, sizeof(void*)*2, x_15);
x_18 = x_17;
x_19 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_15);
x_21 = x_20;
x_22 = lean::box(1);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_15);
x_24 = x_23;
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_11);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_15);
x_26 = x_25;
if (lean::is_scalar(x_13)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_13;
}
lean::cnstr_set(x_27, 0, x_26);
if (lean::is_scalar(x_10)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_10;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_8);
return x_28;
}
else
{
obj* x_30; obj* x_33; obj* x_35; obj* x_37; 
lean::dec(x_6);
x_30 = lean::cnstr_get(x_5, 1);
lean::inc(x_30);
lean::dec(x_5);
x_33 = lean::cnstr_get(x_0, 0);
lean::inc(x_33);
x_35 = l_lean_ir_var_define(x_33, x_1, x_30);
lean::dec(x_33);
x_37 = lean::cnstr_get(x_35, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_45; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_39 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 x_41 = x_35;
} else {
 lean::inc(x_39);
 lean::dec(x_35);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_44 = x_37;
} else {
 lean::inc(x_42);
 lean::dec(x_37);
 x_44 = lean::box(0);
}
x_45 = l_lean_ir_phi_to__format___main(x_0);
x_46 = 0;
x_47 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
x_48 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_45);
lean::cnstr_set_scalar(x_48, sizeof(void*)*2, x_46);
x_49 = x_48;
x_50 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_51 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_50);
lean::cnstr_set_scalar(x_51, sizeof(void*)*2, x_46);
x_52 = x_51;
x_53 = lean::box(1);
x_54 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_53);
lean::cnstr_set_scalar(x_54, sizeof(void*)*2, x_46);
x_55 = x_54;
x_56 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_42);
lean::cnstr_set_scalar(x_56, sizeof(void*)*2, x_46);
x_57 = x_56;
if (lean::is_scalar(x_44)) {
 x_58 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_58 = x_44;
}
lean::cnstr_set(x_58, 0, x_57);
if (lean::is_scalar(x_41)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_41;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_39);
return x_59;
}
else
{
obj* x_61; obj* x_63; obj* x_64; 
lean::dec(x_0);
x_61 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 x_63 = x_35;
} else {
 lean::inc(x_61);
 lean::dec(x_35);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_37);
lean::cnstr_set(x_64, 1, x_61);
return x_64;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_ir_phi_valid__ssa___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_phi_valid__ssa(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_var_declare___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_var_defined(x_5, x_1, x_2);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_7);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_17 = x_10;
} else {
 lean::inc(x_15);
 lean::dec(x_10);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_20 = x_12;
} else {
 lean::inc(x_18);
 lean::dec(x_12);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
if (lean::is_scalar(x_17)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_17;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_15);
return x_22;
}
else
{
obj* x_24; 
lean::dec(x_12);
x_24 = lean::cnstr_get(x_10, 1);
lean::inc(x_24);
lean::dec(x_10);
x_0 = x_7;
x_2 = x_24;
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
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_var_declare___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_var_defined(x_5, x_1, x_2);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_7);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_17 = x_10;
} else {
 lean::inc(x_15);
 lean::dec(x_10);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_20 = x_12;
} else {
 lean::inc(x_18);
 lean::dec(x_12);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
if (lean::is_scalar(x_17)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_17;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_15);
return x_22;
}
else
{
obj* x_24; 
lean::dec(x_12);
x_24 = lean::cnstr_get(x_10, 1);
lean::inc(x_24);
lean::dec(x_10);
x_0 = x_7;
x_2 = x_24;
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
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_var_declare___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_var_defined(x_5, x_1, x_2);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_7);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_17 = x_10;
} else {
 lean::inc(x_15);
 lean::dec(x_10);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_20 = x_12;
} else {
 lean::inc(x_18);
 lean::dec(x_12);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
if (lean::is_scalar(x_17)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_17;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_15);
return x_22;
}
else
{
obj* x_24; 
lean::dec(x_12);
x_24 = lean::cnstr_get(x_10, 1);
lean::inc(x_24);
lean::dec(x_10);
x_0 = x_7;
x_2 = x_24;
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
case 1:
{
obj* x_5; obj* x_7; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = l_lean_ir_var_define(x_5, x_1, x_2);
lean::dec(x_5);
x_3 = x_7;
goto lbl_4;
}
case 3:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 2);
lean::inc(x_13);
x_15 = l_lean_ir_var_define(x_9, x_1, x_2);
lean::dec(x_9);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_13);
lean::dec(x_11);
x_21 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_23 = x_15;
} else {
 lean::inc(x_21);
 lean::dec(x_15);
 x_23 = lean::box(0);
}
x_24 = lean::cnstr_get(x_17, 0);
if (lean::is_exclusive(x_17)) {
 x_26 = x_17;
} else {
 lean::inc(x_24);
 lean::dec(x_17);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_24);
if (lean::is_scalar(x_23)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_23;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_21);
x_3 = x_28;
goto lbl_4;
}
else
{
obj* x_30; obj* x_33; obj* x_35; 
lean::dec(x_17);
x_30 = lean::cnstr_get(x_15, 1);
lean::inc(x_30);
lean::dec(x_15);
x_33 = l_lean_ir_var_defined(x_11, x_1, x_30);
lean::dec(x_30);
x_35 = lean::cnstr_get(x_33, 0);
lean::inc(x_35);
if (lean::obj_tag(x_35) == 0)
{
obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_13);
x_38 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_40 = x_33;
} else {
 lean::inc(x_38);
 lean::dec(x_33);
 x_40 = lean::box(0);
}
x_41 = lean::cnstr_get(x_35, 0);
if (lean::is_exclusive(x_35)) {
 x_43 = x_35;
} else {
 lean::inc(x_41);
 lean::dec(x_35);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_41);
if (lean::is_scalar(x_40)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_40;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_38);
x_3 = x_45;
goto lbl_4;
}
else
{
obj* x_47; obj* x_50; 
lean::dec(x_35);
x_47 = lean::cnstr_get(x_33, 1);
lean::inc(x_47);
lean::dec(x_33);
x_50 = l_lean_ir_var_defined(x_13, x_1, x_47);
lean::dec(x_47);
x_3 = x_50;
goto lbl_4;
}
}
}
case 4:
{
obj* x_52; obj* x_54; 
x_52 = lean::cnstr_get(x_0, 0);
lean::inc(x_52);
x_54 = l_lean_ir_var_defined(x_52, x_1, x_2);
lean::dec(x_2);
x_3 = x_54;
goto lbl_4;
}
case 5:
{
obj* x_56; obj* x_58; obj* x_60; obj* x_62; 
x_56 = lean::cnstr_get(x_0, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_0, 2);
lean::inc(x_58);
x_60 = l_lean_ir_var_define(x_56, x_1, x_2);
lean::dec(x_56);
x_62 = lean::cnstr_get(x_60, 0);
lean::inc(x_62);
if (lean::obj_tag(x_62) == 0)
{
obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_58);
x_65 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 x_67 = x_60;
} else {
 lean::inc(x_65);
 lean::dec(x_60);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_70 = x_62;
} else {
 lean::inc(x_68);
 lean::dec(x_62);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_68);
if (lean::is_scalar(x_67)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_67;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_65);
x_3 = x_72;
goto lbl_4;
}
else
{
obj* x_74; obj* x_77; 
lean::dec(x_62);
x_74 = lean::cnstr_get(x_60, 1);
lean::inc(x_74);
lean::dec(x_60);
x_77 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__1(x_58, x_1, x_74);
x_3 = x_77;
goto lbl_4;
}
}
case 6:
{
obj* x_78; obj* x_80; 
x_78 = lean::cnstr_get(x_0, 0);
lean::inc(x_78);
x_80 = l_lean_ir_var_define(x_78, x_1, x_2);
lean::dec(x_78);
x_3 = x_80;
goto lbl_4;
}
case 7:
{
obj* x_82; obj* x_84; obj* x_86; obj* x_88; 
x_82 = lean::cnstr_get(x_0, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_0, 1);
lean::inc(x_84);
x_86 = l_lean_ir_var_defined(x_82, x_1, x_2);
lean::dec(x_2);
x_88 = lean::cnstr_get(x_86, 0);
lean::inc(x_88);
if (lean::obj_tag(x_88) == 0)
{
obj* x_91; obj* x_93; obj* x_94; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_84);
x_91 = lean::cnstr_get(x_86, 1);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 x_93 = x_86;
} else {
 lean::inc(x_91);
 lean::dec(x_86);
 x_93 = lean::box(0);
}
x_94 = lean::cnstr_get(x_88, 0);
if (lean::is_exclusive(x_88)) {
 x_96 = x_88;
} else {
 lean::inc(x_94);
 lean::dec(x_88);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_94);
if (lean::is_scalar(x_93)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_93;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_91);
x_3 = x_98;
goto lbl_4;
}
else
{
obj* x_100; obj* x_103; 
lean::dec(x_88);
x_100 = lean::cnstr_get(x_86, 1);
lean::inc(x_100);
lean::dec(x_86);
x_103 = l_lean_ir_var_defined(x_84, x_1, x_100);
lean::dec(x_100);
x_3 = x_103;
goto lbl_4;
}
}
case 9:
{
obj* x_105; obj* x_107; obj* x_109; obj* x_111; 
x_105 = lean::cnstr_get(x_0, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_0, 1);
lean::inc(x_107);
x_109 = l_lean_ir_var_defined(x_105, x_1, x_2);
lean::dec(x_2);
x_111 = lean::cnstr_get(x_109, 0);
lean::inc(x_111);
if (lean::obj_tag(x_111) == 0)
{
obj* x_114; obj* x_116; obj* x_117; obj* x_119; obj* x_120; obj* x_121; 
lean::dec(x_107);
x_114 = lean::cnstr_get(x_109, 1);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 x_116 = x_109;
} else {
 lean::inc(x_114);
 lean::dec(x_109);
 x_116 = lean::box(0);
}
x_117 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 x_119 = x_111;
} else {
 lean::inc(x_117);
 lean::dec(x_111);
 x_119 = lean::box(0);
}
if (lean::is_scalar(x_119)) {
 x_120 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_120 = x_119;
}
lean::cnstr_set(x_120, 0, x_117);
if (lean::is_scalar(x_116)) {
 x_121 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_121 = x_116;
}
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_114);
x_3 = x_121;
goto lbl_4;
}
else
{
obj* x_123; obj* x_126; 
lean::dec(x_111);
x_123 = lean::cnstr_get(x_109, 1);
lean::inc(x_123);
lean::dec(x_109);
x_126 = l_lean_ir_var_defined(x_107, x_1, x_123);
lean::dec(x_123);
x_3 = x_126;
goto lbl_4;
}
}
case 11:
{
obj* x_128; obj* x_130; obj* x_132; obj* x_134; 
x_128 = lean::cnstr_get(x_0, 0);
lean::inc(x_128);
x_130 = lean::cnstr_get(x_0, 2);
lean::inc(x_130);
x_132 = l_lean_ir_var_define(x_128, x_1, x_2);
lean::dec(x_128);
x_134 = lean::cnstr_get(x_132, 0);
lean::inc(x_134);
if (lean::obj_tag(x_134) == 0)
{
obj* x_137; obj* x_139; obj* x_140; obj* x_142; obj* x_143; obj* x_144; 
lean::dec(x_130);
x_137 = lean::cnstr_get(x_132, 1);
if (lean::is_exclusive(x_132)) {
 lean::cnstr_release(x_132, 0);
 x_139 = x_132;
} else {
 lean::inc(x_137);
 lean::dec(x_132);
 x_139 = lean::box(0);
}
x_140 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_142 = x_134;
} else {
 lean::inc(x_140);
 lean::dec(x_134);
 x_142 = lean::box(0);
}
if (lean::is_scalar(x_142)) {
 x_143 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_143 = x_142;
}
lean::cnstr_set(x_143, 0, x_140);
if (lean::is_scalar(x_139)) {
 x_144 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_144 = x_139;
}
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_144, 1, x_137);
x_3 = x_144;
goto lbl_4;
}
else
{
obj* x_146; obj* x_149; 
lean::dec(x_134);
x_146 = lean::cnstr_get(x_132, 1);
lean::inc(x_146);
lean::dec(x_132);
x_149 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__2(x_130, x_1, x_146);
x_3 = x_149;
goto lbl_4;
}
}
case 12:
{
obj* x_150; obj* x_152; obj* x_154; obj* x_156; 
x_150 = lean::cnstr_get(x_0, 0);
lean::inc(x_150);
x_152 = lean::cnstr_get(x_0, 1);
lean::inc(x_152);
x_154 = l_lean_ir_var_define(x_150, x_1, x_2);
lean::dec(x_150);
x_156 = lean::cnstr_get(x_154, 0);
lean::inc(x_156);
if (lean::obj_tag(x_156) == 0)
{
obj* x_159; obj* x_161; obj* x_162; obj* x_164; obj* x_165; obj* x_166; 
lean::dec(x_152);
x_159 = lean::cnstr_get(x_154, 1);
if (lean::is_exclusive(x_154)) {
 lean::cnstr_release(x_154, 0);
 x_161 = x_154;
} else {
 lean::inc(x_159);
 lean::dec(x_154);
 x_161 = lean::box(0);
}
x_162 = lean::cnstr_get(x_156, 0);
if (lean::is_exclusive(x_156)) {
 x_164 = x_156;
} else {
 lean::inc(x_162);
 lean::dec(x_156);
 x_164 = lean::box(0);
}
if (lean::is_scalar(x_164)) {
 x_165 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_165 = x_164;
}
lean::cnstr_set(x_165, 0, x_162);
if (lean::is_scalar(x_161)) {
 x_166 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_166 = x_161;
}
lean::cnstr_set(x_166, 0, x_165);
lean::cnstr_set(x_166, 1, x_159);
x_3 = x_166;
goto lbl_4;
}
else
{
obj* x_168; obj* x_171; 
lean::dec(x_156);
x_168 = lean::cnstr_get(x_154, 1);
lean::inc(x_168);
lean::dec(x_154);
x_171 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__3(x_152, x_1, x_168);
x_3 = x_171;
goto lbl_4;
}
}
case 13:
{
obj* x_172; obj* x_174; obj* x_176; obj* x_178; obj* x_180; 
x_172 = lean::cnstr_get(x_0, 0);
lean::inc(x_172);
x_174 = lean::cnstr_get(x_0, 1);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_0, 2);
lean::inc(x_176);
x_178 = l_lean_ir_var_define(x_172, x_1, x_2);
lean::dec(x_172);
x_180 = lean::cnstr_get(x_178, 0);
lean::inc(x_180);
if (lean::obj_tag(x_180) == 0)
{
obj* x_184; obj* x_186; obj* x_187; obj* x_189; obj* x_190; obj* x_191; 
lean::dec(x_174);
lean::dec(x_176);
x_184 = lean::cnstr_get(x_178, 1);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 x_186 = x_178;
} else {
 lean::inc(x_184);
 lean::dec(x_178);
 x_186 = lean::box(0);
}
x_187 = lean::cnstr_get(x_180, 0);
if (lean::is_exclusive(x_180)) {
 x_189 = x_180;
} else {
 lean::inc(x_187);
 lean::dec(x_180);
 x_189 = lean::box(0);
}
if (lean::is_scalar(x_189)) {
 x_190 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_190 = x_189;
}
lean::cnstr_set(x_190, 0, x_187);
if (lean::is_scalar(x_186)) {
 x_191 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_191 = x_186;
}
lean::cnstr_set(x_191, 0, x_190);
lean::cnstr_set(x_191, 1, x_184);
x_3 = x_191;
goto lbl_4;
}
else
{
obj* x_193; obj* x_196; obj* x_198; 
lean::dec(x_180);
x_193 = lean::cnstr_get(x_178, 1);
lean::inc(x_193);
lean::dec(x_178);
x_196 = l_lean_ir_var_defined(x_174, x_1, x_193);
lean::dec(x_193);
x_198 = lean::cnstr_get(x_196, 0);
lean::inc(x_198);
if (lean::obj_tag(x_198) == 0)
{
obj* x_201; obj* x_203; obj* x_204; obj* x_206; obj* x_207; obj* x_208; 
lean::dec(x_176);
x_201 = lean::cnstr_get(x_196, 1);
if (lean::is_exclusive(x_196)) {
 lean::cnstr_release(x_196, 0);
 x_203 = x_196;
} else {
 lean::inc(x_201);
 lean::dec(x_196);
 x_203 = lean::box(0);
}
x_204 = lean::cnstr_get(x_198, 0);
if (lean::is_exclusive(x_198)) {
 x_206 = x_198;
} else {
 lean::inc(x_204);
 lean::dec(x_198);
 x_206 = lean::box(0);
}
if (lean::is_scalar(x_206)) {
 x_207 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_207 = x_206;
}
lean::cnstr_set(x_207, 0, x_204);
if (lean::is_scalar(x_203)) {
 x_208 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_208 = x_203;
}
lean::cnstr_set(x_208, 0, x_207);
lean::cnstr_set(x_208, 1, x_201);
x_3 = x_208;
goto lbl_4;
}
else
{
obj* x_210; obj* x_213; 
lean::dec(x_198);
x_210 = lean::cnstr_get(x_196, 1);
lean::inc(x_210);
lean::dec(x_196);
x_213 = l_lean_ir_var_defined(x_176, x_1, x_210);
lean::dec(x_210);
x_3 = x_213;
goto lbl_4;
}
}
}
case 14:
{
obj* x_215; obj* x_217; obj* x_219; obj* x_221; obj* x_223; 
x_215 = lean::cnstr_get(x_0, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_0, 1);
lean::inc(x_217);
x_219 = lean::cnstr_get(x_0, 2);
lean::inc(x_219);
x_221 = l_lean_ir_var_define(x_215, x_1, x_2);
lean::dec(x_215);
x_223 = lean::cnstr_get(x_221, 0);
lean::inc(x_223);
if (lean::obj_tag(x_223) == 0)
{
obj* x_227; obj* x_229; obj* x_230; obj* x_232; obj* x_233; obj* x_234; 
lean::dec(x_219);
lean::dec(x_217);
x_227 = lean::cnstr_get(x_221, 1);
if (lean::is_exclusive(x_221)) {
 lean::cnstr_release(x_221, 0);
 x_229 = x_221;
} else {
 lean::inc(x_227);
 lean::dec(x_221);
 x_229 = lean::box(0);
}
x_230 = lean::cnstr_get(x_223, 0);
if (lean::is_exclusive(x_223)) {
 x_232 = x_223;
} else {
 lean::inc(x_230);
 lean::dec(x_223);
 x_232 = lean::box(0);
}
if (lean::is_scalar(x_232)) {
 x_233 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_233 = x_232;
}
lean::cnstr_set(x_233, 0, x_230);
if (lean::is_scalar(x_229)) {
 x_234 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_234 = x_229;
}
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_227);
x_3 = x_234;
goto lbl_4;
}
else
{
obj* x_236; obj* x_239; obj* x_241; 
lean::dec(x_223);
x_236 = lean::cnstr_get(x_221, 1);
lean::inc(x_236);
lean::dec(x_221);
x_239 = l_lean_ir_var_defined(x_217, x_1, x_236);
lean::dec(x_236);
x_241 = lean::cnstr_get(x_239, 0);
lean::inc(x_241);
if (lean::obj_tag(x_241) == 0)
{
obj* x_244; obj* x_246; obj* x_247; obj* x_249; obj* x_250; obj* x_251; 
lean::dec(x_219);
x_244 = lean::cnstr_get(x_239, 1);
if (lean::is_exclusive(x_239)) {
 lean::cnstr_release(x_239, 0);
 x_246 = x_239;
} else {
 lean::inc(x_244);
 lean::dec(x_239);
 x_246 = lean::box(0);
}
x_247 = lean::cnstr_get(x_241, 0);
if (lean::is_exclusive(x_241)) {
 x_249 = x_241;
} else {
 lean::inc(x_247);
 lean::dec(x_241);
 x_249 = lean::box(0);
}
if (lean::is_scalar(x_249)) {
 x_250 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_250 = x_249;
}
lean::cnstr_set(x_250, 0, x_247);
if (lean::is_scalar(x_246)) {
 x_251 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_251 = x_246;
}
lean::cnstr_set(x_251, 0, x_250);
lean::cnstr_set(x_251, 1, x_244);
x_3 = x_251;
goto lbl_4;
}
else
{
obj* x_253; obj* x_256; 
lean::dec(x_241);
x_253 = lean::cnstr_get(x_239, 1);
lean::inc(x_253);
lean::dec(x_239);
x_256 = l_lean_ir_var_defined(x_219, x_1, x_253);
lean::dec(x_253);
x_3 = x_256;
goto lbl_4;
}
}
}
case 15:
{
obj* x_258; obj* x_260; obj* x_262; obj* x_264; obj* x_266; 
x_258 = lean::cnstr_get(x_0, 0);
lean::inc(x_258);
x_260 = lean::cnstr_get(x_0, 1);
lean::inc(x_260);
x_262 = lean::cnstr_get(x_0, 2);
lean::inc(x_262);
x_264 = l_lean_ir_var_defined(x_258, x_1, x_2);
lean::dec(x_2);
x_266 = lean::cnstr_get(x_264, 0);
lean::inc(x_266);
if (lean::obj_tag(x_266) == 0)
{
obj* x_270; obj* x_272; obj* x_273; obj* x_275; obj* x_276; obj* x_277; 
lean::dec(x_262);
lean::dec(x_260);
x_270 = lean::cnstr_get(x_264, 1);
if (lean::is_exclusive(x_264)) {
 lean::cnstr_release(x_264, 0);
 x_272 = x_264;
} else {
 lean::inc(x_270);
 lean::dec(x_264);
 x_272 = lean::box(0);
}
x_273 = lean::cnstr_get(x_266, 0);
if (lean::is_exclusive(x_266)) {
 x_275 = x_266;
} else {
 lean::inc(x_273);
 lean::dec(x_266);
 x_275 = lean::box(0);
}
if (lean::is_scalar(x_275)) {
 x_276 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_276 = x_275;
}
lean::cnstr_set(x_276, 0, x_273);
if (lean::is_scalar(x_272)) {
 x_277 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_277 = x_272;
}
lean::cnstr_set(x_277, 0, x_276);
lean::cnstr_set(x_277, 1, x_270);
x_3 = x_277;
goto lbl_4;
}
else
{
obj* x_279; obj* x_282; obj* x_284; 
lean::dec(x_266);
x_279 = lean::cnstr_get(x_264, 1);
lean::inc(x_279);
lean::dec(x_264);
x_282 = l_lean_ir_var_defined(x_260, x_1, x_279);
lean::dec(x_279);
x_284 = lean::cnstr_get(x_282, 0);
lean::inc(x_284);
if (lean::obj_tag(x_284) == 0)
{
obj* x_287; obj* x_289; obj* x_290; obj* x_292; obj* x_293; obj* x_294; 
lean::dec(x_262);
x_287 = lean::cnstr_get(x_282, 1);
if (lean::is_exclusive(x_282)) {
 lean::cnstr_release(x_282, 0);
 x_289 = x_282;
} else {
 lean::inc(x_287);
 lean::dec(x_282);
 x_289 = lean::box(0);
}
x_290 = lean::cnstr_get(x_284, 0);
if (lean::is_exclusive(x_284)) {
 x_292 = x_284;
} else {
 lean::inc(x_290);
 lean::dec(x_284);
 x_292 = lean::box(0);
}
if (lean::is_scalar(x_292)) {
 x_293 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_293 = x_292;
}
lean::cnstr_set(x_293, 0, x_290);
if (lean::is_scalar(x_289)) {
 x_294 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_294 = x_289;
}
lean::cnstr_set(x_294, 0, x_293);
lean::cnstr_set(x_294, 1, x_287);
x_3 = x_294;
goto lbl_4;
}
else
{
obj* x_296; obj* x_299; 
lean::dec(x_284);
x_296 = lean::cnstr_get(x_282, 1);
lean::inc(x_296);
lean::dec(x_282);
x_299 = l_lean_ir_var_defined(x_262, x_1, x_296);
lean::dec(x_296);
x_3 = x_299;
goto lbl_4;
}
}
}
default:
{
obj* x_301; obj* x_303; obj* x_305; obj* x_307; 
x_301 = lean::cnstr_get(x_0, 0);
lean::inc(x_301);
x_303 = lean::cnstr_get(x_0, 1);
lean::inc(x_303);
x_305 = l_lean_ir_var_define(x_301, x_1, x_2);
lean::dec(x_301);
x_307 = lean::cnstr_get(x_305, 0);
lean::inc(x_307);
if (lean::obj_tag(x_307) == 0)
{
obj* x_310; obj* x_312; obj* x_313; obj* x_315; obj* x_316; obj* x_317; 
lean::dec(x_303);
x_310 = lean::cnstr_get(x_305, 1);
if (lean::is_exclusive(x_305)) {
 lean::cnstr_release(x_305, 0);
 x_312 = x_305;
} else {
 lean::inc(x_310);
 lean::dec(x_305);
 x_312 = lean::box(0);
}
x_313 = lean::cnstr_get(x_307, 0);
if (lean::is_exclusive(x_307)) {
 x_315 = x_307;
} else {
 lean::inc(x_313);
 lean::dec(x_307);
 x_315 = lean::box(0);
}
if (lean::is_scalar(x_315)) {
 x_316 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_316 = x_315;
}
lean::cnstr_set(x_316, 0, x_313);
if (lean::is_scalar(x_312)) {
 x_317 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_317 = x_312;
}
lean::cnstr_set(x_317, 0, x_316);
lean::cnstr_set(x_317, 1, x_310);
x_3 = x_317;
goto lbl_4;
}
else
{
obj* x_319; obj* x_322; 
lean::dec(x_307);
x_319 = lean::cnstr_get(x_305, 1);
lean::inc(x_319);
lean::dec(x_305);
x_322 = l_lean_ir_var_defined(x_303, x_1, x_319);
lean::dec(x_319);
x_3 = x_322;
goto lbl_4;
}
}
}
lbl_4:
{
obj* x_324; 
x_324 = lean::cnstr_get(x_3, 0);
lean::inc(x_324);
if (lean::obj_tag(x_324) == 0)
{
obj* x_326; obj* x_328; obj* x_329; obj* x_331; obj* x_332; uint8 x_333; obj* x_334; obj* x_335; obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; obj* x_346; 
x_326 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_328 = x_3;
} else {
 lean::inc(x_326);
 lean::dec(x_3);
 x_328 = lean::box(0);
}
x_329 = lean::cnstr_get(x_324, 0);
if (lean::is_exclusive(x_324)) {
 x_331 = x_324;
} else {
 lean::inc(x_329);
 lean::dec(x_324);
 x_331 = lean::box(0);
}
x_332 = l_lean_ir_instr_to__format___main(x_0);
x_333 = 0;
x_334 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
x_335 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_335, 0, x_334);
lean::cnstr_set(x_335, 1, x_332);
lean::cnstr_set_scalar(x_335, sizeof(void*)*2, x_333);
x_336 = x_335;
x_337 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_338 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_338, 0, x_336);
lean::cnstr_set(x_338, 1, x_337);
lean::cnstr_set_scalar(x_338, sizeof(void*)*2, x_333);
x_339 = x_338;
x_340 = lean::box(1);
x_341 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_341, 0, x_339);
lean::cnstr_set(x_341, 1, x_340);
lean::cnstr_set_scalar(x_341, sizeof(void*)*2, x_333);
x_342 = x_341;
x_343 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_343, 0, x_342);
lean::cnstr_set(x_343, 1, x_329);
lean::cnstr_set_scalar(x_343, sizeof(void*)*2, x_333);
x_344 = x_343;
if (lean::is_scalar(x_331)) {
 x_345 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_345 = x_331;
}
lean::cnstr_set(x_345, 0, x_344);
if (lean::is_scalar(x_328)) {
 x_346 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_346 = x_328;
}
lean::cnstr_set(x_346, 0, x_345);
lean::cnstr_set(x_346, 1, x_326);
return x_346;
}
else
{
obj* x_348; obj* x_350; obj* x_351; 
lean::dec(x_0);
x_348 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_350 = x_3;
} else {
 lean::inc(x_348);
 lean::dec(x_3);
 x_350 = lean::box(0);
}
if (lean::is_scalar(x_350)) {
 x_351 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_351 = x_350;
}
lean::cnstr_set(x_351, 0, x_324);
lean::cnstr_set(x_351, 1, x_348);
return x_351;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__2(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__3(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_ir_instr_valid__ssa___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_instr_valid__ssa(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_ir_terminator_valid__ssa(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
switch (lean::obj_tag(x_0)) {
case 2:
{
obj* x_6; 
x_6 = l_lean_ir_var_declare___closed__1;
lean::inc(x_2);
x_3 = x_6;
x_4 = x_2;
goto lbl_5;
}
default:
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = l_lean_ir_var_defined(x_8, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_3 = x_11;
x_4 = x_13;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_16; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_16 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_18 = x_3;
} else {
 lean::inc(x_16);
 lean::dec(x_3);
 x_18 = lean::box(0);
}
x_19 = l_lean_ir_terminator_to__format___main(x_0);
x_20 = 0;
x_21 = l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_20);
x_23 = x_22;
x_24 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_20);
x_26 = x_25;
x_27 = lean::box(1);
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_20);
x_29 = x_28;
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_16);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_20);
x_31 = x_30;
if (lean::is_scalar(x_18)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_18;
}
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_4);
return x_33;
}
else
{
obj* x_35; 
lean::dec(x_0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_3);
lean::cnstr_set(x_35, 1, x_4);
return x_35;
}
}
}
}
obj* l_lean_ir_terminator_valid__ssa___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_terminator_valid__ssa(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_find__core___main___at_lean_ir_phi_predecessors___spec__3(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
x_6 = lean::cnstr_get(x_0, 3);
x_7 = l_lean_name_quick__lt___main(x_1, x_4);
x_8 = lean::unbox(x_7);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = l_lean_name_quick__lt___main(x_4, x_1);
x_10 = lean::unbox(x_9);
if (x_10 == 0)
{
obj* x_13; obj* x_14; 
lean::inc(x_5);
lean::inc(x_4);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_4);
lean::cnstr_set(x_13, 1, x_5);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
else
{
x_0 = x_6;
goto _start;
}
}
else
{
x_0 = x_3;
goto _start;
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
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
}
}
obj* l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_6; obj* x_7; 
x_3 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
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
obj* l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; obj* x_8; 
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::inc(x_4);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_14; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::dec(x_2);
x_14 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(x_3, x_9);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
lean::dec(x_1);
lean::dec(x_11);
x_17 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_9);
x_18 = 0;
x_19 = l_lean_ir_var_defined___closed__1;
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_17);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_18);
x_21 = x_20;
x_22 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1;
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_18);
x_24 = x_23;
x_25 = l_lean_ir_phi_to__format___main(x_0);
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_18);
x_27 = x_26;
x_28 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_29 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_18);
x_30 = x_29;
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::inc(x_4);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_4);
return x_33;
}
else
{
obj* x_35; obj* x_38; uint8 x_39; 
lean::dec(x_9);
x_35 = lean::cnstr_get(x_14, 0);
lean::inc(x_35);
lean::dec(x_14);
x_38 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_1, x_35);
x_39 = l_option_is__some___main___rarg(x_38);
lean::dec(x_38);
if (x_39 == 0)
{
obj* x_41; obj* x_42; 
x_41 = lean::box(0);
x_42 = l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5(x_1, x_35, x_41);
lean::dec(x_35);
x_1 = x_42;
x_2 = x_11;
goto _start;
}
else
{
obj* x_48; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_58; 
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_35);
x_48 = l_lean_ir_phi_to__format___main(x_0);
x_49 = 0;
x_50 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__2;
x_51 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_48);
lean::cnstr_set_scalar(x_51, sizeof(void*)*2, x_49);
x_52 = x_51;
x_53 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_54 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_53);
lean::cnstr_set_scalar(x_54, sizeof(void*)*2, x_49);
x_55 = x_54;
x_56 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::inc(x_4);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_4);
return x_58;
}
}
}
}
}
obj* l_lean_ir_phi_predecessors(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = l_lean_ir_mk__blockid__set;
x_6 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7(x_0, x_5, x_3, x_1, x_2);
return x_6;
}
}
obj* l_rbnode_find__core___main___at_lean_ir_phi_predecessors___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find__core___main___at_lean_ir_phi_predecessors___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find__core___main___at_lean_ir_phi_predecessors___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find__core___main___at_lean_ir_phi_predecessors___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbtree_find___at_lean_ir_phi_predecessors___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_ir_phi_predecessors___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_ir_phi_predecessors___spec__4(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_ir_phi_predecessors___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_phi_predecessors(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; obj* x_3; 
x_2 = 1;
x_3 = lean::box(x_2);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 3);
x_7 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_0, x_5);
x_8 = l_option_to__bool___main___rarg(x_7);
lean::dec(x_7);
if (x_8 == 0)
{
if (x_8 == 0)
{
obj* x_10; 
x_10 = lean::box(x_8);
return x_10;
}
else
{
x_1 = x_6;
goto _start;
}
}
else
{
obj* x_12; uint8 x_13; 
x_12 = l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(x_0, x_4);
x_13 = lean::unbox(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
x_1 = x_6;
goto _start;
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
obj* x_2; uint8 x_3; 
x_2 = l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(x_1, x_0);
x_3 = lean::unbox(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
obj* x_4; 
x_4 = l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(x_0, x_1);
return x_4;
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
obj* l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_15; obj* x_17; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
lean::inc(x_6);
x_15 = l_lean_ir_phi_predecessors(x_6, x_2, x_3);
lean::dec(x_3);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_20; obj* x_23; obj* x_25; obj* x_26; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_15, 1);
lean::inc(x_20);
lean::dec(x_15);
x_23 = lean::cnstr_get(x_17, 0);
if (lean::is_exclusive(x_17)) {
 x_25 = x_17;
} else {
 lean::inc(x_23);
 lean::dec(x_17);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_23);
x_11 = x_26;
x_12 = x_20;
goto lbl_13;
}
else
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_27; obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
x_27 = lean::cnstr_get(x_15, 1);
lean::inc(x_27);
lean::dec(x_15);
x_30 = lean::cnstr_get(x_17, 0);
if (lean::is_exclusive(x_17)) {
 x_32 = x_17;
} else {
 lean::inc(x_30);
 lean::dec(x_17);
 x_32 = lean::box(0);
}
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_30);
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_33);
x_11 = x_34;
x_12 = x_27;
goto lbl_13;
}
else
{
obj* x_35; obj* x_38; obj* x_40; obj* x_41; obj* x_43; uint8 x_46; 
x_35 = lean::cnstr_get(x_15, 1);
lean::inc(x_35);
lean::dec(x_15);
x_38 = lean::cnstr_get(x_17, 0);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_set(x_17, 0, lean::box(0));
 x_40 = x_17;
} else {
 lean::inc(x_38);
 lean::dec(x_17);
 x_40 = lean::box(0);
}
x_41 = lean::cnstr_get(x_0, 0);
lean::inc(x_41);
x_43 = l_rbtree_seteq___at_lean_ir_phis_check__predecessors___spec__1(x_41, x_38);
lean::dec(x_38);
lean::dec(x_41);
x_46 = lean::unbox(x_43);
if (x_46 == 0)
{
obj* x_48; obj* x_50; uint8 x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_0);
x_48 = lean::cnstr_get(x_6, 0);
lean::inc(x_48);
x_50 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_48);
x_51 = 0;
x_52 = l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___closed__1;
x_53 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_50);
lean::cnstr_set_scalar(x_53, sizeof(void*)*2, x_51);
x_54 = x_53;
x_55 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1;
x_56 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
lean::cnstr_set_scalar(x_56, sizeof(void*)*2, x_51);
x_57 = x_56;
lean::inc(x_6);
x_59 = l_lean_ir_phi_to__format___main(x_6);
x_60 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_60, 0, x_57);
lean::cnstr_set(x_60, 1, x_59);
lean::cnstr_set_scalar(x_60, sizeof(void*)*2, x_51);
x_61 = x_60;
x_62 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_63 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set(x_63, 1, x_62);
lean::cnstr_set_scalar(x_63, sizeof(void*)*2, x_51);
x_64 = x_63;
if (lean::is_scalar(x_40)) {
 x_65 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_65 = x_40;
 lean::cnstr_set_tag(x_40, 0);
}
lean::cnstr_set(x_65, 0, x_64);
x_11 = x_65;
x_12 = x_35;
goto lbl_13;
}
else
{
obj* x_66; 
if (lean::is_scalar(x_40)) {
 x_66 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_66 = x_40;
}
lean::cnstr_set(x_66, 0, x_0);
x_11 = x_66;
x_12 = x_35;
goto lbl_13;
}
}
}
lbl_13:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_68; obj* x_70; obj* x_71; uint8 x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_8);
x_68 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_70 = x_11;
} else {
 lean::inc(x_68);
 lean::dec(x_11);
 x_70 = lean::box(0);
}
x_71 = l_lean_ir_phi_to__format___main(x_6);
x_72 = 0;
x_73 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
x_74 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_71);
lean::cnstr_set_scalar(x_74, sizeof(void*)*2, x_72);
x_75 = x_74;
x_76 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_77 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_77, 0, x_75);
lean::cnstr_set(x_77, 1, x_76);
lean::cnstr_set_scalar(x_77, sizeof(void*)*2, x_72);
x_78 = x_77;
x_79 = lean::box(1);
x_80 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_79);
lean::cnstr_set_scalar(x_80, sizeof(void*)*2, x_72);
x_81 = x_80;
x_82 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_68);
lean::cnstr_set_scalar(x_82, sizeof(void*)*2, x_72);
x_83 = x_82;
if (lean::is_scalar(x_70)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_70;
}
lean::cnstr_set(x_84, 0, x_83);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_12);
return x_85;
}
else
{
lean::dec(x_6);
if (lean::obj_tag(x_11) == 0)
{
obj* x_88; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_8);
x_88 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_90 = x_11;
} else {
 lean::inc(x_88);
 lean::dec(x_11);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_88);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_12);
return x_92;
}
else
{
obj* x_93; 
x_93 = lean::cnstr_get(x_11, 0);
lean::inc(x_93);
lean::dec(x_11);
x_0 = x_93;
x_1 = x_8;
x_3 = x_12;
goto _start;
}
}
}
}
}
}
obj* l_lean_ir_phis_check__predecessors(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::box(0);
x_4 = l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4(x_3, x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_12 = x_5;
} else {
 lean::inc(x_10);
 lean::dec(x_5);
 x_12 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_13 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_13 = x_12;
}
lean::cnstr_set(x_13, 0, x_10);
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_9;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
else
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_5);
x_16 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_18 = x_4;
} else {
 lean::inc(x_16);
 lean::dec(x_4);
 x_18 = lean::box(0);
}
x_19 = l_lean_ir_var_declare___closed__1;
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
return x_20;
}
}
}
obj* l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbtree_subset___at_lean_ir_phis_check__predecessors___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbtree_subset___at_lean_ir_phis_check__predecessors___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbtree_seteq___at_lean_ir_phis_check__predecessors___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbtree_seteq___at_lean_ir_phis_check__predecessors___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_ir_phis_check__predecessors___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_phis_check__predecessors(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_var_declare___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_phi_valid__ssa(x_5, x_1, x_2);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_7);
x_15 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_17 = x_10;
} else {
 lean::inc(x_15);
 lean::dec(x_10);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_20 = x_12;
} else {
 lean::inc(x_18);
 lean::dec(x_12);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
if (lean::is_scalar(x_17)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_17;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_15);
return x_22;
}
else
{
obj* x_24; 
lean::dec(x_12);
x_24 = lean::cnstr_get(x_10, 1);
lean::inc(x_24);
lean::dec(x_10);
x_0 = x_7;
x_2 = x_24;
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
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_var_declare___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_instr_valid__ssa(x_5, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_14 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_16 = x_10;
} else {
 lean::inc(x_14);
 lean::dec(x_10);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_19 = x_11;
} else {
 lean::inc(x_17);
 lean::dec(x_11);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
return x_21;
}
else
{
obj* x_23; 
lean::dec(x_11);
x_23 = lean::cnstr_get(x_10, 1);
lean::inc(x_23);
lean::dec(x_10);
x_0 = x_7;
x_2 = x_23;
goto _start;
}
}
}
}
obj* l_lean_ir_block_valid__ssa__core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::inc(x_6);
x_9 = l_lean_ir_phis_check__predecessors(x_6, x_1, x_2);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_16; obj* x_18; obj* x_19; 
lean::dec(x_6);
x_13 = lean::cnstr_get(x_9, 1);
lean::inc(x_13);
lean::dec(x_9);
x_16 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_18 = x_10;
} else {
 lean::inc(x_16);
 lean::dec(x_10);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
x_3 = x_19;
x_4 = x_13;
goto lbl_5;
}
else
{
obj* x_21; obj* x_24; obj* x_25; 
lean::dec(x_10);
x_21 = lean::cnstr_get(x_9, 1);
lean::inc(x_21);
lean::dec(x_9);
x_24 = l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__1(x_6, x_1, x_21);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_27; obj* x_30; obj* x_32; obj* x_33; 
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_30 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_32 = x_25;
} else {
 lean::inc(x_30);
 lean::dec(x_25);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
x_3 = x_33;
x_4 = x_27;
goto lbl_5;
}
else
{
obj* x_35; obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_25);
x_35 = lean::cnstr_get(x_24, 1);
lean::inc(x_35);
lean::dec(x_24);
x_38 = lean::cnstr_get(x_0, 2);
lean::inc(x_38);
x_40 = l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__2(x_38, x_1, x_35);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_43; obj* x_46; obj* x_48; obj* x_49; 
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
x_46 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_48 = x_41;
} else {
 lean::inc(x_46);
 lean::dec(x_41);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_46);
x_3 = x_49;
x_4 = x_43;
goto lbl_5;
}
else
{
obj* x_51; obj* x_54; obj* x_56; obj* x_58; obj* x_60; 
lean::dec(x_41);
x_51 = lean::cnstr_get(x_40, 1);
lean::inc(x_51);
lean::dec(x_40);
x_54 = lean::cnstr_get(x_0, 3);
lean::inc(x_54);
x_56 = l_lean_ir_terminator_valid__ssa(x_54, x_1, x_51);
lean::dec(x_51);
x_58 = lean::cnstr_get(x_56, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_56, 1);
lean::inc(x_60);
lean::dec(x_56);
x_3 = x_58;
x_4 = x_60;
goto lbl_5;
}
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_63; obj* x_65; obj* x_66; obj* x_69; uint8 x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_63 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_65 = x_3;
} else {
 lean::inc(x_63);
 lean::dec(x_3);
 x_65 = lean::box(0);
}
x_66 = lean::cnstr_get(x_0, 0);
lean::inc(x_66);
lean::dec(x_0);
x_69 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_66);
x_70 = 0;
x_71 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
x_72 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_69);
lean::cnstr_set_scalar(x_72, sizeof(void*)*2, x_70);
x_73 = x_72;
x_74 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_75 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_75, 0, x_73);
lean::cnstr_set(x_75, 1, x_74);
lean::cnstr_set_scalar(x_75, sizeof(void*)*2, x_70);
x_76 = x_75;
x_77 = lean::box(1);
x_78 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_77);
lean::cnstr_set_scalar(x_78, sizeof(void*)*2, x_70);
x_79 = x_78;
x_80 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_63);
lean::cnstr_set_scalar(x_80, sizeof(void*)*2, x_70);
x_81 = x_80;
if (lean::is_scalar(x_65)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_65;
}
lean::cnstr_set(x_82, 0, x_81);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_4);
return x_83;
}
else
{
obj* x_85; 
lean::dec(x_0);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_3);
lean::cnstr_set(x_85, 1, x_4);
return x_85;
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__2(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_ir_block_valid__ssa__core___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_block_valid__ssa__core(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_var_declare___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
x_7 = l_lean_ir_arg_define(x_5, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_12 = x_7;
} else {
 lean::inc(x_10);
 lean::dec(x_7);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_15 = x_8;
} else {
 lean::inc(x_13);
 lean::dec(x_8);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
if (lean::is_scalar(x_12)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_12;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_19; 
lean::dec(x_8);
x_19 = lean::cnstr_get(x_7, 1);
lean::inc(x_19);
lean::dec(x_7);
x_0 = x_6;
x_2 = x_19;
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
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
if (lean::is_scalar(x_8)) {
 x_9 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_9 = x_8;
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
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2___rarg), 4, 0);
return x_2;
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
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_ir_decl_valid__ssa___spec__3___rarg), 4, 0);
return x_2;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_var_declare___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_block_valid__ssa__core(x_5, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_14 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_16 = x_10;
} else {
 lean::inc(x_14);
 lean::dec(x_10);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_19 = x_11;
} else {
 lean::inc(x_17);
 lean::dec(x_11);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
return x_21;
}
else
{
obj* x_23; 
lean::dec(x_11);
x_23 = lean::cnstr_get(x_10, 1);
lean::inc(x_23);
lean::dec(x_10);
x_0 = x_7;
x_2 = x_23;
goto _start;
}
}
}
}
obj* l_lean_ir_decl_valid__ssa___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_block_valid__ssa__core(x_0, x_2, x_3);
return x_4;
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
if (lean::obj_tag(x_0) == 0)
{
obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_0);
x_9 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_9);
return x_12;
}
else
{
obj* x_13; obj* x_15; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 1);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_0);
lean::dec(x_13);
x_19 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_21 = x_4;
} else {
 lean::inc(x_19);
 lean::dec(x_4);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_19);
return x_22;
}
else
{
obj* x_23; obj* x_26; obj* x_29; obj* x_31; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_39; 
x_23 = lean::cnstr_get(x_4, 0);
lean::inc(x_23);
lean::dec(x_4);
x_26 = lean::cnstr_get(x_13, 1);
lean::inc(x_26);
lean::dec(x_13);
x_29 = lean::cnstr_get(x_15, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_15, 1);
lean::inc(x_31);
lean::dec(x_15);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__1___boxed), 3, 1);
lean::closure_set(x_34, 0, x_26);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_decl_valid__ssa___lambda__1___boxed), 4, 1);
lean::closure_set(x_35, 0, x_29);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2___rarg), 4, 1);
lean::closure_set(x_36, 0, x_35);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_ir_decl_valid__ssa___spec__3___rarg), 4, 2);
lean::closure_set(x_37, 0, x_34);
lean::closure_set(x_37, 1, x_36);
lean::inc(x_23);
x_39 = l_lean_ir_ssa__valid__m_run___rarg(x_37, x_23);
if (lean::obj_tag(x_39) == 0)
{
obj* x_42; 
lean::dec(x_23);
lean::dec(x_31);
x_42 = lean::cnstr_get(x_39, 0);
lean::inc(x_42);
lean::dec(x_39);
x_1 = x_42;
goto lbl_2;
}
else
{
obj* x_46; obj* x_48; 
lean::dec(x_39);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__4___boxed), 3, 1);
lean::closure_set(x_46, 0, x_31);
lean::inc(x_23);
x_48 = l_lean_ir_ssa__valid__m_run___rarg(x_46, x_23);
if (lean::obj_tag(x_48) == 0)
{
obj* x_50; 
lean::dec(x_23);
x_50 = lean::cnstr_get(x_48, 0);
lean::inc(x_50);
lean::dec(x_48);
x_1 = x_50;
goto lbl_2;
}
else
{
obj* x_54; obj* x_55; 
lean::dec(x_0);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 x_54 = x_48;
} else {
 lean::dec(x_48);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_23);
return x_55;
}
}
}
}
}
lbl_2:
{
obj* x_56; obj* x_58; obj* x_61; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_56 = l_lean_ir_decl_header___main(x_0);
lean::dec(x_0);
x_58 = lean::cnstr_get(x_56, 0);
lean::inc(x_58);
lean::dec(x_56);
x_61 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_58);
x_62 = 0;
x_63 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
x_64 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_61);
lean::cnstr_set_scalar(x_64, sizeof(void*)*2, x_62);
x_65 = x_64;
x_66 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_67 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set(x_67, 1, x_66);
lean::cnstr_set_scalar(x_67, sizeof(void*)*2, x_62);
x_68 = x_67;
x_69 = lean::box(1);
x_70 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_69);
lean::cnstr_set_scalar(x_70, sizeof(void*)*2, x_62);
x_71 = x_70;
x_72 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_1);
lean::cnstr_set_scalar(x_72, sizeof(void*)*2, x_62);
x_73 = x_72;
x_74 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_74, 0, x_73);
return x_74;
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_reader__t_bind___at_lean_ir_decl_valid__ssa___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_reader__t_bind___at_lean_ir_decl_valid__ssa___spec__3(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__4(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_ir_decl_valid__ssa___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_decl_valid__ssa___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_lean_ir_blockid__check__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_lean_ir_blockid__check__m_run___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_lean_ir_mk__blockid__set;
x_2 = lean::apply_1(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_ir_blockid__check__m_run(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_blockid__check__m_run___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_ir_blockid__check__m_run___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_blockid__check__m_run(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_lean_ir_block_declare(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; uint8 x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_1, x_2);
x_6 = l_option_is__some___main___rarg(x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
x_8 = lean::box(0);
x_9 = l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5(x_1, x_2, x_8);
lean::dec(x_2);
x_11 = l_lean_ir_var_declare___closed__1;
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_9);
return x_12;
}
else
{
obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_13 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_2);
x_14 = 0;
x_15 = l_lean_ir_block_declare___closed__1;
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_13);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_14);
x_17 = x_16;
x_18 = l_lean_ir_block_declare___closed__2;
x_19 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
lean::cnstr_set_scalar(x_19, sizeof(void*)*2, x_14);
x_20 = x_19;
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_1);
return x_22;
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
obj* l_lean_ir_blockid_defined(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_1, x_0);
x_3 = l_option_is__some___main___rarg(x_2);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; 
x_5 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_0);
x_6 = 0;
x_7 = l_lean_ir_blockid_defined___closed__1;
x_8 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_6);
x_9 = x_8;
x_10 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_6);
x_12 = x_11;
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::inc(x_1);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_1);
return x_15;
}
else
{
obj* x_17; obj* x_19; 
lean::dec(x_0);
x_17 = l_lean_ir_var_declare___closed__1;
lean::inc(x_1);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_1);
return x_19;
}
}
}
obj* l_lean_ir_blockid_defined___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_blockid_defined(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_terminator_check__blockids___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_3; 
x_2 = l_lean_ir_var_declare___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_11; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_lean_ir_blockid_defined(x_4, x_1);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_6);
x_14 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_16 = x_9;
} else {
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_19 = x_11;
} else {
 lean::inc(x_17);
 lean::dec(x_11);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
return x_21;
}
else
{
obj* x_23; 
lean::dec(x_11);
x_23 = lean::cnstr_get(x_9, 1);
lean::inc(x_23);
lean::dec(x_9);
x_0 = x_6;
x_1 = x_23;
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
x_2 = x_5;
x_3 = x_1;
goto lbl_4;
}
case 1:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = l_list_mmap_x_27___main___at_lean_ir_terminator_check__blockids___spec__1(x_6, x_1);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_2 = x_9;
x_3 = x_11;
goto lbl_4;
}
default:
{
obj* x_14; obj* x_16; obj* x_18; obj* x_20; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
x_16 = l_lean_ir_blockid_defined(x_14, x_1);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
lean::dec(x_16);
x_2 = x_18;
x_3 = x_20;
goto lbl_4;
}
}
lbl_4:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_23; obj* x_25; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_23 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_25 = x_2;
} else {
 lean::inc(x_23);
 lean::dec(x_2);
 x_25 = lean::box(0);
}
x_26 = l_lean_ir_terminator_to__format___main(x_0);
x_27 = 0;
x_28 = l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
x_29 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_26);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_27);
x_30 = x_29;
x_31 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_32 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
lean::cnstr_set_scalar(x_32, sizeof(void*)*2, x_27);
x_33 = x_32;
x_34 = lean::box(1);
x_35 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_34);
lean::cnstr_set_scalar(x_35, sizeof(void*)*2, x_27);
x_36 = x_35;
x_37 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_23);
lean::cnstr_set_scalar(x_37, sizeof(void*)*2, x_27);
x_38 = x_37;
if (lean::is_scalar(x_25)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_25;
}
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_3);
return x_40;
}
else
{
obj* x_42; 
lean::dec(x_0);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_2);
lean::cnstr_set(x_42, 1, x_3);
return x_42;
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
obj* x_2; obj* x_3; 
x_2 = l_lean_ir_var_declare___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_lean_ir_block_declare(x_4, x_1);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_6);
x_13 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_15 = x_9;
} else {
 lean::inc(x_13);
 lean::dec(x_9);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_18 = x_10;
} else {
 lean::inc(x_16);
 lean::dec(x_10);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_13);
return x_20;
}
else
{
obj* x_22; 
lean::dec(x_10);
x_22 = lean::cnstr_get(x_9, 1);
lean::inc(x_22);
lean::dec(x_9);
x_0 = x_6;
x_1 = x_22;
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
obj* x_2; obj* x_3; 
x_2 = l_lean_ir_var_declare___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_lean_ir_block_check__blockids(x_4, x_1);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_6);
x_13 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_15 = x_9;
} else {
 lean::inc(x_13);
 lean::dec(x_9);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_18 = x_10;
} else {
 lean::inc(x_16);
 lean::dec(x_10);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_13);
return x_20;
}
else
{
obj* x_22; 
lean::dec(x_10);
x_22 = lean::cnstr_get(x_9, 1);
lean::inc(x_22);
lean::dec(x_9);
x_0 = x_6;
x_1 = x_22;
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
obj* x_3; obj* x_4; 
lean::dec(x_0);
x_3 = l_lean_ir_var_declare___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
lean::inc(x_7);
x_11 = l_list_mmap_x_27___main___at_lean_ir_decl_check__blockids___main___spec__1(x_7, x_1);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_24; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_7);
x_15 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_17 = x_11;
} else {
 lean::inc(x_15);
 lean::dec(x_11);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_20 = x_12;
} else {
 lean::inc(x_18);
 lean::dec(x_12);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_5, 0);
lean::inc(x_21);
lean::dec(x_5);
x_24 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_21);
x_25 = 0;
x_26 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_24);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_25);
x_28 = x_27;
x_29 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_25);
x_31 = x_30;
x_32 = lean::box(1);
x_33 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
lean::cnstr_set_scalar(x_33, sizeof(void*)*2, x_25);
x_34 = x_33;
x_35 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_18);
lean::cnstr_set_scalar(x_35, sizeof(void*)*2, x_25);
x_36 = x_35;
if (lean::is_scalar(x_20)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_20;
}
lean::cnstr_set(x_37, 0, x_36);
if (lean::is_scalar(x_17)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_17;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_15);
return x_38;
}
else
{
obj* x_40; obj* x_43; obj* x_44; 
lean::dec(x_12);
x_40 = lean::cnstr_get(x_11, 1);
lean::inc(x_40);
lean::dec(x_11);
x_43 = l_list_mmap_x_27___main___at_lean_ir_decl_check__blockids___main___spec__2(x_7, x_40);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_46; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_55; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_46 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_48 = x_43;
} else {
 lean::inc(x_46);
 lean::dec(x_43);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 x_51 = x_44;
} else {
 lean::inc(x_49);
 lean::dec(x_44);
 x_51 = lean::box(0);
}
x_52 = lean::cnstr_get(x_5, 0);
lean::inc(x_52);
lean::dec(x_5);
x_55 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_52);
x_56 = 0;
x_57 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
x_58 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_55);
lean::cnstr_set_scalar(x_58, sizeof(void*)*2, x_56);
x_59 = x_58;
x_60 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_61 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_60);
lean::cnstr_set_scalar(x_61, sizeof(void*)*2, x_56);
x_62 = x_61;
x_63 = lean::box(1);
x_64 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set(x_64, 1, x_63);
lean::cnstr_set_scalar(x_64, sizeof(void*)*2, x_56);
x_65 = x_64;
x_66 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_49);
lean::cnstr_set_scalar(x_66, sizeof(void*)*2, x_56);
x_67 = x_66;
if (lean::is_scalar(x_51)) {
 x_68 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_68 = x_51;
}
lean::cnstr_set(x_68, 0, x_67);
if (lean::is_scalar(x_48)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_48;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_46);
return x_69;
}
else
{
obj* x_71; obj* x_73; obj* x_74; 
lean::dec(x_5);
x_71 = lean::cnstr_get(x_43, 1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_73 = x_43;
} else {
 lean::inc(x_71);
 lean::dec(x_43);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_44);
lean::cnstr_set(x_74, 1, x_71);
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
if (lean::is_exclusive(x_1)) {
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_7 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_7 = x_6;
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
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_check__blockids___spec__1___rarg), 3, 0);
return x_2;
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
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_bind___at_lean_ir_check__blockids___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_ir_check__blockids___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_5; 
lean::inc(x_1);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::inc(x_1);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* _init_l_lean_ir_check__blockids___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_check__blockids___lambda__1___boxed), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_check__blockids___spec__1___rarg), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_check__blockids(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_decl_check__blockids), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = l_lean_ir_check__blockids___closed__1;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_bind___at_lean_ir_check__blockids___spec__2___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
x_4 = l_lean_ir_blockid__check__m_run___rarg(x_3);
return x_4;
}
}
obj* l_except__t_bind__cont___at_lean_ir_check__blockids___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_except__t_bind__cont___at_lean_ir_check__blockids___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_state__t_bind___at_lean_ir_check__blockids___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_state__t_bind___at_lean_ir_check__blockids___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_ir_check__blockids___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_check__blockids___lambda__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
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
lean::mark_persistent(l_lean_ir_ssa__pre__m);
 l_lean_ir_var_declare___closed__1 = _init_l_lean_ir_var_declare___closed__1();
lean::mark_persistent(l_lean_ir_var_declare___closed__1);
 l_lean_ir_var_declare___closed__2 = _init_l_lean_ir_var_declare___closed__2();
lean::mark_persistent(l_lean_ir_var_declare___closed__2);
 l_lean_ir_decl_declare__vars___main___closed__1 = _init_l_lean_ir_decl_declare__vars___main___closed__1();
lean::mark_persistent(l_lean_ir_decl_declare__vars___main___closed__1);
 l_lean_ir_ssa__valid__m = _init_l_lean_ir_ssa__valid__m();
lean::mark_persistent(l_lean_ir_ssa__valid__m);
 l_lean_ir_var_defined___closed__1 = _init_l_lean_ir_var_defined___closed__1();
lean::mark_persistent(l_lean_ir_var_defined___closed__1);
 l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1 = _init_l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1();
lean::mark_persistent(l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1);
 l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__2 = _init_l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__2();
lean::mark_persistent(l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__2);
 l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___closed__1 = _init_l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___closed__1();
lean::mark_persistent(l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___closed__1);
 l_lean_ir_blockid__check__m = _init_l_lean_ir_blockid__check__m();
lean::mark_persistent(l_lean_ir_blockid__check__m);
 l_lean_ir_block_declare___closed__1 = _init_l_lean_ir_block_declare___closed__1();
lean::mark_persistent(l_lean_ir_block_declare___closed__1);
 l_lean_ir_block_declare___closed__2 = _init_l_lean_ir_block_declare___closed__2();
lean::mark_persistent(l_lean_ir_block_declare___closed__2);
 l_lean_ir_blockid_defined___closed__1 = _init_l_lean_ir_blockid_defined___closed__1();
lean::mark_persistent(l_lean_ir_blockid_defined___closed__1);
 l_lean_ir_check__blockids___closed__1 = _init_l_lean_ir_check__blockids___closed__1();
lean::mark_persistent(l_lean_ir_check__blockids___closed__1);
}
