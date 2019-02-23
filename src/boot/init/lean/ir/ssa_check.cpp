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
obj* l_lean_ir_blockid_defined___closed__1;
obj* l_lean_ir_ssa__valid__m;
obj* l_list_mmap_x_27___main___at_lean_ir_decl_check__blockids___main___spec__1(obj*, obj*);
obj* l_lean_ir_block_declare___closed__1;
obj* l_lean_ir_terminator_valid__ssa(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_ir_phi_valid__ssa(obj*, obj*, obj*);
obj* l_lean_ir_ssa__valid__m_run___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__2___boxed(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__3(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__2(obj*, obj*, obj*);
obj* l_rbmap_find__core___main___at_lean_ir_var_defined___spec__2___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(obj*, obj*, obj*);
obj* l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(obj*);
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(obj*, obj*);
obj* l_lean_ir_decl_valid__ssa___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_ir_instr_valid__ssa___boxed(obj*, obj*, obj*);
obj* l_rbtree_find___at_lean_ir_var_defined___spec__1___boxed(obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2___boxed(obj*, obj*);
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
uint8 l_option_is__some___main___rarg(obj*);
obj* l_rbtree_find___at_lean_ir_var_defined___spec__1(obj*, obj*);
obj* l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(obj*);
obj* l_rbmap_find___main___at_lean_ir_var_declare___spec__1___boxed(obj*, obj*);
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
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2___boxed(obj*);
obj* l_lean_ir_terminator_valid__ssa___boxed(obj*, obj*, obj*);
obj* l_rbnode_find__core___main___at_lean_ir_phi_predecessors___spec__3___boxed(obj*, obj*);
obj* l_lean_ir_var_defined(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_check__blockids___main___spec__2(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_phi_predecessors___spec__4(obj*, obj*, obj*);
obj* l_lean_ir_blockid__check__m;
obj* l_lean_ir_check__blockids(obj*);
obj* l_lean_ir_block_declare(obj*, obj*);
extern obj* l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
obj* l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__2(obj*, obj*, obj*);
obj* l_rbnode_find__core___main___at_lean_ir_var_defined___spec__3___boxed(obj*, obj*);
obj* l_state__t_bind___at_lean_ir_check__blockids___spec__2___rarg(obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___closed__1;
obj* l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_check__blockids___lambda__1___boxed(obj*, obj*);
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
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
obj* l_rbtree_find___at_lean_ir_phi_predecessors___spec__1___boxed(obj*, obj*);
obj* l_lean_ir_decl_check__blockids___main(obj*, obj*);
obj* l_lean_ir_blockid__check__m_run___rarg(obj*);
obj* l_lean_ir_check__blockids___lambda__1(obj*, obj*);
obj* l_lean_ir_instr_valid__ssa(obj*, obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_check__blockids___spec__1___boxed(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1;
obj* l_lean_ir_blockid__check__m_run___boxed(obj*);
extern obj* l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
obj* l_lean_ir_decl_valid__ssa(obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__1___boxed(obj*, obj*, obj*);
extern obj* l_lean_ir_mk__blockid__set;
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg___boxed(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_var_define___spec__3(obj*, obj*, obj*);
obj* l_lean_ir_arg_define(obj*, obj*, obj*);
obj* l_lean_ir_var_declare___closed__2;
obj* l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(obj*);
obj* l_lean_ir_decl_declare__vars(obj*, obj*);
obj* l_rbnode_balance1___main___rarg(obj*, obj*);
obj* l_lean_ir_arg_declare(obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_ir_var_declare___spec__4(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2(obj*);
obj* l_lean_ir_decl_valid__ssa___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_instr_declare__vars(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__1___boxed(obj*, obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_var_define___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_decl_declare__vars___main(obj*, obj*);
extern obj* l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
obj* l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3___boxed(obj*, obj*);
obj* l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__2___boxed(obj*, obj*, obj*);
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
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; uint8 x_13; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_lean_name_quick__lt___main(x_1, x_5);
x_13 = lean::unbox(x_12);
if (x_13 == 0)
{
obj* x_15; uint8 x_17; 
lean::dec(x_3);
x_15 = l_lean_name_quick__lt___main(x_5, x_1);
lean::dec(x_5);
x_17 = lean::unbox(x_15);
if (x_17 == 0)
{
obj* x_19; 
lean::dec(x_9);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_7);
return x_19;
}
else
{
lean::dec(x_7);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
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
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_lean_name_quick__lt___main(x_1, x_9);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
x_18 = l_lean_name_quick__lt___main(x_9, x_1);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_13);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_15;
}
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_9);
lean::cnstr_set(x_25, 2, x_11);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_6);
x_26 = x_25;
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_15;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_9);
lean::cnstr_set(x_28, 2, x_11);
lean::cnstr_set(x_28, 3, x_13);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_6);
x_29 = x_28;
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 2);
x_36 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = l_lean_name_quick__lt___main(x_1, x_32);
x_40 = lean::unbox(x_39);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = l_lean_name_quick__lt___main(x_32, x_1);
x_42 = lean::unbox(x_41);
if (x_42 == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_34);
lean::dec(x_32);
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_30);
lean::cnstr_set(x_45, 1, x_1);
lean::cnstr_set(x_45, 2, x_2);
lean::cnstr_set(x_45, 3, x_36);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
uint8 x_47; 
x_47 = l_rbnode_is__red___main___rarg(x_36);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_38;
}
lean::cnstr_set(x_49, 0, x_30);
lean::cnstr_set(x_49, 1, x_32);
lean::cnstr_set(x_49, 2, x_34);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_6);
x_50 = x_49;
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_52 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_52 = x_38;
}
lean::cnstr_set(x_52, 0, x_30);
lean::cnstr_set(x_52, 1, x_32);
lean::cnstr_set(x_52, 2, x_34);
lean::cnstr_set(x_52, 3, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_6);
x_53 = x_52;
x_54 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_36, x_1, x_2);
x_55 = l_rbnode_balance2___main___rarg(x_53, x_54);
return x_55;
}
}
}
else
{
uint8 x_56; 
x_56 = l_rbnode_is__red___main___rarg(x_30);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_36);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_6);
x_59 = x_58;
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_38;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_32);
lean::cnstr_set(x_61, 2, x_34);
lean::cnstr_set(x_61, 3, x_36);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_6);
x_62 = x_61;
x_63 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_30, x_1, x_2);
x_64 = l_rbnode_balance1___main___rarg(x_62, x_63);
return x_64;
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
obj* x_4; uint8 x_5; 
lean::inc(x_2);
x_4 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(x_2, x_0);
x_5 = l_option_is__some___main___rarg(x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = l_rbnode_insert___at_lean_ir_var_declare___spec__4(x_2, x_0, x_1);
x_8 = l_lean_ir_var_declare___closed__1;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
return x_9;
}
else
{
obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
x_11 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_12 = 0;
x_13 = l_lean_ir_var_declare___closed__2;
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_11);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_12);
x_15 = x_14;
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_2);
return x_17;
}
}
}
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(x_0, x_1);
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
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_ir_instr_declare__vars___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 4:
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_var_declare___closed__1;
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
case 7:
{
obj* x_9; obj* x_10; 
lean::dec(x_1);
lean::dec(x_0);
x_9 = l_lean_ir_var_declare___closed__1;
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_2);
return x_10;
}
case 9:
{
obj* x_13; obj* x_14; 
lean::dec(x_1);
lean::dec(x_0);
x_13 = l_lean_ir_var_declare___closed__1;
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_2);
return x_14;
}
case 15:
{
obj* x_17; obj* x_18; 
lean::dec(x_1);
lean::dec(x_0);
x_17 = l_lean_ir_var_declare___closed__1;
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_2);
return x_18;
}
default:
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_0, 0);
lean::inc(x_19);
lean::dec(x_0);
x_22 = l_lean_ir_var_declare(x_19, x_1, x_2);
return x_22;
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
obj* l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_phi_declare(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
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
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_instr_declare__vars___main(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
goto _start;
}
}
}
}
obj* l_lean_ir_block_declare__vars(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::inc(x_4);
x_7 = l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__1(x_2, x_4, x_1);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_13 = x_7;
} else {
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_16 = x_8;
} else {
 lean::inc(x_14);
 lean::dec(x_8);
 x_16 = lean::box(0);
}
x_17 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_4);
x_18 = 0;
x_19 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_17);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_18);
x_21 = x_20;
x_22 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_18);
x_24 = x_23;
x_25 = lean::box(1);
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_18);
x_27 = x_26;
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_14);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_18);
x_29 = x_28;
if (lean::is_scalar(x_16)) {
 x_30 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_30 = x_16;
}
lean::cnstr_set(x_30, 0, x_29);
if (lean::is_scalar(x_13)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_13;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_11);
return x_31;
}
else
{
obj* x_33; obj* x_36; obj* x_40; obj* x_41; 
lean::dec(x_8);
x_33 = lean::cnstr_get(x_7, 1);
lean::inc(x_33);
lean::dec(x_7);
x_36 = lean::cnstr_get(x_0, 2);
lean::inc(x_36);
lean::dec(x_0);
lean::inc(x_4);
x_40 = l_list_mmap_x_27___main___at_lean_ir_block_declare__vars___spec__2(x_36, x_4, x_33);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_49; uint8 x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_43 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 x_45 = x_40;
} else {
 lean::inc(x_43);
 lean::dec(x_40);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_48 = x_41;
} else {
 lean::inc(x_46);
 lean::dec(x_41);
 x_48 = lean::box(0);
}
x_49 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_4);
x_50 = 0;
x_51 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
x_52 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_49);
lean::cnstr_set_scalar(x_52, sizeof(void*)*2, x_50);
x_53 = x_52;
x_54 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_55 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*2, x_50);
x_56 = x_55;
x_57 = lean::box(1);
x_58 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*2, x_50);
x_59 = x_58;
x_60 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_46);
lean::cnstr_set_scalar(x_60, sizeof(void*)*2, x_50);
x_61 = x_60;
if (lean::is_scalar(x_48)) {
 x_62 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_62 = x_48;
}
lean::cnstr_set(x_62, 0, x_61);
if (lean::is_scalar(x_45)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_45;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_43);
return x_63;
}
else
{
obj* x_65; obj* x_67; obj* x_68; 
lean::dec(x_4);
x_65 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 x_67 = x_40;
} else {
 lean::inc(x_65);
 lean::dec(x_40);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_41);
lean::cnstr_set(x_68, 1, x_65);
return x_68;
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
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_arg_declare(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
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
obj* x_10; obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; 
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
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_13);
x_29 = lean::cnstr_get(x_25, 1);
lean::inc(x_29);
lean::dec(x_25);
x_32 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_34 = x_26;
} else {
 lean::inc(x_32);
 lean::dec(x_26);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
x_18 = x_35;
x_19 = x_29;
goto lbl_20;
}
else
{
obj* x_37; obj* x_40; obj* x_41; obj* x_43; 
lean::dec(x_26);
x_37 = lean::cnstr_get(x_25, 1);
lean::inc(x_37);
lean::dec(x_25);
x_40 = l_lean_ir_block_declare__vars(x_13, x_37);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
x_18 = x_41;
x_19 = x_43;
goto lbl_20;
}
lbl_20:
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_47; obj* x_49; obj* x_50; obj* x_53; uint8 x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_15);
x_47 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_49 = x_18;
} else {
 lean::inc(x_47);
 lean::dec(x_18);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_10, 0);
lean::inc(x_50);
lean::dec(x_10);
x_53 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_50);
x_54 = 0;
x_55 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
x_56 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_53);
lean::cnstr_set_scalar(x_56, sizeof(void*)*2, x_54);
x_57 = x_56;
x_58 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_59 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set(x_59, 1, x_58);
lean::cnstr_set_scalar(x_59, sizeof(void*)*2, x_54);
x_60 = x_59;
x_61 = lean::box(1);
x_62 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_61);
lean::cnstr_set_scalar(x_62, sizeof(void*)*2, x_54);
x_63 = x_62;
x_64 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_47);
lean::cnstr_set_scalar(x_64, sizeof(void*)*2, x_54);
x_65 = x_64;
if (lean::is_scalar(x_49)) {
 x_66 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_66 = x_49;
}
lean::cnstr_set(x_66, 0, x_65);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_19);
return x_67;
}
else
{
obj* x_69; obj* x_70; 
lean::dec(x_18);
x_69 = l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__1(x_15, x_19);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_81; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_72 = lean::cnstr_get(x_69, 1);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 x_74 = x_69;
} else {
 lean::inc(x_72);
 lean::dec(x_69);
 x_74 = lean::box(0);
}
x_75 = lean::cnstr_get(x_70, 0);
if (lean::is_exclusive(x_70)) {
 x_77 = x_70;
} else {
 lean::inc(x_75);
 lean::dec(x_70);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_10, 0);
lean::inc(x_78);
lean::dec(x_10);
x_81 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_78);
x_82 = 0;
x_83 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
x_84 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_81);
lean::cnstr_set_scalar(x_84, sizeof(void*)*2, x_82);
x_85 = x_84;
x_86 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_87 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set(x_87, 1, x_86);
lean::cnstr_set_scalar(x_87, sizeof(void*)*2, x_82);
x_88 = x_87;
x_89 = lean::box(1);
x_90 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_90, 0, x_88);
lean::cnstr_set(x_90, 1, x_89);
lean::cnstr_set_scalar(x_90, sizeof(void*)*2, x_82);
x_91 = x_90;
x_92 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_75);
lean::cnstr_set_scalar(x_92, sizeof(void*)*2, x_82);
x_93 = x_92;
if (lean::is_scalar(x_77)) {
 x_94 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_94 = x_77;
}
lean::cnstr_set(x_94, 0, x_93);
if (lean::is_scalar(x_74)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_74;
}
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_72);
return x_95;
}
else
{
obj* x_97; obj* x_99; obj* x_100; 
lean::dec(x_10);
x_97 = lean::cnstr_get(x_69, 1);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 x_99 = x_69;
} else {
 lean::inc(x_97);
 lean::dec(x_69);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_70);
lean::cnstr_set(x_100, 1, x_97);
return x_100;
}
}
}
}
}
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
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_lean_name_quick__lt___main(x_1, x_9);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
x_18 = l_lean_name_quick__lt___main(x_9, x_1);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_13);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_15;
}
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_9);
lean::cnstr_set(x_25, 2, x_11);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_6);
x_26 = x_25;
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_15;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_9);
lean::cnstr_set(x_28, 2, x_11);
lean::cnstr_set(x_28, 3, x_13);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_6);
x_29 = x_28;
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 2);
x_36 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = l_lean_name_quick__lt___main(x_1, x_32);
x_40 = lean::unbox(x_39);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = l_lean_name_quick__lt___main(x_32, x_1);
x_42 = lean::unbox(x_41);
if (x_42 == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_34);
lean::dec(x_32);
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_30);
lean::cnstr_set(x_45, 1, x_1);
lean::cnstr_set(x_45, 2, x_2);
lean::cnstr_set(x_45, 3, x_36);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
uint8 x_47; 
x_47 = l_rbnode_is__red___main___rarg(x_36);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_38;
}
lean::cnstr_set(x_49, 0, x_30);
lean::cnstr_set(x_49, 1, x_32);
lean::cnstr_set(x_49, 2, x_34);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_6);
x_50 = x_49;
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_52 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_52 = x_38;
}
lean::cnstr_set(x_52, 0, x_30);
lean::cnstr_set(x_52, 1, x_32);
lean::cnstr_set(x_52, 2, x_34);
lean::cnstr_set(x_52, 3, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_6);
x_53 = x_52;
x_54 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_36, x_1, x_2);
x_55 = l_rbnode_balance2___main___rarg(x_53, x_54);
return x_55;
}
}
}
else
{
uint8 x_56; 
x_56 = l_rbnode_is__red___main___rarg(x_30);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_36);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_6);
x_59 = x_58;
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_38;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_32);
lean::cnstr_set(x_61, 2, x_34);
lean::cnstr_set(x_61, 3, x_36);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_6);
x_62 = x_61;
x_63 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_30, x_1, x_2);
x_64 = l_rbnode_balance1___main___rarg(x_62, x_63);
return x_64;
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
obj* l_lean_ir_var_define___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_var_define(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* l_lean_ir_arg_define___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_arg_define(x_0, x_1, x_2);
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
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; uint8 x_13; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_lean_name_quick__lt___main(x_1, x_5);
x_13 = lean::unbox(x_12);
if (x_13 == 0)
{
obj* x_15; uint8 x_16; 
lean::dec(x_3);
x_15 = l_lean_name_quick__lt___main(x_5, x_1);
x_16 = lean::unbox(x_15);
if (x_16 == 0)
{
obj* x_18; obj* x_19; 
lean::dec(x_9);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_5);
lean::cnstr_set(x_18, 1, x_7);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
else
{
lean::dec(x_7);
lean::dec(x_5);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
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
obj* x_4; uint8 x_5; 
lean::inc(x_2);
x_4 = l_rbtree_find___at_lean_ir_var_defined___spec__1(x_2, x_0);
x_5 = l_option_is__some___main___rarg(x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_7 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_0);
x_8 = 0;
x_9 = l_lean_ir_var_defined___closed__1;
x_10 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_8);
x_11 = x_10;
x_12 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_8);
x_14 = x_13;
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_2);
return x_16;
}
else
{
obj* x_18; obj* x_19; 
lean::dec(x_0);
x_18 = l_lean_ir_var_declare___closed__1;
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_2);
return x_19;
}
}
}
obj* l_rbnode_find__core___main___at_lean_ir_var_defined___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find__core___main___at_lean_ir_var_defined___spec__3(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find__core___main___at_lean_ir_var_defined___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find__core___main___at_lean_ir_var_defined___spec__2(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbtree_find___at_lean_ir_var_defined___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbtree_find___at_lean_ir_var_defined___spec__1(x_0, x_1);
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
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_0);
x_5 = l_lean_ir_var_declare___closed__1;
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; uint8 x_14; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_0);
x_13 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(x_0, x_7);
x_14 = l_option_is__some___main___rarg(x_13);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_9);
lean::dec(x_0);
x_18 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_7);
x_19 = 0;
x_20 = l_lean_ir_var_defined___closed__1;
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_18);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_19);
x_22 = x_21;
x_23 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_19);
x_25 = x_24;
x_26 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_3);
return x_27;
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
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_1);
x_6 = l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1(x_1, x_3, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_1);
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
x_16 = l_lean_ir_phi_to__format___main(x_0);
x_17 = 0;
x_18 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
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
obj* x_32; obj* x_35; obj* x_37; obj* x_39; 
lean::dec(x_7);
x_32 = lean::cnstr_get(x_6, 1);
lean::inc(x_32);
lean::dec(x_6);
x_35 = lean::cnstr_get(x_0, 0);
lean::inc(x_35);
x_37 = l_lean_ir_var_define(x_35, x_1, x_32);
lean::dec(x_1);
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
if (lean::obj_tag(x_39) == 0)
{
obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_47; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_41 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_43 = x_37;
} else {
 lean::inc(x_41);
 lean::dec(x_37);
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
x_47 = l_lean_ir_phi_to__format___main(x_0);
x_48 = 0;
x_49 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
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
lean::dec(x_0);
x_63 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_65 = x_37;
} else {
 lean::inc(x_63);
 lean::dec(x_37);
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
obj* l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
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
obj* x_5; obj* x_7; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_var_defined(x_5, x_1, x_2);
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
obj* x_5; obj* x_7; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_var_defined(x_5, x_1, x_2);
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
obj* x_5; obj* x_7; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_var_defined(x_5, x_1, x_2);
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
x_3 = x_7;
goto lbl_4;
}
case 3:
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 2);
lean::inc(x_12);
x_14 = l_lean_ir_var_define(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_12);
lean::dec(x_10);
x_19 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_21 = x_14;
} else {
 lean::inc(x_19);
 lean::dec(x_14);
 x_21 = lean::box(0);
}
x_22 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_24 = x_15;
} else {
 lean::inc(x_22);
 lean::dec(x_15);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_21)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_21;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_19);
x_3 = x_26;
goto lbl_4;
}
else
{
obj* x_28; obj* x_31; obj* x_32; 
lean::dec(x_15);
x_28 = lean::cnstr_get(x_14, 1);
lean::inc(x_28);
lean::dec(x_14);
x_31 = l_lean_ir_var_defined(x_10, x_1, x_28);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_12);
x_35 = lean::cnstr_get(x_31, 1);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 x_37 = x_31;
} else {
 lean::inc(x_35);
 lean::dec(x_31);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_40 = x_32;
} else {
 lean::inc(x_38);
 lean::dec(x_32);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_38);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_35);
x_3 = x_42;
goto lbl_4;
}
else
{
obj* x_44; obj* x_47; 
lean::dec(x_32);
x_44 = lean::cnstr_get(x_31, 1);
lean::inc(x_44);
lean::dec(x_31);
x_47 = l_lean_ir_var_defined(x_12, x_1, x_44);
x_3 = x_47;
goto lbl_4;
}
}
}
case 4:
{
obj* x_48; obj* x_50; 
x_48 = lean::cnstr_get(x_0, 0);
lean::inc(x_48);
x_50 = l_lean_ir_var_defined(x_48, x_1, x_2);
x_3 = x_50;
goto lbl_4;
}
case 5:
{
obj* x_51; obj* x_53; obj* x_55; obj* x_56; 
x_51 = lean::cnstr_get(x_0, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_0, 2);
lean::inc(x_53);
x_55 = l_lean_ir_var_define(x_51, x_1, x_2);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
if (lean::obj_tag(x_56) == 0)
{
obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_53);
x_59 = lean::cnstr_get(x_55, 1);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 x_61 = x_55;
} else {
 lean::inc(x_59);
 lean::dec(x_55);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 x_64 = x_56;
} else {
 lean::inc(x_62);
 lean::dec(x_56);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_62);
if (lean::is_scalar(x_61)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_61;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_59);
x_3 = x_66;
goto lbl_4;
}
else
{
obj* x_68; obj* x_71; 
lean::dec(x_56);
x_68 = lean::cnstr_get(x_55, 1);
lean::inc(x_68);
lean::dec(x_55);
x_71 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__1(x_53, x_1, x_68);
x_3 = x_71;
goto lbl_4;
}
}
case 6:
{
obj* x_72; obj* x_74; 
x_72 = lean::cnstr_get(x_0, 0);
lean::inc(x_72);
x_74 = l_lean_ir_var_define(x_72, x_1, x_2);
x_3 = x_74;
goto lbl_4;
}
case 7:
{
obj* x_75; obj* x_77; obj* x_79; obj* x_80; 
x_75 = lean::cnstr_get(x_0, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_0, 1);
lean::inc(x_77);
x_79 = l_lean_ir_var_defined(x_75, x_1, x_2);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
if (lean::obj_tag(x_80) == 0)
{
obj* x_83; obj* x_85; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_77);
x_83 = lean::cnstr_get(x_79, 1);
if (lean::is_exclusive(x_79)) {
 lean::cnstr_release(x_79, 0);
 x_85 = x_79;
} else {
 lean::inc(x_83);
 lean::dec(x_79);
 x_85 = lean::box(0);
}
x_86 = lean::cnstr_get(x_80, 0);
if (lean::is_exclusive(x_80)) {
 x_88 = x_80;
} else {
 lean::inc(x_86);
 lean::dec(x_80);
 x_88 = lean::box(0);
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_86);
if (lean::is_scalar(x_85)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_85;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_83);
x_3 = x_90;
goto lbl_4;
}
else
{
obj* x_92; obj* x_95; 
lean::dec(x_80);
x_92 = lean::cnstr_get(x_79, 1);
lean::inc(x_92);
lean::dec(x_79);
x_95 = l_lean_ir_var_defined(x_77, x_1, x_92);
x_3 = x_95;
goto lbl_4;
}
}
case 9:
{
obj* x_96; obj* x_98; obj* x_100; obj* x_101; 
x_96 = lean::cnstr_get(x_0, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_0, 1);
lean::inc(x_98);
x_100 = l_lean_ir_var_defined(x_96, x_1, x_2);
x_101 = lean::cnstr_get(x_100, 0);
lean::inc(x_101);
if (lean::obj_tag(x_101) == 0)
{
obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_98);
x_104 = lean::cnstr_get(x_100, 1);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 x_106 = x_100;
} else {
 lean::inc(x_104);
 lean::dec(x_100);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_101, 0);
if (lean::is_exclusive(x_101)) {
 x_109 = x_101;
} else {
 lean::inc(x_107);
 lean::dec(x_101);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_107);
if (lean::is_scalar(x_106)) {
 x_111 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_111 = x_106;
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_104);
x_3 = x_111;
goto lbl_4;
}
else
{
obj* x_113; obj* x_116; 
lean::dec(x_101);
x_113 = lean::cnstr_get(x_100, 1);
lean::inc(x_113);
lean::dec(x_100);
x_116 = l_lean_ir_var_defined(x_98, x_1, x_113);
x_3 = x_116;
goto lbl_4;
}
}
case 11:
{
obj* x_117; obj* x_119; obj* x_121; obj* x_122; 
x_117 = lean::cnstr_get(x_0, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_0, 2);
lean::inc(x_119);
x_121 = l_lean_ir_var_define(x_117, x_1, x_2);
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
if (lean::obj_tag(x_122) == 0)
{
obj* x_125; obj* x_127; obj* x_128; obj* x_130; obj* x_131; obj* x_132; 
lean::dec(x_119);
x_125 = lean::cnstr_get(x_121, 1);
if (lean::is_exclusive(x_121)) {
 lean::cnstr_release(x_121, 0);
 x_127 = x_121;
} else {
 lean::inc(x_125);
 lean::dec(x_121);
 x_127 = lean::box(0);
}
x_128 = lean::cnstr_get(x_122, 0);
if (lean::is_exclusive(x_122)) {
 x_130 = x_122;
} else {
 lean::inc(x_128);
 lean::dec(x_122);
 x_130 = lean::box(0);
}
if (lean::is_scalar(x_130)) {
 x_131 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_131 = x_130;
}
lean::cnstr_set(x_131, 0, x_128);
if (lean::is_scalar(x_127)) {
 x_132 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_132 = x_127;
}
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_125);
x_3 = x_132;
goto lbl_4;
}
else
{
obj* x_134; obj* x_137; 
lean::dec(x_122);
x_134 = lean::cnstr_get(x_121, 1);
lean::inc(x_134);
lean::dec(x_121);
x_137 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__2(x_119, x_1, x_134);
x_3 = x_137;
goto lbl_4;
}
}
case 12:
{
obj* x_138; obj* x_140; obj* x_142; obj* x_143; 
x_138 = lean::cnstr_get(x_0, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_0, 1);
lean::inc(x_140);
x_142 = l_lean_ir_var_define(x_138, x_1, x_2);
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
if (lean::obj_tag(x_143) == 0)
{
obj* x_146; obj* x_148; obj* x_149; obj* x_151; obj* x_152; obj* x_153; 
lean::dec(x_140);
x_146 = lean::cnstr_get(x_142, 1);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 x_148 = x_142;
} else {
 lean::inc(x_146);
 lean::dec(x_142);
 x_148 = lean::box(0);
}
x_149 = lean::cnstr_get(x_143, 0);
if (lean::is_exclusive(x_143)) {
 x_151 = x_143;
} else {
 lean::inc(x_149);
 lean::dec(x_143);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_149);
if (lean::is_scalar(x_148)) {
 x_153 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_153 = x_148;
}
lean::cnstr_set(x_153, 0, x_152);
lean::cnstr_set(x_153, 1, x_146);
x_3 = x_153;
goto lbl_4;
}
else
{
obj* x_155; obj* x_158; 
lean::dec(x_143);
x_155 = lean::cnstr_get(x_142, 1);
lean::inc(x_155);
lean::dec(x_142);
x_158 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__3(x_140, x_1, x_155);
x_3 = x_158;
goto lbl_4;
}
}
case 13:
{
obj* x_159; obj* x_161; obj* x_163; obj* x_165; obj* x_166; 
x_159 = lean::cnstr_get(x_0, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_0, 1);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_0, 2);
lean::inc(x_163);
x_165 = l_lean_ir_var_define(x_159, x_1, x_2);
x_166 = lean::cnstr_get(x_165, 0);
lean::inc(x_166);
if (lean::obj_tag(x_166) == 0)
{
obj* x_170; obj* x_172; obj* x_173; obj* x_175; obj* x_176; obj* x_177; 
lean::dec(x_163);
lean::dec(x_161);
x_170 = lean::cnstr_get(x_165, 1);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 x_172 = x_165;
} else {
 lean::inc(x_170);
 lean::dec(x_165);
 x_172 = lean::box(0);
}
x_173 = lean::cnstr_get(x_166, 0);
if (lean::is_exclusive(x_166)) {
 x_175 = x_166;
} else {
 lean::inc(x_173);
 lean::dec(x_166);
 x_175 = lean::box(0);
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_173);
if (lean::is_scalar(x_172)) {
 x_177 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_177 = x_172;
}
lean::cnstr_set(x_177, 0, x_176);
lean::cnstr_set(x_177, 1, x_170);
x_3 = x_177;
goto lbl_4;
}
else
{
obj* x_179; obj* x_182; obj* x_183; 
lean::dec(x_166);
x_179 = lean::cnstr_get(x_165, 1);
lean::inc(x_179);
lean::dec(x_165);
x_182 = l_lean_ir_var_defined(x_161, x_1, x_179);
x_183 = lean::cnstr_get(x_182, 0);
lean::inc(x_183);
if (lean::obj_tag(x_183) == 0)
{
obj* x_186; obj* x_188; obj* x_189; obj* x_191; obj* x_192; obj* x_193; 
lean::dec(x_163);
x_186 = lean::cnstr_get(x_182, 1);
if (lean::is_exclusive(x_182)) {
 lean::cnstr_release(x_182, 0);
 x_188 = x_182;
} else {
 lean::inc(x_186);
 lean::dec(x_182);
 x_188 = lean::box(0);
}
x_189 = lean::cnstr_get(x_183, 0);
if (lean::is_exclusive(x_183)) {
 x_191 = x_183;
} else {
 lean::inc(x_189);
 lean::dec(x_183);
 x_191 = lean::box(0);
}
if (lean::is_scalar(x_191)) {
 x_192 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_192 = x_191;
}
lean::cnstr_set(x_192, 0, x_189);
if (lean::is_scalar(x_188)) {
 x_193 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_193 = x_188;
}
lean::cnstr_set(x_193, 0, x_192);
lean::cnstr_set(x_193, 1, x_186);
x_3 = x_193;
goto lbl_4;
}
else
{
obj* x_195; obj* x_198; 
lean::dec(x_183);
x_195 = lean::cnstr_get(x_182, 1);
lean::inc(x_195);
lean::dec(x_182);
x_198 = l_lean_ir_var_defined(x_163, x_1, x_195);
x_3 = x_198;
goto lbl_4;
}
}
}
case 14:
{
obj* x_199; obj* x_201; obj* x_203; obj* x_205; obj* x_206; 
x_199 = lean::cnstr_get(x_0, 0);
lean::inc(x_199);
x_201 = lean::cnstr_get(x_0, 1);
lean::inc(x_201);
x_203 = lean::cnstr_get(x_0, 2);
lean::inc(x_203);
x_205 = l_lean_ir_var_define(x_199, x_1, x_2);
x_206 = lean::cnstr_get(x_205, 0);
lean::inc(x_206);
if (lean::obj_tag(x_206) == 0)
{
obj* x_210; obj* x_212; obj* x_213; obj* x_215; obj* x_216; obj* x_217; 
lean::dec(x_203);
lean::dec(x_201);
x_210 = lean::cnstr_get(x_205, 1);
if (lean::is_exclusive(x_205)) {
 lean::cnstr_release(x_205, 0);
 x_212 = x_205;
} else {
 lean::inc(x_210);
 lean::dec(x_205);
 x_212 = lean::box(0);
}
x_213 = lean::cnstr_get(x_206, 0);
if (lean::is_exclusive(x_206)) {
 x_215 = x_206;
} else {
 lean::inc(x_213);
 lean::dec(x_206);
 x_215 = lean::box(0);
}
if (lean::is_scalar(x_215)) {
 x_216 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_216 = x_215;
}
lean::cnstr_set(x_216, 0, x_213);
if (lean::is_scalar(x_212)) {
 x_217 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_217 = x_212;
}
lean::cnstr_set(x_217, 0, x_216);
lean::cnstr_set(x_217, 1, x_210);
x_3 = x_217;
goto lbl_4;
}
else
{
obj* x_219; obj* x_222; obj* x_223; 
lean::dec(x_206);
x_219 = lean::cnstr_get(x_205, 1);
lean::inc(x_219);
lean::dec(x_205);
x_222 = l_lean_ir_var_defined(x_201, x_1, x_219);
x_223 = lean::cnstr_get(x_222, 0);
lean::inc(x_223);
if (lean::obj_tag(x_223) == 0)
{
obj* x_226; obj* x_228; obj* x_229; obj* x_231; obj* x_232; obj* x_233; 
lean::dec(x_203);
x_226 = lean::cnstr_get(x_222, 1);
if (lean::is_exclusive(x_222)) {
 lean::cnstr_release(x_222, 0);
 x_228 = x_222;
} else {
 lean::inc(x_226);
 lean::dec(x_222);
 x_228 = lean::box(0);
}
x_229 = lean::cnstr_get(x_223, 0);
if (lean::is_exclusive(x_223)) {
 x_231 = x_223;
} else {
 lean::inc(x_229);
 lean::dec(x_223);
 x_231 = lean::box(0);
}
if (lean::is_scalar(x_231)) {
 x_232 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_232 = x_231;
}
lean::cnstr_set(x_232, 0, x_229);
if (lean::is_scalar(x_228)) {
 x_233 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_233 = x_228;
}
lean::cnstr_set(x_233, 0, x_232);
lean::cnstr_set(x_233, 1, x_226);
x_3 = x_233;
goto lbl_4;
}
else
{
obj* x_235; obj* x_238; 
lean::dec(x_223);
x_235 = lean::cnstr_get(x_222, 1);
lean::inc(x_235);
lean::dec(x_222);
x_238 = l_lean_ir_var_defined(x_203, x_1, x_235);
x_3 = x_238;
goto lbl_4;
}
}
}
case 15:
{
obj* x_239; obj* x_241; obj* x_243; obj* x_245; obj* x_246; 
x_239 = lean::cnstr_get(x_0, 0);
lean::inc(x_239);
x_241 = lean::cnstr_get(x_0, 1);
lean::inc(x_241);
x_243 = lean::cnstr_get(x_0, 2);
lean::inc(x_243);
x_245 = l_lean_ir_var_defined(x_239, x_1, x_2);
x_246 = lean::cnstr_get(x_245, 0);
lean::inc(x_246);
if (lean::obj_tag(x_246) == 0)
{
obj* x_250; obj* x_252; obj* x_253; obj* x_255; obj* x_256; obj* x_257; 
lean::dec(x_241);
lean::dec(x_243);
x_250 = lean::cnstr_get(x_245, 1);
if (lean::is_exclusive(x_245)) {
 lean::cnstr_release(x_245, 0);
 x_252 = x_245;
} else {
 lean::inc(x_250);
 lean::dec(x_245);
 x_252 = lean::box(0);
}
x_253 = lean::cnstr_get(x_246, 0);
if (lean::is_exclusive(x_246)) {
 x_255 = x_246;
} else {
 lean::inc(x_253);
 lean::dec(x_246);
 x_255 = lean::box(0);
}
if (lean::is_scalar(x_255)) {
 x_256 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_256 = x_255;
}
lean::cnstr_set(x_256, 0, x_253);
if (lean::is_scalar(x_252)) {
 x_257 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_257 = x_252;
}
lean::cnstr_set(x_257, 0, x_256);
lean::cnstr_set(x_257, 1, x_250);
x_3 = x_257;
goto lbl_4;
}
else
{
obj* x_259; obj* x_262; obj* x_263; 
lean::dec(x_246);
x_259 = lean::cnstr_get(x_245, 1);
lean::inc(x_259);
lean::dec(x_245);
x_262 = l_lean_ir_var_defined(x_241, x_1, x_259);
x_263 = lean::cnstr_get(x_262, 0);
lean::inc(x_263);
if (lean::obj_tag(x_263) == 0)
{
obj* x_266; obj* x_268; obj* x_269; obj* x_271; obj* x_272; obj* x_273; 
lean::dec(x_243);
x_266 = lean::cnstr_get(x_262, 1);
if (lean::is_exclusive(x_262)) {
 lean::cnstr_release(x_262, 0);
 x_268 = x_262;
} else {
 lean::inc(x_266);
 lean::dec(x_262);
 x_268 = lean::box(0);
}
x_269 = lean::cnstr_get(x_263, 0);
if (lean::is_exclusive(x_263)) {
 x_271 = x_263;
} else {
 lean::inc(x_269);
 lean::dec(x_263);
 x_271 = lean::box(0);
}
if (lean::is_scalar(x_271)) {
 x_272 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_272 = x_271;
}
lean::cnstr_set(x_272, 0, x_269);
if (lean::is_scalar(x_268)) {
 x_273 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_273 = x_268;
}
lean::cnstr_set(x_273, 0, x_272);
lean::cnstr_set(x_273, 1, x_266);
x_3 = x_273;
goto lbl_4;
}
else
{
obj* x_275; obj* x_278; 
lean::dec(x_263);
x_275 = lean::cnstr_get(x_262, 1);
lean::inc(x_275);
lean::dec(x_262);
x_278 = l_lean_ir_var_defined(x_243, x_1, x_275);
x_3 = x_278;
goto lbl_4;
}
}
}
default:
{
obj* x_279; obj* x_281; obj* x_283; obj* x_284; 
x_279 = lean::cnstr_get(x_0, 0);
lean::inc(x_279);
x_281 = lean::cnstr_get(x_0, 1);
lean::inc(x_281);
x_283 = l_lean_ir_var_define(x_279, x_1, x_2);
x_284 = lean::cnstr_get(x_283, 0);
lean::inc(x_284);
if (lean::obj_tag(x_284) == 0)
{
obj* x_287; obj* x_289; obj* x_290; obj* x_292; obj* x_293; obj* x_294; 
lean::dec(x_281);
x_287 = lean::cnstr_get(x_283, 1);
if (lean::is_exclusive(x_283)) {
 lean::cnstr_release(x_283, 0);
 x_289 = x_283;
} else {
 lean::inc(x_287);
 lean::dec(x_283);
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
x_296 = lean::cnstr_get(x_283, 1);
lean::inc(x_296);
lean::dec(x_283);
x_299 = l_lean_ir_var_defined(x_281, x_1, x_296);
x_3 = x_299;
goto lbl_4;
}
}
}
lbl_4:
{
obj* x_300; 
x_300 = lean::cnstr_get(x_3, 0);
lean::inc(x_300);
if (lean::obj_tag(x_300) == 0)
{
obj* x_302; obj* x_304; obj* x_305; obj* x_307; obj* x_308; uint8 x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; 
x_302 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_304 = x_3;
} else {
 lean::inc(x_302);
 lean::dec(x_3);
 x_304 = lean::box(0);
}
x_305 = lean::cnstr_get(x_300, 0);
if (lean::is_exclusive(x_300)) {
 x_307 = x_300;
} else {
 lean::inc(x_305);
 lean::dec(x_300);
 x_307 = lean::box(0);
}
x_308 = l_lean_ir_instr_to__format___main(x_0);
x_309 = 0;
x_310 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
x_311 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_311, 0, x_310);
lean::cnstr_set(x_311, 1, x_308);
lean::cnstr_set_scalar(x_311, sizeof(void*)*2, x_309);
x_312 = x_311;
x_313 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_314 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_314, 0, x_312);
lean::cnstr_set(x_314, 1, x_313);
lean::cnstr_set_scalar(x_314, sizeof(void*)*2, x_309);
x_315 = x_314;
x_316 = lean::box(1);
x_317 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_317, 0, x_315);
lean::cnstr_set(x_317, 1, x_316);
lean::cnstr_set_scalar(x_317, sizeof(void*)*2, x_309);
x_318 = x_317;
x_319 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_319, 0, x_318);
lean::cnstr_set(x_319, 1, x_305);
lean::cnstr_set_scalar(x_319, sizeof(void*)*2, x_309);
x_320 = x_319;
if (lean::is_scalar(x_307)) {
 x_321 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_321 = x_307;
}
lean::cnstr_set(x_321, 0, x_320);
if (lean::is_scalar(x_304)) {
 x_322 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_322 = x_304;
}
lean::cnstr_set(x_322, 0, x_321);
lean::cnstr_set(x_322, 1, x_302);
return x_322;
}
else
{
obj* x_324; obj* x_326; obj* x_327; 
lean::dec(x_0);
x_324 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_326 = x_3;
} else {
 lean::inc(x_324);
 lean::dec(x_3);
 x_326 = lean::box(0);
}
if (lean::is_scalar(x_326)) {
 x_327 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_327 = x_326;
}
lean::cnstr_set(x_327, 0, x_300);
lean::cnstr_set(x_327, 1, x_324);
return x_327;
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
x_3 = x_6;
x_4 = x_2;
goto lbl_5;
}
default:
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = l_lean_ir_var_defined(x_7, x_1, x_2);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_3 = x_10;
x_4 = x_12;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_15; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_15 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_17 = x_3;
} else {
 lean::inc(x_15);
 lean::dec(x_3);
 x_17 = lean::box(0);
}
x_18 = l_lean_ir_terminator_to__format___main(x_0);
x_19 = 0;
x_20 = l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_18);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_19);
x_22 = x_21;
x_23 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_19);
x_25 = x_24;
x_26 = lean::box(1);
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_19);
x_28 = x_27;
x_29 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_15);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_19);
x_30 = x_29;
if (lean::is_scalar(x_17)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_17;
}
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_4);
return x_32;
}
else
{
obj* x_34; 
lean::dec(x_0);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_3);
lean::cnstr_set(x_34, 1, x_4);
return x_34;
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
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_12; uint8 x_13; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_lean_name_quick__lt___main(x_1, x_5);
x_13 = lean::unbox(x_12);
if (x_13 == 0)
{
obj* x_15; uint8 x_16; 
lean::dec(x_3);
x_15 = l_lean_name_quick__lt___main(x_5, x_1);
x_16 = lean::unbox(x_15);
if (x_16 == 0)
{
obj* x_18; obj* x_19; 
lean::dec(x_9);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_5);
lean::cnstr_set(x_18, 1, x_7);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
else
{
lean::dec(x_7);
lean::dec(x_5);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
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
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_lean_name_quick__lt___main(x_1, x_9);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
x_18 = l_lean_name_quick__lt___main(x_9, x_1);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_13);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_15;
}
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_9);
lean::cnstr_set(x_25, 2, x_11);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_6);
x_26 = x_25;
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_15;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_9);
lean::cnstr_set(x_28, 2, x_11);
lean::cnstr_set(x_28, 3, x_13);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_6);
x_29 = x_28;
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 2);
x_36 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = l_lean_name_quick__lt___main(x_1, x_32);
x_40 = lean::unbox(x_39);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = l_lean_name_quick__lt___main(x_32, x_1);
x_42 = lean::unbox(x_41);
if (x_42 == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_34);
lean::dec(x_32);
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_30);
lean::cnstr_set(x_45, 1, x_1);
lean::cnstr_set(x_45, 2, x_2);
lean::cnstr_set(x_45, 3, x_36);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
uint8 x_47; 
x_47 = l_rbnode_is__red___main___rarg(x_36);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_38;
}
lean::cnstr_set(x_49, 0, x_30);
lean::cnstr_set(x_49, 1, x_32);
lean::cnstr_set(x_49, 2, x_34);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_6);
x_50 = x_49;
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_52 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_52 = x_38;
}
lean::cnstr_set(x_52, 0, x_30);
lean::cnstr_set(x_52, 1, x_32);
lean::cnstr_set(x_52, 2, x_34);
lean::cnstr_set(x_52, 3, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_6);
x_53 = x_52;
x_54 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_36, x_1, x_2);
x_55 = l_rbnode_balance2___main___rarg(x_53, x_54);
return x_55;
}
}
}
else
{
uint8 x_56; 
x_56 = l_rbnode_is__red___main___rarg(x_30);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_36);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_6);
x_59 = x_58;
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_38;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_32);
lean::cnstr_set(x_61, 2, x_34);
lean::cnstr_set(x_61, 3, x_36);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_6);
x_62 = x_61;
x_63 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_30, x_1, x_2);
x_64 = l_rbnode_balance1___main___rarg(x_62, x_63);
return x_64;
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
obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_1);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_15; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_3);
x_15 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(x_3, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_11);
x_19 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_9);
x_20 = 0;
x_21 = l_lean_ir_var_defined___closed__1;
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_19);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_20);
x_23 = x_22;
x_24 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1;
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_20);
x_26 = x_25;
x_27 = l_lean_ir_phi_to__format___main(x_0);
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_20);
x_29 = x_28;
x_30 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_31 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
lean::cnstr_set_scalar(x_31, sizeof(void*)*2, x_20);
x_32 = x_31;
x_33 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_4);
return x_34;
}
else
{
obj* x_36; obj* x_40; uint8 x_41; 
lean::dec(x_9);
x_36 = lean::cnstr_get(x_15, 0);
lean::inc(x_36);
lean::dec(x_15);
lean::inc(x_1);
x_40 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_1, x_36);
x_41 = l_option_is__some___main___rarg(x_40);
lean::dec(x_40);
if (x_41 == 0)
{
obj* x_43; obj* x_44; 
x_43 = lean::box(0);
x_44 = l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5(x_1, x_36, x_43);
x_1 = x_44;
x_2 = x_11;
goto _start;
}
else
{
obj* x_50; uint8 x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_11);
lean::dec(x_36);
x_50 = l_lean_ir_phi_to__format___main(x_0);
x_51 = 0;
x_52 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__2;
x_53 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_50);
lean::cnstr_set_scalar(x_53, sizeof(void*)*2, x_51);
x_54 = x_53;
x_55 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_56 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_55);
lean::cnstr_set_scalar(x_56, sizeof(void*)*2, x_51);
x_57 = x_56;
x_58 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_4);
return x_59;
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
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find__core___main___at_lean_ir_phi_predecessors___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find__core___main___at_lean_ir_phi_predecessors___spec__2(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbtree_find___at_lean_ir_phi_predecessors___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; obj* x_4; 
lean::dec(x_0);
x_3 = 1;
x_4 = lean::box(x_3);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; uint8 x_10; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 1);
x_7 = lean::cnstr_get(x_1, 3);
lean::inc(x_0);
x_9 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_0, x_6);
x_10 = l_option_to__bool___main___rarg(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
if (x_10 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = lean::box(x_10);
return x_13;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
obj* x_16; uint8 x_17; 
lean::inc(x_0);
x_16 = l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(x_0, x_5);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
lean::dec(x_0);
return x_16;
}
else
{
x_1 = x_7;
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
obj* x_3; uint8 x_4; 
lean::inc(x_1);
x_3 = l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(x_1, x_0);
x_4 = lean::unbox(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_3;
}
else
{
obj* x_7; 
x_7 = l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(x_0, x_1);
lean::dec(x_1);
return x_7;
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
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_17; obj* x_18; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_2);
lean::inc(x_7);
x_17 = l_lean_ir_phi_predecessors(x_7, x_2, x_3);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_0);
x_21 = lean::cnstr_get(x_17, 1);
lean::inc(x_21);
lean::dec(x_17);
x_24 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_26 = x_18;
} else {
 lean::inc(x_24);
 lean::dec(x_18);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_24);
x_12 = x_27;
x_13 = x_21;
goto lbl_14;
}
else
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_28; obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
x_28 = lean::cnstr_get(x_17, 1);
lean::inc(x_28);
lean::dec(x_17);
x_31 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_33 = x_18;
} else {
 lean::inc(x_31);
 lean::dec(x_18);
 x_33 = lean::box(0);
}
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_31);
if (lean::is_scalar(x_33)) {
 x_35 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_35 = x_33;
}
lean::cnstr_set(x_35, 0, x_34);
x_12 = x_35;
x_13 = x_28;
goto lbl_14;
}
else
{
obj* x_36; obj* x_39; obj* x_41; obj* x_42; obj* x_44; uint8 x_45; 
x_36 = lean::cnstr_get(x_17, 1);
lean::inc(x_36);
lean::dec(x_17);
x_39 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_set(x_18, 0, lean::box(0));
 x_41 = x_18;
} else {
 lean::inc(x_39);
 lean::dec(x_18);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_0, 0);
lean::inc(x_42);
x_44 = l_rbtree_seteq___at_lean_ir_phis_check__predecessors___spec__1(x_42, x_39);
x_45 = lean::unbox(x_44);
if (x_45 == 0)
{
obj* x_47; obj* x_49; uint8 x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_0);
x_47 = lean::cnstr_get(x_7, 0);
lean::inc(x_47);
x_49 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_47);
x_50 = 0;
x_51 = l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___closed__1;
x_52 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_49);
lean::cnstr_set_scalar(x_52, sizeof(void*)*2, x_50);
x_53 = x_52;
x_54 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1;
x_55 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*2, x_50);
x_56 = x_55;
lean::inc(x_7);
x_58 = l_lean_ir_phi_to__format___main(x_7);
x_59 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_58);
lean::cnstr_set_scalar(x_59, sizeof(void*)*2, x_50);
x_60 = x_59;
x_61 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_62 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_61);
lean::cnstr_set_scalar(x_62, sizeof(void*)*2, x_50);
x_63 = x_62;
if (lean::is_scalar(x_41)) {
 x_64 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_64 = x_41;
 lean::cnstr_set_tag(x_41, 0);
}
lean::cnstr_set(x_64, 0, x_63);
x_12 = x_64;
x_13 = x_36;
goto lbl_14;
}
else
{
obj* x_65; 
if (lean::is_scalar(x_41)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_41;
}
lean::cnstr_set(x_65, 0, x_0);
x_12 = x_65;
x_13 = x_36;
goto lbl_14;
}
}
}
lbl_14:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_68; obj* x_70; obj* x_71; uint8 x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_9);
lean::dec(x_2);
x_68 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_70 = x_12;
} else {
 lean::inc(x_68);
 lean::dec(x_12);
 x_70 = lean::box(0);
}
x_71 = l_lean_ir_phi_to__format___main(x_7);
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
lean::cnstr_set(x_85, 1, x_13);
return x_85;
}
else
{
lean::dec(x_7);
if (lean::obj_tag(x_12) == 0)
{
obj* x_89; obj* x_91; obj* x_92; obj* x_93; 
lean::dec(x_9);
lean::dec(x_2);
x_89 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_91 = x_12;
} else {
 lean::inc(x_89);
 lean::dec(x_12);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_89);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_13);
return x_93;
}
else
{
obj* x_94; 
x_94 = lean::cnstr_get(x_12, 0);
lean::inc(x_94);
lean::dec(x_12);
x_0 = x_94;
x_1 = x_9;
x_3 = x_13;
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
return x_2;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_phi_valid__ssa(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
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
obj* x_3; obj* x_4; obj* x_6; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::inc(x_1);
lean::inc(x_6);
x_10 = l_lean_ir_phis_check__predecessors(x_6, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_6);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
lean::dec(x_10);
x_18 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_20 = x_11;
} else {
 lean::inc(x_18);
 lean::dec(x_11);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
x_3 = x_21;
x_4 = x_15;
goto lbl_5;
}
else
{
obj* x_23; obj* x_27; obj* x_28; 
lean::dec(x_11);
x_23 = lean::cnstr_get(x_10, 1);
lean::inc(x_23);
lean::dec(x_10);
lean::inc(x_1);
x_27 = l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__1(x_6, x_1, x_23);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_31; obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_1);
x_31 = lean::cnstr_get(x_27, 1);
lean::inc(x_31);
lean::dec(x_27);
x_34 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_36 = x_28;
} else {
 lean::inc(x_34);
 lean::dec(x_28);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
x_3 = x_37;
x_4 = x_31;
goto lbl_5;
}
else
{
obj* x_39; obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_28);
x_39 = lean::cnstr_get(x_27, 1);
lean::inc(x_39);
lean::dec(x_27);
x_42 = lean::cnstr_get(x_0, 2);
lean::inc(x_42);
x_44 = l_list_mmap_x_27___main___at_lean_ir_block_valid__ssa__core___spec__2(x_42, x_1, x_39);
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
if (lean::obj_tag(x_45) == 0)
{
obj* x_48; obj* x_51; obj* x_53; obj* x_54; 
lean::dec(x_1);
x_48 = lean::cnstr_get(x_44, 1);
lean::inc(x_48);
lean::dec(x_44);
x_51 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 x_53 = x_45;
} else {
 lean::inc(x_51);
 lean::dec(x_45);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_51);
x_3 = x_54;
x_4 = x_48;
goto lbl_5;
}
else
{
obj* x_56; obj* x_59; obj* x_61; obj* x_63; obj* x_65; 
lean::dec(x_45);
x_56 = lean::cnstr_get(x_44, 1);
lean::inc(x_56);
lean::dec(x_44);
x_59 = lean::cnstr_get(x_0, 3);
lean::inc(x_59);
x_61 = l_lean_ir_terminator_valid__ssa(x_59, x_1, x_56);
lean::dec(x_1);
x_63 = lean::cnstr_get(x_61, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_61, 1);
lean::inc(x_65);
lean::dec(x_61);
x_3 = x_63;
x_4 = x_65;
goto lbl_5;
}
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_68; obj* x_70; obj* x_71; obj* x_74; uint8 x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_68 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_70 = x_3;
} else {
 lean::inc(x_68);
 lean::dec(x_3);
 x_70 = lean::box(0);
}
x_71 = lean::cnstr_get(x_0, 0);
lean::inc(x_71);
lean::dec(x_0);
x_74 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_71);
x_75 = 0;
x_76 = l_lean_ir_block_decorate__error___rarg___lambda__1___closed__1;
x_77 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_74);
lean::cnstr_set_scalar(x_77, sizeof(void*)*2, x_75);
x_78 = x_77;
x_79 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_80 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_79);
lean::cnstr_set_scalar(x_80, sizeof(void*)*2, x_75);
x_81 = x_80;
x_82 = lean::box(1);
x_83 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_83, 0, x_81);
lean::cnstr_set(x_83, 1, x_82);
lean::cnstr_set_scalar(x_83, sizeof(void*)*2, x_75);
x_84 = x_83;
x_85 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_68);
lean::cnstr_set_scalar(x_85, sizeof(void*)*2, x_75);
x_86 = x_85;
if (lean::is_scalar(x_70)) {
 x_87 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_87 = x_70;
}
lean::cnstr_set(x_87, 0, x_86);
x_88 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_4);
return x_88;
}
else
{
obj* x_90; 
lean::dec(x_0);
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_3);
lean::cnstr_set(x_90, 1, x_4);
return x_90;
}
}
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
obj* x_5; obj* x_7; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_arg_define(x_5, x_1, x_2);
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
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_block_valid__ssa__core(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
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
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__4), 3, 1);
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
obj* l_lean_ir_decl_valid__ssa___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_decl_valid__ssa___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
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
obj* x_2; obj* x_6; uint8 x_7; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
lean::inc(x_1);
x_6 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_1, x_2);
x_7 = l_option_is__some___main___rarg(x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::box(0);
x_10 = l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5(x_1, x_2, x_9);
x_11 = l_lean_ir_var_declare___closed__1;
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
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
obj* x_3; uint8 x_4; 
lean::inc(x_1);
x_3 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_1, x_0);
x_4 = l_option_is__some___main___rarg(x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_6 = l_lean_to__fmt___at_lean_ir_terminator_to__format___main___spec__4(x_0);
x_7 = 0;
x_8 = l_lean_ir_blockid_defined___closed__1;
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
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_1);
return x_15;
}
else
{
obj* x_17; obj* x_18; 
lean::dec(x_0);
x_17 = l_lean_ir_var_declare___closed__1;
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_1);
return x_18;
}
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
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_lean_ir_blockid_defined(x_4, x_1);
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
obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
x_16 = l_lean_ir_blockid_defined(x_14, x_1);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_2 = x_17;
x_3 = x_19;
goto lbl_4;
}
}
lbl_4:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_22 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_24 = x_2;
} else {
 lean::inc(x_22);
 lean::dec(x_2);
 x_24 = lean::box(0);
}
x_25 = l_lean_ir_terminator_to__format___main(x_0);
x_26 = 0;
x_27 = l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_25);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_26);
x_29 = x_28;
x_30 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_31 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
lean::cnstr_set_scalar(x_31, sizeof(void*)*2, x_26);
x_32 = x_31;
x_33 = lean::box(1);
x_34 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
lean::cnstr_set_scalar(x_34, sizeof(void*)*2, x_26);
x_35 = x_34;
x_36 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_22);
lean::cnstr_set_scalar(x_36, sizeof(void*)*2, x_26);
x_37 = x_36;
if (lean::is_scalar(x_24)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_24;
}
lean::cnstr_set(x_38, 0, x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_3);
return x_39;
}
else
{
obj* x_41; 
lean::dec(x_0);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_2);
lean::cnstr_set(x_41, 1, x_3);
return x_41;
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
obj* x_3; obj* x_4; 
lean::inc(x_1);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
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
