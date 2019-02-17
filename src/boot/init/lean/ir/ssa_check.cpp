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
return x_0;
}
}
obj* l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_20; uint8 x_21; 
lean::dec(x_4);
lean::inc(x_1);
x_20 = l_lean_name_quick__lt___main(x_6, x_1);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_25; 
lean::dec(x_10);
lean::dec(x_1);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_8);
return x_25;
}
else
{
lean::dec(x_8);
x_0 = x_10;
goto _start;
}
}
else
{
lean::dec(x_10);
lean::dec(x_6);
lean::dec(x_8);
x_0 = x_4;
goto _start;
}
}
default:
{
obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_43; uint8 x_44; 
x_32 = lean::cnstr_get(x_0, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 2);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_0, 3);
lean::inc(x_38);
lean::dec(x_0);
lean::inc(x_34);
lean::inc(x_1);
x_43 = l_lean_name_quick__lt___main(x_1, x_34);
x_44 = lean::unbox(x_43);
lean::dec(x_43);
if (x_44 == 0)
{
obj* x_48; uint8 x_49; 
lean::dec(x_32);
lean::inc(x_1);
x_48 = l_lean_name_quick__lt___main(x_34, x_1);
x_49 = lean::unbox(x_48);
lean::dec(x_48);
if (x_49 == 0)
{
obj* x_53; 
lean::dec(x_1);
lean::dec(x_38);
x_53 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_53, 0, x_36);
return x_53;
}
else
{
lean::dec(x_36);
x_0 = x_38;
goto _start;
}
}
else
{
lean::dec(x_36);
lean::dec(x_38);
lean::dec(x_34);
x_0 = x_32;
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
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
lean::cnstr_set(x_3, 3, x_0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_12 = x_0;
}
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_20; uint8 x_21; 
lean::inc(x_1);
lean::inc(x_6);
x_20 = l_lean_name_quick__lt___main(x_6, x_1);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_25; 
lean::dec(x_8);
lean::dec(x_6);
if (lean::is_scalar(x_12)) {
 x_25 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_25 = x_12;
}
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_1);
lean::cnstr_set(x_25, 2, x_2);
lean::cnstr_set(x_25, 3, x_10);
return x_25;
}
else
{
obj* x_26; obj* x_27; 
x_26 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_10, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_27 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_27 = x_12;
}
lean::cnstr_set(x_27, 0, x_4);
lean::cnstr_set(x_27, 1, x_6);
lean::cnstr_set(x_27, 2, x_8);
lean::cnstr_set(x_27, 3, x_26);
return x_27;
}
}
else
{
obj* x_28; obj* x_29; 
x_28 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_4, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_29 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_29 = x_12;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_6);
lean::cnstr_set(x_29, 2, x_8);
lean::cnstr_set(x_29, 3, x_10);
return x_29;
}
}
default:
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_41; uint8 x_42; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 3);
lean::inc(x_36);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_38 = x_0;
}
lean::inc(x_32);
lean::inc(x_1);
x_41 = l_lean_name_quick__lt___main(x_1, x_32);
x_42 = lean::unbox(x_41);
lean::dec(x_41);
if (x_42 == 0)
{
obj* x_46; uint8 x_47; 
lean::inc(x_1);
lean::inc(x_32);
x_46 = l_lean_name_quick__lt___main(x_32, x_1);
x_47 = lean::unbox(x_46);
lean::dec(x_46);
if (x_47 == 0)
{
obj* x_51; 
lean::dec(x_32);
lean::dec(x_34);
if (lean::is_scalar(x_38)) {
 x_51 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_51 = x_38;
}
lean::cnstr_set(x_51, 0, x_30);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_36);
return x_51;
}
else
{
uint8 x_53; 
lean::inc(x_36);
x_53 = l_rbnode_get__color___main___rarg(x_36);
if (x_53 == 0)
{
obj* x_55; obj* x_56; 
lean::dec(x_38);
x_55 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_36, x_1, x_2);
x_56 = l_rbnode_balance2__node___main___rarg(x_55, x_32, x_34, x_30);
return x_56;
}
else
{
obj* x_57; obj* x_58; 
x_57 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_30);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_57);
return x_58;
}
}
}
else
{
uint8 x_60; 
lean::inc(x_30);
x_60 = l_rbnode_get__color___main___rarg(x_30);
if (x_60 == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_38);
x_62 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_30, x_1, x_2);
x_63 = l_rbnode_balance1__node___main___rarg(x_62, x_32, x_34, x_36);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
x_64 = l_rbnode_ins___main___at_lean_ir_var_declare___spec__5(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_65 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_65 = x_38;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_32);
lean::cnstr_set(x_65, 2, x_34);
lean::cnstr_set(x_65, 3, x_36);
return x_65;
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
obj* l_lean_ir_instr_declare__vars___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 4:
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
case 7:
{
obj* x_10; obj* x_12; 
lean::dec(x_1);
lean::dec(x_0);
x_10 = l_lean_ir_var_declare___closed__1;
lean::inc(x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_2);
return x_12;
}
case 9:
{
obj* x_15; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_15 = l_lean_ir_var_declare___closed__1;
lean::inc(x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_2);
return x_17;
}
case 15:
{
obj* x_20; obj* x_22; 
lean::dec(x_1);
lean::dec(x_0);
x_20 = l_lean_ir_var_declare___closed__1;
lean::inc(x_20);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_2);
return x_22;
}
default:
{
obj* x_23; obj* x_26; 
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = l_lean_ir_var_declare(x_23, x_1, x_2);
return x_26;
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
}
lean::cnstr_set(x_29, 0, x_28);
if (lean::is_scalar(x_10)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_10;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
x_13 = l_lean_ir_phi_declare(x_7, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_0 = x_9;
x_2 = x_16;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
x_13 = l_lean_ir_instr_declare__vars___main(x_7, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_0 = x_9;
x_2 = x_16;
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
}
lean::cnstr_set(x_32, 0, x_31);
if (lean::is_scalar(x_12)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_12;
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
obj* x_2; obj* x_4; 
x_2 = l_lean_ir_var_declare___closed__1;
lean::inc(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_block_declare__vars(x_5, x_1);
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
obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_19 = x_11;
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_15)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_15;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_13);
return x_21;
}
else
{
lean::dec(x_15);
lean::dec(x_11);
x_0 = x_7;
x_1 = x_13;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
x_13 = l_lean_ir_arg_declare(x_7, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_0 = x_9;
x_2 = x_16;
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
obj* x_12; obj* x_14; 
lean::dec(x_6);
x_12 = l_lean_ir_decl_declare__vars___main___closed__1;
lean::inc(x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_1);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_30; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
lean::dec(x_8);
x_23 = lean::cnstr_get(x_6, 1);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_15, 0);
lean::inc(x_25);
x_27 = l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__2(x_23, x_25, x_1);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_15);
x_34 = lean::cnstr_get(x_28, 0);
lean::inc(x_34);
if (lean::is_shared(x_28)) {
 lean::dec(x_28);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_28, 0);
 x_36 = x_28;
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
x_20 = x_37;
x_21 = x_30;
goto lbl_22;
}
else
{
obj* x_39; obj* x_40; obj* x_42; 
lean::dec(x_28);
x_39 = l_lean_ir_block_declare__vars(x_15, x_30);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
x_20 = x_40;
x_21 = x_42;
goto lbl_22;
}
lbl_22:
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_46; obj* x_48; obj* x_49; obj* x_52; uint8 x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_17);
x_46 = lean::cnstr_get(x_20, 0);
lean::inc(x_46);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_48 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_48 = x_20;
}
x_49 = lean::cnstr_get(x_6, 0);
lean::inc(x_49);
lean::dec(x_6);
x_52 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_49);
x_53 = 0;
x_54 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_54);
x_56 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_52);
lean::cnstr_set_scalar(x_56, sizeof(void*)*2, x_53);
x_57 = x_56;
x_58 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_58);
x_60 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_60, 0, x_57);
lean::cnstr_set(x_60, 1, x_58);
lean::cnstr_set_scalar(x_60, sizeof(void*)*2, x_53);
x_61 = x_60;
x_62 = lean::box(1);
x_63 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set(x_63, 1, x_62);
lean::cnstr_set_scalar(x_63, sizeof(void*)*2, x_53);
x_64 = x_63;
x_65 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_46);
lean::cnstr_set_scalar(x_65, sizeof(void*)*2, x_53);
x_66 = x_65;
if (lean::is_scalar(x_48)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_48;
}
lean::cnstr_set(x_67, 0, x_66);
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_21);
return x_68;
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_73; obj* x_75; 
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_69 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_69 = x_20;
}
x_70 = l_list_mmap_x_27___main___at_lean_ir_decl_declare__vars___main___spec__1(x_17, x_21);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_75 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 lean::cnstr_release(x_70, 1);
 x_75 = x_70;
}
if (lean::obj_tag(x_71) == 0)
{
obj* x_76; obj* x_79; obj* x_82; uint8 x_83; obj* x_84; obj* x_86; obj* x_87; obj* x_88; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_76 = lean::cnstr_get(x_71, 0);
lean::inc(x_76);
lean::dec(x_71);
x_79 = lean::cnstr_get(x_6, 0);
lean::inc(x_79);
lean::dec(x_6);
x_82 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_79);
x_83 = 0;
x_84 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_84);
x_86 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_86, 0, x_84);
lean::cnstr_set(x_86, 1, x_82);
lean::cnstr_set_scalar(x_86, sizeof(void*)*2, x_83);
x_87 = x_86;
x_88 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_88);
x_90 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_90, 0, x_87);
lean::cnstr_set(x_90, 1, x_88);
lean::cnstr_set_scalar(x_90, sizeof(void*)*2, x_83);
x_91 = x_90;
x_92 = lean::box(1);
x_93 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_93, 0, x_91);
lean::cnstr_set(x_93, 1, x_92);
lean::cnstr_set_scalar(x_93, sizeof(void*)*2, x_83);
x_94 = x_93;
x_95 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_76);
lean::cnstr_set_scalar(x_95, sizeof(void*)*2, x_83);
x_96 = x_95;
if (lean::is_scalar(x_69)) {
 x_97 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_97 = x_69;
 lean::cnstr_set_tag(x_69, 0);
}
lean::cnstr_set(x_97, 0, x_96);
if (lean::is_scalar(x_75)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_75;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_73);
return x_98;
}
else
{
obj* x_101; 
lean::dec(x_6);
lean::dec(x_69);
if (lean::is_scalar(x_75)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_75;
}
lean::cnstr_set(x_101, 0, x_71);
lean::cnstr_set(x_101, 1, x_73);
return x_101;
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
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
lean::cnstr_set(x_3, 3, x_0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_12 = x_0;
}
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_20; uint8 x_21; 
lean::inc(x_1);
lean::inc(x_6);
x_20 = l_lean_name_quick__lt___main(x_6, x_1);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_25; 
lean::dec(x_8);
lean::dec(x_6);
if (lean::is_scalar(x_12)) {
 x_25 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_25 = x_12;
}
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_1);
lean::cnstr_set(x_25, 2, x_2);
lean::cnstr_set(x_25, 3, x_10);
return x_25;
}
else
{
obj* x_26; obj* x_27; 
x_26 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_10, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_27 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_27 = x_12;
}
lean::cnstr_set(x_27, 0, x_4);
lean::cnstr_set(x_27, 1, x_6);
lean::cnstr_set(x_27, 2, x_8);
lean::cnstr_set(x_27, 3, x_26);
return x_27;
}
}
else
{
obj* x_28; obj* x_29; 
x_28 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_4, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_29 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_29 = x_12;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_6);
lean::cnstr_set(x_29, 2, x_8);
lean::cnstr_set(x_29, 3, x_10);
return x_29;
}
}
default:
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_41; uint8 x_42; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 3);
lean::inc(x_36);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_38 = x_0;
}
lean::inc(x_32);
lean::inc(x_1);
x_41 = l_lean_name_quick__lt___main(x_1, x_32);
x_42 = lean::unbox(x_41);
lean::dec(x_41);
if (x_42 == 0)
{
obj* x_46; uint8 x_47; 
lean::inc(x_1);
lean::inc(x_32);
x_46 = l_lean_name_quick__lt___main(x_32, x_1);
x_47 = lean::unbox(x_46);
lean::dec(x_46);
if (x_47 == 0)
{
obj* x_51; 
lean::dec(x_32);
lean::dec(x_34);
if (lean::is_scalar(x_38)) {
 x_51 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_51 = x_38;
}
lean::cnstr_set(x_51, 0, x_30);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_36);
return x_51;
}
else
{
uint8 x_53; 
lean::inc(x_36);
x_53 = l_rbnode_get__color___main___rarg(x_36);
if (x_53 == 0)
{
obj* x_55; obj* x_56; 
lean::dec(x_38);
x_55 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_36, x_1, x_2);
x_56 = l_rbnode_balance2__node___main___rarg(x_55, x_32, x_34, x_30);
return x_56;
}
else
{
obj* x_57; obj* x_58; 
x_57 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_30);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_57);
return x_58;
}
}
}
else
{
uint8 x_60; 
lean::inc(x_30);
x_60 = l_rbnode_get__color___main___rarg(x_30);
if (x_60 == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_38);
x_62 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_30, x_1, x_2);
x_63 = l_rbnode_balance1__node___main___rarg(x_62, x_32, x_34, x_36);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
x_64 = l_rbnode_ins___main___at_lean_ir_var_define___spec__3(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_65 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_65 = x_38;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_32);
lean::cnstr_set(x_65, 2, x_34);
lean::cnstr_set(x_65, 3, x_36);
return x_65;
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
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_21; uint8 x_22; 
lean::dec(x_4);
lean::inc(x_1);
lean::inc(x_6);
x_21 = l_lean_name_quick__lt___main(x_6, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_10);
lean::dec(x_1);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_6);
lean::cnstr_set(x_26, 1, x_8);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
else
{
lean::dec(x_6);
lean::dec(x_8);
x_0 = x_10;
goto _start;
}
}
else
{
lean::dec(x_10);
lean::dec(x_6);
lean::dec(x_8);
x_0 = x_4;
goto _start;
}
}
default:
{
obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_46; uint8 x_47; 
x_35 = lean::cnstr_get(x_0, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 1);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_0, 2);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_0, 3);
lean::inc(x_41);
lean::dec(x_0);
lean::inc(x_37);
lean::inc(x_1);
x_46 = l_lean_name_quick__lt___main(x_1, x_37);
x_47 = lean::unbox(x_46);
lean::dec(x_46);
if (x_47 == 0)
{
obj* x_52; uint8 x_53; 
lean::dec(x_35);
lean::inc(x_1);
lean::inc(x_37);
x_52 = l_lean_name_quick__lt___main(x_37, x_1);
x_53 = lean::unbox(x_52);
lean::dec(x_52);
if (x_53 == 0)
{
obj* x_57; obj* x_58; 
lean::dec(x_1);
lean::dec(x_41);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_37);
lean::cnstr_set(x_57, 1, x_39);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
return x_58;
}
else
{
lean::dec(x_37);
lean::dec(x_39);
x_0 = x_41;
goto _start;
}
}
else
{
lean::dec(x_37);
lean::dec(x_41);
lean::dec(x_39);
x_0 = x_35;
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
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_6 = x_2;
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
obj* l_list_mmap_x_27___main___at_lean_ir_phi_valid__ssa___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = l_lean_ir_var_declare___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_16; uint8 x_17; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_9);
lean::inc(x_0);
x_16 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(x_0, x_9);
x_17 = l_option_is__some___main___rarg(x_16);
if (x_17 == 0)
{
obj* x_21; uint8 x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_2);
x_21 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_9);
x_22 = 0;
x_23 = l_lean_ir_var_defined___closed__1;
lean::inc(x_23);
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_21);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_22);
x_26 = x_25;
x_27 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_27);
x_29 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_29, 0, x_26);
lean::cnstr_set(x_29, 1, x_27);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_22);
x_30 = x_29;
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_3);
return x_32;
}
else
{
lean::dec(x_9);
x_1 = x_11;
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
}
lean::cnstr_set(x_32, 0, x_31);
if (lean::is_scalar(x_12)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_12;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
x_13 = l_lean_ir_var_defined(x_7, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_0 = x_9;
x_2 = x_16;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
x_13 = l_lean_ir_var_defined(x_7, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_0 = x_9;
x_2 = x_16;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
x_13 = l_lean_ir_var_defined(x_7, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_0 = x_9;
x_2 = x_16;
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
}
lean::cnstr_set(x_21, 0, x_18);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_13);
x_3 = x_22;
goto lbl_4;
}
else
{
obj* x_25; 
lean::dec(x_11);
lean::dec(x_15);
x_25 = l_lean_ir_var_defined(x_7, x_1, x_13);
x_3 = x_25;
goto lbl_4;
}
}
case 2:
{
obj* x_26; obj* x_28; obj* x_31; obj* x_32; obj* x_34; obj* x_36; 
x_26 = lean::cnstr_get(x_0, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_0, 1);
lean::inc(x_28);
lean::inc(x_1);
x_31 = l_lean_ir_var_define(x_26, x_1, x_2);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_36 = x_31;
}
if (lean::obj_tag(x_32) == 0)
{
obj* x_39; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_1);
lean::dec(x_28);
x_39 = lean::cnstr_get(x_32, 0);
lean::inc(x_39);
if (lean::is_shared(x_32)) {
 lean::dec(x_32);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_32, 0);
 x_41 = x_32;
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_39);
if (lean::is_scalar(x_36)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_36;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_34);
x_3 = x_43;
goto lbl_4;
}
else
{
obj* x_46; 
lean::dec(x_32);
lean::dec(x_36);
x_46 = l_lean_ir_var_defined(x_28, x_1, x_34);
x_3 = x_46;
goto lbl_4;
}
}
case 3:
{
obj* x_47; obj* x_49; obj* x_51; obj* x_54; obj* x_55; obj* x_57; obj* x_59; 
x_47 = lean::cnstr_get(x_0, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_0, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_0, 2);
lean::inc(x_51);
lean::inc(x_1);
x_54 = l_lean_ir_var_define(x_47, x_1, x_2);
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_59 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 lean::cnstr_release(x_54, 1);
 x_59 = x_54;
}
if (lean::obj_tag(x_55) == 0)
{
obj* x_63; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_1);
lean::dec(x_51);
lean::dec(x_49);
x_63 = lean::cnstr_get(x_55, 0);
lean::inc(x_63);
if (lean::is_shared(x_55)) {
 lean::dec(x_55);
 x_65 = lean::box(0);
} else {
 lean::cnstr_release(x_55, 0);
 x_65 = x_55;
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_63);
if (lean::is_scalar(x_59)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_59;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_57);
x_3 = x_67;
goto lbl_4;
}
else
{
obj* x_68; obj* x_70; obj* x_71; obj* x_73; 
if (lean::is_shared(x_55)) {
 lean::dec(x_55);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_55, 0);
 x_68 = x_55;
}
lean::inc(x_1);
x_70 = l_lean_ir_var_defined(x_49, x_1, x_57);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
lean::dec(x_70);
if (lean::obj_tag(x_71) == 0)
{
obj* x_78; obj* x_81; obj* x_82; 
lean::dec(x_1);
lean::dec(x_51);
x_78 = lean::cnstr_get(x_71, 0);
lean::inc(x_78);
lean::dec(x_71);
if (lean::is_scalar(x_68)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_68;
 lean::cnstr_set_tag(x_68, 0);
}
lean::cnstr_set(x_81, 0, x_78);
if (lean::is_scalar(x_59)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_59;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_73);
x_3 = x_82;
goto lbl_4;
}
else
{
obj* x_86; 
lean::dec(x_59);
lean::dec(x_68);
lean::dec(x_71);
x_86 = l_lean_ir_var_defined(x_51, x_1, x_73);
x_3 = x_86;
goto lbl_4;
}
}
}
case 4:
{
obj* x_87; obj* x_89; 
x_87 = lean::cnstr_get(x_0, 0);
lean::inc(x_87);
x_89 = l_lean_ir_var_defined(x_87, x_1, x_2);
x_3 = x_89;
goto lbl_4;
}
case 5:
{
obj* x_90; obj* x_92; obj* x_95; obj* x_96; obj* x_98; obj* x_100; 
x_90 = lean::cnstr_get(x_0, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_0, 2);
lean::inc(x_92);
lean::inc(x_1);
x_95 = l_lean_ir_var_define(x_90, x_1, x_2);
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_95, 1);
lean::inc(x_98);
if (lean::is_shared(x_95)) {
 lean::dec(x_95);
 x_100 = lean::box(0);
} else {
 lean::cnstr_release(x_95, 0);
 lean::cnstr_release(x_95, 1);
 x_100 = x_95;
}
if (lean::obj_tag(x_96) == 0)
{
obj* x_103; obj* x_105; obj* x_106; obj* x_107; 
lean::dec(x_1);
lean::dec(x_92);
x_103 = lean::cnstr_get(x_96, 0);
lean::inc(x_103);
if (lean::is_shared(x_96)) {
 lean::dec(x_96);
 x_105 = lean::box(0);
} else {
 lean::cnstr_release(x_96, 0);
 x_105 = x_96;
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_103);
if (lean::is_scalar(x_100)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_100;
}
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_98);
x_3 = x_107;
goto lbl_4;
}
else
{
obj* x_110; 
lean::dec(x_96);
lean::dec(x_100);
x_110 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__1(x_92, x_1, x_98);
x_3 = x_110;
goto lbl_4;
}
}
case 7:
{
obj* x_111; obj* x_113; obj* x_116; obj* x_117; obj* x_119; obj* x_121; 
x_111 = lean::cnstr_get(x_0, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_0, 1);
lean::inc(x_113);
lean::inc(x_1);
x_116 = l_lean_ir_var_defined(x_111, x_1, x_2);
x_117 = lean::cnstr_get(x_116, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_116, 1);
lean::inc(x_119);
if (lean::is_shared(x_116)) {
 lean::dec(x_116);
 x_121 = lean::box(0);
} else {
 lean::cnstr_release(x_116, 0);
 lean::cnstr_release(x_116, 1);
 x_121 = x_116;
}
if (lean::obj_tag(x_117) == 0)
{
obj* x_124; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_113);
lean::dec(x_1);
x_124 = lean::cnstr_get(x_117, 0);
lean::inc(x_124);
if (lean::is_shared(x_117)) {
 lean::dec(x_117);
 x_126 = lean::box(0);
} else {
 lean::cnstr_release(x_117, 0);
 x_126 = x_117;
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_124);
if (lean::is_scalar(x_121)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_121;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_119);
x_3 = x_128;
goto lbl_4;
}
else
{
obj* x_131; 
lean::dec(x_121);
lean::dec(x_117);
x_131 = l_lean_ir_var_defined(x_113, x_1, x_119);
x_3 = x_131;
goto lbl_4;
}
}
case 8:
{
obj* x_132; obj* x_134; obj* x_137; obj* x_138; obj* x_140; obj* x_142; 
x_132 = lean::cnstr_get(x_0, 0);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_0, 1);
lean::inc(x_134);
lean::inc(x_1);
x_137 = l_lean_ir_var_define(x_132, x_1, x_2);
x_138 = lean::cnstr_get(x_137, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_137, 1);
lean::inc(x_140);
if (lean::is_shared(x_137)) {
 lean::dec(x_137);
 x_142 = lean::box(0);
} else {
 lean::cnstr_release(x_137, 0);
 lean::cnstr_release(x_137, 1);
 x_142 = x_137;
}
if (lean::obj_tag(x_138) == 0)
{
obj* x_145; obj* x_147; obj* x_148; obj* x_149; 
lean::dec(x_134);
lean::dec(x_1);
x_145 = lean::cnstr_get(x_138, 0);
lean::inc(x_145);
if (lean::is_shared(x_138)) {
 lean::dec(x_138);
 x_147 = lean::box(0);
} else {
 lean::cnstr_release(x_138, 0);
 x_147 = x_138;
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_145);
if (lean::is_scalar(x_142)) {
 x_149 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_149 = x_142;
}
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_140);
x_3 = x_149;
goto lbl_4;
}
else
{
obj* x_152; 
lean::dec(x_142);
lean::dec(x_138);
x_152 = l_lean_ir_var_defined(x_134, x_1, x_140);
x_3 = x_152;
goto lbl_4;
}
}
case 9:
{
obj* x_153; obj* x_155; obj* x_158; obj* x_159; obj* x_161; obj* x_163; 
x_153 = lean::cnstr_get(x_0, 0);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_0, 1);
lean::inc(x_155);
lean::inc(x_1);
x_158 = l_lean_ir_var_defined(x_153, x_1, x_2);
x_159 = lean::cnstr_get(x_158, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_158, 1);
lean::inc(x_161);
if (lean::is_shared(x_158)) {
 lean::dec(x_158);
 x_163 = lean::box(0);
} else {
 lean::cnstr_release(x_158, 0);
 lean::cnstr_release(x_158, 1);
 x_163 = x_158;
}
if (lean::obj_tag(x_159) == 0)
{
obj* x_166; obj* x_168; obj* x_169; obj* x_170; 
lean::dec(x_155);
lean::dec(x_1);
x_166 = lean::cnstr_get(x_159, 0);
lean::inc(x_166);
if (lean::is_shared(x_159)) {
 lean::dec(x_159);
 x_168 = lean::box(0);
} else {
 lean::cnstr_release(x_159, 0);
 x_168 = x_159;
}
if (lean::is_scalar(x_168)) {
 x_169 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_169 = x_168;
}
lean::cnstr_set(x_169, 0, x_166);
if (lean::is_scalar(x_163)) {
 x_170 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_170 = x_163;
}
lean::cnstr_set(x_170, 0, x_169);
lean::cnstr_set(x_170, 1, x_161);
x_3 = x_170;
goto lbl_4;
}
else
{
obj* x_173; 
lean::dec(x_163);
lean::dec(x_159);
x_173 = l_lean_ir_var_defined(x_155, x_1, x_161);
x_3 = x_173;
goto lbl_4;
}
}
case 10:
{
obj* x_174; obj* x_176; obj* x_179; obj* x_180; obj* x_182; obj* x_184; 
x_174 = lean::cnstr_get(x_0, 0);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_0, 1);
lean::inc(x_176);
lean::inc(x_1);
x_179 = l_lean_ir_var_define(x_174, x_1, x_2);
x_180 = lean::cnstr_get(x_179, 0);
lean::inc(x_180);
x_182 = lean::cnstr_get(x_179, 1);
lean::inc(x_182);
if (lean::is_shared(x_179)) {
 lean::dec(x_179);
 x_184 = lean::box(0);
} else {
 lean::cnstr_release(x_179, 0);
 lean::cnstr_release(x_179, 1);
 x_184 = x_179;
}
if (lean::obj_tag(x_180) == 0)
{
obj* x_187; obj* x_189; obj* x_190; obj* x_191; 
lean::dec(x_1);
lean::dec(x_176);
x_187 = lean::cnstr_get(x_180, 0);
lean::inc(x_187);
if (lean::is_shared(x_180)) {
 lean::dec(x_180);
 x_189 = lean::box(0);
} else {
 lean::cnstr_release(x_180, 0);
 x_189 = x_180;
}
if (lean::is_scalar(x_189)) {
 x_190 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_190 = x_189;
}
lean::cnstr_set(x_190, 0, x_187);
if (lean::is_scalar(x_184)) {
 x_191 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_191 = x_184;
}
lean::cnstr_set(x_191, 0, x_190);
lean::cnstr_set(x_191, 1, x_182);
x_3 = x_191;
goto lbl_4;
}
else
{
obj* x_194; 
lean::dec(x_184);
lean::dec(x_180);
x_194 = l_lean_ir_var_defined(x_176, x_1, x_182);
x_3 = x_194;
goto lbl_4;
}
}
case 11:
{
obj* x_195; obj* x_197; obj* x_200; obj* x_201; obj* x_203; obj* x_205; 
x_195 = lean::cnstr_get(x_0, 0);
lean::inc(x_195);
x_197 = lean::cnstr_get(x_0, 2);
lean::inc(x_197);
lean::inc(x_1);
x_200 = l_lean_ir_var_define(x_195, x_1, x_2);
x_201 = lean::cnstr_get(x_200, 0);
lean::inc(x_201);
x_203 = lean::cnstr_get(x_200, 1);
lean::inc(x_203);
if (lean::is_shared(x_200)) {
 lean::dec(x_200);
 x_205 = lean::box(0);
} else {
 lean::cnstr_release(x_200, 0);
 lean::cnstr_release(x_200, 1);
 x_205 = x_200;
}
if (lean::obj_tag(x_201) == 0)
{
obj* x_208; obj* x_210; obj* x_211; obj* x_212; 
lean::dec(x_1);
lean::dec(x_197);
x_208 = lean::cnstr_get(x_201, 0);
lean::inc(x_208);
if (lean::is_shared(x_201)) {
 lean::dec(x_201);
 x_210 = lean::box(0);
} else {
 lean::cnstr_release(x_201, 0);
 x_210 = x_201;
}
if (lean::is_scalar(x_210)) {
 x_211 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_211 = x_210;
}
lean::cnstr_set(x_211, 0, x_208);
if (lean::is_scalar(x_205)) {
 x_212 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_212 = x_205;
}
lean::cnstr_set(x_212, 0, x_211);
lean::cnstr_set(x_212, 1, x_203);
x_3 = x_212;
goto lbl_4;
}
else
{
obj* x_215; 
lean::dec(x_205);
lean::dec(x_201);
x_215 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__2(x_197, x_1, x_203);
x_3 = x_215;
goto lbl_4;
}
}
case 12:
{
obj* x_216; obj* x_218; obj* x_221; obj* x_222; obj* x_224; obj* x_226; 
x_216 = lean::cnstr_get(x_0, 0);
lean::inc(x_216);
x_218 = lean::cnstr_get(x_0, 1);
lean::inc(x_218);
lean::inc(x_1);
x_221 = l_lean_ir_var_define(x_216, x_1, x_2);
x_222 = lean::cnstr_get(x_221, 0);
lean::inc(x_222);
x_224 = lean::cnstr_get(x_221, 1);
lean::inc(x_224);
if (lean::is_shared(x_221)) {
 lean::dec(x_221);
 x_226 = lean::box(0);
} else {
 lean::cnstr_release(x_221, 0);
 lean::cnstr_release(x_221, 1);
 x_226 = x_221;
}
if (lean::obj_tag(x_222) == 0)
{
obj* x_229; obj* x_231; obj* x_232; obj* x_233; 
lean::dec(x_1);
lean::dec(x_218);
x_229 = lean::cnstr_get(x_222, 0);
lean::inc(x_229);
if (lean::is_shared(x_222)) {
 lean::dec(x_222);
 x_231 = lean::box(0);
} else {
 lean::cnstr_release(x_222, 0);
 x_231 = x_222;
}
if (lean::is_scalar(x_231)) {
 x_232 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_232 = x_231;
}
lean::cnstr_set(x_232, 0, x_229);
if (lean::is_scalar(x_226)) {
 x_233 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_233 = x_226;
}
lean::cnstr_set(x_233, 0, x_232);
lean::cnstr_set(x_233, 1, x_224);
x_3 = x_233;
goto lbl_4;
}
else
{
obj* x_236; 
lean::dec(x_222);
lean::dec(x_226);
x_236 = l_list_mmap_x_27___main___at_lean_ir_instr_valid__ssa___spec__3(x_218, x_1, x_224);
x_3 = x_236;
goto lbl_4;
}
}
case 13:
{
obj* x_237; obj* x_239; obj* x_241; obj* x_244; obj* x_245; obj* x_247; obj* x_249; 
x_237 = lean::cnstr_get(x_0, 0);
lean::inc(x_237);
x_239 = lean::cnstr_get(x_0, 1);
lean::inc(x_239);
x_241 = lean::cnstr_get(x_0, 2);
lean::inc(x_241);
lean::inc(x_1);
x_244 = l_lean_ir_var_define(x_237, x_1, x_2);
x_245 = lean::cnstr_get(x_244, 0);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_244, 1);
lean::inc(x_247);
if (lean::is_shared(x_244)) {
 lean::dec(x_244);
 x_249 = lean::box(0);
} else {
 lean::cnstr_release(x_244, 0);
 lean::cnstr_release(x_244, 1);
 x_249 = x_244;
}
if (lean::obj_tag(x_245) == 0)
{
obj* x_253; obj* x_255; obj* x_256; obj* x_257; 
lean::dec(x_1);
lean::dec(x_241);
lean::dec(x_239);
x_253 = lean::cnstr_get(x_245, 0);
lean::inc(x_253);
if (lean::is_shared(x_245)) {
 lean::dec(x_245);
 x_255 = lean::box(0);
} else {
 lean::cnstr_release(x_245, 0);
 x_255 = x_245;
}
if (lean::is_scalar(x_255)) {
 x_256 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_256 = x_255;
}
lean::cnstr_set(x_256, 0, x_253);
if (lean::is_scalar(x_249)) {
 x_257 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_257 = x_249;
}
lean::cnstr_set(x_257, 0, x_256);
lean::cnstr_set(x_257, 1, x_247);
x_3 = x_257;
goto lbl_4;
}
else
{
obj* x_258; obj* x_260; obj* x_261; obj* x_263; 
if (lean::is_shared(x_245)) {
 lean::dec(x_245);
 x_258 = lean::box(0);
} else {
 lean::cnstr_release(x_245, 0);
 x_258 = x_245;
}
lean::inc(x_1);
x_260 = l_lean_ir_var_defined(x_239, x_1, x_247);
x_261 = lean::cnstr_get(x_260, 0);
lean::inc(x_261);
x_263 = lean::cnstr_get(x_260, 1);
lean::inc(x_263);
lean::dec(x_260);
if (lean::obj_tag(x_261) == 0)
{
obj* x_268; obj* x_271; obj* x_272; 
lean::dec(x_1);
lean::dec(x_241);
x_268 = lean::cnstr_get(x_261, 0);
lean::inc(x_268);
lean::dec(x_261);
if (lean::is_scalar(x_258)) {
 x_271 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_271 = x_258;
 lean::cnstr_set_tag(x_258, 0);
}
lean::cnstr_set(x_271, 0, x_268);
if (lean::is_scalar(x_249)) {
 x_272 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_272 = x_249;
}
lean::cnstr_set(x_272, 0, x_271);
lean::cnstr_set(x_272, 1, x_263);
x_3 = x_272;
goto lbl_4;
}
else
{
obj* x_276; 
lean::dec(x_249);
lean::dec(x_261);
lean::dec(x_258);
x_276 = l_lean_ir_var_defined(x_241, x_1, x_263);
x_3 = x_276;
goto lbl_4;
}
}
}
case 14:
{
obj* x_277; obj* x_279; obj* x_281; obj* x_284; obj* x_285; obj* x_287; obj* x_289; 
x_277 = lean::cnstr_get(x_0, 0);
lean::inc(x_277);
x_279 = lean::cnstr_get(x_0, 1);
lean::inc(x_279);
x_281 = lean::cnstr_get(x_0, 2);
lean::inc(x_281);
lean::inc(x_1);
x_284 = l_lean_ir_var_define(x_277, x_1, x_2);
x_285 = lean::cnstr_get(x_284, 0);
lean::inc(x_285);
x_287 = lean::cnstr_get(x_284, 1);
lean::inc(x_287);
if (lean::is_shared(x_284)) {
 lean::dec(x_284);
 x_289 = lean::box(0);
} else {
 lean::cnstr_release(x_284, 0);
 lean::cnstr_release(x_284, 1);
 x_289 = x_284;
}
if (lean::obj_tag(x_285) == 0)
{
obj* x_293; obj* x_295; obj* x_296; obj* x_297; 
lean::dec(x_1);
lean::dec(x_279);
lean::dec(x_281);
x_293 = lean::cnstr_get(x_285, 0);
lean::inc(x_293);
if (lean::is_shared(x_285)) {
 lean::dec(x_285);
 x_295 = lean::box(0);
} else {
 lean::cnstr_release(x_285, 0);
 x_295 = x_285;
}
if (lean::is_scalar(x_295)) {
 x_296 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_296 = x_295;
}
lean::cnstr_set(x_296, 0, x_293);
if (lean::is_scalar(x_289)) {
 x_297 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_297 = x_289;
}
lean::cnstr_set(x_297, 0, x_296);
lean::cnstr_set(x_297, 1, x_287);
x_3 = x_297;
goto lbl_4;
}
else
{
obj* x_298; obj* x_300; obj* x_301; obj* x_303; 
if (lean::is_shared(x_285)) {
 lean::dec(x_285);
 x_298 = lean::box(0);
} else {
 lean::cnstr_release(x_285, 0);
 x_298 = x_285;
}
lean::inc(x_1);
x_300 = l_lean_ir_var_defined(x_279, x_1, x_287);
x_301 = lean::cnstr_get(x_300, 0);
lean::inc(x_301);
x_303 = lean::cnstr_get(x_300, 1);
lean::inc(x_303);
lean::dec(x_300);
if (lean::obj_tag(x_301) == 0)
{
obj* x_308; obj* x_311; obj* x_312; 
lean::dec(x_1);
lean::dec(x_281);
x_308 = lean::cnstr_get(x_301, 0);
lean::inc(x_308);
lean::dec(x_301);
if (lean::is_scalar(x_298)) {
 x_311 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_311 = x_298;
 lean::cnstr_set_tag(x_298, 0);
}
lean::cnstr_set(x_311, 0, x_308);
if (lean::is_scalar(x_289)) {
 x_312 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_312 = x_289;
}
lean::cnstr_set(x_312, 0, x_311);
lean::cnstr_set(x_312, 1, x_303);
x_3 = x_312;
goto lbl_4;
}
else
{
obj* x_316; 
lean::dec(x_301);
lean::dec(x_298);
lean::dec(x_289);
x_316 = l_lean_ir_var_defined(x_281, x_1, x_303);
x_3 = x_316;
goto lbl_4;
}
}
}
case 15:
{
obj* x_317; obj* x_319; obj* x_321; obj* x_324; obj* x_325; obj* x_327; obj* x_329; 
x_317 = lean::cnstr_get(x_0, 0);
lean::inc(x_317);
x_319 = lean::cnstr_get(x_0, 1);
lean::inc(x_319);
x_321 = lean::cnstr_get(x_0, 2);
lean::inc(x_321);
lean::inc(x_1);
x_324 = l_lean_ir_var_defined(x_317, x_1, x_2);
x_325 = lean::cnstr_get(x_324, 0);
lean::inc(x_325);
x_327 = lean::cnstr_get(x_324, 1);
lean::inc(x_327);
if (lean::is_shared(x_324)) {
 lean::dec(x_324);
 x_329 = lean::box(0);
} else {
 lean::cnstr_release(x_324, 0);
 lean::cnstr_release(x_324, 1);
 x_329 = x_324;
}
if (lean::obj_tag(x_325) == 0)
{
obj* x_333; obj* x_335; obj* x_336; obj* x_337; 
lean::dec(x_319);
lean::dec(x_321);
lean::dec(x_1);
x_333 = lean::cnstr_get(x_325, 0);
lean::inc(x_333);
if (lean::is_shared(x_325)) {
 lean::dec(x_325);
 x_335 = lean::box(0);
} else {
 lean::cnstr_release(x_325, 0);
 x_335 = x_325;
}
if (lean::is_scalar(x_335)) {
 x_336 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_336 = x_335;
}
lean::cnstr_set(x_336, 0, x_333);
if (lean::is_scalar(x_329)) {
 x_337 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_337 = x_329;
}
lean::cnstr_set(x_337, 0, x_336);
lean::cnstr_set(x_337, 1, x_327);
x_3 = x_337;
goto lbl_4;
}
else
{
obj* x_338; obj* x_340; obj* x_341; obj* x_343; 
if (lean::is_shared(x_325)) {
 lean::dec(x_325);
 x_338 = lean::box(0);
} else {
 lean::cnstr_release(x_325, 0);
 x_338 = x_325;
}
lean::inc(x_1);
x_340 = l_lean_ir_var_defined(x_319, x_1, x_327);
x_341 = lean::cnstr_get(x_340, 0);
lean::inc(x_341);
x_343 = lean::cnstr_get(x_340, 1);
lean::inc(x_343);
lean::dec(x_340);
if (lean::obj_tag(x_341) == 0)
{
obj* x_348; obj* x_351; obj* x_352; 
lean::dec(x_321);
lean::dec(x_1);
x_348 = lean::cnstr_get(x_341, 0);
lean::inc(x_348);
lean::dec(x_341);
if (lean::is_scalar(x_338)) {
 x_351 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_351 = x_338;
 lean::cnstr_set_tag(x_338, 0);
}
lean::cnstr_set(x_351, 0, x_348);
if (lean::is_scalar(x_329)) {
 x_352 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_352 = x_329;
}
lean::cnstr_set(x_352, 0, x_351);
lean::cnstr_set(x_352, 1, x_343);
x_3 = x_352;
goto lbl_4;
}
else
{
obj* x_356; 
lean::dec(x_329);
lean::dec(x_341);
lean::dec(x_338);
x_356 = l_lean_ir_var_defined(x_321, x_1, x_343);
x_3 = x_356;
goto lbl_4;
}
}
}
default:
{
obj* x_357; obj* x_359; 
x_357 = lean::cnstr_get(x_0, 0);
lean::inc(x_357);
x_359 = l_lean_ir_var_define(x_357, x_1, x_2);
x_3 = x_359;
goto lbl_4;
}
}
lbl_4:
{
obj* x_360; obj* x_362; obj* x_364; 
x_360 = lean::cnstr_get(x_3, 0);
lean::inc(x_360);
x_362 = lean::cnstr_get(x_3, 1);
lean::inc(x_362);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_364 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_364 = x_3;
}
if (lean::obj_tag(x_360) == 0)
{
obj* x_365; obj* x_367; obj* x_368; uint8 x_369; obj* x_370; obj* x_372; obj* x_373; obj* x_374; obj* x_376; obj* x_377; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; 
x_365 = lean::cnstr_get(x_360, 0);
lean::inc(x_365);
if (lean::is_shared(x_360)) {
 lean::dec(x_360);
 x_367 = lean::box(0);
} else {
 lean::cnstr_release(x_360, 0);
 x_367 = x_360;
}
x_368 = l_lean_ir_instr_to__format___main(x_0);
x_369 = 0;
x_370 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_370);
x_372 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_372, 0, x_370);
lean::cnstr_set(x_372, 1, x_368);
lean::cnstr_set_scalar(x_372, sizeof(void*)*2, x_369);
x_373 = x_372;
x_374 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_374);
x_376 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_376, 0, x_373);
lean::cnstr_set(x_376, 1, x_374);
lean::cnstr_set_scalar(x_376, sizeof(void*)*2, x_369);
x_377 = x_376;
x_378 = lean::box(1);
x_379 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_379, 0, x_377);
lean::cnstr_set(x_379, 1, x_378);
lean::cnstr_set_scalar(x_379, sizeof(void*)*2, x_369);
x_380 = x_379;
x_381 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_381, 0, x_380);
lean::cnstr_set(x_381, 1, x_365);
lean::cnstr_set_scalar(x_381, sizeof(void*)*2, x_369);
x_382 = x_381;
if (lean::is_scalar(x_367)) {
 x_383 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_383 = x_367;
}
lean::cnstr_set(x_383, 0, x_382);
if (lean::is_scalar(x_364)) {
 x_384 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_384 = x_364;
}
lean::cnstr_set(x_384, 0, x_383);
lean::cnstr_set(x_384, 1, x_362);
return x_384;
}
else
{
obj* x_386; 
lean::dec(x_0);
if (lean::is_scalar(x_364)) {
 x_386 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_386 = x_364;
}
lean::cnstr_set(x_386, 0, x_360);
lean::cnstr_set(x_386, 1, x_362);
return x_386;
}
}
}
}
obj* l_lean_ir_terminator_valid__ssa(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
switch (lean::obj_tag(x_0)) {
case 2:
{
obj* x_7; 
lean::dec(x_1);
x_7 = l_lean_ir_var_declare___closed__1;
lean::inc(x_7);
x_3 = x_7;
x_4 = x_2;
goto lbl_5;
}
default:
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = l_lean_ir_var_defined(x_9, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_3 = x_12;
x_4 = x_14;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_17; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_17 = lean::cnstr_get(x_3, 0);
lean::inc(x_17);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_19 = x_3;
}
x_20 = l_lean_ir_terminator_to__format___main(x_0);
x_21 = 0;
x_22 = l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_20);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_21);
x_25 = x_24;
x_26 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_26);
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_26);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_21);
x_29 = x_28;
x_30 = lean::box(1);
x_31 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
lean::cnstr_set_scalar(x_31, sizeof(void*)*2, x_21);
x_32 = x_31;
x_33 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_17);
lean::cnstr_set_scalar(x_33, sizeof(void*)*2, x_21);
x_34 = x_33;
if (lean::is_scalar(x_19)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_19;
}
lean::cnstr_set(x_35, 0, x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_4);
return x_36;
}
else
{
obj* x_38; 
lean::dec(x_0);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_3);
lean::cnstr_set(x_38, 1, x_4);
return x_38;
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
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_21; uint8 x_22; 
lean::dec(x_4);
lean::inc(x_1);
lean::inc(x_6);
x_21 = l_lean_name_quick__lt___main(x_6, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_10);
lean::dec(x_1);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_6);
lean::cnstr_set(x_26, 1, x_8);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
else
{
lean::dec(x_6);
lean::dec(x_8);
x_0 = x_10;
goto _start;
}
}
else
{
lean::dec(x_10);
lean::dec(x_6);
lean::dec(x_8);
x_0 = x_4;
goto _start;
}
}
default:
{
obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_46; uint8 x_47; 
x_35 = lean::cnstr_get(x_0, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 1);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_0, 2);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_0, 3);
lean::inc(x_41);
lean::dec(x_0);
lean::inc(x_37);
lean::inc(x_1);
x_46 = l_lean_name_quick__lt___main(x_1, x_37);
x_47 = lean::unbox(x_46);
lean::dec(x_46);
if (x_47 == 0)
{
obj* x_52; uint8 x_53; 
lean::dec(x_35);
lean::inc(x_1);
lean::inc(x_37);
x_52 = l_lean_name_quick__lt___main(x_37, x_1);
x_53 = lean::unbox(x_52);
lean::dec(x_52);
if (x_53 == 0)
{
obj* x_57; obj* x_58; 
lean::dec(x_1);
lean::dec(x_41);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_37);
lean::cnstr_set(x_57, 1, x_39);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
return x_58;
}
else
{
lean::dec(x_37);
lean::dec(x_39);
x_0 = x_41;
goto _start;
}
}
else
{
lean::dec(x_37);
lean::dec(x_41);
lean::dec(x_39);
x_0 = x_35;
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
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_6 = x_2;
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
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
lean::cnstr_set(x_3, 3, x_0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_12 = x_0;
}
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_20; uint8 x_21; 
lean::inc(x_1);
lean::inc(x_6);
x_20 = l_lean_name_quick__lt___main(x_6, x_1);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_25; 
lean::dec(x_8);
lean::dec(x_6);
if (lean::is_scalar(x_12)) {
 x_25 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_25 = x_12;
}
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_1);
lean::cnstr_set(x_25, 2, x_2);
lean::cnstr_set(x_25, 3, x_10);
return x_25;
}
else
{
obj* x_26; obj* x_27; 
x_26 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_10, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_27 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_27 = x_12;
}
lean::cnstr_set(x_27, 0, x_4);
lean::cnstr_set(x_27, 1, x_6);
lean::cnstr_set(x_27, 2, x_8);
lean::cnstr_set(x_27, 3, x_26);
return x_27;
}
}
else
{
obj* x_28; obj* x_29; 
x_28 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_4, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_29 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_29 = x_12;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_6);
lean::cnstr_set(x_29, 2, x_8);
lean::cnstr_set(x_29, 3, x_10);
return x_29;
}
}
default:
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_41; uint8 x_42; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 3);
lean::inc(x_36);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_38 = x_0;
}
lean::inc(x_32);
lean::inc(x_1);
x_41 = l_lean_name_quick__lt___main(x_1, x_32);
x_42 = lean::unbox(x_41);
lean::dec(x_41);
if (x_42 == 0)
{
obj* x_46; uint8 x_47; 
lean::inc(x_1);
lean::inc(x_32);
x_46 = l_lean_name_quick__lt___main(x_32, x_1);
x_47 = lean::unbox(x_46);
lean::dec(x_46);
if (x_47 == 0)
{
obj* x_51; 
lean::dec(x_32);
lean::dec(x_34);
if (lean::is_scalar(x_38)) {
 x_51 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_51 = x_38;
}
lean::cnstr_set(x_51, 0, x_30);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_36);
return x_51;
}
else
{
uint8 x_53; 
lean::inc(x_36);
x_53 = l_rbnode_get__color___main___rarg(x_36);
if (x_53 == 0)
{
obj* x_55; obj* x_56; 
lean::dec(x_38);
x_55 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_36, x_1, x_2);
x_56 = l_rbnode_balance2__node___main___rarg(x_55, x_32, x_34, x_30);
return x_56;
}
else
{
obj* x_57; obj* x_58; 
x_57 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_30);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_57);
return x_58;
}
}
}
else
{
uint8 x_60; 
lean::inc(x_30);
x_60 = l_rbnode_get__color___main___rarg(x_30);
if (x_60 == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_38);
x_62 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_30, x_1, x_2);
x_63 = l_rbnode_balance1__node___main___rarg(x_62, x_32, x_34, x_36);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
x_64 = l_rbnode_ins___main___at_lean_ir_phi_predecessors___spec__6(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_65 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_65 = x_38;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_32);
lean::cnstr_set(x_65, 2, x_34);
lean::cnstr_set(x_65, 3, x_36);
return x_65;
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
obj* x_9; obj* x_11; obj* x_16; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_9);
lean::inc(x_3);
x_16 = l_rbnode_find___main___at_lean_ir_var_declare___spec__2___rarg(x_3, x_9);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; uint8 x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_11);
x_20 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_9);
x_21 = 0;
x_22 = l_lean_ir_var_defined___closed__1;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_20);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_21);
x_25 = x_24;
x_26 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1;
lean::inc(x_26);
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_26);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_21);
x_29 = x_28;
x_30 = l_lean_ir_phi_to__format___main(x_0);
x_31 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
lean::cnstr_set_scalar(x_31, sizeof(void*)*2, x_21);
x_32 = x_31;
x_33 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_33);
x_35 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_33);
lean::cnstr_set_scalar(x_35, sizeof(void*)*2, x_21);
x_36 = x_35;
x_37 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_37, 0, x_36);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_4);
return x_38;
}
else
{
obj* x_40; obj* x_45; uint8 x_46; 
lean::dec(x_9);
x_40 = lean::cnstr_get(x_16, 0);
lean::inc(x_40);
lean::dec(x_16);
lean::inc(x_40);
lean::inc(x_1);
x_45 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_1, x_40);
x_46 = l_option_is__some___main___rarg(x_45);
if (x_46 == 0)
{
obj* x_47; obj* x_48; 
x_47 = lean::box(0);
x_48 = l_rbnode_insert___at_lean_ir_phi_predecessors___spec__5(x_1, x_40, x_47);
x_1 = x_48;
x_2 = x_11;
goto _start;
}
else
{
obj* x_54; uint8 x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_11);
lean::dec(x_40);
x_54 = l_lean_ir_phi_to__format___main(x_0);
x_55 = 0;
x_56 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__2;
lean::inc(x_56);
x_58 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_54);
lean::cnstr_set_scalar(x_58, sizeof(void*)*2, x_55);
x_59 = x_58;
x_60 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_60);
x_62 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_62, 0, x_59);
lean::cnstr_set(x_62, 1, x_60);
lean::cnstr_set_scalar(x_62, sizeof(void*)*2, x_55);
x_63 = x_62;
x_64 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_64, 0, x_63);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_4);
return x_65;
}
}
}
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
uint8 x_3; obj* x_4; 
lean::dec(x_0);
x_3 = 1;
x_4 = lean::box(x_3);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_13; uint8 x_14; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 3);
lean::inc(x_9);
lean::dec(x_1);
lean::inc(x_0);
x_13 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_0, x_7);
x_14 = l_option_to__bool___main___rarg(x_13);
if (x_14 == 0)
{
lean::dec(x_5);
if (x_14 == 0)
{
obj* x_18; 
lean::dec(x_9);
lean::dec(x_0);
x_18 = lean::box(x_14);
return x_18;
}
else
{
x_1 = x_9;
goto _start;
}
}
else
{
obj* x_21; uint8 x_22; 
lean::inc(x_0);
x_21 = l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(x_0, x_5);
x_22 = lean::unbox(x_21);
if (x_22 == 0)
{
lean::dec(x_9);
lean::dec(x_0);
return x_21;
}
else
{
lean::dec(x_21);
x_1 = x_9;
goto _start;
}
}
}
default:
{
obj* x_27; obj* x_29; obj* x_31; obj* x_35; uint8 x_36; 
x_27 = lean::cnstr_get(x_1, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_1, 1);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_1, 3);
lean::inc(x_31);
lean::dec(x_1);
lean::inc(x_0);
x_35 = l_rbtree_find___at_lean_ir_phi_predecessors___spec__1(x_0, x_29);
x_36 = l_option_to__bool___main___rarg(x_35);
if (x_36 == 0)
{
lean::dec(x_27);
if (x_36 == 0)
{
obj* x_40; 
lean::dec(x_0);
lean::dec(x_31);
x_40 = lean::box(x_36);
return x_40;
}
else
{
x_1 = x_31;
goto _start;
}
}
else
{
obj* x_43; uint8 x_44; 
lean::inc(x_0);
x_43 = l_rbnode_all___main___at_lean_ir_phis_check__predecessors___spec__3(x_0, x_27);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
lean::dec(x_0);
lean::dec(x_31);
return x_43;
}
else
{
lean::dec(x_43);
x_1 = x_31;
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
obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_17; obj* x_18; obj* x_20; 
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
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
if (lean::obj_tag(x_18) == 0)
{
obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_0);
x_24 = lean::cnstr_get(x_18, 0);
lean::inc(x_24);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 x_26 = x_18;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_24);
x_12 = x_27;
x_13 = x_20;
goto lbl_14;
}
else
{
obj* x_28; obj* x_30; 
x_28 = lean::cnstr_get(x_18, 0);
lean::inc(x_28);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 x_30 = x_18;
}
if (lean::obj_tag(x_0) == 0)
{
obj* x_31; obj* x_32; 
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_28);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
x_12 = x_32;
x_13 = x_20;
goto lbl_14;
}
else
{
obj* x_33; obj* x_35; uint8 x_36; 
x_33 = lean::cnstr_get(x_0, 0);
lean::inc(x_33);
x_35 = l_rbtree_seteq___at_lean_ir_phis_check__predecessors___spec__1(x_33, x_28);
x_36 = lean::unbox(x_35);
lean::dec(x_35);
if (x_36 == 0)
{
obj* x_39; obj* x_41; uint8 x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_0);
x_39 = lean::cnstr_get(x_7, 0);
lean::inc(x_39);
x_41 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__1(x_39);
x_42 = 0;
x_43 = l_list_mfoldl___main___at_lean_ir_phis_check__predecessors___spec__4___closed__1;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_41);
lean::cnstr_set_scalar(x_45, sizeof(void*)*2, x_42);
x_46 = x_45;
x_47 = l_list_mfoldl___main___at_lean_ir_phi_predecessors___spec__7___closed__1;
lean::inc(x_47);
x_49 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_49, 0, x_46);
lean::cnstr_set(x_49, 1, x_47);
lean::cnstr_set_scalar(x_49, sizeof(void*)*2, x_42);
x_50 = x_49;
lean::inc(x_7);
x_52 = l_lean_ir_phi_to__format___main(x_7);
x_53 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set(x_53, 1, x_52);
lean::cnstr_set_scalar(x_53, sizeof(void*)*2, x_42);
x_54 = x_53;
x_55 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_55);
x_57 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_57, 0, x_54);
lean::cnstr_set(x_57, 1, x_55);
lean::cnstr_set_scalar(x_57, sizeof(void*)*2, x_42);
x_58 = x_57;
if (lean::is_scalar(x_30)) {
 x_59 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_59 = x_30;
 lean::cnstr_set_tag(x_30, 0);
}
lean::cnstr_set(x_59, 0, x_58);
x_12 = x_59;
x_13 = x_20;
goto lbl_14;
}
else
{
obj* x_60; 
if (lean::is_scalar(x_30)) {
 x_60 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_60 = x_30;
}
lean::cnstr_set(x_60, 0, x_0);
x_12 = x_60;
x_13 = x_20;
goto lbl_14;
}
}
}
lbl_14:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_63; obj* x_65; obj* x_66; uint8 x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_9);
lean::dec(x_2);
x_63 = lean::cnstr_get(x_12, 0);
lean::inc(x_63);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_65 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_65 = x_12;
}
x_66 = l_lean_ir_phi_to__format___main(x_7);
x_67 = 0;
x_68 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__1;
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
lean::cnstr_set(x_79, 1, x_63);
lean::cnstr_set_scalar(x_79, sizeof(void*)*2, x_67);
x_80 = x_79;
if (lean::is_scalar(x_65)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_65;
}
lean::cnstr_set(x_81, 0, x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_13);
return x_82;
}
else
{
lean::dec(x_7);
if (lean::obj_tag(x_12) == 0)
{
obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_9);
lean::dec(x_2);
x_86 = lean::cnstr_get(x_12, 0);
lean::inc(x_86);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_88 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_88 = x_12;
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_86);
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_13);
return x_90;
}
else
{
obj* x_91; 
x_91 = lean::cnstr_get(x_12, 0);
lean::inc(x_91);
lean::dec(x_12);
x_0 = x_91;
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
obj* x_16; obj* x_18; 
lean::dec(x_5);
x_16 = l_lean_ir_var_declare___closed__1;
lean::inc(x_16);
if (lean::is_scalar(x_9)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_9;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
x_13 = l_lean_ir_phi_valid__ssa(x_7, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_0 = x_9;
x_2 = x_16;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
x_13 = l_lean_ir_instr_valid__ssa(x_7, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_0 = x_9;
x_2 = x_16;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
x_13 = l_lean_ir_arg_define(x_7, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_0 = x_9;
x_2 = x_16;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_var_declare___closed__1;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
x_13 = l_lean_ir_block_valid__ssa__core(x_7, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_0 = x_9;
x_2 = x_16;
goto _start;
}
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
obj* x_22; 
lean::dec(x_17);
lean::dec(x_0);
if (lean::is_scalar(x_10)) {
 x_22 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_22 = x_10;
}
lean::cnstr_set(x_22, 0, x_8);
return x_22;
}
else
{
obj* x_23; obj* x_25; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
x_23 = lean::cnstr_get(x_15, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_15, 1);
lean::inc(x_25);
lean::dec(x_15);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__1), 3, 1);
lean::closure_set(x_28, 0, x_17);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_decl_valid__ssa___lambda__1), 4, 1);
lean::closure_set(x_29, 0, x_23);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_bind__cont___at_lean_ir_decl_valid__ssa___spec__2___rarg), 4, 1);
lean::closure_set(x_30, 0, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_ir_decl_valid__ssa___spec__3___rarg), 4, 2);
lean::closure_set(x_31, 0, x_28);
lean::closure_set(x_31, 1, x_30);
lean::inc(x_8);
x_33 = l_lean_ir_ssa__valid__m_run___rarg(x_31, x_8);
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_25);
x_37 = lean::cnstr_get(x_33, 0);
lean::inc(x_37);
lean::dec(x_33);
x_1 = x_37;
goto lbl_2;
}
else
{
obj* x_41; obj* x_43; 
lean::dec(x_33);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_list_mmap_x_27___main___at_lean_ir_decl_valid__ssa___spec__4), 3, 1);
lean::closure_set(x_41, 0, x_25);
lean::inc(x_8);
x_43 = l_lean_ir_ssa__valid__m_run___rarg(x_41, x_8);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; 
lean::dec(x_8);
lean::dec(x_10);
x_46 = lean::cnstr_get(x_43, 0);
lean::inc(x_46);
lean::dec(x_43);
x_1 = x_46;
goto lbl_2;
}
else
{
obj* x_51; 
lean::dec(x_0);
lean::dec(x_43);
if (lean::is_scalar(x_10)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_10;
}
lean::cnstr_set(x_51, 0, x_8);
return x_51;
}
}
}
}
}
lbl_2:
{
obj* x_52; obj* x_53; obj* x_56; uint8 x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_52 = l_lean_ir_decl_header___main(x_0);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
lean::dec(x_52);
x_56 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_53);
x_57 = 0;
x_58 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
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
x_66 = lean::box(1);
x_67 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set(x_67, 1, x_66);
lean::cnstr_set_scalar(x_67, sizeof(void*)*2, x_57);
x_68 = x_67;
x_69 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_1);
lean::cnstr_set_scalar(x_69, sizeof(void*)*2, x_57);
x_70 = x_69;
x_71 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_71, 0, x_70);
return x_71;
}
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
obj* l_list_mmap_x_27___main___at_lean_ir_terminator_check__blockids___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_4; 
x_2 = l_lean_ir_var_declare___closed__1;
lean::inc(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_blockid_defined(x_5, x_1);
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
obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_19 = x_11;
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_15)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_15;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_13);
return x_21;
}
else
{
lean::dec(x_15);
lean::dec(x_11);
x_0 = x_7;
x_1 = x_13;
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
obj* x_2; obj* x_4; 
x_2 = l_lean_ir_var_declare___closed__1;
lean::inc(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_block_declare(x_5, x_1);
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
obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_19 = x_11;
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_15)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_15;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_13);
return x_21;
}
else
{
lean::dec(x_15);
lean::dec(x_11);
x_0 = x_7;
x_1 = x_13;
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
obj* x_2; obj* x_4; 
x_2 = l_lean_ir_var_declare___closed__1;
lean::inc(x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_ir_block_check__blockids(x_5, x_1);
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
obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_19 = x_11;
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_15)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_15;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_13);
return x_21;
}
else
{
lean::dec(x_15);
lean::dec(x_11);
x_0 = x_7;
x_1 = x_13;
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
}
lean::cnstr_set(x_40, 0, x_39);
if (lean::is_scalar(x_17)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_17;
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
