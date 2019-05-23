// Lean compiler output
// Module: init.lean.compiler.ir.default
// Imports: init.lean.compiler.ir.basic init.lean.compiler.ir.format init.lean.compiler.ir.compilerm init.lean.compiler.ir.pushproj init.lean.compiler.ir.elimdead init.lean.compiler.ir.simpcase init.lean.compiler.ir.resetreuse init.lean.compiler.ir.normids init.lean.compiler.ir.checker init.lean.compiler.ir.borrow init.lean.compiler.ir.boxing init.lean.compiler.ir.rc init.lean.compiler.ir.expandresetreuse init.lean.compiler.ir.emitcpp
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
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(obj*, obj*);
extern obj* l_Array_empty___closed__1;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__5;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__2;
obj* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
obj* l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
obj* l_Lean_IR_Decl_expandResetReuse___main(obj*);
obj* l_Lean_IR_Decl_pushProj___main(obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__11;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__14;
extern obj* l_Lean_IR_tracePrefixOptionName;
extern obj* l_Lean_IR_ExplicitRC_getDecl___closed__1;
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_inferBorrow(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_default_1__compileAux(obj*, obj*, obj*);
obj* l_Lean_IR_Decl_elimDead___main(obj*);
obj* l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__8;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__7;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__4;
obj* l_Lean_IR_Decl_insertResetReuse___main(obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
obj* l_Array_hmmapAux___main___at_Lean_IR_inferBorrow___spec__1(obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
namespace lean {
namespace ir {
obj* compile_core(obj*, obj*, obj*);
}}
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__17;
obj* l_Lean_IR_Decl_simpCase___main(obj*);
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_Lean_IR_explicitRC(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(obj*, obj*);
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(obj*, obj*);
obj* l_Lean_IR_explicitBoxing(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(obj* x_0, obj* x_1) {
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = l_Lean_IR_ExplicitRC_getDecl___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = l_Lean_IR_Decl_pushProj___main(x_6);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_0, x_10);
x_12 = lean::array_fset(x_8, x_0, x_9);
lean::dec(x_0);
x_0 = x_11;
x_1 = x_12;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(obj* x_0, obj* x_1) {
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = l_Lean_IR_ExplicitRC_getDecl___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = l_Lean_IR_Decl_insertResetReuse___main(x_6);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_0, x_10);
x_12 = lean::array_fset(x_8, x_0, x_9);
lean::dec(x_0);
x_0 = x_11;
x_1 = x_12;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(obj* x_0, obj* x_1) {
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = l_Lean_IR_ExplicitRC_getDecl___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = l_Lean_IR_Decl_elimDead___main(x_6);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_0, x_10);
x_12 = lean::array_fset(x_8, x_0, x_9);
lean::dec(x_0);
x_0 = x_11;
x_1 = x_12;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(obj* x_0, obj* x_1) {
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = l_Lean_IR_ExplicitRC_getDecl___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = l_Lean_IR_Decl_simpCase___main(x_6);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_0, x_10);
x_12 = lean::array_fset(x_8, x_0, x_9);
lean::dec(x_0);
x_0 = x_11;
x_1 = x_12;
goto _start;
}
}
}
obj* l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(obj* x_0, obj* x_1) {
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
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = l_Lean_IR_ExplicitRC_getDecl___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = l_Lean_IR_Decl_expandResetReuse___main(x_6);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_0, x_10);
x_12 = lean::array_fset(x_8, x_0, x_9);
lean::dec(x_0);
x_0 = x_11;
x_1 = x_12;
goto _start;
}
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("init");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("init");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("push_proj");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("push_proj");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("reset_reuse");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("reset_reuse");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__7() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("elim_dead");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__8() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("elim_dead");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__9() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("simp_case");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__10() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("simp_case");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__11() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("borrow");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__12() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("borrow");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__13() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("boxing");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__14() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("boxing");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__15() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("rc");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__16() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("rc");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__17() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("expand_reset_reuse");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__18() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("expand_reset_reuse");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_default_1__compileAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
x_3 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__1;
x_4 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__2;
lean::inc(x_1);
lean::inc(x_0);
x_7 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_3, x_4, x_0, x_1, x_2);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; 
x_8 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_10 = x_7;
} else {
 lean::inc(x_8);
 lean::dec(x_7);
 x_10 = lean::box(0);
}
x_11 = lean::box(0);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
x_13 = lean::mk_nat_obj(0ul);
lean::inc(x_0);
x_15 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_0, x_0, x_13, x_1, x_12);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_25; 
x_16 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_18 = x_15;
} else {
 lean::inc(x_16);
 lean::dec(x_15);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_11);
lean::cnstr_set(x_19, 1, x_16);
x_20 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_13, x_0);
x_21 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
x_22 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__4;
lean::inc(x_1);
lean::inc(x_20);
x_25 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_21, x_22, x_20, x_1, x_19);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_35; 
x_26 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_28 = x_25;
} else {
 lean::inc(x_26);
 lean::dec(x_25);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_11);
lean::cnstr_set(x_29, 1, x_26);
x_30 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(x_13, x_20);
x_31 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__5;
x_32 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
lean::inc(x_1);
lean::inc(x_30);
x_35 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_31, x_32, x_30, x_1, x_29);
if (lean::obj_tag(x_35) == 0)
{
obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_45; 
x_36 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 x_38 = x_35;
} else {
 lean::inc(x_36);
 lean::dec(x_35);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_11);
lean::cnstr_set(x_39, 1, x_36);
x_40 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(x_13, x_30);
x_41 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__7;
x_42 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__8;
lean::inc(x_1);
lean::inc(x_40);
x_45 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_41, x_42, x_40, x_1, x_39);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_55; 
x_46 = lean::cnstr_get(x_45, 1);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 x_48 = x_45;
} else {
 lean::inc(x_46);
 lean::dec(x_45);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_11);
lean::cnstr_set(x_49, 1, x_46);
x_50 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(x_13, x_40);
x_51 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
x_52 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
lean::inc(x_1);
lean::inc(x_50);
x_55 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_51, x_52, x_50, x_1, x_49);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_56 = lean::cnstr_get(x_55, 1);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 x_58 = x_55;
} else {
 lean::inc(x_56);
 lean::dec(x_55);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_11);
lean::cnstr_set(x_59, 1, x_56);
x_60 = l_Array_hmmapAux___main___at_Lean_IR_inferBorrow___spec__1(x_13, x_50);
x_61 = l_Lean_IR_inferBorrow(x_60, x_1, x_59);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_72; 
x_62 = lean::cnstr_get(x_61, 0);
x_64 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 x_66 = x_61;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_61);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_11);
lean::cnstr_set(x_67, 1, x_64);
x_68 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__11;
x_69 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean::inc(x_1);
lean::inc(x_62);
x_72 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_68, x_69, x_62, x_1, x_67);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; obj* x_75; obj* x_76; obj* x_77; 
x_73 = lean::cnstr_get(x_72, 1);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 x_75 = x_72;
} else {
 lean::inc(x_73);
 lean::dec(x_72);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_11);
lean::cnstr_set(x_76, 1, x_73);
x_77 = l_Lean_IR_explicitBoxing(x_62, x_1, x_76);
if (lean::obj_tag(x_77) == 0)
{
obj* x_78; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_88; 
x_78 = lean::cnstr_get(x_77, 0);
x_80 = lean::cnstr_get(x_77, 1);
if (lean::is_exclusive(x_77)) {
 x_82 = x_77;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_77);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_11);
lean::cnstr_set(x_83, 1, x_80);
x_84 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
x_85 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__14;
lean::inc(x_1);
lean::inc(x_78);
x_88 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_84, x_85, x_78, x_1, x_83);
if (lean::obj_tag(x_88) == 0)
{
obj* x_89; obj* x_91; obj* x_92; obj* x_93; 
x_89 = lean::cnstr_get(x_88, 1);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 x_91 = x_88;
} else {
 lean::inc(x_89);
 lean::dec(x_88);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_11);
lean::cnstr_set(x_92, 1, x_89);
x_93 = l_Lean_IR_explicitRC(x_78, x_1, x_92);
if (lean::obj_tag(x_93) == 0)
{
obj* x_94; obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_104; 
x_94 = lean::cnstr_get(x_93, 0);
x_96 = lean::cnstr_get(x_93, 1);
if (lean::is_exclusive(x_93)) {
 x_98 = x_93;
} else {
 lean::inc(x_94);
 lean::inc(x_96);
 lean::dec(x_93);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_11);
lean::cnstr_set(x_99, 1, x_96);
x_100 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
x_101 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
lean::inc(x_1);
lean::inc(x_94);
x_104 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_100, x_101, x_94, x_1, x_99);
if (lean::obj_tag(x_104) == 0)
{
obj* x_105; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_114; 
x_105 = lean::cnstr_get(x_104, 1);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 x_107 = x_104;
} else {
 lean::inc(x_105);
 lean::dec(x_104);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_11);
lean::cnstr_set(x_108, 1, x_105);
x_109 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_13, x_94);
x_110 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__17;
x_111 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean::inc(x_1);
lean::inc(x_109);
x_114 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_110, x_111, x_109, x_1, x_108);
if (lean::obj_tag(x_114) == 0)
{
obj* x_115; obj* x_117; obj* x_118; obj* x_120; 
x_115 = lean::cnstr_get(x_114, 1);
if (lean::is_exclusive(x_114)) {
 lean::cnstr_release(x_114, 0);
 x_117 = x_114;
} else {
 lean::inc(x_115);
 lean::dec(x_114);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_11);
lean::cnstr_set(x_118, 1, x_115);
lean::inc(x_109);
x_120 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_109, x_109, x_13, x_1, x_118);
if (lean::obj_tag(x_120) == 0)
{
obj* x_121; obj* x_123; obj* x_124; obj* x_125; 
x_121 = lean::cnstr_get(x_120, 1);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_release(x_120, 0);
 x_123 = x_120;
} else {
 lean::inc(x_121);
 lean::dec(x_120);
 x_123 = lean::box(0);
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_11);
lean::cnstr_set(x_124, 1, x_121);
x_125 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_109, x_13, x_1, x_124);
lean::dec(x_1);
lean::dec(x_109);
if (lean::obj_tag(x_125) == 0)
{
obj* x_128; obj* x_130; obj* x_131; 
x_128 = lean::cnstr_get(x_125, 1);
if (lean::is_exclusive(x_125)) {
 lean::cnstr_release(x_125, 0);
 x_130 = x_125;
} else {
 lean::inc(x_128);
 lean::dec(x_125);
 x_130 = lean::box(0);
}
if (lean::is_scalar(x_130)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_130;
}
lean::cnstr_set(x_131, 0, x_11);
lean::cnstr_set(x_131, 1, x_128);
return x_131;
}
else
{
obj* x_132; obj* x_134; obj* x_136; obj* x_137; 
x_132 = lean::cnstr_get(x_125, 0);
x_134 = lean::cnstr_get(x_125, 1);
if (lean::is_exclusive(x_125)) {
 x_136 = x_125;
} else {
 lean::inc(x_132);
 lean::inc(x_134);
 lean::dec(x_125);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_132);
lean::cnstr_set(x_137, 1, x_134);
return x_137;
}
}
else
{
obj* x_140; obj* x_142; obj* x_144; obj* x_145; 
lean::dec(x_1);
lean::dec(x_109);
x_140 = lean::cnstr_get(x_120, 0);
x_142 = lean::cnstr_get(x_120, 1);
if (lean::is_exclusive(x_120)) {
 x_144 = x_120;
} else {
 lean::inc(x_140);
 lean::inc(x_142);
 lean::dec(x_120);
 x_144 = lean::box(0);
}
if (lean::is_scalar(x_144)) {
 x_145 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_145 = x_144;
}
lean::cnstr_set(x_145, 0, x_140);
lean::cnstr_set(x_145, 1, x_142);
return x_145;
}
}
else
{
obj* x_148; obj* x_150; obj* x_152; obj* x_153; 
lean::dec(x_1);
lean::dec(x_109);
x_148 = lean::cnstr_get(x_114, 0);
x_150 = lean::cnstr_get(x_114, 1);
if (lean::is_exclusive(x_114)) {
 x_152 = x_114;
} else {
 lean::inc(x_148);
 lean::inc(x_150);
 lean::dec(x_114);
 x_152 = lean::box(0);
}
if (lean::is_scalar(x_152)) {
 x_153 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_153 = x_152;
}
lean::cnstr_set(x_153, 0, x_148);
lean::cnstr_set(x_153, 1, x_150);
return x_153;
}
}
else
{
obj* x_156; obj* x_158; obj* x_160; obj* x_161; 
lean::dec(x_1);
lean::dec(x_94);
x_156 = lean::cnstr_get(x_104, 0);
x_158 = lean::cnstr_get(x_104, 1);
if (lean::is_exclusive(x_104)) {
 x_160 = x_104;
} else {
 lean::inc(x_156);
 lean::inc(x_158);
 lean::dec(x_104);
 x_160 = lean::box(0);
}
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_156);
lean::cnstr_set(x_161, 1, x_158);
return x_161;
}
}
else
{
obj* x_163; obj* x_165; obj* x_167; obj* x_168; 
lean::dec(x_1);
x_163 = lean::cnstr_get(x_93, 0);
x_165 = lean::cnstr_get(x_93, 1);
if (lean::is_exclusive(x_93)) {
 x_167 = x_93;
} else {
 lean::inc(x_163);
 lean::inc(x_165);
 lean::dec(x_93);
 x_167 = lean::box(0);
}
if (lean::is_scalar(x_167)) {
 x_168 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_168 = x_167;
}
lean::cnstr_set(x_168, 0, x_163);
lean::cnstr_set(x_168, 1, x_165);
return x_168;
}
}
else
{
obj* x_171; obj* x_173; obj* x_175; obj* x_176; 
lean::dec(x_1);
lean::dec(x_78);
x_171 = lean::cnstr_get(x_88, 0);
x_173 = lean::cnstr_get(x_88, 1);
if (lean::is_exclusive(x_88)) {
 x_175 = x_88;
} else {
 lean::inc(x_171);
 lean::inc(x_173);
 lean::dec(x_88);
 x_175 = lean::box(0);
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_171);
lean::cnstr_set(x_176, 1, x_173);
return x_176;
}
}
else
{
obj* x_178; obj* x_180; obj* x_182; obj* x_183; 
lean::dec(x_1);
x_178 = lean::cnstr_get(x_77, 0);
x_180 = lean::cnstr_get(x_77, 1);
if (lean::is_exclusive(x_77)) {
 x_182 = x_77;
} else {
 lean::inc(x_178);
 lean::inc(x_180);
 lean::dec(x_77);
 x_182 = lean::box(0);
}
if (lean::is_scalar(x_182)) {
 x_183 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_183 = x_182;
}
lean::cnstr_set(x_183, 0, x_178);
lean::cnstr_set(x_183, 1, x_180);
return x_183;
}
}
else
{
obj* x_186; obj* x_188; obj* x_190; obj* x_191; 
lean::dec(x_1);
lean::dec(x_62);
x_186 = lean::cnstr_get(x_72, 0);
x_188 = lean::cnstr_get(x_72, 1);
if (lean::is_exclusive(x_72)) {
 x_190 = x_72;
} else {
 lean::inc(x_186);
 lean::inc(x_188);
 lean::dec(x_72);
 x_190 = lean::box(0);
}
if (lean::is_scalar(x_190)) {
 x_191 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_191 = x_190;
}
lean::cnstr_set(x_191, 0, x_186);
lean::cnstr_set(x_191, 1, x_188);
return x_191;
}
}
else
{
obj* x_193; obj* x_195; obj* x_197; obj* x_198; 
lean::dec(x_1);
x_193 = lean::cnstr_get(x_61, 0);
x_195 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 x_197 = x_61;
} else {
 lean::inc(x_193);
 lean::inc(x_195);
 lean::dec(x_61);
 x_197 = lean::box(0);
}
if (lean::is_scalar(x_197)) {
 x_198 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_198 = x_197;
}
lean::cnstr_set(x_198, 0, x_193);
lean::cnstr_set(x_198, 1, x_195);
return x_198;
}
}
else
{
obj* x_201; obj* x_203; obj* x_205; obj* x_206; 
lean::dec(x_1);
lean::dec(x_50);
x_201 = lean::cnstr_get(x_55, 0);
x_203 = lean::cnstr_get(x_55, 1);
if (lean::is_exclusive(x_55)) {
 x_205 = x_55;
} else {
 lean::inc(x_201);
 lean::inc(x_203);
 lean::dec(x_55);
 x_205 = lean::box(0);
}
if (lean::is_scalar(x_205)) {
 x_206 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_206 = x_205;
}
lean::cnstr_set(x_206, 0, x_201);
lean::cnstr_set(x_206, 1, x_203);
return x_206;
}
}
else
{
obj* x_209; obj* x_211; obj* x_213; obj* x_214; 
lean::dec(x_1);
lean::dec(x_40);
x_209 = lean::cnstr_get(x_45, 0);
x_211 = lean::cnstr_get(x_45, 1);
if (lean::is_exclusive(x_45)) {
 x_213 = x_45;
} else {
 lean::inc(x_209);
 lean::inc(x_211);
 lean::dec(x_45);
 x_213 = lean::box(0);
}
if (lean::is_scalar(x_213)) {
 x_214 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_214 = x_213;
}
lean::cnstr_set(x_214, 0, x_209);
lean::cnstr_set(x_214, 1, x_211);
return x_214;
}
}
else
{
obj* x_217; obj* x_219; obj* x_221; obj* x_222; 
lean::dec(x_1);
lean::dec(x_30);
x_217 = lean::cnstr_get(x_35, 0);
x_219 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 x_221 = x_35;
} else {
 lean::inc(x_217);
 lean::inc(x_219);
 lean::dec(x_35);
 x_221 = lean::box(0);
}
if (lean::is_scalar(x_221)) {
 x_222 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_222 = x_221;
}
lean::cnstr_set(x_222, 0, x_217);
lean::cnstr_set(x_222, 1, x_219);
return x_222;
}
}
else
{
obj* x_225; obj* x_227; obj* x_229; obj* x_230; 
lean::dec(x_1);
lean::dec(x_20);
x_225 = lean::cnstr_get(x_25, 0);
x_227 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_229 = x_25;
} else {
 lean::inc(x_225);
 lean::inc(x_227);
 lean::dec(x_25);
 x_229 = lean::box(0);
}
if (lean::is_scalar(x_229)) {
 x_230 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_230 = x_229;
}
lean::cnstr_set(x_230, 0, x_225);
lean::cnstr_set(x_230, 1, x_227);
return x_230;
}
}
else
{
obj* x_233; obj* x_235; obj* x_237; obj* x_238; 
lean::dec(x_1);
lean::dec(x_0);
x_233 = lean::cnstr_get(x_15, 0);
x_235 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 x_237 = x_15;
} else {
 lean::inc(x_233);
 lean::inc(x_235);
 lean::dec(x_15);
 x_237 = lean::box(0);
}
if (lean::is_scalar(x_237)) {
 x_238 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_238 = x_237;
}
lean::cnstr_set(x_238, 0, x_233);
lean::cnstr_set(x_238, 1, x_235);
return x_238;
}
}
else
{
obj* x_241; obj* x_243; obj* x_245; obj* x_246; 
lean::dec(x_1);
lean::dec(x_0);
x_241 = lean::cnstr_get(x_7, 0);
x_243 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_245 = x_7;
} else {
 lean::inc(x_241);
 lean::inc(x_243);
 lean::dec(x_7);
 x_245 = lean::box(0);
}
if (lean::is_scalar(x_245)) {
 x_246 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_246 = x_245;
}
lean::cnstr_set(x_246, 0, x_241);
lean::cnstr_set(x_246, 1, x_243);
return x_246;
}
}
}
namespace lean {
namespace ir {
obj* compile_core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = l_Array_empty___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_4);
x_7 = l___private_init_lean_compiler_ir_default_1__compileAux(x_2, x_1, x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_17; 
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_11);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_13);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
else
{
obj* x_18; obj* x_20; obj* x_23; obj* x_26; obj* x_27; 
x_18 = lean::cnstr_get(x_7, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_7, 1);
lean::inc(x_20);
lean::dec(x_7);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
x_26 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_26, 0, x_18);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
}
}
}}
obj* initialize_init_lean_compiler_ir_basic(obj*);
obj* initialize_init_lean_compiler_ir_format(obj*);
obj* initialize_init_lean_compiler_ir_compilerm(obj*);
obj* initialize_init_lean_compiler_ir_pushproj(obj*);
obj* initialize_init_lean_compiler_ir_elimdead(obj*);
obj* initialize_init_lean_compiler_ir_simpcase(obj*);
obj* initialize_init_lean_compiler_ir_resetreuse(obj*);
obj* initialize_init_lean_compiler_ir_normids(obj*);
obj* initialize_init_lean_compiler_ir_checker(obj*);
obj* initialize_init_lean_compiler_ir_borrow(obj*);
obj* initialize_init_lean_compiler_ir_boxing(obj*);
obj* initialize_init_lean_compiler_ir_rc(obj*);
obj* initialize_init_lean_compiler_ir_expandresetreuse(obj*);
obj* initialize_init_lean_compiler_ir_emitcpp(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_default(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_format(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_pushproj(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_elimdead(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_simpcase(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_resetreuse(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_normids(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_checker(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_borrow(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_boxing(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_rc(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_expandresetreuse(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_emitcpp(w);
if (io_result_is_error(w)) return w;
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__1 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__1);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__2 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__2();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__2);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__3 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__3();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__3);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__4 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__4();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__4);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__5 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__5();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__5);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__6 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__6();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__6);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__7 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__7();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__7);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__8 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__8();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__8);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__9 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__9();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__9);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__10 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__10();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__10);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__11 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__11();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__11);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__12 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__12();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__12);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__13 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__13();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__13);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__14 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__14();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__14);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__15 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__15();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__15);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__16 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__16();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__16);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__17 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__17();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__17);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__18 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__18();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__18);
return w;
}
