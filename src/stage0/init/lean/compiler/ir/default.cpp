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
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__20;
obj* l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
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
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
obj* l_Lean_IR_ExpandResetReuse_main(obj*);
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
x_9 = l_Lean_IR_ExpandResetReuse_main(x_6);
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
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__19() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::mk_string("result");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = l_Lean_IR_tracePrefixOptionName;
x_4 = l_Lean_Name_append___main(x_3, x_2);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__20() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("result");
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
obj* x_115; obj* x_117; obj* x_118; obj* x_119; obj* x_122; 
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
x_119 = l_Array_hmmapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_13, x_109);
lean::inc(x_1);
lean::inc(x_119);
x_122 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_21, x_22, x_119, x_1, x_118);
if (lean::obj_tag(x_122) == 0)
{
obj* x_123; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_131; 
x_123 = lean::cnstr_get(x_122, 1);
if (lean::is_exclusive(x_122)) {
 lean::cnstr_release(x_122, 0);
 x_125 = x_122;
} else {
 lean::inc(x_123);
 lean::dec(x_122);
 x_125 = lean::box(0);
}
if (lean::is_scalar(x_125)) {
 x_126 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_126 = x_125;
}
lean::cnstr_set(x_126, 0, x_11);
lean::cnstr_set(x_126, 1, x_123);
x_127 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_128 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__20;
lean::inc(x_1);
lean::inc(x_119);
x_131 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_127, x_128, x_119, x_1, x_126);
if (lean::obj_tag(x_131) == 0)
{
obj* x_132; obj* x_134; obj* x_135; obj* x_137; 
x_132 = lean::cnstr_get(x_131, 1);
if (lean::is_exclusive(x_131)) {
 lean::cnstr_release(x_131, 0);
 x_134 = x_131;
} else {
 lean::inc(x_132);
 lean::dec(x_131);
 x_134 = lean::box(0);
}
if (lean::is_scalar(x_134)) {
 x_135 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_135 = x_134;
}
lean::cnstr_set(x_135, 0, x_11);
lean::cnstr_set(x_135, 1, x_132);
lean::inc(x_119);
x_137 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_119, x_119, x_13, x_1, x_135);
if (lean::obj_tag(x_137) == 0)
{
obj* x_138; obj* x_140; obj* x_141; obj* x_142; 
x_138 = lean::cnstr_get(x_137, 1);
if (lean::is_exclusive(x_137)) {
 lean::cnstr_release(x_137, 0);
 x_140 = x_137;
} else {
 lean::inc(x_138);
 lean::dec(x_137);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_11);
lean::cnstr_set(x_141, 1, x_138);
x_142 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_119, x_13, x_1, x_141);
lean::dec(x_1);
lean::dec(x_119);
if (lean::obj_tag(x_142) == 0)
{
obj* x_145; obj* x_147; obj* x_148; 
x_145 = lean::cnstr_get(x_142, 1);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 x_147 = x_142;
} else {
 lean::inc(x_145);
 lean::dec(x_142);
 x_147 = lean::box(0);
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_11);
lean::cnstr_set(x_148, 1, x_145);
return x_148;
}
else
{
obj* x_149; obj* x_151; obj* x_153; obj* x_154; 
x_149 = lean::cnstr_get(x_142, 0);
x_151 = lean::cnstr_get(x_142, 1);
if (lean::is_exclusive(x_142)) {
 x_153 = x_142;
} else {
 lean::inc(x_149);
 lean::inc(x_151);
 lean::dec(x_142);
 x_153 = lean::box(0);
}
if (lean::is_scalar(x_153)) {
 x_154 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_154 = x_153;
}
lean::cnstr_set(x_154, 0, x_149);
lean::cnstr_set(x_154, 1, x_151);
return x_154;
}
}
else
{
obj* x_157; obj* x_159; obj* x_161; obj* x_162; 
lean::dec(x_119);
lean::dec(x_1);
x_157 = lean::cnstr_get(x_137, 0);
x_159 = lean::cnstr_get(x_137, 1);
if (lean::is_exclusive(x_137)) {
 x_161 = x_137;
} else {
 lean::inc(x_157);
 lean::inc(x_159);
 lean::dec(x_137);
 x_161 = lean::box(0);
}
if (lean::is_scalar(x_161)) {
 x_162 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_162 = x_161;
}
lean::cnstr_set(x_162, 0, x_157);
lean::cnstr_set(x_162, 1, x_159);
return x_162;
}
}
else
{
obj* x_165; obj* x_167; obj* x_169; obj* x_170; 
lean::dec(x_119);
lean::dec(x_1);
x_165 = lean::cnstr_get(x_131, 0);
x_167 = lean::cnstr_get(x_131, 1);
if (lean::is_exclusive(x_131)) {
 x_169 = x_131;
} else {
 lean::inc(x_165);
 lean::inc(x_167);
 lean::dec(x_131);
 x_169 = lean::box(0);
}
if (lean::is_scalar(x_169)) {
 x_170 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_170 = x_169;
}
lean::cnstr_set(x_170, 0, x_165);
lean::cnstr_set(x_170, 1, x_167);
return x_170;
}
}
else
{
obj* x_173; obj* x_175; obj* x_177; obj* x_178; 
lean::dec(x_119);
lean::dec(x_1);
x_173 = lean::cnstr_get(x_122, 0);
x_175 = lean::cnstr_get(x_122, 1);
if (lean::is_exclusive(x_122)) {
 x_177 = x_122;
} else {
 lean::inc(x_173);
 lean::inc(x_175);
 lean::dec(x_122);
 x_177 = lean::box(0);
}
if (lean::is_scalar(x_177)) {
 x_178 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_178 = x_177;
}
lean::cnstr_set(x_178, 0, x_173);
lean::cnstr_set(x_178, 1, x_175);
return x_178;
}
}
else
{
obj* x_181; obj* x_183; obj* x_185; obj* x_186; 
lean::dec(x_1);
lean::dec(x_109);
x_181 = lean::cnstr_get(x_114, 0);
x_183 = lean::cnstr_get(x_114, 1);
if (lean::is_exclusive(x_114)) {
 x_185 = x_114;
} else {
 lean::inc(x_181);
 lean::inc(x_183);
 lean::dec(x_114);
 x_185 = lean::box(0);
}
if (lean::is_scalar(x_185)) {
 x_186 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_186 = x_185;
}
lean::cnstr_set(x_186, 0, x_181);
lean::cnstr_set(x_186, 1, x_183);
return x_186;
}
}
else
{
obj* x_189; obj* x_191; obj* x_193; obj* x_194; 
lean::dec(x_1);
lean::dec(x_94);
x_189 = lean::cnstr_get(x_104, 0);
x_191 = lean::cnstr_get(x_104, 1);
if (lean::is_exclusive(x_104)) {
 x_193 = x_104;
} else {
 lean::inc(x_189);
 lean::inc(x_191);
 lean::dec(x_104);
 x_193 = lean::box(0);
}
if (lean::is_scalar(x_193)) {
 x_194 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_194 = x_193;
}
lean::cnstr_set(x_194, 0, x_189);
lean::cnstr_set(x_194, 1, x_191);
return x_194;
}
}
else
{
obj* x_196; obj* x_198; obj* x_200; obj* x_201; 
lean::dec(x_1);
x_196 = lean::cnstr_get(x_93, 0);
x_198 = lean::cnstr_get(x_93, 1);
if (lean::is_exclusive(x_93)) {
 x_200 = x_93;
} else {
 lean::inc(x_196);
 lean::inc(x_198);
 lean::dec(x_93);
 x_200 = lean::box(0);
}
if (lean::is_scalar(x_200)) {
 x_201 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_201 = x_200;
}
lean::cnstr_set(x_201, 0, x_196);
lean::cnstr_set(x_201, 1, x_198);
return x_201;
}
}
else
{
obj* x_204; obj* x_206; obj* x_208; obj* x_209; 
lean::dec(x_1);
lean::dec(x_78);
x_204 = lean::cnstr_get(x_88, 0);
x_206 = lean::cnstr_get(x_88, 1);
if (lean::is_exclusive(x_88)) {
 x_208 = x_88;
} else {
 lean::inc(x_204);
 lean::inc(x_206);
 lean::dec(x_88);
 x_208 = lean::box(0);
}
if (lean::is_scalar(x_208)) {
 x_209 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_209 = x_208;
}
lean::cnstr_set(x_209, 0, x_204);
lean::cnstr_set(x_209, 1, x_206);
return x_209;
}
}
else
{
obj* x_211; obj* x_213; obj* x_215; obj* x_216; 
lean::dec(x_1);
x_211 = lean::cnstr_get(x_77, 0);
x_213 = lean::cnstr_get(x_77, 1);
if (lean::is_exclusive(x_77)) {
 x_215 = x_77;
} else {
 lean::inc(x_211);
 lean::inc(x_213);
 lean::dec(x_77);
 x_215 = lean::box(0);
}
if (lean::is_scalar(x_215)) {
 x_216 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_216 = x_215;
}
lean::cnstr_set(x_216, 0, x_211);
lean::cnstr_set(x_216, 1, x_213);
return x_216;
}
}
else
{
obj* x_219; obj* x_221; obj* x_223; obj* x_224; 
lean::dec(x_1);
lean::dec(x_62);
x_219 = lean::cnstr_get(x_72, 0);
x_221 = lean::cnstr_get(x_72, 1);
if (lean::is_exclusive(x_72)) {
 x_223 = x_72;
} else {
 lean::inc(x_219);
 lean::inc(x_221);
 lean::dec(x_72);
 x_223 = lean::box(0);
}
if (lean::is_scalar(x_223)) {
 x_224 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_224 = x_223;
}
lean::cnstr_set(x_224, 0, x_219);
lean::cnstr_set(x_224, 1, x_221);
return x_224;
}
}
else
{
obj* x_226; obj* x_228; obj* x_230; obj* x_231; 
lean::dec(x_1);
x_226 = lean::cnstr_get(x_61, 0);
x_228 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 x_230 = x_61;
} else {
 lean::inc(x_226);
 lean::inc(x_228);
 lean::dec(x_61);
 x_230 = lean::box(0);
}
if (lean::is_scalar(x_230)) {
 x_231 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_231 = x_230;
}
lean::cnstr_set(x_231, 0, x_226);
lean::cnstr_set(x_231, 1, x_228);
return x_231;
}
}
else
{
obj* x_234; obj* x_236; obj* x_238; obj* x_239; 
lean::dec(x_1);
lean::dec(x_50);
x_234 = lean::cnstr_get(x_55, 0);
x_236 = lean::cnstr_get(x_55, 1);
if (lean::is_exclusive(x_55)) {
 x_238 = x_55;
} else {
 lean::inc(x_234);
 lean::inc(x_236);
 lean::dec(x_55);
 x_238 = lean::box(0);
}
if (lean::is_scalar(x_238)) {
 x_239 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_239 = x_238;
}
lean::cnstr_set(x_239, 0, x_234);
lean::cnstr_set(x_239, 1, x_236);
return x_239;
}
}
else
{
obj* x_242; obj* x_244; obj* x_246; obj* x_247; 
lean::dec(x_1);
lean::dec(x_40);
x_242 = lean::cnstr_get(x_45, 0);
x_244 = lean::cnstr_get(x_45, 1);
if (lean::is_exclusive(x_45)) {
 x_246 = x_45;
} else {
 lean::inc(x_242);
 lean::inc(x_244);
 lean::dec(x_45);
 x_246 = lean::box(0);
}
if (lean::is_scalar(x_246)) {
 x_247 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_247 = x_246;
}
lean::cnstr_set(x_247, 0, x_242);
lean::cnstr_set(x_247, 1, x_244);
return x_247;
}
}
else
{
obj* x_250; obj* x_252; obj* x_254; obj* x_255; 
lean::dec(x_1);
lean::dec(x_30);
x_250 = lean::cnstr_get(x_35, 0);
x_252 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 x_254 = x_35;
} else {
 lean::inc(x_250);
 lean::inc(x_252);
 lean::dec(x_35);
 x_254 = lean::box(0);
}
if (lean::is_scalar(x_254)) {
 x_255 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_255 = x_254;
}
lean::cnstr_set(x_255, 0, x_250);
lean::cnstr_set(x_255, 1, x_252);
return x_255;
}
}
else
{
obj* x_258; obj* x_260; obj* x_262; obj* x_263; 
lean::dec(x_1);
lean::dec(x_20);
x_258 = lean::cnstr_get(x_25, 0);
x_260 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_262 = x_25;
} else {
 lean::inc(x_258);
 lean::inc(x_260);
 lean::dec(x_25);
 x_262 = lean::box(0);
}
if (lean::is_scalar(x_262)) {
 x_263 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_263 = x_262;
}
lean::cnstr_set(x_263, 0, x_258);
lean::cnstr_set(x_263, 1, x_260);
return x_263;
}
}
else
{
obj* x_266; obj* x_268; obj* x_270; obj* x_271; 
lean::dec(x_1);
lean::dec(x_0);
x_266 = lean::cnstr_get(x_15, 0);
x_268 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 x_270 = x_15;
} else {
 lean::inc(x_266);
 lean::inc(x_268);
 lean::dec(x_15);
 x_270 = lean::box(0);
}
if (lean::is_scalar(x_270)) {
 x_271 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_271 = x_270;
}
lean::cnstr_set(x_271, 0, x_266);
lean::cnstr_set(x_271, 1, x_268);
return x_271;
}
}
else
{
obj* x_274; obj* x_276; obj* x_278; obj* x_279; 
lean::dec(x_1);
lean::dec(x_0);
x_274 = lean::cnstr_get(x_7, 0);
x_276 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_278 = x_7;
} else {
 lean::inc(x_274);
 lean::inc(x_276);
 lean::dec(x_7);
 x_278 = lean::box(0);
}
if (lean::is_scalar(x_278)) {
 x_279 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_279 = x_278;
}
lean::cnstr_set(x_279, 0, x_274);
lean::cnstr_set(x_279, 1, x_276);
return x_279;
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
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__19 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__19();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__19);
 l___private_init_lean_compiler_ir_default_1__compileAux___closed__20 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__20();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__20);
return w;
}
