// Lean compiler output
// Module: init.lean.compiler.ir.default
// Imports: init.lean.compiler.ir.basic init.lean.compiler.ir.format init.lean.compiler.ir.compilerm init.lean.compiler.ir.pushproj init.lean.compiler.ir.elimdead init.lean.compiler.ir.simpcase init.lean.compiler.ir.resetreuse init.lean.compiler.ir.normids init.lean.compiler.ir.checker init.lean.compiler.ir.borrow init.lean.compiler.ir.boxing init.lean.compiler.ir.rc init.lean.compiler.ir.expandresetreuse init.lean.compiler.ir.emitcpp init.lean.compiler.ir.emitc
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
obj* l_unsafeCast(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
extern obj* l_Array_empty___closed__1;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__5;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__2;
obj* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Decl_pushProj(obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__20;
obj* l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__11;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__14;
extern obj* l_Lean_IR_tracePrefixOptionName;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__23;
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(obj*, obj*);
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
extern "C" uint8 lean_nat_dec_lt(obj*, obj*);
obj* l_Lean_IR_inferBorrow(obj*, obj*, obj*);
obj* l_Lean_IR_Decl_elimDead(obj*);
obj* l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__1;
obj* l_Array_fget(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
extern "C" obj* lean_nat_add(obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux(obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__8;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__7;
obj* l_Lean_IR_Decl_simpCase(obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
obj* l_Lean_IR_Decl_insertResetReuse(obj*);
obj* l_Lean_IR_ExpandResetReuse_main(obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__4;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___boxed(obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__26;
obj* l_Array_size(obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
extern "C" obj* lean_ir_compile(obj*, obj*, obj*);
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(obj*, obj*);
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__17;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
extern obj* l_Lean_mkInitAttr___closed__2;
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
obj* l_Lean_Name_append___main(obj*, obj*);
obj* l_Lean_IR_explicitRC(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
obj* l_Lean_IR_explicitBoxing(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean::box(0);
lean::inc(x_7);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
lean::inc(x_7);
x_11 = l_Lean_IR_Decl_pushProj(x_7);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_10, x_1, x_14);
lean::dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean::box(0);
lean::inc(x_7);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
lean::inc(x_7);
x_11 = l_Lean_IR_Decl_insertResetReuse(x_7);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_10, x_1, x_14);
lean::dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean::box(0);
lean::inc(x_7);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
lean::inc(x_7);
x_11 = l_Lean_IR_Decl_elimDead(x_7);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_10, x_1, x_14);
lean::dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean::box(0);
lean::inc(x_7);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
lean::inc(x_7);
x_11 = l_Lean_IR_Decl_simpCase(x_7);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_10, x_1, x_14);
lean::dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
obj* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean::box(0);
lean::inc(x_7);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
lean::inc(x_7);
x_11 = l_Lean_IR_ExpandResetReuse_main(x_7);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_10, x_1, x_14);
lean::dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l_Lean_mkInitAttr___closed__2;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("push_proj");
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("reset_reuse");
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__8() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("elim_dead");
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__9() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__10() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__11() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("simp_case");
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__12() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__13() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__14() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("borrow");
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__15() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__16() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__17() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("boxing");
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__18() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__19() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__20() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("rc");
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__21() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__20;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__22() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__23() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("expand_reset_reuse");
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__24() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__23;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__25() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__26() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("result");
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__28() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_default_1__compileAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__1;
x_5 = l_Lean_mkInitAttr___closed__2;
lean::inc(x_1);
x_6 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_4, x_5, x_1, x_2, x_3);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_6, 0);
lean::dec(x_8);
x_9 = lean::box(0);
lean::cnstr_set(x_6, 0, x_9);
x_10 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_11 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1, x_1, x_10, x_2, x_6);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_11, 0);
lean::dec(x_13);
lean::cnstr_set(x_11, 0, x_9);
x_14 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_1);
x_15 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__4;
x_16 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
lean::inc(x_14);
x_17 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_14, x_2, x_11);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_17, 0);
lean::dec(x_19);
lean::cnstr_set(x_17, 0, x_9);
x_20 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(x_10, x_14);
x_21 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__7;
x_22 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
lean::inc(x_20);
x_23 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_21, x_22, x_20, x_2, x_17);
if (lean::obj_tag(x_23) == 0)
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_25 = lean::cnstr_get(x_23, 0);
lean::dec(x_25);
lean::cnstr_set(x_23, 0, x_9);
x_26 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(x_10, x_20);
x_27 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
x_28 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
lean::inc(x_26);
x_29 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_27, x_28, x_26, x_2, x_23);
if (lean::obj_tag(x_29) == 0)
{
uint8 x_30; 
x_30 = !lean::is_exclusive(x_29);
if (x_30 == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_29, 0);
lean::dec(x_31);
lean::cnstr_set(x_29, 0, x_9);
x_32 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(x_10, x_26);
x_33 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
x_34 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean::inc(x_32);
x_35 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_33, x_34, x_32, x_2, x_29);
if (lean::obj_tag(x_35) == 0)
{
uint8 x_36; 
x_36 = !lean::is_exclusive(x_35);
if (x_36 == 0)
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_35, 0);
lean::dec(x_37);
lean::cnstr_set(x_35, 0, x_9);
x_38 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_32);
x_39 = l_Lean_IR_inferBorrow(x_38, x_2, x_35);
if (lean::obj_tag(x_39) == 0)
{
uint8 x_40; 
x_40 = !lean::is_exclusive(x_39);
if (x_40 == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_41 = lean::cnstr_get(x_39, 0);
lean::cnstr_set(x_39, 0, x_9);
x_42 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_43 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean::inc(x_41);
x_44 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_42, x_43, x_41, x_2, x_39);
if (lean::obj_tag(x_44) == 0)
{
uint8 x_45; 
x_45 = !lean::is_exclusive(x_44);
if (x_45 == 0)
{
obj* x_46; obj* x_47; 
x_46 = lean::cnstr_get(x_44, 0);
lean::dec(x_46);
lean::cnstr_set(x_44, 0, x_9);
x_47 = l_Lean_IR_explicitBoxing(x_41, x_2, x_44);
if (lean::obj_tag(x_47) == 0)
{
uint8 x_48; 
x_48 = !lean::is_exclusive(x_47);
if (x_48 == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_49 = lean::cnstr_get(x_47, 0);
lean::cnstr_set(x_47, 0, x_9);
x_50 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_51 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean::inc(x_49);
x_52 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_50, x_51, x_49, x_2, x_47);
if (lean::obj_tag(x_52) == 0)
{
uint8 x_53; 
x_53 = !lean::is_exclusive(x_52);
if (x_53 == 0)
{
obj* x_54; obj* x_55; 
x_54 = lean::cnstr_get(x_52, 0);
lean::dec(x_54);
lean::cnstr_set(x_52, 0, x_9);
x_55 = l_Lean_IR_explicitRC(x_49, x_2, x_52);
if (lean::obj_tag(x_55) == 0)
{
uint8 x_56; 
x_56 = !lean::is_exclusive(x_55);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_57 = lean::cnstr_get(x_55, 0);
lean::cnstr_set(x_55, 0, x_9);
x_58 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_59 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean::inc(x_57);
x_60 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_58, x_59, x_57, x_2, x_55);
if (lean::obj_tag(x_60) == 0)
{
uint8 x_61; 
x_61 = !lean::is_exclusive(x_60);
if (x_61 == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_62 = lean::cnstr_get(x_60, 0);
lean::dec(x_62);
lean::cnstr_set(x_60, 0, x_9);
x_63 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_57);
x_64 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_65 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean::inc(x_63);
x_66 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_64, x_65, x_63, x_2, x_60);
if (lean::obj_tag(x_66) == 0)
{
uint8 x_67; 
x_67 = !lean::is_exclusive(x_66);
if (x_67 == 0)
{
obj* x_68; obj* x_69; obj* x_70; 
x_68 = lean::cnstr_get(x_66, 0);
lean::dec(x_68);
lean::cnstr_set(x_66, 0, x_9);
x_69 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_63);
lean::inc(x_69);
x_70 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_69, x_2, x_66);
if (lean::obj_tag(x_70) == 0)
{
uint8 x_71; 
x_71 = !lean::is_exclusive(x_70);
if (x_71 == 0)
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_72 = lean::cnstr_get(x_70, 0);
lean::dec(x_72);
lean::cnstr_set(x_70, 0, x_9);
x_73 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_74 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_69);
x_75 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_73, x_74, x_69, x_2, x_70);
if (lean::obj_tag(x_75) == 0)
{
uint8 x_76; 
x_76 = !lean::is_exclusive(x_75);
if (x_76 == 0)
{
obj* x_77; obj* x_78; 
x_77 = lean::cnstr_get(x_75, 0);
lean::dec(x_77);
lean::cnstr_set(x_75, 0, x_9);
lean::inc(x_69);
x_78 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_69, x_69, x_10, x_2, x_75);
if (lean::obj_tag(x_78) == 0)
{
uint8 x_79; 
x_79 = !lean::is_exclusive(x_78);
if (x_79 == 0)
{
obj* x_80; obj* x_81; 
x_80 = lean::cnstr_get(x_78, 0);
lean::dec(x_80);
lean::cnstr_set(x_78, 0, x_9);
x_81 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_69, x_10, x_2, x_78);
lean::dec(x_69);
if (lean::obj_tag(x_81) == 0)
{
uint8 x_82; 
x_82 = !lean::is_exclusive(x_81);
if (x_82 == 0)
{
obj* x_83; 
x_83 = lean::cnstr_get(x_81, 0);
lean::dec(x_83);
lean::cnstr_set(x_81, 0, x_9);
return x_81;
}
else
{
obj* x_84; obj* x_85; 
x_84 = lean::cnstr_get(x_81, 1);
lean::inc(x_84);
lean::dec(x_81);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_9);
lean::cnstr_set(x_85, 1, x_84);
return x_85;
}
}
else
{
uint8 x_86; 
x_86 = !lean::is_exclusive(x_81);
if (x_86 == 0)
{
return x_81;
}
else
{
obj* x_87; obj* x_88; obj* x_89; 
x_87 = lean::cnstr_get(x_81, 0);
x_88 = lean::cnstr_get(x_81, 1);
lean::inc(x_88);
lean::inc(x_87);
lean::dec(x_81);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_87);
lean::cnstr_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
obj* x_90; obj* x_91; obj* x_92; 
x_90 = lean::cnstr_get(x_78, 1);
lean::inc(x_90);
lean::dec(x_78);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_9);
lean::cnstr_set(x_91, 1, x_90);
x_92 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_69, x_10, x_2, x_91);
lean::dec(x_69);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; obj* x_94; obj* x_95; 
x_93 = lean::cnstr_get(x_92, 1);
lean::inc(x_93);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_94 = x_92;
} else {
 lean::dec_ref(x_92);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_9);
lean::cnstr_set(x_95, 1, x_93);
return x_95;
}
else
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_96 = lean::cnstr_get(x_92, 0);
lean::inc(x_96);
x_97 = lean::cnstr_get(x_92, 1);
lean::inc(x_97);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_98 = x_92;
} else {
 lean::dec_ref(x_92);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
lean::cnstr_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
uint8 x_100; 
lean::dec(x_69);
x_100 = !lean::is_exclusive(x_78);
if (x_100 == 0)
{
return x_78;
}
else
{
obj* x_101; obj* x_102; obj* x_103; 
x_101 = lean::cnstr_get(x_78, 0);
x_102 = lean::cnstr_get(x_78, 1);
lean::inc(x_102);
lean::inc(x_101);
lean::dec(x_78);
x_103 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_103, 0, x_101);
lean::cnstr_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
obj* x_104; obj* x_105; obj* x_106; 
x_104 = lean::cnstr_get(x_75, 1);
lean::inc(x_104);
lean::dec(x_75);
x_105 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_105, 0, x_9);
lean::cnstr_set(x_105, 1, x_104);
lean::inc(x_69);
x_106 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_69, x_69, x_10, x_2, x_105);
if (lean::obj_tag(x_106) == 0)
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_107 = lean::cnstr_get(x_106, 1);
lean::inc(x_107);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 lean::cnstr_release(x_106, 1);
 x_108 = x_106;
} else {
 lean::dec_ref(x_106);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_9);
lean::cnstr_set(x_109, 1, x_107);
x_110 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_69, x_10, x_2, x_109);
lean::dec(x_69);
if (lean::obj_tag(x_110) == 0)
{
obj* x_111; obj* x_112; obj* x_113; 
x_111 = lean::cnstr_get(x_110, 1);
lean::inc(x_111);
if (lean::is_exclusive(x_110)) {
 lean::cnstr_release(x_110, 0);
 lean::cnstr_release(x_110, 1);
 x_112 = x_110;
} else {
 lean::dec_ref(x_110);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_9);
lean::cnstr_set(x_113, 1, x_111);
return x_113;
}
else
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_114 = lean::cnstr_get(x_110, 0);
lean::inc(x_114);
x_115 = lean::cnstr_get(x_110, 1);
lean::inc(x_115);
if (lean::is_exclusive(x_110)) {
 lean::cnstr_release(x_110, 0);
 lean::cnstr_release(x_110, 1);
 x_116 = x_110;
} else {
 lean::dec_ref(x_110);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_114);
lean::cnstr_set(x_117, 1, x_115);
return x_117;
}
}
else
{
obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
lean::dec(x_69);
x_118 = lean::cnstr_get(x_106, 0);
lean::inc(x_118);
x_119 = lean::cnstr_get(x_106, 1);
lean::inc(x_119);
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 lean::cnstr_release(x_106, 1);
 x_120 = x_106;
} else {
 lean::dec_ref(x_106);
 x_120 = lean::box(0);
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_118);
lean::cnstr_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
uint8 x_122; 
lean::dec(x_69);
x_122 = !lean::is_exclusive(x_75);
if (x_122 == 0)
{
return x_75;
}
else
{
obj* x_123; obj* x_124; obj* x_125; 
x_123 = lean::cnstr_get(x_75, 0);
x_124 = lean::cnstr_get(x_75, 1);
lean::inc(x_124);
lean::inc(x_123);
lean::dec(x_75);
x_125 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_125, 0, x_123);
lean::cnstr_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
x_126 = lean::cnstr_get(x_70, 1);
lean::inc(x_126);
lean::dec(x_70);
x_127 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_127, 0, x_9);
lean::cnstr_set(x_127, 1, x_126);
x_128 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_129 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_69);
x_130 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_128, x_129, x_69, x_2, x_127);
if (lean::obj_tag(x_130) == 0)
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_131 = lean::cnstr_get(x_130, 1);
lean::inc(x_131);
if (lean::is_exclusive(x_130)) {
 lean::cnstr_release(x_130, 0);
 lean::cnstr_release(x_130, 1);
 x_132 = x_130;
} else {
 lean::dec_ref(x_130);
 x_132 = lean::box(0);
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_133 = x_132;
}
lean::cnstr_set(x_133, 0, x_9);
lean::cnstr_set(x_133, 1, x_131);
lean::inc(x_69);
x_134 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_69, x_69, x_10, x_2, x_133);
if (lean::obj_tag(x_134) == 0)
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
x_135 = lean::cnstr_get(x_134, 1);
lean::inc(x_135);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 lean::cnstr_release(x_134, 1);
 x_136 = x_134;
} else {
 lean::dec_ref(x_134);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_9);
lean::cnstr_set(x_137, 1, x_135);
x_138 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_69, x_10, x_2, x_137);
lean::dec(x_69);
if (lean::obj_tag(x_138) == 0)
{
obj* x_139; obj* x_140; obj* x_141; 
x_139 = lean::cnstr_get(x_138, 1);
lean::inc(x_139);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_release(x_138, 1);
 x_140 = x_138;
} else {
 lean::dec_ref(x_138);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_9);
lean::cnstr_set(x_141, 1, x_139);
return x_141;
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_142 = lean::cnstr_get(x_138, 0);
lean::inc(x_142);
x_143 = lean::cnstr_get(x_138, 1);
lean::inc(x_143);
if (lean::is_exclusive(x_138)) {
 lean::cnstr_release(x_138, 0);
 lean::cnstr_release(x_138, 1);
 x_144 = x_138;
} else {
 lean::dec_ref(x_138);
 x_144 = lean::box(0);
}
if (lean::is_scalar(x_144)) {
 x_145 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_145 = x_144;
}
lean::cnstr_set(x_145, 0, x_142);
lean::cnstr_set(x_145, 1, x_143);
return x_145;
}
}
else
{
obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
lean::dec(x_69);
x_146 = lean::cnstr_get(x_134, 0);
lean::inc(x_146);
x_147 = lean::cnstr_get(x_134, 1);
lean::inc(x_147);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 lean::cnstr_release(x_134, 1);
 x_148 = x_134;
} else {
 lean::dec_ref(x_134);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_146);
lean::cnstr_set(x_149, 1, x_147);
return x_149;
}
}
else
{
obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
lean::dec(x_69);
x_150 = lean::cnstr_get(x_130, 0);
lean::inc(x_150);
x_151 = lean::cnstr_get(x_130, 1);
lean::inc(x_151);
if (lean::is_exclusive(x_130)) {
 lean::cnstr_release(x_130, 0);
 lean::cnstr_release(x_130, 1);
 x_152 = x_130;
} else {
 lean::dec_ref(x_130);
 x_152 = lean::box(0);
}
if (lean::is_scalar(x_152)) {
 x_153 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_153 = x_152;
}
lean::cnstr_set(x_153, 0, x_150);
lean::cnstr_set(x_153, 1, x_151);
return x_153;
}
}
}
else
{
uint8 x_154; 
lean::dec(x_69);
x_154 = !lean::is_exclusive(x_70);
if (x_154 == 0)
{
return x_70;
}
else
{
obj* x_155; obj* x_156; obj* x_157; 
x_155 = lean::cnstr_get(x_70, 0);
x_156 = lean::cnstr_get(x_70, 1);
lean::inc(x_156);
lean::inc(x_155);
lean::dec(x_70);
x_157 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_157, 0, x_155);
lean::cnstr_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
x_158 = lean::cnstr_get(x_66, 1);
lean::inc(x_158);
lean::dec(x_66);
x_159 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_159, 0, x_9);
lean::cnstr_set(x_159, 1, x_158);
x_160 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_63);
lean::inc(x_160);
x_161 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_160, x_2, x_159);
if (lean::obj_tag(x_161) == 0)
{
obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
x_162 = lean::cnstr_get(x_161, 1);
lean::inc(x_162);
if (lean::is_exclusive(x_161)) {
 lean::cnstr_release(x_161, 0);
 lean::cnstr_release(x_161, 1);
 x_163 = x_161;
} else {
 lean::dec_ref(x_161);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_9);
lean::cnstr_set(x_164, 1, x_162);
x_165 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_166 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_160);
x_167 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_165, x_166, x_160, x_2, x_164);
if (lean::obj_tag(x_167) == 0)
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
x_168 = lean::cnstr_get(x_167, 1);
lean::inc(x_168);
if (lean::is_exclusive(x_167)) {
 lean::cnstr_release(x_167, 0);
 lean::cnstr_release(x_167, 1);
 x_169 = x_167;
} else {
 lean::dec_ref(x_167);
 x_169 = lean::box(0);
}
if (lean::is_scalar(x_169)) {
 x_170 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_170 = x_169;
}
lean::cnstr_set(x_170, 0, x_9);
lean::cnstr_set(x_170, 1, x_168);
lean::inc(x_160);
x_171 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_160, x_160, x_10, x_2, x_170);
if (lean::obj_tag(x_171) == 0)
{
obj* x_172; obj* x_173; obj* x_174; obj* x_175; 
x_172 = lean::cnstr_get(x_171, 1);
lean::inc(x_172);
if (lean::is_exclusive(x_171)) {
 lean::cnstr_release(x_171, 0);
 lean::cnstr_release(x_171, 1);
 x_173 = x_171;
} else {
 lean::dec_ref(x_171);
 x_173 = lean::box(0);
}
if (lean::is_scalar(x_173)) {
 x_174 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_174 = x_173;
}
lean::cnstr_set(x_174, 0, x_9);
lean::cnstr_set(x_174, 1, x_172);
x_175 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_160, x_10, x_2, x_174);
lean::dec(x_160);
if (lean::obj_tag(x_175) == 0)
{
obj* x_176; obj* x_177; obj* x_178; 
x_176 = lean::cnstr_get(x_175, 1);
lean::inc(x_176);
if (lean::is_exclusive(x_175)) {
 lean::cnstr_release(x_175, 0);
 lean::cnstr_release(x_175, 1);
 x_177 = x_175;
} else {
 lean::dec_ref(x_175);
 x_177 = lean::box(0);
}
if (lean::is_scalar(x_177)) {
 x_178 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_178 = x_177;
}
lean::cnstr_set(x_178, 0, x_9);
lean::cnstr_set(x_178, 1, x_176);
return x_178;
}
else
{
obj* x_179; obj* x_180; obj* x_181; obj* x_182; 
x_179 = lean::cnstr_get(x_175, 0);
lean::inc(x_179);
x_180 = lean::cnstr_get(x_175, 1);
lean::inc(x_180);
if (lean::is_exclusive(x_175)) {
 lean::cnstr_release(x_175, 0);
 lean::cnstr_release(x_175, 1);
 x_181 = x_175;
} else {
 lean::dec_ref(x_175);
 x_181 = lean::box(0);
}
if (lean::is_scalar(x_181)) {
 x_182 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_182 = x_181;
}
lean::cnstr_set(x_182, 0, x_179);
lean::cnstr_set(x_182, 1, x_180);
return x_182;
}
}
else
{
obj* x_183; obj* x_184; obj* x_185; obj* x_186; 
lean::dec(x_160);
x_183 = lean::cnstr_get(x_171, 0);
lean::inc(x_183);
x_184 = lean::cnstr_get(x_171, 1);
lean::inc(x_184);
if (lean::is_exclusive(x_171)) {
 lean::cnstr_release(x_171, 0);
 lean::cnstr_release(x_171, 1);
 x_185 = x_171;
} else {
 lean::dec_ref(x_171);
 x_185 = lean::box(0);
}
if (lean::is_scalar(x_185)) {
 x_186 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_186 = x_185;
}
lean::cnstr_set(x_186, 0, x_183);
lean::cnstr_set(x_186, 1, x_184);
return x_186;
}
}
else
{
obj* x_187; obj* x_188; obj* x_189; obj* x_190; 
lean::dec(x_160);
x_187 = lean::cnstr_get(x_167, 0);
lean::inc(x_187);
x_188 = lean::cnstr_get(x_167, 1);
lean::inc(x_188);
if (lean::is_exclusive(x_167)) {
 lean::cnstr_release(x_167, 0);
 lean::cnstr_release(x_167, 1);
 x_189 = x_167;
} else {
 lean::dec_ref(x_167);
 x_189 = lean::box(0);
}
if (lean::is_scalar(x_189)) {
 x_190 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_190 = x_189;
}
lean::cnstr_set(x_190, 0, x_187);
lean::cnstr_set(x_190, 1, x_188);
return x_190;
}
}
else
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; 
lean::dec(x_160);
x_191 = lean::cnstr_get(x_161, 0);
lean::inc(x_191);
x_192 = lean::cnstr_get(x_161, 1);
lean::inc(x_192);
if (lean::is_exclusive(x_161)) {
 lean::cnstr_release(x_161, 0);
 lean::cnstr_release(x_161, 1);
 x_193 = x_161;
} else {
 lean::dec_ref(x_161);
 x_193 = lean::box(0);
}
if (lean::is_scalar(x_193)) {
 x_194 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_194 = x_193;
}
lean::cnstr_set(x_194, 0, x_191);
lean::cnstr_set(x_194, 1, x_192);
return x_194;
}
}
}
else
{
uint8 x_195; 
lean::dec(x_63);
x_195 = !lean::is_exclusive(x_66);
if (x_195 == 0)
{
return x_66;
}
else
{
obj* x_196; obj* x_197; obj* x_198; 
x_196 = lean::cnstr_get(x_66, 0);
x_197 = lean::cnstr_get(x_66, 1);
lean::inc(x_197);
lean::inc(x_196);
lean::dec(x_66);
x_198 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_198, 0, x_196);
lean::cnstr_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; 
x_199 = lean::cnstr_get(x_60, 1);
lean::inc(x_199);
lean::dec(x_60);
x_200 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_200, 0, x_9);
lean::cnstr_set(x_200, 1, x_199);
x_201 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_57);
x_202 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_203 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean::inc(x_201);
x_204 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_202, x_203, x_201, x_2, x_200);
if (lean::obj_tag(x_204) == 0)
{
obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; 
x_205 = lean::cnstr_get(x_204, 1);
lean::inc(x_205);
if (lean::is_exclusive(x_204)) {
 lean::cnstr_release(x_204, 0);
 lean::cnstr_release(x_204, 1);
 x_206 = x_204;
} else {
 lean::dec_ref(x_204);
 x_206 = lean::box(0);
}
if (lean::is_scalar(x_206)) {
 x_207 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_207 = x_206;
}
lean::cnstr_set(x_207, 0, x_9);
lean::cnstr_set(x_207, 1, x_205);
x_208 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_201);
lean::inc(x_208);
x_209 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_208, x_2, x_207);
if (lean::obj_tag(x_209) == 0)
{
obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; 
x_210 = lean::cnstr_get(x_209, 1);
lean::inc(x_210);
if (lean::is_exclusive(x_209)) {
 lean::cnstr_release(x_209, 0);
 lean::cnstr_release(x_209, 1);
 x_211 = x_209;
} else {
 lean::dec_ref(x_209);
 x_211 = lean::box(0);
}
if (lean::is_scalar(x_211)) {
 x_212 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_212 = x_211;
}
lean::cnstr_set(x_212, 0, x_9);
lean::cnstr_set(x_212, 1, x_210);
x_213 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_214 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_208);
x_215 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_213, x_214, x_208, x_2, x_212);
if (lean::obj_tag(x_215) == 0)
{
obj* x_216; obj* x_217; obj* x_218; obj* x_219; 
x_216 = lean::cnstr_get(x_215, 1);
lean::inc(x_216);
if (lean::is_exclusive(x_215)) {
 lean::cnstr_release(x_215, 0);
 lean::cnstr_release(x_215, 1);
 x_217 = x_215;
} else {
 lean::dec_ref(x_215);
 x_217 = lean::box(0);
}
if (lean::is_scalar(x_217)) {
 x_218 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_218 = x_217;
}
lean::cnstr_set(x_218, 0, x_9);
lean::cnstr_set(x_218, 1, x_216);
lean::inc(x_208);
x_219 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_208, x_208, x_10, x_2, x_218);
if (lean::obj_tag(x_219) == 0)
{
obj* x_220; obj* x_221; obj* x_222; obj* x_223; 
x_220 = lean::cnstr_get(x_219, 1);
lean::inc(x_220);
if (lean::is_exclusive(x_219)) {
 lean::cnstr_release(x_219, 0);
 lean::cnstr_release(x_219, 1);
 x_221 = x_219;
} else {
 lean::dec_ref(x_219);
 x_221 = lean::box(0);
}
if (lean::is_scalar(x_221)) {
 x_222 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_222 = x_221;
}
lean::cnstr_set(x_222, 0, x_9);
lean::cnstr_set(x_222, 1, x_220);
x_223 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_208, x_10, x_2, x_222);
lean::dec(x_208);
if (lean::obj_tag(x_223) == 0)
{
obj* x_224; obj* x_225; obj* x_226; 
x_224 = lean::cnstr_get(x_223, 1);
lean::inc(x_224);
if (lean::is_exclusive(x_223)) {
 lean::cnstr_release(x_223, 0);
 lean::cnstr_release(x_223, 1);
 x_225 = x_223;
} else {
 lean::dec_ref(x_223);
 x_225 = lean::box(0);
}
if (lean::is_scalar(x_225)) {
 x_226 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_226 = x_225;
}
lean::cnstr_set(x_226, 0, x_9);
lean::cnstr_set(x_226, 1, x_224);
return x_226;
}
else
{
obj* x_227; obj* x_228; obj* x_229; obj* x_230; 
x_227 = lean::cnstr_get(x_223, 0);
lean::inc(x_227);
x_228 = lean::cnstr_get(x_223, 1);
lean::inc(x_228);
if (lean::is_exclusive(x_223)) {
 lean::cnstr_release(x_223, 0);
 lean::cnstr_release(x_223, 1);
 x_229 = x_223;
} else {
 lean::dec_ref(x_223);
 x_229 = lean::box(0);
}
if (lean::is_scalar(x_229)) {
 x_230 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_230 = x_229;
}
lean::cnstr_set(x_230, 0, x_227);
lean::cnstr_set(x_230, 1, x_228);
return x_230;
}
}
else
{
obj* x_231; obj* x_232; obj* x_233; obj* x_234; 
lean::dec(x_208);
x_231 = lean::cnstr_get(x_219, 0);
lean::inc(x_231);
x_232 = lean::cnstr_get(x_219, 1);
lean::inc(x_232);
if (lean::is_exclusive(x_219)) {
 lean::cnstr_release(x_219, 0);
 lean::cnstr_release(x_219, 1);
 x_233 = x_219;
} else {
 lean::dec_ref(x_219);
 x_233 = lean::box(0);
}
if (lean::is_scalar(x_233)) {
 x_234 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_234 = x_233;
}
lean::cnstr_set(x_234, 0, x_231);
lean::cnstr_set(x_234, 1, x_232);
return x_234;
}
}
else
{
obj* x_235; obj* x_236; obj* x_237; obj* x_238; 
lean::dec(x_208);
x_235 = lean::cnstr_get(x_215, 0);
lean::inc(x_235);
x_236 = lean::cnstr_get(x_215, 1);
lean::inc(x_236);
if (lean::is_exclusive(x_215)) {
 lean::cnstr_release(x_215, 0);
 lean::cnstr_release(x_215, 1);
 x_237 = x_215;
} else {
 lean::dec_ref(x_215);
 x_237 = lean::box(0);
}
if (lean::is_scalar(x_237)) {
 x_238 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_238 = x_237;
}
lean::cnstr_set(x_238, 0, x_235);
lean::cnstr_set(x_238, 1, x_236);
return x_238;
}
}
else
{
obj* x_239; obj* x_240; obj* x_241; obj* x_242; 
lean::dec(x_208);
x_239 = lean::cnstr_get(x_209, 0);
lean::inc(x_239);
x_240 = lean::cnstr_get(x_209, 1);
lean::inc(x_240);
if (lean::is_exclusive(x_209)) {
 lean::cnstr_release(x_209, 0);
 lean::cnstr_release(x_209, 1);
 x_241 = x_209;
} else {
 lean::dec_ref(x_209);
 x_241 = lean::box(0);
}
if (lean::is_scalar(x_241)) {
 x_242 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_242 = x_241;
}
lean::cnstr_set(x_242, 0, x_239);
lean::cnstr_set(x_242, 1, x_240);
return x_242;
}
}
else
{
obj* x_243; obj* x_244; obj* x_245; obj* x_246; 
lean::dec(x_201);
x_243 = lean::cnstr_get(x_204, 0);
lean::inc(x_243);
x_244 = lean::cnstr_get(x_204, 1);
lean::inc(x_244);
if (lean::is_exclusive(x_204)) {
 lean::cnstr_release(x_204, 0);
 lean::cnstr_release(x_204, 1);
 x_245 = x_204;
} else {
 lean::dec_ref(x_204);
 x_245 = lean::box(0);
}
if (lean::is_scalar(x_245)) {
 x_246 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_246 = x_245;
}
lean::cnstr_set(x_246, 0, x_243);
lean::cnstr_set(x_246, 1, x_244);
return x_246;
}
}
}
else
{
uint8 x_247; 
lean::dec(x_57);
x_247 = !lean::is_exclusive(x_60);
if (x_247 == 0)
{
return x_60;
}
else
{
obj* x_248; obj* x_249; obj* x_250; 
x_248 = lean::cnstr_get(x_60, 0);
x_249 = lean::cnstr_get(x_60, 1);
lean::inc(x_249);
lean::inc(x_248);
lean::dec(x_60);
x_250 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_250, 0, x_248);
lean::cnstr_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; 
x_251 = lean::cnstr_get(x_55, 0);
x_252 = lean::cnstr_get(x_55, 1);
lean::inc(x_252);
lean::inc(x_251);
lean::dec(x_55);
x_253 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_253, 0, x_9);
lean::cnstr_set(x_253, 1, x_252);
x_254 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_255 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean::inc(x_251);
x_256 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_254, x_255, x_251, x_2, x_253);
if (lean::obj_tag(x_256) == 0)
{
obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; 
x_257 = lean::cnstr_get(x_256, 1);
lean::inc(x_257);
if (lean::is_exclusive(x_256)) {
 lean::cnstr_release(x_256, 0);
 lean::cnstr_release(x_256, 1);
 x_258 = x_256;
} else {
 lean::dec_ref(x_256);
 x_258 = lean::box(0);
}
if (lean::is_scalar(x_258)) {
 x_259 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_259 = x_258;
}
lean::cnstr_set(x_259, 0, x_9);
lean::cnstr_set(x_259, 1, x_257);
x_260 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_251);
x_261 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_262 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean::inc(x_260);
x_263 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_261, x_262, x_260, x_2, x_259);
if (lean::obj_tag(x_263) == 0)
{
obj* x_264; obj* x_265; obj* x_266; obj* x_267; obj* x_268; 
x_264 = lean::cnstr_get(x_263, 1);
lean::inc(x_264);
if (lean::is_exclusive(x_263)) {
 lean::cnstr_release(x_263, 0);
 lean::cnstr_release(x_263, 1);
 x_265 = x_263;
} else {
 lean::dec_ref(x_263);
 x_265 = lean::box(0);
}
if (lean::is_scalar(x_265)) {
 x_266 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_266 = x_265;
}
lean::cnstr_set(x_266, 0, x_9);
lean::cnstr_set(x_266, 1, x_264);
x_267 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_260);
lean::inc(x_267);
x_268 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_267, x_2, x_266);
if (lean::obj_tag(x_268) == 0)
{
obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_269 = lean::cnstr_get(x_268, 1);
lean::inc(x_269);
if (lean::is_exclusive(x_268)) {
 lean::cnstr_release(x_268, 0);
 lean::cnstr_release(x_268, 1);
 x_270 = x_268;
} else {
 lean::dec_ref(x_268);
 x_270 = lean::box(0);
}
if (lean::is_scalar(x_270)) {
 x_271 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_271 = x_270;
}
lean::cnstr_set(x_271, 0, x_9);
lean::cnstr_set(x_271, 1, x_269);
x_272 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_273 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_267);
x_274 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_272, x_273, x_267, x_2, x_271);
if (lean::obj_tag(x_274) == 0)
{
obj* x_275; obj* x_276; obj* x_277; obj* x_278; 
x_275 = lean::cnstr_get(x_274, 1);
lean::inc(x_275);
if (lean::is_exclusive(x_274)) {
 lean::cnstr_release(x_274, 0);
 lean::cnstr_release(x_274, 1);
 x_276 = x_274;
} else {
 lean::dec_ref(x_274);
 x_276 = lean::box(0);
}
if (lean::is_scalar(x_276)) {
 x_277 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_277 = x_276;
}
lean::cnstr_set(x_277, 0, x_9);
lean::cnstr_set(x_277, 1, x_275);
lean::inc(x_267);
x_278 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_267, x_267, x_10, x_2, x_277);
if (lean::obj_tag(x_278) == 0)
{
obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_279 = lean::cnstr_get(x_278, 1);
lean::inc(x_279);
if (lean::is_exclusive(x_278)) {
 lean::cnstr_release(x_278, 0);
 lean::cnstr_release(x_278, 1);
 x_280 = x_278;
} else {
 lean::dec_ref(x_278);
 x_280 = lean::box(0);
}
if (lean::is_scalar(x_280)) {
 x_281 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_281 = x_280;
}
lean::cnstr_set(x_281, 0, x_9);
lean::cnstr_set(x_281, 1, x_279);
x_282 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_267, x_10, x_2, x_281);
lean::dec(x_267);
if (lean::obj_tag(x_282) == 0)
{
obj* x_283; obj* x_284; obj* x_285; 
x_283 = lean::cnstr_get(x_282, 1);
lean::inc(x_283);
if (lean::is_exclusive(x_282)) {
 lean::cnstr_release(x_282, 0);
 lean::cnstr_release(x_282, 1);
 x_284 = x_282;
} else {
 lean::dec_ref(x_282);
 x_284 = lean::box(0);
}
if (lean::is_scalar(x_284)) {
 x_285 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_285 = x_284;
}
lean::cnstr_set(x_285, 0, x_9);
lean::cnstr_set(x_285, 1, x_283);
return x_285;
}
else
{
obj* x_286; obj* x_287; obj* x_288; obj* x_289; 
x_286 = lean::cnstr_get(x_282, 0);
lean::inc(x_286);
x_287 = lean::cnstr_get(x_282, 1);
lean::inc(x_287);
if (lean::is_exclusive(x_282)) {
 lean::cnstr_release(x_282, 0);
 lean::cnstr_release(x_282, 1);
 x_288 = x_282;
} else {
 lean::dec_ref(x_282);
 x_288 = lean::box(0);
}
if (lean::is_scalar(x_288)) {
 x_289 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_289 = x_288;
}
lean::cnstr_set(x_289, 0, x_286);
lean::cnstr_set(x_289, 1, x_287);
return x_289;
}
}
else
{
obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
lean::dec(x_267);
x_290 = lean::cnstr_get(x_278, 0);
lean::inc(x_290);
x_291 = lean::cnstr_get(x_278, 1);
lean::inc(x_291);
if (lean::is_exclusive(x_278)) {
 lean::cnstr_release(x_278, 0);
 lean::cnstr_release(x_278, 1);
 x_292 = x_278;
} else {
 lean::dec_ref(x_278);
 x_292 = lean::box(0);
}
if (lean::is_scalar(x_292)) {
 x_293 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_293 = x_292;
}
lean::cnstr_set(x_293, 0, x_290);
lean::cnstr_set(x_293, 1, x_291);
return x_293;
}
}
else
{
obj* x_294; obj* x_295; obj* x_296; obj* x_297; 
lean::dec(x_267);
x_294 = lean::cnstr_get(x_274, 0);
lean::inc(x_294);
x_295 = lean::cnstr_get(x_274, 1);
lean::inc(x_295);
if (lean::is_exclusive(x_274)) {
 lean::cnstr_release(x_274, 0);
 lean::cnstr_release(x_274, 1);
 x_296 = x_274;
} else {
 lean::dec_ref(x_274);
 x_296 = lean::box(0);
}
if (lean::is_scalar(x_296)) {
 x_297 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_297 = x_296;
}
lean::cnstr_set(x_297, 0, x_294);
lean::cnstr_set(x_297, 1, x_295);
return x_297;
}
}
else
{
obj* x_298; obj* x_299; obj* x_300; obj* x_301; 
lean::dec(x_267);
x_298 = lean::cnstr_get(x_268, 0);
lean::inc(x_298);
x_299 = lean::cnstr_get(x_268, 1);
lean::inc(x_299);
if (lean::is_exclusive(x_268)) {
 lean::cnstr_release(x_268, 0);
 lean::cnstr_release(x_268, 1);
 x_300 = x_268;
} else {
 lean::dec_ref(x_268);
 x_300 = lean::box(0);
}
if (lean::is_scalar(x_300)) {
 x_301 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_301 = x_300;
}
lean::cnstr_set(x_301, 0, x_298);
lean::cnstr_set(x_301, 1, x_299);
return x_301;
}
}
else
{
obj* x_302; obj* x_303; obj* x_304; obj* x_305; 
lean::dec(x_260);
x_302 = lean::cnstr_get(x_263, 0);
lean::inc(x_302);
x_303 = lean::cnstr_get(x_263, 1);
lean::inc(x_303);
if (lean::is_exclusive(x_263)) {
 lean::cnstr_release(x_263, 0);
 lean::cnstr_release(x_263, 1);
 x_304 = x_263;
} else {
 lean::dec_ref(x_263);
 x_304 = lean::box(0);
}
if (lean::is_scalar(x_304)) {
 x_305 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_305 = x_304;
}
lean::cnstr_set(x_305, 0, x_302);
lean::cnstr_set(x_305, 1, x_303);
return x_305;
}
}
else
{
obj* x_306; obj* x_307; obj* x_308; obj* x_309; 
lean::dec(x_251);
x_306 = lean::cnstr_get(x_256, 0);
lean::inc(x_306);
x_307 = lean::cnstr_get(x_256, 1);
lean::inc(x_307);
if (lean::is_exclusive(x_256)) {
 lean::cnstr_release(x_256, 0);
 lean::cnstr_release(x_256, 1);
 x_308 = x_256;
} else {
 lean::dec_ref(x_256);
 x_308 = lean::box(0);
}
if (lean::is_scalar(x_308)) {
 x_309 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_309 = x_308;
}
lean::cnstr_set(x_309, 0, x_306);
lean::cnstr_set(x_309, 1, x_307);
return x_309;
}
}
}
else
{
uint8 x_310; 
x_310 = !lean::is_exclusive(x_55);
if (x_310 == 0)
{
return x_55;
}
else
{
obj* x_311; obj* x_312; obj* x_313; 
x_311 = lean::cnstr_get(x_55, 0);
x_312 = lean::cnstr_get(x_55, 1);
lean::inc(x_312);
lean::inc(x_311);
lean::dec(x_55);
x_313 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_313, 0, x_311);
lean::cnstr_set(x_313, 1, x_312);
return x_313;
}
}
}
else
{
obj* x_314; obj* x_315; obj* x_316; 
x_314 = lean::cnstr_get(x_52, 1);
lean::inc(x_314);
lean::dec(x_52);
x_315 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_315, 0, x_9);
lean::cnstr_set(x_315, 1, x_314);
x_316 = l_Lean_IR_explicitRC(x_49, x_2, x_315);
if (lean::obj_tag(x_316) == 0)
{
obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; obj* x_323; 
x_317 = lean::cnstr_get(x_316, 0);
lean::inc(x_317);
x_318 = lean::cnstr_get(x_316, 1);
lean::inc(x_318);
if (lean::is_exclusive(x_316)) {
 lean::cnstr_release(x_316, 0);
 lean::cnstr_release(x_316, 1);
 x_319 = x_316;
} else {
 lean::dec_ref(x_316);
 x_319 = lean::box(0);
}
if (lean::is_scalar(x_319)) {
 x_320 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_320 = x_319;
}
lean::cnstr_set(x_320, 0, x_9);
lean::cnstr_set(x_320, 1, x_318);
x_321 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_322 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean::inc(x_317);
x_323 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_321, x_322, x_317, x_2, x_320);
if (lean::obj_tag(x_323) == 0)
{
obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; obj* x_330; 
x_324 = lean::cnstr_get(x_323, 1);
lean::inc(x_324);
if (lean::is_exclusive(x_323)) {
 lean::cnstr_release(x_323, 0);
 lean::cnstr_release(x_323, 1);
 x_325 = x_323;
} else {
 lean::dec_ref(x_323);
 x_325 = lean::box(0);
}
if (lean::is_scalar(x_325)) {
 x_326 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_326 = x_325;
}
lean::cnstr_set(x_326, 0, x_9);
lean::cnstr_set(x_326, 1, x_324);
x_327 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_317);
x_328 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_329 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean::inc(x_327);
x_330 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_328, x_329, x_327, x_2, x_326);
if (lean::obj_tag(x_330) == 0)
{
obj* x_331; obj* x_332; obj* x_333; obj* x_334; obj* x_335; 
x_331 = lean::cnstr_get(x_330, 1);
lean::inc(x_331);
if (lean::is_exclusive(x_330)) {
 lean::cnstr_release(x_330, 0);
 lean::cnstr_release(x_330, 1);
 x_332 = x_330;
} else {
 lean::dec_ref(x_330);
 x_332 = lean::box(0);
}
if (lean::is_scalar(x_332)) {
 x_333 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_333 = x_332;
}
lean::cnstr_set(x_333, 0, x_9);
lean::cnstr_set(x_333, 1, x_331);
x_334 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_327);
lean::inc(x_334);
x_335 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_334, x_2, x_333);
if (lean::obj_tag(x_335) == 0)
{
obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; 
x_336 = lean::cnstr_get(x_335, 1);
lean::inc(x_336);
if (lean::is_exclusive(x_335)) {
 lean::cnstr_release(x_335, 0);
 lean::cnstr_release(x_335, 1);
 x_337 = x_335;
} else {
 lean::dec_ref(x_335);
 x_337 = lean::box(0);
}
if (lean::is_scalar(x_337)) {
 x_338 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_338 = x_337;
}
lean::cnstr_set(x_338, 0, x_9);
lean::cnstr_set(x_338, 1, x_336);
x_339 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_340 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_334);
x_341 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_339, x_340, x_334, x_2, x_338);
if (lean::obj_tag(x_341) == 0)
{
obj* x_342; obj* x_343; obj* x_344; obj* x_345; 
x_342 = lean::cnstr_get(x_341, 1);
lean::inc(x_342);
if (lean::is_exclusive(x_341)) {
 lean::cnstr_release(x_341, 0);
 lean::cnstr_release(x_341, 1);
 x_343 = x_341;
} else {
 lean::dec_ref(x_341);
 x_343 = lean::box(0);
}
if (lean::is_scalar(x_343)) {
 x_344 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_344 = x_343;
}
lean::cnstr_set(x_344, 0, x_9);
lean::cnstr_set(x_344, 1, x_342);
lean::inc(x_334);
x_345 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_334, x_334, x_10, x_2, x_344);
if (lean::obj_tag(x_345) == 0)
{
obj* x_346; obj* x_347; obj* x_348; obj* x_349; 
x_346 = lean::cnstr_get(x_345, 1);
lean::inc(x_346);
if (lean::is_exclusive(x_345)) {
 lean::cnstr_release(x_345, 0);
 lean::cnstr_release(x_345, 1);
 x_347 = x_345;
} else {
 lean::dec_ref(x_345);
 x_347 = lean::box(0);
}
if (lean::is_scalar(x_347)) {
 x_348 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_348 = x_347;
}
lean::cnstr_set(x_348, 0, x_9);
lean::cnstr_set(x_348, 1, x_346);
x_349 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_334, x_10, x_2, x_348);
lean::dec(x_334);
if (lean::obj_tag(x_349) == 0)
{
obj* x_350; obj* x_351; obj* x_352; 
x_350 = lean::cnstr_get(x_349, 1);
lean::inc(x_350);
if (lean::is_exclusive(x_349)) {
 lean::cnstr_release(x_349, 0);
 lean::cnstr_release(x_349, 1);
 x_351 = x_349;
} else {
 lean::dec_ref(x_349);
 x_351 = lean::box(0);
}
if (lean::is_scalar(x_351)) {
 x_352 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_352 = x_351;
}
lean::cnstr_set(x_352, 0, x_9);
lean::cnstr_set(x_352, 1, x_350);
return x_352;
}
else
{
obj* x_353; obj* x_354; obj* x_355; obj* x_356; 
x_353 = lean::cnstr_get(x_349, 0);
lean::inc(x_353);
x_354 = lean::cnstr_get(x_349, 1);
lean::inc(x_354);
if (lean::is_exclusive(x_349)) {
 lean::cnstr_release(x_349, 0);
 lean::cnstr_release(x_349, 1);
 x_355 = x_349;
} else {
 lean::dec_ref(x_349);
 x_355 = lean::box(0);
}
if (lean::is_scalar(x_355)) {
 x_356 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_356 = x_355;
}
lean::cnstr_set(x_356, 0, x_353);
lean::cnstr_set(x_356, 1, x_354);
return x_356;
}
}
else
{
obj* x_357; obj* x_358; obj* x_359; obj* x_360; 
lean::dec(x_334);
x_357 = lean::cnstr_get(x_345, 0);
lean::inc(x_357);
x_358 = lean::cnstr_get(x_345, 1);
lean::inc(x_358);
if (lean::is_exclusive(x_345)) {
 lean::cnstr_release(x_345, 0);
 lean::cnstr_release(x_345, 1);
 x_359 = x_345;
} else {
 lean::dec_ref(x_345);
 x_359 = lean::box(0);
}
if (lean::is_scalar(x_359)) {
 x_360 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_360 = x_359;
}
lean::cnstr_set(x_360, 0, x_357);
lean::cnstr_set(x_360, 1, x_358);
return x_360;
}
}
else
{
obj* x_361; obj* x_362; obj* x_363; obj* x_364; 
lean::dec(x_334);
x_361 = lean::cnstr_get(x_341, 0);
lean::inc(x_361);
x_362 = lean::cnstr_get(x_341, 1);
lean::inc(x_362);
if (lean::is_exclusive(x_341)) {
 lean::cnstr_release(x_341, 0);
 lean::cnstr_release(x_341, 1);
 x_363 = x_341;
} else {
 lean::dec_ref(x_341);
 x_363 = lean::box(0);
}
if (lean::is_scalar(x_363)) {
 x_364 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_364 = x_363;
}
lean::cnstr_set(x_364, 0, x_361);
lean::cnstr_set(x_364, 1, x_362);
return x_364;
}
}
else
{
obj* x_365; obj* x_366; obj* x_367; obj* x_368; 
lean::dec(x_334);
x_365 = lean::cnstr_get(x_335, 0);
lean::inc(x_365);
x_366 = lean::cnstr_get(x_335, 1);
lean::inc(x_366);
if (lean::is_exclusive(x_335)) {
 lean::cnstr_release(x_335, 0);
 lean::cnstr_release(x_335, 1);
 x_367 = x_335;
} else {
 lean::dec_ref(x_335);
 x_367 = lean::box(0);
}
if (lean::is_scalar(x_367)) {
 x_368 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_368 = x_367;
}
lean::cnstr_set(x_368, 0, x_365);
lean::cnstr_set(x_368, 1, x_366);
return x_368;
}
}
else
{
obj* x_369; obj* x_370; obj* x_371; obj* x_372; 
lean::dec(x_327);
x_369 = lean::cnstr_get(x_330, 0);
lean::inc(x_369);
x_370 = lean::cnstr_get(x_330, 1);
lean::inc(x_370);
if (lean::is_exclusive(x_330)) {
 lean::cnstr_release(x_330, 0);
 lean::cnstr_release(x_330, 1);
 x_371 = x_330;
} else {
 lean::dec_ref(x_330);
 x_371 = lean::box(0);
}
if (lean::is_scalar(x_371)) {
 x_372 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_372 = x_371;
}
lean::cnstr_set(x_372, 0, x_369);
lean::cnstr_set(x_372, 1, x_370);
return x_372;
}
}
else
{
obj* x_373; obj* x_374; obj* x_375; obj* x_376; 
lean::dec(x_317);
x_373 = lean::cnstr_get(x_323, 0);
lean::inc(x_373);
x_374 = lean::cnstr_get(x_323, 1);
lean::inc(x_374);
if (lean::is_exclusive(x_323)) {
 lean::cnstr_release(x_323, 0);
 lean::cnstr_release(x_323, 1);
 x_375 = x_323;
} else {
 lean::dec_ref(x_323);
 x_375 = lean::box(0);
}
if (lean::is_scalar(x_375)) {
 x_376 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_376 = x_375;
}
lean::cnstr_set(x_376, 0, x_373);
lean::cnstr_set(x_376, 1, x_374);
return x_376;
}
}
else
{
obj* x_377; obj* x_378; obj* x_379; obj* x_380; 
x_377 = lean::cnstr_get(x_316, 0);
lean::inc(x_377);
x_378 = lean::cnstr_get(x_316, 1);
lean::inc(x_378);
if (lean::is_exclusive(x_316)) {
 lean::cnstr_release(x_316, 0);
 lean::cnstr_release(x_316, 1);
 x_379 = x_316;
} else {
 lean::dec_ref(x_316);
 x_379 = lean::box(0);
}
if (lean::is_scalar(x_379)) {
 x_380 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_380 = x_379;
}
lean::cnstr_set(x_380, 0, x_377);
lean::cnstr_set(x_380, 1, x_378);
return x_380;
}
}
}
else
{
uint8 x_381; 
lean::dec(x_49);
x_381 = !lean::is_exclusive(x_52);
if (x_381 == 0)
{
return x_52;
}
else
{
obj* x_382; obj* x_383; obj* x_384; 
x_382 = lean::cnstr_get(x_52, 0);
x_383 = lean::cnstr_get(x_52, 1);
lean::inc(x_383);
lean::inc(x_382);
lean::dec(x_52);
x_384 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_384, 0, x_382);
lean::cnstr_set(x_384, 1, x_383);
return x_384;
}
}
}
else
{
obj* x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; 
x_385 = lean::cnstr_get(x_47, 0);
x_386 = lean::cnstr_get(x_47, 1);
lean::inc(x_386);
lean::inc(x_385);
lean::dec(x_47);
x_387 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_387, 0, x_9);
lean::cnstr_set(x_387, 1, x_386);
x_388 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_389 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean::inc(x_385);
x_390 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_388, x_389, x_385, x_2, x_387);
if (lean::obj_tag(x_390) == 0)
{
obj* x_391; obj* x_392; obj* x_393; obj* x_394; 
x_391 = lean::cnstr_get(x_390, 1);
lean::inc(x_391);
if (lean::is_exclusive(x_390)) {
 lean::cnstr_release(x_390, 0);
 lean::cnstr_release(x_390, 1);
 x_392 = x_390;
} else {
 lean::dec_ref(x_390);
 x_392 = lean::box(0);
}
if (lean::is_scalar(x_392)) {
 x_393 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_393 = x_392;
}
lean::cnstr_set(x_393, 0, x_9);
lean::cnstr_set(x_393, 1, x_391);
x_394 = l_Lean_IR_explicitRC(x_385, x_2, x_393);
if (lean::obj_tag(x_394) == 0)
{
obj* x_395; obj* x_396; obj* x_397; obj* x_398; obj* x_399; obj* x_400; obj* x_401; 
x_395 = lean::cnstr_get(x_394, 0);
lean::inc(x_395);
x_396 = lean::cnstr_get(x_394, 1);
lean::inc(x_396);
if (lean::is_exclusive(x_394)) {
 lean::cnstr_release(x_394, 0);
 lean::cnstr_release(x_394, 1);
 x_397 = x_394;
} else {
 lean::dec_ref(x_394);
 x_397 = lean::box(0);
}
if (lean::is_scalar(x_397)) {
 x_398 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_398 = x_397;
}
lean::cnstr_set(x_398, 0, x_9);
lean::cnstr_set(x_398, 1, x_396);
x_399 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_400 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean::inc(x_395);
x_401 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_399, x_400, x_395, x_2, x_398);
if (lean::obj_tag(x_401) == 0)
{
obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; obj* x_407; obj* x_408; 
x_402 = lean::cnstr_get(x_401, 1);
lean::inc(x_402);
if (lean::is_exclusive(x_401)) {
 lean::cnstr_release(x_401, 0);
 lean::cnstr_release(x_401, 1);
 x_403 = x_401;
} else {
 lean::dec_ref(x_401);
 x_403 = lean::box(0);
}
if (lean::is_scalar(x_403)) {
 x_404 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_404 = x_403;
}
lean::cnstr_set(x_404, 0, x_9);
lean::cnstr_set(x_404, 1, x_402);
x_405 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_395);
x_406 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_407 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean::inc(x_405);
x_408 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_406, x_407, x_405, x_2, x_404);
if (lean::obj_tag(x_408) == 0)
{
obj* x_409; obj* x_410; obj* x_411; obj* x_412; obj* x_413; 
x_409 = lean::cnstr_get(x_408, 1);
lean::inc(x_409);
if (lean::is_exclusive(x_408)) {
 lean::cnstr_release(x_408, 0);
 lean::cnstr_release(x_408, 1);
 x_410 = x_408;
} else {
 lean::dec_ref(x_408);
 x_410 = lean::box(0);
}
if (lean::is_scalar(x_410)) {
 x_411 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_411 = x_410;
}
lean::cnstr_set(x_411, 0, x_9);
lean::cnstr_set(x_411, 1, x_409);
x_412 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_405);
lean::inc(x_412);
x_413 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_412, x_2, x_411);
if (lean::obj_tag(x_413) == 0)
{
obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; 
x_414 = lean::cnstr_get(x_413, 1);
lean::inc(x_414);
if (lean::is_exclusive(x_413)) {
 lean::cnstr_release(x_413, 0);
 lean::cnstr_release(x_413, 1);
 x_415 = x_413;
} else {
 lean::dec_ref(x_413);
 x_415 = lean::box(0);
}
if (lean::is_scalar(x_415)) {
 x_416 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_416 = x_415;
}
lean::cnstr_set(x_416, 0, x_9);
lean::cnstr_set(x_416, 1, x_414);
x_417 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_418 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_412);
x_419 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_417, x_418, x_412, x_2, x_416);
if (lean::obj_tag(x_419) == 0)
{
obj* x_420; obj* x_421; obj* x_422; obj* x_423; 
x_420 = lean::cnstr_get(x_419, 1);
lean::inc(x_420);
if (lean::is_exclusive(x_419)) {
 lean::cnstr_release(x_419, 0);
 lean::cnstr_release(x_419, 1);
 x_421 = x_419;
} else {
 lean::dec_ref(x_419);
 x_421 = lean::box(0);
}
if (lean::is_scalar(x_421)) {
 x_422 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_422 = x_421;
}
lean::cnstr_set(x_422, 0, x_9);
lean::cnstr_set(x_422, 1, x_420);
lean::inc(x_412);
x_423 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_412, x_412, x_10, x_2, x_422);
if (lean::obj_tag(x_423) == 0)
{
obj* x_424; obj* x_425; obj* x_426; obj* x_427; 
x_424 = lean::cnstr_get(x_423, 1);
lean::inc(x_424);
if (lean::is_exclusive(x_423)) {
 lean::cnstr_release(x_423, 0);
 lean::cnstr_release(x_423, 1);
 x_425 = x_423;
} else {
 lean::dec_ref(x_423);
 x_425 = lean::box(0);
}
if (lean::is_scalar(x_425)) {
 x_426 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_426 = x_425;
}
lean::cnstr_set(x_426, 0, x_9);
lean::cnstr_set(x_426, 1, x_424);
x_427 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_412, x_10, x_2, x_426);
lean::dec(x_412);
if (lean::obj_tag(x_427) == 0)
{
obj* x_428; obj* x_429; obj* x_430; 
x_428 = lean::cnstr_get(x_427, 1);
lean::inc(x_428);
if (lean::is_exclusive(x_427)) {
 lean::cnstr_release(x_427, 0);
 lean::cnstr_release(x_427, 1);
 x_429 = x_427;
} else {
 lean::dec_ref(x_427);
 x_429 = lean::box(0);
}
if (lean::is_scalar(x_429)) {
 x_430 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_430 = x_429;
}
lean::cnstr_set(x_430, 0, x_9);
lean::cnstr_set(x_430, 1, x_428);
return x_430;
}
else
{
obj* x_431; obj* x_432; obj* x_433; obj* x_434; 
x_431 = lean::cnstr_get(x_427, 0);
lean::inc(x_431);
x_432 = lean::cnstr_get(x_427, 1);
lean::inc(x_432);
if (lean::is_exclusive(x_427)) {
 lean::cnstr_release(x_427, 0);
 lean::cnstr_release(x_427, 1);
 x_433 = x_427;
} else {
 lean::dec_ref(x_427);
 x_433 = lean::box(0);
}
if (lean::is_scalar(x_433)) {
 x_434 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_434 = x_433;
}
lean::cnstr_set(x_434, 0, x_431);
lean::cnstr_set(x_434, 1, x_432);
return x_434;
}
}
else
{
obj* x_435; obj* x_436; obj* x_437; obj* x_438; 
lean::dec(x_412);
x_435 = lean::cnstr_get(x_423, 0);
lean::inc(x_435);
x_436 = lean::cnstr_get(x_423, 1);
lean::inc(x_436);
if (lean::is_exclusive(x_423)) {
 lean::cnstr_release(x_423, 0);
 lean::cnstr_release(x_423, 1);
 x_437 = x_423;
} else {
 lean::dec_ref(x_423);
 x_437 = lean::box(0);
}
if (lean::is_scalar(x_437)) {
 x_438 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_438 = x_437;
}
lean::cnstr_set(x_438, 0, x_435);
lean::cnstr_set(x_438, 1, x_436);
return x_438;
}
}
else
{
obj* x_439; obj* x_440; obj* x_441; obj* x_442; 
lean::dec(x_412);
x_439 = lean::cnstr_get(x_419, 0);
lean::inc(x_439);
x_440 = lean::cnstr_get(x_419, 1);
lean::inc(x_440);
if (lean::is_exclusive(x_419)) {
 lean::cnstr_release(x_419, 0);
 lean::cnstr_release(x_419, 1);
 x_441 = x_419;
} else {
 lean::dec_ref(x_419);
 x_441 = lean::box(0);
}
if (lean::is_scalar(x_441)) {
 x_442 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_442 = x_441;
}
lean::cnstr_set(x_442, 0, x_439);
lean::cnstr_set(x_442, 1, x_440);
return x_442;
}
}
else
{
obj* x_443; obj* x_444; obj* x_445; obj* x_446; 
lean::dec(x_412);
x_443 = lean::cnstr_get(x_413, 0);
lean::inc(x_443);
x_444 = lean::cnstr_get(x_413, 1);
lean::inc(x_444);
if (lean::is_exclusive(x_413)) {
 lean::cnstr_release(x_413, 0);
 lean::cnstr_release(x_413, 1);
 x_445 = x_413;
} else {
 lean::dec_ref(x_413);
 x_445 = lean::box(0);
}
if (lean::is_scalar(x_445)) {
 x_446 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_446 = x_445;
}
lean::cnstr_set(x_446, 0, x_443);
lean::cnstr_set(x_446, 1, x_444);
return x_446;
}
}
else
{
obj* x_447; obj* x_448; obj* x_449; obj* x_450; 
lean::dec(x_405);
x_447 = lean::cnstr_get(x_408, 0);
lean::inc(x_447);
x_448 = lean::cnstr_get(x_408, 1);
lean::inc(x_448);
if (lean::is_exclusive(x_408)) {
 lean::cnstr_release(x_408, 0);
 lean::cnstr_release(x_408, 1);
 x_449 = x_408;
} else {
 lean::dec_ref(x_408);
 x_449 = lean::box(0);
}
if (lean::is_scalar(x_449)) {
 x_450 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_450 = x_449;
}
lean::cnstr_set(x_450, 0, x_447);
lean::cnstr_set(x_450, 1, x_448);
return x_450;
}
}
else
{
obj* x_451; obj* x_452; obj* x_453; obj* x_454; 
lean::dec(x_395);
x_451 = lean::cnstr_get(x_401, 0);
lean::inc(x_451);
x_452 = lean::cnstr_get(x_401, 1);
lean::inc(x_452);
if (lean::is_exclusive(x_401)) {
 lean::cnstr_release(x_401, 0);
 lean::cnstr_release(x_401, 1);
 x_453 = x_401;
} else {
 lean::dec_ref(x_401);
 x_453 = lean::box(0);
}
if (lean::is_scalar(x_453)) {
 x_454 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_454 = x_453;
}
lean::cnstr_set(x_454, 0, x_451);
lean::cnstr_set(x_454, 1, x_452);
return x_454;
}
}
else
{
obj* x_455; obj* x_456; obj* x_457; obj* x_458; 
x_455 = lean::cnstr_get(x_394, 0);
lean::inc(x_455);
x_456 = lean::cnstr_get(x_394, 1);
lean::inc(x_456);
if (lean::is_exclusive(x_394)) {
 lean::cnstr_release(x_394, 0);
 lean::cnstr_release(x_394, 1);
 x_457 = x_394;
} else {
 lean::dec_ref(x_394);
 x_457 = lean::box(0);
}
if (lean::is_scalar(x_457)) {
 x_458 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_458 = x_457;
}
lean::cnstr_set(x_458, 0, x_455);
lean::cnstr_set(x_458, 1, x_456);
return x_458;
}
}
else
{
obj* x_459; obj* x_460; obj* x_461; obj* x_462; 
lean::dec(x_385);
x_459 = lean::cnstr_get(x_390, 0);
lean::inc(x_459);
x_460 = lean::cnstr_get(x_390, 1);
lean::inc(x_460);
if (lean::is_exclusive(x_390)) {
 lean::cnstr_release(x_390, 0);
 lean::cnstr_release(x_390, 1);
 x_461 = x_390;
} else {
 lean::dec_ref(x_390);
 x_461 = lean::box(0);
}
if (lean::is_scalar(x_461)) {
 x_462 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_462 = x_461;
}
lean::cnstr_set(x_462, 0, x_459);
lean::cnstr_set(x_462, 1, x_460);
return x_462;
}
}
}
else
{
uint8 x_463; 
x_463 = !lean::is_exclusive(x_47);
if (x_463 == 0)
{
return x_47;
}
else
{
obj* x_464; obj* x_465; obj* x_466; 
x_464 = lean::cnstr_get(x_47, 0);
x_465 = lean::cnstr_get(x_47, 1);
lean::inc(x_465);
lean::inc(x_464);
lean::dec(x_47);
x_466 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_466, 0, x_464);
lean::cnstr_set(x_466, 1, x_465);
return x_466;
}
}
}
else
{
obj* x_467; obj* x_468; obj* x_469; 
x_467 = lean::cnstr_get(x_44, 1);
lean::inc(x_467);
lean::dec(x_44);
x_468 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_468, 0, x_9);
lean::cnstr_set(x_468, 1, x_467);
x_469 = l_Lean_IR_explicitBoxing(x_41, x_2, x_468);
if (lean::obj_tag(x_469) == 0)
{
obj* x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; 
x_470 = lean::cnstr_get(x_469, 0);
lean::inc(x_470);
x_471 = lean::cnstr_get(x_469, 1);
lean::inc(x_471);
if (lean::is_exclusive(x_469)) {
 lean::cnstr_release(x_469, 0);
 lean::cnstr_release(x_469, 1);
 x_472 = x_469;
} else {
 lean::dec_ref(x_469);
 x_472 = lean::box(0);
}
if (lean::is_scalar(x_472)) {
 x_473 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_473 = x_472;
}
lean::cnstr_set(x_473, 0, x_9);
lean::cnstr_set(x_473, 1, x_471);
x_474 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_475 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean::inc(x_470);
x_476 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_474, x_475, x_470, x_2, x_473);
if (lean::obj_tag(x_476) == 0)
{
obj* x_477; obj* x_478; obj* x_479; obj* x_480; 
x_477 = lean::cnstr_get(x_476, 1);
lean::inc(x_477);
if (lean::is_exclusive(x_476)) {
 lean::cnstr_release(x_476, 0);
 lean::cnstr_release(x_476, 1);
 x_478 = x_476;
} else {
 lean::dec_ref(x_476);
 x_478 = lean::box(0);
}
if (lean::is_scalar(x_478)) {
 x_479 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_479 = x_478;
}
lean::cnstr_set(x_479, 0, x_9);
lean::cnstr_set(x_479, 1, x_477);
x_480 = l_Lean_IR_explicitRC(x_470, x_2, x_479);
if (lean::obj_tag(x_480) == 0)
{
obj* x_481; obj* x_482; obj* x_483; obj* x_484; obj* x_485; obj* x_486; obj* x_487; 
x_481 = lean::cnstr_get(x_480, 0);
lean::inc(x_481);
x_482 = lean::cnstr_get(x_480, 1);
lean::inc(x_482);
if (lean::is_exclusive(x_480)) {
 lean::cnstr_release(x_480, 0);
 lean::cnstr_release(x_480, 1);
 x_483 = x_480;
} else {
 lean::dec_ref(x_480);
 x_483 = lean::box(0);
}
if (lean::is_scalar(x_483)) {
 x_484 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_484 = x_483;
}
lean::cnstr_set(x_484, 0, x_9);
lean::cnstr_set(x_484, 1, x_482);
x_485 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_486 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean::inc(x_481);
x_487 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_485, x_486, x_481, x_2, x_484);
if (lean::obj_tag(x_487) == 0)
{
obj* x_488; obj* x_489; obj* x_490; obj* x_491; obj* x_492; obj* x_493; obj* x_494; 
x_488 = lean::cnstr_get(x_487, 1);
lean::inc(x_488);
if (lean::is_exclusive(x_487)) {
 lean::cnstr_release(x_487, 0);
 lean::cnstr_release(x_487, 1);
 x_489 = x_487;
} else {
 lean::dec_ref(x_487);
 x_489 = lean::box(0);
}
if (lean::is_scalar(x_489)) {
 x_490 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_490 = x_489;
}
lean::cnstr_set(x_490, 0, x_9);
lean::cnstr_set(x_490, 1, x_488);
x_491 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_481);
x_492 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_493 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean::inc(x_491);
x_494 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_492, x_493, x_491, x_2, x_490);
if (lean::obj_tag(x_494) == 0)
{
obj* x_495; obj* x_496; obj* x_497; obj* x_498; obj* x_499; 
x_495 = lean::cnstr_get(x_494, 1);
lean::inc(x_495);
if (lean::is_exclusive(x_494)) {
 lean::cnstr_release(x_494, 0);
 lean::cnstr_release(x_494, 1);
 x_496 = x_494;
} else {
 lean::dec_ref(x_494);
 x_496 = lean::box(0);
}
if (lean::is_scalar(x_496)) {
 x_497 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_497 = x_496;
}
lean::cnstr_set(x_497, 0, x_9);
lean::cnstr_set(x_497, 1, x_495);
x_498 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_491);
lean::inc(x_498);
x_499 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_498, x_2, x_497);
if (lean::obj_tag(x_499) == 0)
{
obj* x_500; obj* x_501; obj* x_502; obj* x_503; obj* x_504; obj* x_505; 
x_500 = lean::cnstr_get(x_499, 1);
lean::inc(x_500);
if (lean::is_exclusive(x_499)) {
 lean::cnstr_release(x_499, 0);
 lean::cnstr_release(x_499, 1);
 x_501 = x_499;
} else {
 lean::dec_ref(x_499);
 x_501 = lean::box(0);
}
if (lean::is_scalar(x_501)) {
 x_502 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_502 = x_501;
}
lean::cnstr_set(x_502, 0, x_9);
lean::cnstr_set(x_502, 1, x_500);
x_503 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_504 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_498);
x_505 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_503, x_504, x_498, x_2, x_502);
if (lean::obj_tag(x_505) == 0)
{
obj* x_506; obj* x_507; obj* x_508; obj* x_509; 
x_506 = lean::cnstr_get(x_505, 1);
lean::inc(x_506);
if (lean::is_exclusive(x_505)) {
 lean::cnstr_release(x_505, 0);
 lean::cnstr_release(x_505, 1);
 x_507 = x_505;
} else {
 lean::dec_ref(x_505);
 x_507 = lean::box(0);
}
if (lean::is_scalar(x_507)) {
 x_508 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_508 = x_507;
}
lean::cnstr_set(x_508, 0, x_9);
lean::cnstr_set(x_508, 1, x_506);
lean::inc(x_498);
x_509 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_498, x_498, x_10, x_2, x_508);
if (lean::obj_tag(x_509) == 0)
{
obj* x_510; obj* x_511; obj* x_512; obj* x_513; 
x_510 = lean::cnstr_get(x_509, 1);
lean::inc(x_510);
if (lean::is_exclusive(x_509)) {
 lean::cnstr_release(x_509, 0);
 lean::cnstr_release(x_509, 1);
 x_511 = x_509;
} else {
 lean::dec_ref(x_509);
 x_511 = lean::box(0);
}
if (lean::is_scalar(x_511)) {
 x_512 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_512 = x_511;
}
lean::cnstr_set(x_512, 0, x_9);
lean::cnstr_set(x_512, 1, x_510);
x_513 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_498, x_10, x_2, x_512);
lean::dec(x_498);
if (lean::obj_tag(x_513) == 0)
{
obj* x_514; obj* x_515; obj* x_516; 
x_514 = lean::cnstr_get(x_513, 1);
lean::inc(x_514);
if (lean::is_exclusive(x_513)) {
 lean::cnstr_release(x_513, 0);
 lean::cnstr_release(x_513, 1);
 x_515 = x_513;
} else {
 lean::dec_ref(x_513);
 x_515 = lean::box(0);
}
if (lean::is_scalar(x_515)) {
 x_516 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_516 = x_515;
}
lean::cnstr_set(x_516, 0, x_9);
lean::cnstr_set(x_516, 1, x_514);
return x_516;
}
else
{
obj* x_517; obj* x_518; obj* x_519; obj* x_520; 
x_517 = lean::cnstr_get(x_513, 0);
lean::inc(x_517);
x_518 = lean::cnstr_get(x_513, 1);
lean::inc(x_518);
if (lean::is_exclusive(x_513)) {
 lean::cnstr_release(x_513, 0);
 lean::cnstr_release(x_513, 1);
 x_519 = x_513;
} else {
 lean::dec_ref(x_513);
 x_519 = lean::box(0);
}
if (lean::is_scalar(x_519)) {
 x_520 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_520 = x_519;
}
lean::cnstr_set(x_520, 0, x_517);
lean::cnstr_set(x_520, 1, x_518);
return x_520;
}
}
else
{
obj* x_521; obj* x_522; obj* x_523; obj* x_524; 
lean::dec(x_498);
x_521 = lean::cnstr_get(x_509, 0);
lean::inc(x_521);
x_522 = lean::cnstr_get(x_509, 1);
lean::inc(x_522);
if (lean::is_exclusive(x_509)) {
 lean::cnstr_release(x_509, 0);
 lean::cnstr_release(x_509, 1);
 x_523 = x_509;
} else {
 lean::dec_ref(x_509);
 x_523 = lean::box(0);
}
if (lean::is_scalar(x_523)) {
 x_524 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_524 = x_523;
}
lean::cnstr_set(x_524, 0, x_521);
lean::cnstr_set(x_524, 1, x_522);
return x_524;
}
}
else
{
obj* x_525; obj* x_526; obj* x_527; obj* x_528; 
lean::dec(x_498);
x_525 = lean::cnstr_get(x_505, 0);
lean::inc(x_525);
x_526 = lean::cnstr_get(x_505, 1);
lean::inc(x_526);
if (lean::is_exclusive(x_505)) {
 lean::cnstr_release(x_505, 0);
 lean::cnstr_release(x_505, 1);
 x_527 = x_505;
} else {
 lean::dec_ref(x_505);
 x_527 = lean::box(0);
}
if (lean::is_scalar(x_527)) {
 x_528 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_528 = x_527;
}
lean::cnstr_set(x_528, 0, x_525);
lean::cnstr_set(x_528, 1, x_526);
return x_528;
}
}
else
{
obj* x_529; obj* x_530; obj* x_531; obj* x_532; 
lean::dec(x_498);
x_529 = lean::cnstr_get(x_499, 0);
lean::inc(x_529);
x_530 = lean::cnstr_get(x_499, 1);
lean::inc(x_530);
if (lean::is_exclusive(x_499)) {
 lean::cnstr_release(x_499, 0);
 lean::cnstr_release(x_499, 1);
 x_531 = x_499;
} else {
 lean::dec_ref(x_499);
 x_531 = lean::box(0);
}
if (lean::is_scalar(x_531)) {
 x_532 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_532 = x_531;
}
lean::cnstr_set(x_532, 0, x_529);
lean::cnstr_set(x_532, 1, x_530);
return x_532;
}
}
else
{
obj* x_533; obj* x_534; obj* x_535; obj* x_536; 
lean::dec(x_491);
x_533 = lean::cnstr_get(x_494, 0);
lean::inc(x_533);
x_534 = lean::cnstr_get(x_494, 1);
lean::inc(x_534);
if (lean::is_exclusive(x_494)) {
 lean::cnstr_release(x_494, 0);
 lean::cnstr_release(x_494, 1);
 x_535 = x_494;
} else {
 lean::dec_ref(x_494);
 x_535 = lean::box(0);
}
if (lean::is_scalar(x_535)) {
 x_536 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_536 = x_535;
}
lean::cnstr_set(x_536, 0, x_533);
lean::cnstr_set(x_536, 1, x_534);
return x_536;
}
}
else
{
obj* x_537; obj* x_538; obj* x_539; obj* x_540; 
lean::dec(x_481);
x_537 = lean::cnstr_get(x_487, 0);
lean::inc(x_537);
x_538 = lean::cnstr_get(x_487, 1);
lean::inc(x_538);
if (lean::is_exclusive(x_487)) {
 lean::cnstr_release(x_487, 0);
 lean::cnstr_release(x_487, 1);
 x_539 = x_487;
} else {
 lean::dec_ref(x_487);
 x_539 = lean::box(0);
}
if (lean::is_scalar(x_539)) {
 x_540 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_540 = x_539;
}
lean::cnstr_set(x_540, 0, x_537);
lean::cnstr_set(x_540, 1, x_538);
return x_540;
}
}
else
{
obj* x_541; obj* x_542; obj* x_543; obj* x_544; 
x_541 = lean::cnstr_get(x_480, 0);
lean::inc(x_541);
x_542 = lean::cnstr_get(x_480, 1);
lean::inc(x_542);
if (lean::is_exclusive(x_480)) {
 lean::cnstr_release(x_480, 0);
 lean::cnstr_release(x_480, 1);
 x_543 = x_480;
} else {
 lean::dec_ref(x_480);
 x_543 = lean::box(0);
}
if (lean::is_scalar(x_543)) {
 x_544 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_544 = x_543;
}
lean::cnstr_set(x_544, 0, x_541);
lean::cnstr_set(x_544, 1, x_542);
return x_544;
}
}
else
{
obj* x_545; obj* x_546; obj* x_547; obj* x_548; 
lean::dec(x_470);
x_545 = lean::cnstr_get(x_476, 0);
lean::inc(x_545);
x_546 = lean::cnstr_get(x_476, 1);
lean::inc(x_546);
if (lean::is_exclusive(x_476)) {
 lean::cnstr_release(x_476, 0);
 lean::cnstr_release(x_476, 1);
 x_547 = x_476;
} else {
 lean::dec_ref(x_476);
 x_547 = lean::box(0);
}
if (lean::is_scalar(x_547)) {
 x_548 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_548 = x_547;
}
lean::cnstr_set(x_548, 0, x_545);
lean::cnstr_set(x_548, 1, x_546);
return x_548;
}
}
else
{
obj* x_549; obj* x_550; obj* x_551; obj* x_552; 
x_549 = lean::cnstr_get(x_469, 0);
lean::inc(x_549);
x_550 = lean::cnstr_get(x_469, 1);
lean::inc(x_550);
if (lean::is_exclusive(x_469)) {
 lean::cnstr_release(x_469, 0);
 lean::cnstr_release(x_469, 1);
 x_551 = x_469;
} else {
 lean::dec_ref(x_469);
 x_551 = lean::box(0);
}
if (lean::is_scalar(x_551)) {
 x_552 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_552 = x_551;
}
lean::cnstr_set(x_552, 0, x_549);
lean::cnstr_set(x_552, 1, x_550);
return x_552;
}
}
}
else
{
uint8 x_553; 
lean::dec(x_41);
x_553 = !lean::is_exclusive(x_44);
if (x_553 == 0)
{
return x_44;
}
else
{
obj* x_554; obj* x_555; obj* x_556; 
x_554 = lean::cnstr_get(x_44, 0);
x_555 = lean::cnstr_get(x_44, 1);
lean::inc(x_555);
lean::inc(x_554);
lean::dec(x_44);
x_556 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_556, 0, x_554);
lean::cnstr_set(x_556, 1, x_555);
return x_556;
}
}
}
else
{
obj* x_557; obj* x_558; obj* x_559; obj* x_560; obj* x_561; obj* x_562; 
x_557 = lean::cnstr_get(x_39, 0);
x_558 = lean::cnstr_get(x_39, 1);
lean::inc(x_558);
lean::inc(x_557);
lean::dec(x_39);
x_559 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_559, 0, x_9);
lean::cnstr_set(x_559, 1, x_558);
x_560 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_561 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean::inc(x_557);
x_562 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_560, x_561, x_557, x_2, x_559);
if (lean::obj_tag(x_562) == 0)
{
obj* x_563; obj* x_564; obj* x_565; obj* x_566; 
x_563 = lean::cnstr_get(x_562, 1);
lean::inc(x_563);
if (lean::is_exclusive(x_562)) {
 lean::cnstr_release(x_562, 0);
 lean::cnstr_release(x_562, 1);
 x_564 = x_562;
} else {
 lean::dec_ref(x_562);
 x_564 = lean::box(0);
}
if (lean::is_scalar(x_564)) {
 x_565 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_565 = x_564;
}
lean::cnstr_set(x_565, 0, x_9);
lean::cnstr_set(x_565, 1, x_563);
x_566 = l_Lean_IR_explicitBoxing(x_557, x_2, x_565);
if (lean::obj_tag(x_566) == 0)
{
obj* x_567; obj* x_568; obj* x_569; obj* x_570; obj* x_571; obj* x_572; obj* x_573; 
x_567 = lean::cnstr_get(x_566, 0);
lean::inc(x_567);
x_568 = lean::cnstr_get(x_566, 1);
lean::inc(x_568);
if (lean::is_exclusive(x_566)) {
 lean::cnstr_release(x_566, 0);
 lean::cnstr_release(x_566, 1);
 x_569 = x_566;
} else {
 lean::dec_ref(x_566);
 x_569 = lean::box(0);
}
if (lean::is_scalar(x_569)) {
 x_570 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_570 = x_569;
}
lean::cnstr_set(x_570, 0, x_9);
lean::cnstr_set(x_570, 1, x_568);
x_571 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_572 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean::inc(x_567);
x_573 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_571, x_572, x_567, x_2, x_570);
if (lean::obj_tag(x_573) == 0)
{
obj* x_574; obj* x_575; obj* x_576; obj* x_577; 
x_574 = lean::cnstr_get(x_573, 1);
lean::inc(x_574);
if (lean::is_exclusive(x_573)) {
 lean::cnstr_release(x_573, 0);
 lean::cnstr_release(x_573, 1);
 x_575 = x_573;
} else {
 lean::dec_ref(x_573);
 x_575 = lean::box(0);
}
if (lean::is_scalar(x_575)) {
 x_576 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_576 = x_575;
}
lean::cnstr_set(x_576, 0, x_9);
lean::cnstr_set(x_576, 1, x_574);
x_577 = l_Lean_IR_explicitRC(x_567, x_2, x_576);
if (lean::obj_tag(x_577) == 0)
{
obj* x_578; obj* x_579; obj* x_580; obj* x_581; obj* x_582; obj* x_583; obj* x_584; 
x_578 = lean::cnstr_get(x_577, 0);
lean::inc(x_578);
x_579 = lean::cnstr_get(x_577, 1);
lean::inc(x_579);
if (lean::is_exclusive(x_577)) {
 lean::cnstr_release(x_577, 0);
 lean::cnstr_release(x_577, 1);
 x_580 = x_577;
} else {
 lean::dec_ref(x_577);
 x_580 = lean::box(0);
}
if (lean::is_scalar(x_580)) {
 x_581 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_581 = x_580;
}
lean::cnstr_set(x_581, 0, x_9);
lean::cnstr_set(x_581, 1, x_579);
x_582 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_583 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean::inc(x_578);
x_584 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_582, x_583, x_578, x_2, x_581);
if (lean::obj_tag(x_584) == 0)
{
obj* x_585; obj* x_586; obj* x_587; obj* x_588; obj* x_589; obj* x_590; obj* x_591; 
x_585 = lean::cnstr_get(x_584, 1);
lean::inc(x_585);
if (lean::is_exclusive(x_584)) {
 lean::cnstr_release(x_584, 0);
 lean::cnstr_release(x_584, 1);
 x_586 = x_584;
} else {
 lean::dec_ref(x_584);
 x_586 = lean::box(0);
}
if (lean::is_scalar(x_586)) {
 x_587 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_587 = x_586;
}
lean::cnstr_set(x_587, 0, x_9);
lean::cnstr_set(x_587, 1, x_585);
x_588 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_578);
x_589 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_590 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean::inc(x_588);
x_591 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_589, x_590, x_588, x_2, x_587);
if (lean::obj_tag(x_591) == 0)
{
obj* x_592; obj* x_593; obj* x_594; obj* x_595; obj* x_596; 
x_592 = lean::cnstr_get(x_591, 1);
lean::inc(x_592);
if (lean::is_exclusive(x_591)) {
 lean::cnstr_release(x_591, 0);
 lean::cnstr_release(x_591, 1);
 x_593 = x_591;
} else {
 lean::dec_ref(x_591);
 x_593 = lean::box(0);
}
if (lean::is_scalar(x_593)) {
 x_594 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_594 = x_593;
}
lean::cnstr_set(x_594, 0, x_9);
lean::cnstr_set(x_594, 1, x_592);
x_595 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_588);
lean::inc(x_595);
x_596 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_595, x_2, x_594);
if (lean::obj_tag(x_596) == 0)
{
obj* x_597; obj* x_598; obj* x_599; obj* x_600; obj* x_601; obj* x_602; 
x_597 = lean::cnstr_get(x_596, 1);
lean::inc(x_597);
if (lean::is_exclusive(x_596)) {
 lean::cnstr_release(x_596, 0);
 lean::cnstr_release(x_596, 1);
 x_598 = x_596;
} else {
 lean::dec_ref(x_596);
 x_598 = lean::box(0);
}
if (lean::is_scalar(x_598)) {
 x_599 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_599 = x_598;
}
lean::cnstr_set(x_599, 0, x_9);
lean::cnstr_set(x_599, 1, x_597);
x_600 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_601 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_595);
x_602 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_600, x_601, x_595, x_2, x_599);
if (lean::obj_tag(x_602) == 0)
{
obj* x_603; obj* x_604; obj* x_605; obj* x_606; 
x_603 = lean::cnstr_get(x_602, 1);
lean::inc(x_603);
if (lean::is_exclusive(x_602)) {
 lean::cnstr_release(x_602, 0);
 lean::cnstr_release(x_602, 1);
 x_604 = x_602;
} else {
 lean::dec_ref(x_602);
 x_604 = lean::box(0);
}
if (lean::is_scalar(x_604)) {
 x_605 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_605 = x_604;
}
lean::cnstr_set(x_605, 0, x_9);
lean::cnstr_set(x_605, 1, x_603);
lean::inc(x_595);
x_606 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_595, x_595, x_10, x_2, x_605);
if (lean::obj_tag(x_606) == 0)
{
obj* x_607; obj* x_608; obj* x_609; obj* x_610; 
x_607 = lean::cnstr_get(x_606, 1);
lean::inc(x_607);
if (lean::is_exclusive(x_606)) {
 lean::cnstr_release(x_606, 0);
 lean::cnstr_release(x_606, 1);
 x_608 = x_606;
} else {
 lean::dec_ref(x_606);
 x_608 = lean::box(0);
}
if (lean::is_scalar(x_608)) {
 x_609 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_609 = x_608;
}
lean::cnstr_set(x_609, 0, x_9);
lean::cnstr_set(x_609, 1, x_607);
x_610 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_595, x_10, x_2, x_609);
lean::dec(x_595);
if (lean::obj_tag(x_610) == 0)
{
obj* x_611; obj* x_612; obj* x_613; 
x_611 = lean::cnstr_get(x_610, 1);
lean::inc(x_611);
if (lean::is_exclusive(x_610)) {
 lean::cnstr_release(x_610, 0);
 lean::cnstr_release(x_610, 1);
 x_612 = x_610;
} else {
 lean::dec_ref(x_610);
 x_612 = lean::box(0);
}
if (lean::is_scalar(x_612)) {
 x_613 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_613 = x_612;
}
lean::cnstr_set(x_613, 0, x_9);
lean::cnstr_set(x_613, 1, x_611);
return x_613;
}
else
{
obj* x_614; obj* x_615; obj* x_616; obj* x_617; 
x_614 = lean::cnstr_get(x_610, 0);
lean::inc(x_614);
x_615 = lean::cnstr_get(x_610, 1);
lean::inc(x_615);
if (lean::is_exclusive(x_610)) {
 lean::cnstr_release(x_610, 0);
 lean::cnstr_release(x_610, 1);
 x_616 = x_610;
} else {
 lean::dec_ref(x_610);
 x_616 = lean::box(0);
}
if (lean::is_scalar(x_616)) {
 x_617 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_617 = x_616;
}
lean::cnstr_set(x_617, 0, x_614);
lean::cnstr_set(x_617, 1, x_615);
return x_617;
}
}
else
{
obj* x_618; obj* x_619; obj* x_620; obj* x_621; 
lean::dec(x_595);
x_618 = lean::cnstr_get(x_606, 0);
lean::inc(x_618);
x_619 = lean::cnstr_get(x_606, 1);
lean::inc(x_619);
if (lean::is_exclusive(x_606)) {
 lean::cnstr_release(x_606, 0);
 lean::cnstr_release(x_606, 1);
 x_620 = x_606;
} else {
 lean::dec_ref(x_606);
 x_620 = lean::box(0);
}
if (lean::is_scalar(x_620)) {
 x_621 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_621 = x_620;
}
lean::cnstr_set(x_621, 0, x_618);
lean::cnstr_set(x_621, 1, x_619);
return x_621;
}
}
else
{
obj* x_622; obj* x_623; obj* x_624; obj* x_625; 
lean::dec(x_595);
x_622 = lean::cnstr_get(x_602, 0);
lean::inc(x_622);
x_623 = lean::cnstr_get(x_602, 1);
lean::inc(x_623);
if (lean::is_exclusive(x_602)) {
 lean::cnstr_release(x_602, 0);
 lean::cnstr_release(x_602, 1);
 x_624 = x_602;
} else {
 lean::dec_ref(x_602);
 x_624 = lean::box(0);
}
if (lean::is_scalar(x_624)) {
 x_625 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_625 = x_624;
}
lean::cnstr_set(x_625, 0, x_622);
lean::cnstr_set(x_625, 1, x_623);
return x_625;
}
}
else
{
obj* x_626; obj* x_627; obj* x_628; obj* x_629; 
lean::dec(x_595);
x_626 = lean::cnstr_get(x_596, 0);
lean::inc(x_626);
x_627 = lean::cnstr_get(x_596, 1);
lean::inc(x_627);
if (lean::is_exclusive(x_596)) {
 lean::cnstr_release(x_596, 0);
 lean::cnstr_release(x_596, 1);
 x_628 = x_596;
} else {
 lean::dec_ref(x_596);
 x_628 = lean::box(0);
}
if (lean::is_scalar(x_628)) {
 x_629 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_629 = x_628;
}
lean::cnstr_set(x_629, 0, x_626);
lean::cnstr_set(x_629, 1, x_627);
return x_629;
}
}
else
{
obj* x_630; obj* x_631; obj* x_632; obj* x_633; 
lean::dec(x_588);
x_630 = lean::cnstr_get(x_591, 0);
lean::inc(x_630);
x_631 = lean::cnstr_get(x_591, 1);
lean::inc(x_631);
if (lean::is_exclusive(x_591)) {
 lean::cnstr_release(x_591, 0);
 lean::cnstr_release(x_591, 1);
 x_632 = x_591;
} else {
 lean::dec_ref(x_591);
 x_632 = lean::box(0);
}
if (lean::is_scalar(x_632)) {
 x_633 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_633 = x_632;
}
lean::cnstr_set(x_633, 0, x_630);
lean::cnstr_set(x_633, 1, x_631);
return x_633;
}
}
else
{
obj* x_634; obj* x_635; obj* x_636; obj* x_637; 
lean::dec(x_578);
x_634 = lean::cnstr_get(x_584, 0);
lean::inc(x_634);
x_635 = lean::cnstr_get(x_584, 1);
lean::inc(x_635);
if (lean::is_exclusive(x_584)) {
 lean::cnstr_release(x_584, 0);
 lean::cnstr_release(x_584, 1);
 x_636 = x_584;
} else {
 lean::dec_ref(x_584);
 x_636 = lean::box(0);
}
if (lean::is_scalar(x_636)) {
 x_637 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_637 = x_636;
}
lean::cnstr_set(x_637, 0, x_634);
lean::cnstr_set(x_637, 1, x_635);
return x_637;
}
}
else
{
obj* x_638; obj* x_639; obj* x_640; obj* x_641; 
x_638 = lean::cnstr_get(x_577, 0);
lean::inc(x_638);
x_639 = lean::cnstr_get(x_577, 1);
lean::inc(x_639);
if (lean::is_exclusive(x_577)) {
 lean::cnstr_release(x_577, 0);
 lean::cnstr_release(x_577, 1);
 x_640 = x_577;
} else {
 lean::dec_ref(x_577);
 x_640 = lean::box(0);
}
if (lean::is_scalar(x_640)) {
 x_641 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_641 = x_640;
}
lean::cnstr_set(x_641, 0, x_638);
lean::cnstr_set(x_641, 1, x_639);
return x_641;
}
}
else
{
obj* x_642; obj* x_643; obj* x_644; obj* x_645; 
lean::dec(x_567);
x_642 = lean::cnstr_get(x_573, 0);
lean::inc(x_642);
x_643 = lean::cnstr_get(x_573, 1);
lean::inc(x_643);
if (lean::is_exclusive(x_573)) {
 lean::cnstr_release(x_573, 0);
 lean::cnstr_release(x_573, 1);
 x_644 = x_573;
} else {
 lean::dec_ref(x_573);
 x_644 = lean::box(0);
}
if (lean::is_scalar(x_644)) {
 x_645 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_645 = x_644;
}
lean::cnstr_set(x_645, 0, x_642);
lean::cnstr_set(x_645, 1, x_643);
return x_645;
}
}
else
{
obj* x_646; obj* x_647; obj* x_648; obj* x_649; 
x_646 = lean::cnstr_get(x_566, 0);
lean::inc(x_646);
x_647 = lean::cnstr_get(x_566, 1);
lean::inc(x_647);
if (lean::is_exclusive(x_566)) {
 lean::cnstr_release(x_566, 0);
 lean::cnstr_release(x_566, 1);
 x_648 = x_566;
} else {
 lean::dec_ref(x_566);
 x_648 = lean::box(0);
}
if (lean::is_scalar(x_648)) {
 x_649 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_649 = x_648;
}
lean::cnstr_set(x_649, 0, x_646);
lean::cnstr_set(x_649, 1, x_647);
return x_649;
}
}
else
{
obj* x_650; obj* x_651; obj* x_652; obj* x_653; 
lean::dec(x_557);
x_650 = lean::cnstr_get(x_562, 0);
lean::inc(x_650);
x_651 = lean::cnstr_get(x_562, 1);
lean::inc(x_651);
if (lean::is_exclusive(x_562)) {
 lean::cnstr_release(x_562, 0);
 lean::cnstr_release(x_562, 1);
 x_652 = x_562;
} else {
 lean::dec_ref(x_562);
 x_652 = lean::box(0);
}
if (lean::is_scalar(x_652)) {
 x_653 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_653 = x_652;
}
lean::cnstr_set(x_653, 0, x_650);
lean::cnstr_set(x_653, 1, x_651);
return x_653;
}
}
}
else
{
uint8 x_654; 
x_654 = !lean::is_exclusive(x_39);
if (x_654 == 0)
{
return x_39;
}
else
{
obj* x_655; obj* x_656; obj* x_657; 
x_655 = lean::cnstr_get(x_39, 0);
x_656 = lean::cnstr_get(x_39, 1);
lean::inc(x_656);
lean::inc(x_655);
lean::dec(x_39);
x_657 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_657, 0, x_655);
lean::cnstr_set(x_657, 1, x_656);
return x_657;
}
}
}
else
{
obj* x_658; obj* x_659; obj* x_660; obj* x_661; 
x_658 = lean::cnstr_get(x_35, 1);
lean::inc(x_658);
lean::dec(x_35);
x_659 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_659, 0, x_9);
lean::cnstr_set(x_659, 1, x_658);
x_660 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_32);
x_661 = l_Lean_IR_inferBorrow(x_660, x_2, x_659);
if (lean::obj_tag(x_661) == 0)
{
obj* x_662; obj* x_663; obj* x_664; obj* x_665; obj* x_666; obj* x_667; obj* x_668; 
x_662 = lean::cnstr_get(x_661, 0);
lean::inc(x_662);
x_663 = lean::cnstr_get(x_661, 1);
lean::inc(x_663);
if (lean::is_exclusive(x_661)) {
 lean::cnstr_release(x_661, 0);
 lean::cnstr_release(x_661, 1);
 x_664 = x_661;
} else {
 lean::dec_ref(x_661);
 x_664 = lean::box(0);
}
if (lean::is_scalar(x_664)) {
 x_665 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_665 = x_664;
}
lean::cnstr_set(x_665, 0, x_9);
lean::cnstr_set(x_665, 1, x_663);
x_666 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_667 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean::inc(x_662);
x_668 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_666, x_667, x_662, x_2, x_665);
if (lean::obj_tag(x_668) == 0)
{
obj* x_669; obj* x_670; obj* x_671; obj* x_672; 
x_669 = lean::cnstr_get(x_668, 1);
lean::inc(x_669);
if (lean::is_exclusive(x_668)) {
 lean::cnstr_release(x_668, 0);
 lean::cnstr_release(x_668, 1);
 x_670 = x_668;
} else {
 lean::dec_ref(x_668);
 x_670 = lean::box(0);
}
if (lean::is_scalar(x_670)) {
 x_671 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_671 = x_670;
}
lean::cnstr_set(x_671, 0, x_9);
lean::cnstr_set(x_671, 1, x_669);
x_672 = l_Lean_IR_explicitBoxing(x_662, x_2, x_671);
if (lean::obj_tag(x_672) == 0)
{
obj* x_673; obj* x_674; obj* x_675; obj* x_676; obj* x_677; obj* x_678; obj* x_679; 
x_673 = lean::cnstr_get(x_672, 0);
lean::inc(x_673);
x_674 = lean::cnstr_get(x_672, 1);
lean::inc(x_674);
if (lean::is_exclusive(x_672)) {
 lean::cnstr_release(x_672, 0);
 lean::cnstr_release(x_672, 1);
 x_675 = x_672;
} else {
 lean::dec_ref(x_672);
 x_675 = lean::box(0);
}
if (lean::is_scalar(x_675)) {
 x_676 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_676 = x_675;
}
lean::cnstr_set(x_676, 0, x_9);
lean::cnstr_set(x_676, 1, x_674);
x_677 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_678 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean::inc(x_673);
x_679 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_677, x_678, x_673, x_2, x_676);
if (lean::obj_tag(x_679) == 0)
{
obj* x_680; obj* x_681; obj* x_682; obj* x_683; 
x_680 = lean::cnstr_get(x_679, 1);
lean::inc(x_680);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_release(x_679, 0);
 lean::cnstr_release(x_679, 1);
 x_681 = x_679;
} else {
 lean::dec_ref(x_679);
 x_681 = lean::box(0);
}
if (lean::is_scalar(x_681)) {
 x_682 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_682 = x_681;
}
lean::cnstr_set(x_682, 0, x_9);
lean::cnstr_set(x_682, 1, x_680);
x_683 = l_Lean_IR_explicitRC(x_673, x_2, x_682);
if (lean::obj_tag(x_683) == 0)
{
obj* x_684; obj* x_685; obj* x_686; obj* x_687; obj* x_688; obj* x_689; obj* x_690; 
x_684 = lean::cnstr_get(x_683, 0);
lean::inc(x_684);
x_685 = lean::cnstr_get(x_683, 1);
lean::inc(x_685);
if (lean::is_exclusive(x_683)) {
 lean::cnstr_release(x_683, 0);
 lean::cnstr_release(x_683, 1);
 x_686 = x_683;
} else {
 lean::dec_ref(x_683);
 x_686 = lean::box(0);
}
if (lean::is_scalar(x_686)) {
 x_687 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_687 = x_686;
}
lean::cnstr_set(x_687, 0, x_9);
lean::cnstr_set(x_687, 1, x_685);
x_688 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_689 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean::inc(x_684);
x_690 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_688, x_689, x_684, x_2, x_687);
if (lean::obj_tag(x_690) == 0)
{
obj* x_691; obj* x_692; obj* x_693; obj* x_694; obj* x_695; obj* x_696; obj* x_697; 
x_691 = lean::cnstr_get(x_690, 1);
lean::inc(x_691);
if (lean::is_exclusive(x_690)) {
 lean::cnstr_release(x_690, 0);
 lean::cnstr_release(x_690, 1);
 x_692 = x_690;
} else {
 lean::dec_ref(x_690);
 x_692 = lean::box(0);
}
if (lean::is_scalar(x_692)) {
 x_693 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_693 = x_692;
}
lean::cnstr_set(x_693, 0, x_9);
lean::cnstr_set(x_693, 1, x_691);
x_694 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_684);
x_695 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_696 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean::inc(x_694);
x_697 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_695, x_696, x_694, x_2, x_693);
if (lean::obj_tag(x_697) == 0)
{
obj* x_698; obj* x_699; obj* x_700; obj* x_701; obj* x_702; 
x_698 = lean::cnstr_get(x_697, 1);
lean::inc(x_698);
if (lean::is_exclusive(x_697)) {
 lean::cnstr_release(x_697, 0);
 lean::cnstr_release(x_697, 1);
 x_699 = x_697;
} else {
 lean::dec_ref(x_697);
 x_699 = lean::box(0);
}
if (lean::is_scalar(x_699)) {
 x_700 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_700 = x_699;
}
lean::cnstr_set(x_700, 0, x_9);
lean::cnstr_set(x_700, 1, x_698);
x_701 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_694);
lean::inc(x_701);
x_702 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_701, x_2, x_700);
if (lean::obj_tag(x_702) == 0)
{
obj* x_703; obj* x_704; obj* x_705; obj* x_706; obj* x_707; obj* x_708; 
x_703 = lean::cnstr_get(x_702, 1);
lean::inc(x_703);
if (lean::is_exclusive(x_702)) {
 lean::cnstr_release(x_702, 0);
 lean::cnstr_release(x_702, 1);
 x_704 = x_702;
} else {
 lean::dec_ref(x_702);
 x_704 = lean::box(0);
}
if (lean::is_scalar(x_704)) {
 x_705 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_705 = x_704;
}
lean::cnstr_set(x_705, 0, x_9);
lean::cnstr_set(x_705, 1, x_703);
x_706 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_707 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_701);
x_708 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_706, x_707, x_701, x_2, x_705);
if (lean::obj_tag(x_708) == 0)
{
obj* x_709; obj* x_710; obj* x_711; obj* x_712; 
x_709 = lean::cnstr_get(x_708, 1);
lean::inc(x_709);
if (lean::is_exclusive(x_708)) {
 lean::cnstr_release(x_708, 0);
 lean::cnstr_release(x_708, 1);
 x_710 = x_708;
} else {
 lean::dec_ref(x_708);
 x_710 = lean::box(0);
}
if (lean::is_scalar(x_710)) {
 x_711 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_711 = x_710;
}
lean::cnstr_set(x_711, 0, x_9);
lean::cnstr_set(x_711, 1, x_709);
lean::inc(x_701);
x_712 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_701, x_701, x_10, x_2, x_711);
if (lean::obj_tag(x_712) == 0)
{
obj* x_713; obj* x_714; obj* x_715; obj* x_716; 
x_713 = lean::cnstr_get(x_712, 1);
lean::inc(x_713);
if (lean::is_exclusive(x_712)) {
 lean::cnstr_release(x_712, 0);
 lean::cnstr_release(x_712, 1);
 x_714 = x_712;
} else {
 lean::dec_ref(x_712);
 x_714 = lean::box(0);
}
if (lean::is_scalar(x_714)) {
 x_715 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_715 = x_714;
}
lean::cnstr_set(x_715, 0, x_9);
lean::cnstr_set(x_715, 1, x_713);
x_716 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_701, x_10, x_2, x_715);
lean::dec(x_701);
if (lean::obj_tag(x_716) == 0)
{
obj* x_717; obj* x_718; obj* x_719; 
x_717 = lean::cnstr_get(x_716, 1);
lean::inc(x_717);
if (lean::is_exclusive(x_716)) {
 lean::cnstr_release(x_716, 0);
 lean::cnstr_release(x_716, 1);
 x_718 = x_716;
} else {
 lean::dec_ref(x_716);
 x_718 = lean::box(0);
}
if (lean::is_scalar(x_718)) {
 x_719 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_719 = x_718;
}
lean::cnstr_set(x_719, 0, x_9);
lean::cnstr_set(x_719, 1, x_717);
return x_719;
}
else
{
obj* x_720; obj* x_721; obj* x_722; obj* x_723; 
x_720 = lean::cnstr_get(x_716, 0);
lean::inc(x_720);
x_721 = lean::cnstr_get(x_716, 1);
lean::inc(x_721);
if (lean::is_exclusive(x_716)) {
 lean::cnstr_release(x_716, 0);
 lean::cnstr_release(x_716, 1);
 x_722 = x_716;
} else {
 lean::dec_ref(x_716);
 x_722 = lean::box(0);
}
if (lean::is_scalar(x_722)) {
 x_723 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_723 = x_722;
}
lean::cnstr_set(x_723, 0, x_720);
lean::cnstr_set(x_723, 1, x_721);
return x_723;
}
}
else
{
obj* x_724; obj* x_725; obj* x_726; obj* x_727; 
lean::dec(x_701);
x_724 = lean::cnstr_get(x_712, 0);
lean::inc(x_724);
x_725 = lean::cnstr_get(x_712, 1);
lean::inc(x_725);
if (lean::is_exclusive(x_712)) {
 lean::cnstr_release(x_712, 0);
 lean::cnstr_release(x_712, 1);
 x_726 = x_712;
} else {
 lean::dec_ref(x_712);
 x_726 = lean::box(0);
}
if (lean::is_scalar(x_726)) {
 x_727 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_727 = x_726;
}
lean::cnstr_set(x_727, 0, x_724);
lean::cnstr_set(x_727, 1, x_725);
return x_727;
}
}
else
{
obj* x_728; obj* x_729; obj* x_730; obj* x_731; 
lean::dec(x_701);
x_728 = lean::cnstr_get(x_708, 0);
lean::inc(x_728);
x_729 = lean::cnstr_get(x_708, 1);
lean::inc(x_729);
if (lean::is_exclusive(x_708)) {
 lean::cnstr_release(x_708, 0);
 lean::cnstr_release(x_708, 1);
 x_730 = x_708;
} else {
 lean::dec_ref(x_708);
 x_730 = lean::box(0);
}
if (lean::is_scalar(x_730)) {
 x_731 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_731 = x_730;
}
lean::cnstr_set(x_731, 0, x_728);
lean::cnstr_set(x_731, 1, x_729);
return x_731;
}
}
else
{
obj* x_732; obj* x_733; obj* x_734; obj* x_735; 
lean::dec(x_701);
x_732 = lean::cnstr_get(x_702, 0);
lean::inc(x_732);
x_733 = lean::cnstr_get(x_702, 1);
lean::inc(x_733);
if (lean::is_exclusive(x_702)) {
 lean::cnstr_release(x_702, 0);
 lean::cnstr_release(x_702, 1);
 x_734 = x_702;
} else {
 lean::dec_ref(x_702);
 x_734 = lean::box(0);
}
if (lean::is_scalar(x_734)) {
 x_735 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_735 = x_734;
}
lean::cnstr_set(x_735, 0, x_732);
lean::cnstr_set(x_735, 1, x_733);
return x_735;
}
}
else
{
obj* x_736; obj* x_737; obj* x_738; obj* x_739; 
lean::dec(x_694);
x_736 = lean::cnstr_get(x_697, 0);
lean::inc(x_736);
x_737 = lean::cnstr_get(x_697, 1);
lean::inc(x_737);
if (lean::is_exclusive(x_697)) {
 lean::cnstr_release(x_697, 0);
 lean::cnstr_release(x_697, 1);
 x_738 = x_697;
} else {
 lean::dec_ref(x_697);
 x_738 = lean::box(0);
}
if (lean::is_scalar(x_738)) {
 x_739 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_739 = x_738;
}
lean::cnstr_set(x_739, 0, x_736);
lean::cnstr_set(x_739, 1, x_737);
return x_739;
}
}
else
{
obj* x_740; obj* x_741; obj* x_742; obj* x_743; 
lean::dec(x_684);
x_740 = lean::cnstr_get(x_690, 0);
lean::inc(x_740);
x_741 = lean::cnstr_get(x_690, 1);
lean::inc(x_741);
if (lean::is_exclusive(x_690)) {
 lean::cnstr_release(x_690, 0);
 lean::cnstr_release(x_690, 1);
 x_742 = x_690;
} else {
 lean::dec_ref(x_690);
 x_742 = lean::box(0);
}
if (lean::is_scalar(x_742)) {
 x_743 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_743 = x_742;
}
lean::cnstr_set(x_743, 0, x_740);
lean::cnstr_set(x_743, 1, x_741);
return x_743;
}
}
else
{
obj* x_744; obj* x_745; obj* x_746; obj* x_747; 
x_744 = lean::cnstr_get(x_683, 0);
lean::inc(x_744);
x_745 = lean::cnstr_get(x_683, 1);
lean::inc(x_745);
if (lean::is_exclusive(x_683)) {
 lean::cnstr_release(x_683, 0);
 lean::cnstr_release(x_683, 1);
 x_746 = x_683;
} else {
 lean::dec_ref(x_683);
 x_746 = lean::box(0);
}
if (lean::is_scalar(x_746)) {
 x_747 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_747 = x_746;
}
lean::cnstr_set(x_747, 0, x_744);
lean::cnstr_set(x_747, 1, x_745);
return x_747;
}
}
else
{
obj* x_748; obj* x_749; obj* x_750; obj* x_751; 
lean::dec(x_673);
x_748 = lean::cnstr_get(x_679, 0);
lean::inc(x_748);
x_749 = lean::cnstr_get(x_679, 1);
lean::inc(x_749);
if (lean::is_exclusive(x_679)) {
 lean::cnstr_release(x_679, 0);
 lean::cnstr_release(x_679, 1);
 x_750 = x_679;
} else {
 lean::dec_ref(x_679);
 x_750 = lean::box(0);
}
if (lean::is_scalar(x_750)) {
 x_751 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_751 = x_750;
}
lean::cnstr_set(x_751, 0, x_748);
lean::cnstr_set(x_751, 1, x_749);
return x_751;
}
}
else
{
obj* x_752; obj* x_753; obj* x_754; obj* x_755; 
x_752 = lean::cnstr_get(x_672, 0);
lean::inc(x_752);
x_753 = lean::cnstr_get(x_672, 1);
lean::inc(x_753);
if (lean::is_exclusive(x_672)) {
 lean::cnstr_release(x_672, 0);
 lean::cnstr_release(x_672, 1);
 x_754 = x_672;
} else {
 lean::dec_ref(x_672);
 x_754 = lean::box(0);
}
if (lean::is_scalar(x_754)) {
 x_755 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_755 = x_754;
}
lean::cnstr_set(x_755, 0, x_752);
lean::cnstr_set(x_755, 1, x_753);
return x_755;
}
}
else
{
obj* x_756; obj* x_757; obj* x_758; obj* x_759; 
lean::dec(x_662);
x_756 = lean::cnstr_get(x_668, 0);
lean::inc(x_756);
x_757 = lean::cnstr_get(x_668, 1);
lean::inc(x_757);
if (lean::is_exclusive(x_668)) {
 lean::cnstr_release(x_668, 0);
 lean::cnstr_release(x_668, 1);
 x_758 = x_668;
} else {
 lean::dec_ref(x_668);
 x_758 = lean::box(0);
}
if (lean::is_scalar(x_758)) {
 x_759 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_759 = x_758;
}
lean::cnstr_set(x_759, 0, x_756);
lean::cnstr_set(x_759, 1, x_757);
return x_759;
}
}
else
{
obj* x_760; obj* x_761; obj* x_762; obj* x_763; 
x_760 = lean::cnstr_get(x_661, 0);
lean::inc(x_760);
x_761 = lean::cnstr_get(x_661, 1);
lean::inc(x_761);
if (lean::is_exclusive(x_661)) {
 lean::cnstr_release(x_661, 0);
 lean::cnstr_release(x_661, 1);
 x_762 = x_661;
} else {
 lean::dec_ref(x_661);
 x_762 = lean::box(0);
}
if (lean::is_scalar(x_762)) {
 x_763 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_763 = x_762;
}
lean::cnstr_set(x_763, 0, x_760);
lean::cnstr_set(x_763, 1, x_761);
return x_763;
}
}
}
else
{
uint8 x_764; 
lean::dec(x_32);
x_764 = !lean::is_exclusive(x_35);
if (x_764 == 0)
{
return x_35;
}
else
{
obj* x_765; obj* x_766; obj* x_767; 
x_765 = lean::cnstr_get(x_35, 0);
x_766 = lean::cnstr_get(x_35, 1);
lean::inc(x_766);
lean::inc(x_765);
lean::dec(x_35);
x_767 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_767, 0, x_765);
lean::cnstr_set(x_767, 1, x_766);
return x_767;
}
}
}
else
{
obj* x_768; obj* x_769; obj* x_770; obj* x_771; obj* x_772; obj* x_773; 
x_768 = lean::cnstr_get(x_29, 1);
lean::inc(x_768);
lean::dec(x_29);
x_769 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_769, 0, x_9);
lean::cnstr_set(x_769, 1, x_768);
x_770 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(x_10, x_26);
x_771 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
x_772 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean::inc(x_770);
x_773 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_771, x_772, x_770, x_2, x_769);
if (lean::obj_tag(x_773) == 0)
{
obj* x_774; obj* x_775; obj* x_776; obj* x_777; obj* x_778; 
x_774 = lean::cnstr_get(x_773, 1);
lean::inc(x_774);
if (lean::is_exclusive(x_773)) {
 lean::cnstr_release(x_773, 0);
 lean::cnstr_release(x_773, 1);
 x_775 = x_773;
} else {
 lean::dec_ref(x_773);
 x_775 = lean::box(0);
}
if (lean::is_scalar(x_775)) {
 x_776 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_776 = x_775;
}
lean::cnstr_set(x_776, 0, x_9);
lean::cnstr_set(x_776, 1, x_774);
x_777 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_770);
x_778 = l_Lean_IR_inferBorrow(x_777, x_2, x_776);
if (lean::obj_tag(x_778) == 0)
{
obj* x_779; obj* x_780; obj* x_781; obj* x_782; obj* x_783; obj* x_784; obj* x_785; 
x_779 = lean::cnstr_get(x_778, 0);
lean::inc(x_779);
x_780 = lean::cnstr_get(x_778, 1);
lean::inc(x_780);
if (lean::is_exclusive(x_778)) {
 lean::cnstr_release(x_778, 0);
 lean::cnstr_release(x_778, 1);
 x_781 = x_778;
} else {
 lean::dec_ref(x_778);
 x_781 = lean::box(0);
}
if (lean::is_scalar(x_781)) {
 x_782 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_782 = x_781;
}
lean::cnstr_set(x_782, 0, x_9);
lean::cnstr_set(x_782, 1, x_780);
x_783 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_784 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean::inc(x_779);
x_785 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_783, x_784, x_779, x_2, x_782);
if (lean::obj_tag(x_785) == 0)
{
obj* x_786; obj* x_787; obj* x_788; obj* x_789; 
x_786 = lean::cnstr_get(x_785, 1);
lean::inc(x_786);
if (lean::is_exclusive(x_785)) {
 lean::cnstr_release(x_785, 0);
 lean::cnstr_release(x_785, 1);
 x_787 = x_785;
} else {
 lean::dec_ref(x_785);
 x_787 = lean::box(0);
}
if (lean::is_scalar(x_787)) {
 x_788 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_788 = x_787;
}
lean::cnstr_set(x_788, 0, x_9);
lean::cnstr_set(x_788, 1, x_786);
x_789 = l_Lean_IR_explicitBoxing(x_779, x_2, x_788);
if (lean::obj_tag(x_789) == 0)
{
obj* x_790; obj* x_791; obj* x_792; obj* x_793; obj* x_794; obj* x_795; obj* x_796; 
x_790 = lean::cnstr_get(x_789, 0);
lean::inc(x_790);
x_791 = lean::cnstr_get(x_789, 1);
lean::inc(x_791);
if (lean::is_exclusive(x_789)) {
 lean::cnstr_release(x_789, 0);
 lean::cnstr_release(x_789, 1);
 x_792 = x_789;
} else {
 lean::dec_ref(x_789);
 x_792 = lean::box(0);
}
if (lean::is_scalar(x_792)) {
 x_793 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_793 = x_792;
}
lean::cnstr_set(x_793, 0, x_9);
lean::cnstr_set(x_793, 1, x_791);
x_794 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_795 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean::inc(x_790);
x_796 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_794, x_795, x_790, x_2, x_793);
if (lean::obj_tag(x_796) == 0)
{
obj* x_797; obj* x_798; obj* x_799; obj* x_800; 
x_797 = lean::cnstr_get(x_796, 1);
lean::inc(x_797);
if (lean::is_exclusive(x_796)) {
 lean::cnstr_release(x_796, 0);
 lean::cnstr_release(x_796, 1);
 x_798 = x_796;
} else {
 lean::dec_ref(x_796);
 x_798 = lean::box(0);
}
if (lean::is_scalar(x_798)) {
 x_799 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_799 = x_798;
}
lean::cnstr_set(x_799, 0, x_9);
lean::cnstr_set(x_799, 1, x_797);
x_800 = l_Lean_IR_explicitRC(x_790, x_2, x_799);
if (lean::obj_tag(x_800) == 0)
{
obj* x_801; obj* x_802; obj* x_803; obj* x_804; obj* x_805; obj* x_806; obj* x_807; 
x_801 = lean::cnstr_get(x_800, 0);
lean::inc(x_801);
x_802 = lean::cnstr_get(x_800, 1);
lean::inc(x_802);
if (lean::is_exclusive(x_800)) {
 lean::cnstr_release(x_800, 0);
 lean::cnstr_release(x_800, 1);
 x_803 = x_800;
} else {
 lean::dec_ref(x_800);
 x_803 = lean::box(0);
}
if (lean::is_scalar(x_803)) {
 x_804 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_804 = x_803;
}
lean::cnstr_set(x_804, 0, x_9);
lean::cnstr_set(x_804, 1, x_802);
x_805 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_806 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean::inc(x_801);
x_807 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_805, x_806, x_801, x_2, x_804);
if (lean::obj_tag(x_807) == 0)
{
obj* x_808; obj* x_809; obj* x_810; obj* x_811; obj* x_812; obj* x_813; obj* x_814; 
x_808 = lean::cnstr_get(x_807, 1);
lean::inc(x_808);
if (lean::is_exclusive(x_807)) {
 lean::cnstr_release(x_807, 0);
 lean::cnstr_release(x_807, 1);
 x_809 = x_807;
} else {
 lean::dec_ref(x_807);
 x_809 = lean::box(0);
}
if (lean::is_scalar(x_809)) {
 x_810 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_810 = x_809;
}
lean::cnstr_set(x_810, 0, x_9);
lean::cnstr_set(x_810, 1, x_808);
x_811 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_801);
x_812 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_813 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean::inc(x_811);
x_814 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_812, x_813, x_811, x_2, x_810);
if (lean::obj_tag(x_814) == 0)
{
obj* x_815; obj* x_816; obj* x_817; obj* x_818; obj* x_819; 
x_815 = lean::cnstr_get(x_814, 1);
lean::inc(x_815);
if (lean::is_exclusive(x_814)) {
 lean::cnstr_release(x_814, 0);
 lean::cnstr_release(x_814, 1);
 x_816 = x_814;
} else {
 lean::dec_ref(x_814);
 x_816 = lean::box(0);
}
if (lean::is_scalar(x_816)) {
 x_817 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_817 = x_816;
}
lean::cnstr_set(x_817, 0, x_9);
lean::cnstr_set(x_817, 1, x_815);
x_818 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_811);
lean::inc(x_818);
x_819 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_818, x_2, x_817);
if (lean::obj_tag(x_819) == 0)
{
obj* x_820; obj* x_821; obj* x_822; obj* x_823; obj* x_824; obj* x_825; 
x_820 = lean::cnstr_get(x_819, 1);
lean::inc(x_820);
if (lean::is_exclusive(x_819)) {
 lean::cnstr_release(x_819, 0);
 lean::cnstr_release(x_819, 1);
 x_821 = x_819;
} else {
 lean::dec_ref(x_819);
 x_821 = lean::box(0);
}
if (lean::is_scalar(x_821)) {
 x_822 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_822 = x_821;
}
lean::cnstr_set(x_822, 0, x_9);
lean::cnstr_set(x_822, 1, x_820);
x_823 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_824 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_818);
x_825 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_823, x_824, x_818, x_2, x_822);
if (lean::obj_tag(x_825) == 0)
{
obj* x_826; obj* x_827; obj* x_828; obj* x_829; 
x_826 = lean::cnstr_get(x_825, 1);
lean::inc(x_826);
if (lean::is_exclusive(x_825)) {
 lean::cnstr_release(x_825, 0);
 lean::cnstr_release(x_825, 1);
 x_827 = x_825;
} else {
 lean::dec_ref(x_825);
 x_827 = lean::box(0);
}
if (lean::is_scalar(x_827)) {
 x_828 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_828 = x_827;
}
lean::cnstr_set(x_828, 0, x_9);
lean::cnstr_set(x_828, 1, x_826);
lean::inc(x_818);
x_829 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_818, x_818, x_10, x_2, x_828);
if (lean::obj_tag(x_829) == 0)
{
obj* x_830; obj* x_831; obj* x_832; obj* x_833; 
x_830 = lean::cnstr_get(x_829, 1);
lean::inc(x_830);
if (lean::is_exclusive(x_829)) {
 lean::cnstr_release(x_829, 0);
 lean::cnstr_release(x_829, 1);
 x_831 = x_829;
} else {
 lean::dec_ref(x_829);
 x_831 = lean::box(0);
}
if (lean::is_scalar(x_831)) {
 x_832 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_832 = x_831;
}
lean::cnstr_set(x_832, 0, x_9);
lean::cnstr_set(x_832, 1, x_830);
x_833 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_818, x_10, x_2, x_832);
lean::dec(x_818);
if (lean::obj_tag(x_833) == 0)
{
obj* x_834; obj* x_835; obj* x_836; 
x_834 = lean::cnstr_get(x_833, 1);
lean::inc(x_834);
if (lean::is_exclusive(x_833)) {
 lean::cnstr_release(x_833, 0);
 lean::cnstr_release(x_833, 1);
 x_835 = x_833;
} else {
 lean::dec_ref(x_833);
 x_835 = lean::box(0);
}
if (lean::is_scalar(x_835)) {
 x_836 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_836 = x_835;
}
lean::cnstr_set(x_836, 0, x_9);
lean::cnstr_set(x_836, 1, x_834);
return x_836;
}
else
{
obj* x_837; obj* x_838; obj* x_839; obj* x_840; 
x_837 = lean::cnstr_get(x_833, 0);
lean::inc(x_837);
x_838 = lean::cnstr_get(x_833, 1);
lean::inc(x_838);
if (lean::is_exclusive(x_833)) {
 lean::cnstr_release(x_833, 0);
 lean::cnstr_release(x_833, 1);
 x_839 = x_833;
} else {
 lean::dec_ref(x_833);
 x_839 = lean::box(0);
}
if (lean::is_scalar(x_839)) {
 x_840 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_840 = x_839;
}
lean::cnstr_set(x_840, 0, x_837);
lean::cnstr_set(x_840, 1, x_838);
return x_840;
}
}
else
{
obj* x_841; obj* x_842; obj* x_843; obj* x_844; 
lean::dec(x_818);
x_841 = lean::cnstr_get(x_829, 0);
lean::inc(x_841);
x_842 = lean::cnstr_get(x_829, 1);
lean::inc(x_842);
if (lean::is_exclusive(x_829)) {
 lean::cnstr_release(x_829, 0);
 lean::cnstr_release(x_829, 1);
 x_843 = x_829;
} else {
 lean::dec_ref(x_829);
 x_843 = lean::box(0);
}
if (lean::is_scalar(x_843)) {
 x_844 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_844 = x_843;
}
lean::cnstr_set(x_844, 0, x_841);
lean::cnstr_set(x_844, 1, x_842);
return x_844;
}
}
else
{
obj* x_845; obj* x_846; obj* x_847; obj* x_848; 
lean::dec(x_818);
x_845 = lean::cnstr_get(x_825, 0);
lean::inc(x_845);
x_846 = lean::cnstr_get(x_825, 1);
lean::inc(x_846);
if (lean::is_exclusive(x_825)) {
 lean::cnstr_release(x_825, 0);
 lean::cnstr_release(x_825, 1);
 x_847 = x_825;
} else {
 lean::dec_ref(x_825);
 x_847 = lean::box(0);
}
if (lean::is_scalar(x_847)) {
 x_848 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_848 = x_847;
}
lean::cnstr_set(x_848, 0, x_845);
lean::cnstr_set(x_848, 1, x_846);
return x_848;
}
}
else
{
obj* x_849; obj* x_850; obj* x_851; obj* x_852; 
lean::dec(x_818);
x_849 = lean::cnstr_get(x_819, 0);
lean::inc(x_849);
x_850 = lean::cnstr_get(x_819, 1);
lean::inc(x_850);
if (lean::is_exclusive(x_819)) {
 lean::cnstr_release(x_819, 0);
 lean::cnstr_release(x_819, 1);
 x_851 = x_819;
} else {
 lean::dec_ref(x_819);
 x_851 = lean::box(0);
}
if (lean::is_scalar(x_851)) {
 x_852 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_852 = x_851;
}
lean::cnstr_set(x_852, 0, x_849);
lean::cnstr_set(x_852, 1, x_850);
return x_852;
}
}
else
{
obj* x_853; obj* x_854; obj* x_855; obj* x_856; 
lean::dec(x_811);
x_853 = lean::cnstr_get(x_814, 0);
lean::inc(x_853);
x_854 = lean::cnstr_get(x_814, 1);
lean::inc(x_854);
if (lean::is_exclusive(x_814)) {
 lean::cnstr_release(x_814, 0);
 lean::cnstr_release(x_814, 1);
 x_855 = x_814;
} else {
 lean::dec_ref(x_814);
 x_855 = lean::box(0);
}
if (lean::is_scalar(x_855)) {
 x_856 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_856 = x_855;
}
lean::cnstr_set(x_856, 0, x_853);
lean::cnstr_set(x_856, 1, x_854);
return x_856;
}
}
else
{
obj* x_857; obj* x_858; obj* x_859; obj* x_860; 
lean::dec(x_801);
x_857 = lean::cnstr_get(x_807, 0);
lean::inc(x_857);
x_858 = lean::cnstr_get(x_807, 1);
lean::inc(x_858);
if (lean::is_exclusive(x_807)) {
 lean::cnstr_release(x_807, 0);
 lean::cnstr_release(x_807, 1);
 x_859 = x_807;
} else {
 lean::dec_ref(x_807);
 x_859 = lean::box(0);
}
if (lean::is_scalar(x_859)) {
 x_860 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_860 = x_859;
}
lean::cnstr_set(x_860, 0, x_857);
lean::cnstr_set(x_860, 1, x_858);
return x_860;
}
}
else
{
obj* x_861; obj* x_862; obj* x_863; obj* x_864; 
x_861 = lean::cnstr_get(x_800, 0);
lean::inc(x_861);
x_862 = lean::cnstr_get(x_800, 1);
lean::inc(x_862);
if (lean::is_exclusive(x_800)) {
 lean::cnstr_release(x_800, 0);
 lean::cnstr_release(x_800, 1);
 x_863 = x_800;
} else {
 lean::dec_ref(x_800);
 x_863 = lean::box(0);
}
if (lean::is_scalar(x_863)) {
 x_864 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_864 = x_863;
}
lean::cnstr_set(x_864, 0, x_861);
lean::cnstr_set(x_864, 1, x_862);
return x_864;
}
}
else
{
obj* x_865; obj* x_866; obj* x_867; obj* x_868; 
lean::dec(x_790);
x_865 = lean::cnstr_get(x_796, 0);
lean::inc(x_865);
x_866 = lean::cnstr_get(x_796, 1);
lean::inc(x_866);
if (lean::is_exclusive(x_796)) {
 lean::cnstr_release(x_796, 0);
 lean::cnstr_release(x_796, 1);
 x_867 = x_796;
} else {
 lean::dec_ref(x_796);
 x_867 = lean::box(0);
}
if (lean::is_scalar(x_867)) {
 x_868 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_868 = x_867;
}
lean::cnstr_set(x_868, 0, x_865);
lean::cnstr_set(x_868, 1, x_866);
return x_868;
}
}
else
{
obj* x_869; obj* x_870; obj* x_871; obj* x_872; 
x_869 = lean::cnstr_get(x_789, 0);
lean::inc(x_869);
x_870 = lean::cnstr_get(x_789, 1);
lean::inc(x_870);
if (lean::is_exclusive(x_789)) {
 lean::cnstr_release(x_789, 0);
 lean::cnstr_release(x_789, 1);
 x_871 = x_789;
} else {
 lean::dec_ref(x_789);
 x_871 = lean::box(0);
}
if (lean::is_scalar(x_871)) {
 x_872 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_872 = x_871;
}
lean::cnstr_set(x_872, 0, x_869);
lean::cnstr_set(x_872, 1, x_870);
return x_872;
}
}
else
{
obj* x_873; obj* x_874; obj* x_875; obj* x_876; 
lean::dec(x_779);
x_873 = lean::cnstr_get(x_785, 0);
lean::inc(x_873);
x_874 = lean::cnstr_get(x_785, 1);
lean::inc(x_874);
if (lean::is_exclusive(x_785)) {
 lean::cnstr_release(x_785, 0);
 lean::cnstr_release(x_785, 1);
 x_875 = x_785;
} else {
 lean::dec_ref(x_785);
 x_875 = lean::box(0);
}
if (lean::is_scalar(x_875)) {
 x_876 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_876 = x_875;
}
lean::cnstr_set(x_876, 0, x_873);
lean::cnstr_set(x_876, 1, x_874);
return x_876;
}
}
else
{
obj* x_877; obj* x_878; obj* x_879; obj* x_880; 
x_877 = lean::cnstr_get(x_778, 0);
lean::inc(x_877);
x_878 = lean::cnstr_get(x_778, 1);
lean::inc(x_878);
if (lean::is_exclusive(x_778)) {
 lean::cnstr_release(x_778, 0);
 lean::cnstr_release(x_778, 1);
 x_879 = x_778;
} else {
 lean::dec_ref(x_778);
 x_879 = lean::box(0);
}
if (lean::is_scalar(x_879)) {
 x_880 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_880 = x_879;
}
lean::cnstr_set(x_880, 0, x_877);
lean::cnstr_set(x_880, 1, x_878);
return x_880;
}
}
else
{
obj* x_881; obj* x_882; obj* x_883; obj* x_884; 
lean::dec(x_770);
x_881 = lean::cnstr_get(x_773, 0);
lean::inc(x_881);
x_882 = lean::cnstr_get(x_773, 1);
lean::inc(x_882);
if (lean::is_exclusive(x_773)) {
 lean::cnstr_release(x_773, 0);
 lean::cnstr_release(x_773, 1);
 x_883 = x_773;
} else {
 lean::dec_ref(x_773);
 x_883 = lean::box(0);
}
if (lean::is_scalar(x_883)) {
 x_884 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_884 = x_883;
}
lean::cnstr_set(x_884, 0, x_881);
lean::cnstr_set(x_884, 1, x_882);
return x_884;
}
}
}
else
{
uint8 x_885; 
lean::dec(x_26);
x_885 = !lean::is_exclusive(x_29);
if (x_885 == 0)
{
return x_29;
}
else
{
obj* x_886; obj* x_887; obj* x_888; 
x_886 = lean::cnstr_get(x_29, 0);
x_887 = lean::cnstr_get(x_29, 1);
lean::inc(x_887);
lean::inc(x_886);
lean::dec(x_29);
x_888 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_888, 0, x_886);
lean::cnstr_set(x_888, 1, x_887);
return x_888;
}
}
}
else
{
obj* x_889; obj* x_890; obj* x_891; obj* x_892; obj* x_893; obj* x_894; 
x_889 = lean::cnstr_get(x_23, 1);
lean::inc(x_889);
lean::dec(x_23);
x_890 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_890, 0, x_9);
lean::cnstr_set(x_890, 1, x_889);
x_891 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(x_10, x_20);
x_892 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
x_893 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
lean::inc(x_891);
x_894 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_892, x_893, x_891, x_2, x_890);
if (lean::obj_tag(x_894) == 0)
{
obj* x_895; obj* x_896; obj* x_897; obj* x_898; obj* x_899; obj* x_900; obj* x_901; 
x_895 = lean::cnstr_get(x_894, 1);
lean::inc(x_895);
if (lean::is_exclusive(x_894)) {
 lean::cnstr_release(x_894, 0);
 lean::cnstr_release(x_894, 1);
 x_896 = x_894;
} else {
 lean::dec_ref(x_894);
 x_896 = lean::box(0);
}
if (lean::is_scalar(x_896)) {
 x_897 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_897 = x_896;
}
lean::cnstr_set(x_897, 0, x_9);
lean::cnstr_set(x_897, 1, x_895);
x_898 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(x_10, x_891);
x_899 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
x_900 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean::inc(x_898);
x_901 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_899, x_900, x_898, x_2, x_897);
if (lean::obj_tag(x_901) == 0)
{
obj* x_902; obj* x_903; obj* x_904; obj* x_905; obj* x_906; 
x_902 = lean::cnstr_get(x_901, 1);
lean::inc(x_902);
if (lean::is_exclusive(x_901)) {
 lean::cnstr_release(x_901, 0);
 lean::cnstr_release(x_901, 1);
 x_903 = x_901;
} else {
 lean::dec_ref(x_901);
 x_903 = lean::box(0);
}
if (lean::is_scalar(x_903)) {
 x_904 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_904 = x_903;
}
lean::cnstr_set(x_904, 0, x_9);
lean::cnstr_set(x_904, 1, x_902);
x_905 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_898);
x_906 = l_Lean_IR_inferBorrow(x_905, x_2, x_904);
if (lean::obj_tag(x_906) == 0)
{
obj* x_907; obj* x_908; obj* x_909; obj* x_910; obj* x_911; obj* x_912; obj* x_913; 
x_907 = lean::cnstr_get(x_906, 0);
lean::inc(x_907);
x_908 = lean::cnstr_get(x_906, 1);
lean::inc(x_908);
if (lean::is_exclusive(x_906)) {
 lean::cnstr_release(x_906, 0);
 lean::cnstr_release(x_906, 1);
 x_909 = x_906;
} else {
 lean::dec_ref(x_906);
 x_909 = lean::box(0);
}
if (lean::is_scalar(x_909)) {
 x_910 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_910 = x_909;
}
lean::cnstr_set(x_910, 0, x_9);
lean::cnstr_set(x_910, 1, x_908);
x_911 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_912 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean::inc(x_907);
x_913 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_911, x_912, x_907, x_2, x_910);
if (lean::obj_tag(x_913) == 0)
{
obj* x_914; obj* x_915; obj* x_916; obj* x_917; 
x_914 = lean::cnstr_get(x_913, 1);
lean::inc(x_914);
if (lean::is_exclusive(x_913)) {
 lean::cnstr_release(x_913, 0);
 lean::cnstr_release(x_913, 1);
 x_915 = x_913;
} else {
 lean::dec_ref(x_913);
 x_915 = lean::box(0);
}
if (lean::is_scalar(x_915)) {
 x_916 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_916 = x_915;
}
lean::cnstr_set(x_916, 0, x_9);
lean::cnstr_set(x_916, 1, x_914);
x_917 = l_Lean_IR_explicitBoxing(x_907, x_2, x_916);
if (lean::obj_tag(x_917) == 0)
{
obj* x_918; obj* x_919; obj* x_920; obj* x_921; obj* x_922; obj* x_923; obj* x_924; 
x_918 = lean::cnstr_get(x_917, 0);
lean::inc(x_918);
x_919 = lean::cnstr_get(x_917, 1);
lean::inc(x_919);
if (lean::is_exclusive(x_917)) {
 lean::cnstr_release(x_917, 0);
 lean::cnstr_release(x_917, 1);
 x_920 = x_917;
} else {
 lean::dec_ref(x_917);
 x_920 = lean::box(0);
}
if (lean::is_scalar(x_920)) {
 x_921 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_921 = x_920;
}
lean::cnstr_set(x_921, 0, x_9);
lean::cnstr_set(x_921, 1, x_919);
x_922 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_923 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean::inc(x_918);
x_924 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_922, x_923, x_918, x_2, x_921);
if (lean::obj_tag(x_924) == 0)
{
obj* x_925; obj* x_926; obj* x_927; obj* x_928; 
x_925 = lean::cnstr_get(x_924, 1);
lean::inc(x_925);
if (lean::is_exclusive(x_924)) {
 lean::cnstr_release(x_924, 0);
 lean::cnstr_release(x_924, 1);
 x_926 = x_924;
} else {
 lean::dec_ref(x_924);
 x_926 = lean::box(0);
}
if (lean::is_scalar(x_926)) {
 x_927 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_927 = x_926;
}
lean::cnstr_set(x_927, 0, x_9);
lean::cnstr_set(x_927, 1, x_925);
x_928 = l_Lean_IR_explicitRC(x_918, x_2, x_927);
if (lean::obj_tag(x_928) == 0)
{
obj* x_929; obj* x_930; obj* x_931; obj* x_932; obj* x_933; obj* x_934; obj* x_935; 
x_929 = lean::cnstr_get(x_928, 0);
lean::inc(x_929);
x_930 = lean::cnstr_get(x_928, 1);
lean::inc(x_930);
if (lean::is_exclusive(x_928)) {
 lean::cnstr_release(x_928, 0);
 lean::cnstr_release(x_928, 1);
 x_931 = x_928;
} else {
 lean::dec_ref(x_928);
 x_931 = lean::box(0);
}
if (lean::is_scalar(x_931)) {
 x_932 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_932 = x_931;
}
lean::cnstr_set(x_932, 0, x_9);
lean::cnstr_set(x_932, 1, x_930);
x_933 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_934 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean::inc(x_929);
x_935 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_933, x_934, x_929, x_2, x_932);
if (lean::obj_tag(x_935) == 0)
{
obj* x_936; obj* x_937; obj* x_938; obj* x_939; obj* x_940; obj* x_941; obj* x_942; 
x_936 = lean::cnstr_get(x_935, 1);
lean::inc(x_936);
if (lean::is_exclusive(x_935)) {
 lean::cnstr_release(x_935, 0);
 lean::cnstr_release(x_935, 1);
 x_937 = x_935;
} else {
 lean::dec_ref(x_935);
 x_937 = lean::box(0);
}
if (lean::is_scalar(x_937)) {
 x_938 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_938 = x_937;
}
lean::cnstr_set(x_938, 0, x_9);
lean::cnstr_set(x_938, 1, x_936);
x_939 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_929);
x_940 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_941 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean::inc(x_939);
x_942 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_940, x_941, x_939, x_2, x_938);
if (lean::obj_tag(x_942) == 0)
{
obj* x_943; obj* x_944; obj* x_945; obj* x_946; obj* x_947; 
x_943 = lean::cnstr_get(x_942, 1);
lean::inc(x_943);
if (lean::is_exclusive(x_942)) {
 lean::cnstr_release(x_942, 0);
 lean::cnstr_release(x_942, 1);
 x_944 = x_942;
} else {
 lean::dec_ref(x_942);
 x_944 = lean::box(0);
}
if (lean::is_scalar(x_944)) {
 x_945 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_945 = x_944;
}
lean::cnstr_set(x_945, 0, x_9);
lean::cnstr_set(x_945, 1, x_943);
x_946 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_939);
lean::inc(x_946);
x_947 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_946, x_2, x_945);
if (lean::obj_tag(x_947) == 0)
{
obj* x_948; obj* x_949; obj* x_950; obj* x_951; obj* x_952; obj* x_953; 
x_948 = lean::cnstr_get(x_947, 1);
lean::inc(x_948);
if (lean::is_exclusive(x_947)) {
 lean::cnstr_release(x_947, 0);
 lean::cnstr_release(x_947, 1);
 x_949 = x_947;
} else {
 lean::dec_ref(x_947);
 x_949 = lean::box(0);
}
if (lean::is_scalar(x_949)) {
 x_950 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_950 = x_949;
}
lean::cnstr_set(x_950, 0, x_9);
lean::cnstr_set(x_950, 1, x_948);
x_951 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_952 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_946);
x_953 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_951, x_952, x_946, x_2, x_950);
if (lean::obj_tag(x_953) == 0)
{
obj* x_954; obj* x_955; obj* x_956; obj* x_957; 
x_954 = lean::cnstr_get(x_953, 1);
lean::inc(x_954);
if (lean::is_exclusive(x_953)) {
 lean::cnstr_release(x_953, 0);
 lean::cnstr_release(x_953, 1);
 x_955 = x_953;
} else {
 lean::dec_ref(x_953);
 x_955 = lean::box(0);
}
if (lean::is_scalar(x_955)) {
 x_956 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_956 = x_955;
}
lean::cnstr_set(x_956, 0, x_9);
lean::cnstr_set(x_956, 1, x_954);
lean::inc(x_946);
x_957 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_946, x_946, x_10, x_2, x_956);
if (lean::obj_tag(x_957) == 0)
{
obj* x_958; obj* x_959; obj* x_960; obj* x_961; 
x_958 = lean::cnstr_get(x_957, 1);
lean::inc(x_958);
if (lean::is_exclusive(x_957)) {
 lean::cnstr_release(x_957, 0);
 lean::cnstr_release(x_957, 1);
 x_959 = x_957;
} else {
 lean::dec_ref(x_957);
 x_959 = lean::box(0);
}
if (lean::is_scalar(x_959)) {
 x_960 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_960 = x_959;
}
lean::cnstr_set(x_960, 0, x_9);
lean::cnstr_set(x_960, 1, x_958);
x_961 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_946, x_10, x_2, x_960);
lean::dec(x_946);
if (lean::obj_tag(x_961) == 0)
{
obj* x_962; obj* x_963; obj* x_964; 
x_962 = lean::cnstr_get(x_961, 1);
lean::inc(x_962);
if (lean::is_exclusive(x_961)) {
 lean::cnstr_release(x_961, 0);
 lean::cnstr_release(x_961, 1);
 x_963 = x_961;
} else {
 lean::dec_ref(x_961);
 x_963 = lean::box(0);
}
if (lean::is_scalar(x_963)) {
 x_964 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_964 = x_963;
}
lean::cnstr_set(x_964, 0, x_9);
lean::cnstr_set(x_964, 1, x_962);
return x_964;
}
else
{
obj* x_965; obj* x_966; obj* x_967; obj* x_968; 
x_965 = lean::cnstr_get(x_961, 0);
lean::inc(x_965);
x_966 = lean::cnstr_get(x_961, 1);
lean::inc(x_966);
if (lean::is_exclusive(x_961)) {
 lean::cnstr_release(x_961, 0);
 lean::cnstr_release(x_961, 1);
 x_967 = x_961;
} else {
 lean::dec_ref(x_961);
 x_967 = lean::box(0);
}
if (lean::is_scalar(x_967)) {
 x_968 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_968 = x_967;
}
lean::cnstr_set(x_968, 0, x_965);
lean::cnstr_set(x_968, 1, x_966);
return x_968;
}
}
else
{
obj* x_969; obj* x_970; obj* x_971; obj* x_972; 
lean::dec(x_946);
x_969 = lean::cnstr_get(x_957, 0);
lean::inc(x_969);
x_970 = lean::cnstr_get(x_957, 1);
lean::inc(x_970);
if (lean::is_exclusive(x_957)) {
 lean::cnstr_release(x_957, 0);
 lean::cnstr_release(x_957, 1);
 x_971 = x_957;
} else {
 lean::dec_ref(x_957);
 x_971 = lean::box(0);
}
if (lean::is_scalar(x_971)) {
 x_972 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_972 = x_971;
}
lean::cnstr_set(x_972, 0, x_969);
lean::cnstr_set(x_972, 1, x_970);
return x_972;
}
}
else
{
obj* x_973; obj* x_974; obj* x_975; obj* x_976; 
lean::dec(x_946);
x_973 = lean::cnstr_get(x_953, 0);
lean::inc(x_973);
x_974 = lean::cnstr_get(x_953, 1);
lean::inc(x_974);
if (lean::is_exclusive(x_953)) {
 lean::cnstr_release(x_953, 0);
 lean::cnstr_release(x_953, 1);
 x_975 = x_953;
} else {
 lean::dec_ref(x_953);
 x_975 = lean::box(0);
}
if (lean::is_scalar(x_975)) {
 x_976 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_976 = x_975;
}
lean::cnstr_set(x_976, 0, x_973);
lean::cnstr_set(x_976, 1, x_974);
return x_976;
}
}
else
{
obj* x_977; obj* x_978; obj* x_979; obj* x_980; 
lean::dec(x_946);
x_977 = lean::cnstr_get(x_947, 0);
lean::inc(x_977);
x_978 = lean::cnstr_get(x_947, 1);
lean::inc(x_978);
if (lean::is_exclusive(x_947)) {
 lean::cnstr_release(x_947, 0);
 lean::cnstr_release(x_947, 1);
 x_979 = x_947;
} else {
 lean::dec_ref(x_947);
 x_979 = lean::box(0);
}
if (lean::is_scalar(x_979)) {
 x_980 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_980 = x_979;
}
lean::cnstr_set(x_980, 0, x_977);
lean::cnstr_set(x_980, 1, x_978);
return x_980;
}
}
else
{
obj* x_981; obj* x_982; obj* x_983; obj* x_984; 
lean::dec(x_939);
x_981 = lean::cnstr_get(x_942, 0);
lean::inc(x_981);
x_982 = lean::cnstr_get(x_942, 1);
lean::inc(x_982);
if (lean::is_exclusive(x_942)) {
 lean::cnstr_release(x_942, 0);
 lean::cnstr_release(x_942, 1);
 x_983 = x_942;
} else {
 lean::dec_ref(x_942);
 x_983 = lean::box(0);
}
if (lean::is_scalar(x_983)) {
 x_984 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_984 = x_983;
}
lean::cnstr_set(x_984, 0, x_981);
lean::cnstr_set(x_984, 1, x_982);
return x_984;
}
}
else
{
obj* x_985; obj* x_986; obj* x_987; obj* x_988; 
lean::dec(x_929);
x_985 = lean::cnstr_get(x_935, 0);
lean::inc(x_985);
x_986 = lean::cnstr_get(x_935, 1);
lean::inc(x_986);
if (lean::is_exclusive(x_935)) {
 lean::cnstr_release(x_935, 0);
 lean::cnstr_release(x_935, 1);
 x_987 = x_935;
} else {
 lean::dec_ref(x_935);
 x_987 = lean::box(0);
}
if (lean::is_scalar(x_987)) {
 x_988 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_988 = x_987;
}
lean::cnstr_set(x_988, 0, x_985);
lean::cnstr_set(x_988, 1, x_986);
return x_988;
}
}
else
{
obj* x_989; obj* x_990; obj* x_991; obj* x_992; 
x_989 = lean::cnstr_get(x_928, 0);
lean::inc(x_989);
x_990 = lean::cnstr_get(x_928, 1);
lean::inc(x_990);
if (lean::is_exclusive(x_928)) {
 lean::cnstr_release(x_928, 0);
 lean::cnstr_release(x_928, 1);
 x_991 = x_928;
} else {
 lean::dec_ref(x_928);
 x_991 = lean::box(0);
}
if (lean::is_scalar(x_991)) {
 x_992 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_992 = x_991;
}
lean::cnstr_set(x_992, 0, x_989);
lean::cnstr_set(x_992, 1, x_990);
return x_992;
}
}
else
{
obj* x_993; obj* x_994; obj* x_995; obj* x_996; 
lean::dec(x_918);
x_993 = lean::cnstr_get(x_924, 0);
lean::inc(x_993);
x_994 = lean::cnstr_get(x_924, 1);
lean::inc(x_994);
if (lean::is_exclusive(x_924)) {
 lean::cnstr_release(x_924, 0);
 lean::cnstr_release(x_924, 1);
 x_995 = x_924;
} else {
 lean::dec_ref(x_924);
 x_995 = lean::box(0);
}
if (lean::is_scalar(x_995)) {
 x_996 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_996 = x_995;
}
lean::cnstr_set(x_996, 0, x_993);
lean::cnstr_set(x_996, 1, x_994);
return x_996;
}
}
else
{
obj* x_997; obj* x_998; obj* x_999; obj* x_1000; 
x_997 = lean::cnstr_get(x_917, 0);
lean::inc(x_997);
x_998 = lean::cnstr_get(x_917, 1);
lean::inc(x_998);
if (lean::is_exclusive(x_917)) {
 lean::cnstr_release(x_917, 0);
 lean::cnstr_release(x_917, 1);
 x_999 = x_917;
} else {
 lean::dec_ref(x_917);
 x_999 = lean::box(0);
}
if (lean::is_scalar(x_999)) {
 x_1000 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1000 = x_999;
}
lean::cnstr_set(x_1000, 0, x_997);
lean::cnstr_set(x_1000, 1, x_998);
return x_1000;
}
}
else
{
obj* x_1001; obj* x_1002; obj* x_1003; obj* x_1004; 
lean::dec(x_907);
x_1001 = lean::cnstr_get(x_913, 0);
lean::inc(x_1001);
x_1002 = lean::cnstr_get(x_913, 1);
lean::inc(x_1002);
if (lean::is_exclusive(x_913)) {
 lean::cnstr_release(x_913, 0);
 lean::cnstr_release(x_913, 1);
 x_1003 = x_913;
} else {
 lean::dec_ref(x_913);
 x_1003 = lean::box(0);
}
if (lean::is_scalar(x_1003)) {
 x_1004 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1004 = x_1003;
}
lean::cnstr_set(x_1004, 0, x_1001);
lean::cnstr_set(x_1004, 1, x_1002);
return x_1004;
}
}
else
{
obj* x_1005; obj* x_1006; obj* x_1007; obj* x_1008; 
x_1005 = lean::cnstr_get(x_906, 0);
lean::inc(x_1005);
x_1006 = lean::cnstr_get(x_906, 1);
lean::inc(x_1006);
if (lean::is_exclusive(x_906)) {
 lean::cnstr_release(x_906, 0);
 lean::cnstr_release(x_906, 1);
 x_1007 = x_906;
} else {
 lean::dec_ref(x_906);
 x_1007 = lean::box(0);
}
if (lean::is_scalar(x_1007)) {
 x_1008 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1008 = x_1007;
}
lean::cnstr_set(x_1008, 0, x_1005);
lean::cnstr_set(x_1008, 1, x_1006);
return x_1008;
}
}
else
{
obj* x_1009; obj* x_1010; obj* x_1011; obj* x_1012; 
lean::dec(x_898);
x_1009 = lean::cnstr_get(x_901, 0);
lean::inc(x_1009);
x_1010 = lean::cnstr_get(x_901, 1);
lean::inc(x_1010);
if (lean::is_exclusive(x_901)) {
 lean::cnstr_release(x_901, 0);
 lean::cnstr_release(x_901, 1);
 x_1011 = x_901;
} else {
 lean::dec_ref(x_901);
 x_1011 = lean::box(0);
}
if (lean::is_scalar(x_1011)) {
 x_1012 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1012 = x_1011;
}
lean::cnstr_set(x_1012, 0, x_1009);
lean::cnstr_set(x_1012, 1, x_1010);
return x_1012;
}
}
else
{
obj* x_1013; obj* x_1014; obj* x_1015; obj* x_1016; 
lean::dec(x_891);
x_1013 = lean::cnstr_get(x_894, 0);
lean::inc(x_1013);
x_1014 = lean::cnstr_get(x_894, 1);
lean::inc(x_1014);
if (lean::is_exclusive(x_894)) {
 lean::cnstr_release(x_894, 0);
 lean::cnstr_release(x_894, 1);
 x_1015 = x_894;
} else {
 lean::dec_ref(x_894);
 x_1015 = lean::box(0);
}
if (lean::is_scalar(x_1015)) {
 x_1016 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1016 = x_1015;
}
lean::cnstr_set(x_1016, 0, x_1013);
lean::cnstr_set(x_1016, 1, x_1014);
return x_1016;
}
}
}
else
{
uint8 x_1017; 
lean::dec(x_20);
x_1017 = !lean::is_exclusive(x_23);
if (x_1017 == 0)
{
return x_23;
}
else
{
obj* x_1018; obj* x_1019; obj* x_1020; 
x_1018 = lean::cnstr_get(x_23, 0);
x_1019 = lean::cnstr_get(x_23, 1);
lean::inc(x_1019);
lean::inc(x_1018);
lean::dec(x_23);
x_1020 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_1020, 0, x_1018);
lean::cnstr_set(x_1020, 1, x_1019);
return x_1020;
}
}
}
else
{
obj* x_1021; obj* x_1022; obj* x_1023; obj* x_1024; obj* x_1025; obj* x_1026; 
x_1021 = lean::cnstr_get(x_17, 1);
lean::inc(x_1021);
lean::dec(x_17);
x_1022 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1022, 0, x_9);
lean::cnstr_set(x_1022, 1, x_1021);
x_1023 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(x_10, x_14);
x_1024 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__7;
x_1025 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
lean::inc(x_1023);
x_1026 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1024, x_1025, x_1023, x_2, x_1022);
if (lean::obj_tag(x_1026) == 0)
{
obj* x_1027; obj* x_1028; obj* x_1029; obj* x_1030; obj* x_1031; obj* x_1032; obj* x_1033; 
x_1027 = lean::cnstr_get(x_1026, 1);
lean::inc(x_1027);
if (lean::is_exclusive(x_1026)) {
 lean::cnstr_release(x_1026, 0);
 lean::cnstr_release(x_1026, 1);
 x_1028 = x_1026;
} else {
 lean::dec_ref(x_1026);
 x_1028 = lean::box(0);
}
if (lean::is_scalar(x_1028)) {
 x_1029 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1029 = x_1028;
}
lean::cnstr_set(x_1029, 0, x_9);
lean::cnstr_set(x_1029, 1, x_1027);
x_1030 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(x_10, x_1023);
x_1031 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
x_1032 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
lean::inc(x_1030);
x_1033 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1031, x_1032, x_1030, x_2, x_1029);
if (lean::obj_tag(x_1033) == 0)
{
obj* x_1034; obj* x_1035; obj* x_1036; obj* x_1037; obj* x_1038; obj* x_1039; obj* x_1040; 
x_1034 = lean::cnstr_get(x_1033, 1);
lean::inc(x_1034);
if (lean::is_exclusive(x_1033)) {
 lean::cnstr_release(x_1033, 0);
 lean::cnstr_release(x_1033, 1);
 x_1035 = x_1033;
} else {
 lean::dec_ref(x_1033);
 x_1035 = lean::box(0);
}
if (lean::is_scalar(x_1035)) {
 x_1036 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1036 = x_1035;
}
lean::cnstr_set(x_1036, 0, x_9);
lean::cnstr_set(x_1036, 1, x_1034);
x_1037 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(x_10, x_1030);
x_1038 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
x_1039 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean::inc(x_1037);
x_1040 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1038, x_1039, x_1037, x_2, x_1036);
if (lean::obj_tag(x_1040) == 0)
{
obj* x_1041; obj* x_1042; obj* x_1043; obj* x_1044; obj* x_1045; 
x_1041 = lean::cnstr_get(x_1040, 1);
lean::inc(x_1041);
if (lean::is_exclusive(x_1040)) {
 lean::cnstr_release(x_1040, 0);
 lean::cnstr_release(x_1040, 1);
 x_1042 = x_1040;
} else {
 lean::dec_ref(x_1040);
 x_1042 = lean::box(0);
}
if (lean::is_scalar(x_1042)) {
 x_1043 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1043 = x_1042;
}
lean::cnstr_set(x_1043, 0, x_9);
lean::cnstr_set(x_1043, 1, x_1041);
x_1044 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_1037);
x_1045 = l_Lean_IR_inferBorrow(x_1044, x_2, x_1043);
if (lean::obj_tag(x_1045) == 0)
{
obj* x_1046; obj* x_1047; obj* x_1048; obj* x_1049; obj* x_1050; obj* x_1051; obj* x_1052; 
x_1046 = lean::cnstr_get(x_1045, 0);
lean::inc(x_1046);
x_1047 = lean::cnstr_get(x_1045, 1);
lean::inc(x_1047);
if (lean::is_exclusive(x_1045)) {
 lean::cnstr_release(x_1045, 0);
 lean::cnstr_release(x_1045, 1);
 x_1048 = x_1045;
} else {
 lean::dec_ref(x_1045);
 x_1048 = lean::box(0);
}
if (lean::is_scalar(x_1048)) {
 x_1049 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1049 = x_1048;
}
lean::cnstr_set(x_1049, 0, x_9);
lean::cnstr_set(x_1049, 1, x_1047);
x_1050 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_1051 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean::inc(x_1046);
x_1052 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1050, x_1051, x_1046, x_2, x_1049);
if (lean::obj_tag(x_1052) == 0)
{
obj* x_1053; obj* x_1054; obj* x_1055; obj* x_1056; 
x_1053 = lean::cnstr_get(x_1052, 1);
lean::inc(x_1053);
if (lean::is_exclusive(x_1052)) {
 lean::cnstr_release(x_1052, 0);
 lean::cnstr_release(x_1052, 1);
 x_1054 = x_1052;
} else {
 lean::dec_ref(x_1052);
 x_1054 = lean::box(0);
}
if (lean::is_scalar(x_1054)) {
 x_1055 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1055 = x_1054;
}
lean::cnstr_set(x_1055, 0, x_9);
lean::cnstr_set(x_1055, 1, x_1053);
x_1056 = l_Lean_IR_explicitBoxing(x_1046, x_2, x_1055);
if (lean::obj_tag(x_1056) == 0)
{
obj* x_1057; obj* x_1058; obj* x_1059; obj* x_1060; obj* x_1061; obj* x_1062; obj* x_1063; 
x_1057 = lean::cnstr_get(x_1056, 0);
lean::inc(x_1057);
x_1058 = lean::cnstr_get(x_1056, 1);
lean::inc(x_1058);
if (lean::is_exclusive(x_1056)) {
 lean::cnstr_release(x_1056, 0);
 lean::cnstr_release(x_1056, 1);
 x_1059 = x_1056;
} else {
 lean::dec_ref(x_1056);
 x_1059 = lean::box(0);
}
if (lean::is_scalar(x_1059)) {
 x_1060 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1060 = x_1059;
}
lean::cnstr_set(x_1060, 0, x_9);
lean::cnstr_set(x_1060, 1, x_1058);
x_1061 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_1062 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean::inc(x_1057);
x_1063 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1061, x_1062, x_1057, x_2, x_1060);
if (lean::obj_tag(x_1063) == 0)
{
obj* x_1064; obj* x_1065; obj* x_1066; obj* x_1067; 
x_1064 = lean::cnstr_get(x_1063, 1);
lean::inc(x_1064);
if (lean::is_exclusive(x_1063)) {
 lean::cnstr_release(x_1063, 0);
 lean::cnstr_release(x_1063, 1);
 x_1065 = x_1063;
} else {
 lean::dec_ref(x_1063);
 x_1065 = lean::box(0);
}
if (lean::is_scalar(x_1065)) {
 x_1066 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1066 = x_1065;
}
lean::cnstr_set(x_1066, 0, x_9);
lean::cnstr_set(x_1066, 1, x_1064);
x_1067 = l_Lean_IR_explicitRC(x_1057, x_2, x_1066);
if (lean::obj_tag(x_1067) == 0)
{
obj* x_1068; obj* x_1069; obj* x_1070; obj* x_1071; obj* x_1072; obj* x_1073; obj* x_1074; 
x_1068 = lean::cnstr_get(x_1067, 0);
lean::inc(x_1068);
x_1069 = lean::cnstr_get(x_1067, 1);
lean::inc(x_1069);
if (lean::is_exclusive(x_1067)) {
 lean::cnstr_release(x_1067, 0);
 lean::cnstr_release(x_1067, 1);
 x_1070 = x_1067;
} else {
 lean::dec_ref(x_1067);
 x_1070 = lean::box(0);
}
if (lean::is_scalar(x_1070)) {
 x_1071 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1071 = x_1070;
}
lean::cnstr_set(x_1071, 0, x_9);
lean::cnstr_set(x_1071, 1, x_1069);
x_1072 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_1073 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean::inc(x_1068);
x_1074 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1072, x_1073, x_1068, x_2, x_1071);
if (lean::obj_tag(x_1074) == 0)
{
obj* x_1075; obj* x_1076; obj* x_1077; obj* x_1078; obj* x_1079; obj* x_1080; obj* x_1081; 
x_1075 = lean::cnstr_get(x_1074, 1);
lean::inc(x_1075);
if (lean::is_exclusive(x_1074)) {
 lean::cnstr_release(x_1074, 0);
 lean::cnstr_release(x_1074, 1);
 x_1076 = x_1074;
} else {
 lean::dec_ref(x_1074);
 x_1076 = lean::box(0);
}
if (lean::is_scalar(x_1076)) {
 x_1077 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1077 = x_1076;
}
lean::cnstr_set(x_1077, 0, x_9);
lean::cnstr_set(x_1077, 1, x_1075);
x_1078 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_1068);
x_1079 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_1080 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean::inc(x_1078);
x_1081 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1079, x_1080, x_1078, x_2, x_1077);
if (lean::obj_tag(x_1081) == 0)
{
obj* x_1082; obj* x_1083; obj* x_1084; obj* x_1085; obj* x_1086; 
x_1082 = lean::cnstr_get(x_1081, 1);
lean::inc(x_1082);
if (lean::is_exclusive(x_1081)) {
 lean::cnstr_release(x_1081, 0);
 lean::cnstr_release(x_1081, 1);
 x_1083 = x_1081;
} else {
 lean::dec_ref(x_1081);
 x_1083 = lean::box(0);
}
if (lean::is_scalar(x_1083)) {
 x_1084 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1084 = x_1083;
}
lean::cnstr_set(x_1084, 0, x_9);
lean::cnstr_set(x_1084, 1, x_1082);
x_1085 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_1078);
lean::inc(x_1085);
x_1086 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_1085, x_2, x_1084);
if (lean::obj_tag(x_1086) == 0)
{
obj* x_1087; obj* x_1088; obj* x_1089; obj* x_1090; obj* x_1091; obj* x_1092; 
x_1087 = lean::cnstr_get(x_1086, 1);
lean::inc(x_1087);
if (lean::is_exclusive(x_1086)) {
 lean::cnstr_release(x_1086, 0);
 lean::cnstr_release(x_1086, 1);
 x_1088 = x_1086;
} else {
 lean::dec_ref(x_1086);
 x_1088 = lean::box(0);
}
if (lean::is_scalar(x_1088)) {
 x_1089 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1089 = x_1088;
}
lean::cnstr_set(x_1089, 0, x_9);
lean::cnstr_set(x_1089, 1, x_1087);
x_1090 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_1091 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_1085);
x_1092 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1090, x_1091, x_1085, x_2, x_1089);
if (lean::obj_tag(x_1092) == 0)
{
obj* x_1093; obj* x_1094; obj* x_1095; obj* x_1096; 
x_1093 = lean::cnstr_get(x_1092, 1);
lean::inc(x_1093);
if (lean::is_exclusive(x_1092)) {
 lean::cnstr_release(x_1092, 0);
 lean::cnstr_release(x_1092, 1);
 x_1094 = x_1092;
} else {
 lean::dec_ref(x_1092);
 x_1094 = lean::box(0);
}
if (lean::is_scalar(x_1094)) {
 x_1095 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1095 = x_1094;
}
lean::cnstr_set(x_1095, 0, x_9);
lean::cnstr_set(x_1095, 1, x_1093);
lean::inc(x_1085);
x_1096 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1085, x_1085, x_10, x_2, x_1095);
if (lean::obj_tag(x_1096) == 0)
{
obj* x_1097; obj* x_1098; obj* x_1099; obj* x_1100; 
x_1097 = lean::cnstr_get(x_1096, 1);
lean::inc(x_1097);
if (lean::is_exclusive(x_1096)) {
 lean::cnstr_release(x_1096, 0);
 lean::cnstr_release(x_1096, 1);
 x_1098 = x_1096;
} else {
 lean::dec_ref(x_1096);
 x_1098 = lean::box(0);
}
if (lean::is_scalar(x_1098)) {
 x_1099 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1099 = x_1098;
}
lean::cnstr_set(x_1099, 0, x_9);
lean::cnstr_set(x_1099, 1, x_1097);
x_1100 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_1085, x_10, x_2, x_1099);
lean::dec(x_1085);
if (lean::obj_tag(x_1100) == 0)
{
obj* x_1101; obj* x_1102; obj* x_1103; 
x_1101 = lean::cnstr_get(x_1100, 1);
lean::inc(x_1101);
if (lean::is_exclusive(x_1100)) {
 lean::cnstr_release(x_1100, 0);
 lean::cnstr_release(x_1100, 1);
 x_1102 = x_1100;
} else {
 lean::dec_ref(x_1100);
 x_1102 = lean::box(0);
}
if (lean::is_scalar(x_1102)) {
 x_1103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1103 = x_1102;
}
lean::cnstr_set(x_1103, 0, x_9);
lean::cnstr_set(x_1103, 1, x_1101);
return x_1103;
}
else
{
obj* x_1104; obj* x_1105; obj* x_1106; obj* x_1107; 
x_1104 = lean::cnstr_get(x_1100, 0);
lean::inc(x_1104);
x_1105 = lean::cnstr_get(x_1100, 1);
lean::inc(x_1105);
if (lean::is_exclusive(x_1100)) {
 lean::cnstr_release(x_1100, 0);
 lean::cnstr_release(x_1100, 1);
 x_1106 = x_1100;
} else {
 lean::dec_ref(x_1100);
 x_1106 = lean::box(0);
}
if (lean::is_scalar(x_1106)) {
 x_1107 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1107 = x_1106;
}
lean::cnstr_set(x_1107, 0, x_1104);
lean::cnstr_set(x_1107, 1, x_1105);
return x_1107;
}
}
else
{
obj* x_1108; obj* x_1109; obj* x_1110; obj* x_1111; 
lean::dec(x_1085);
x_1108 = lean::cnstr_get(x_1096, 0);
lean::inc(x_1108);
x_1109 = lean::cnstr_get(x_1096, 1);
lean::inc(x_1109);
if (lean::is_exclusive(x_1096)) {
 lean::cnstr_release(x_1096, 0);
 lean::cnstr_release(x_1096, 1);
 x_1110 = x_1096;
} else {
 lean::dec_ref(x_1096);
 x_1110 = lean::box(0);
}
if (lean::is_scalar(x_1110)) {
 x_1111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1111 = x_1110;
}
lean::cnstr_set(x_1111, 0, x_1108);
lean::cnstr_set(x_1111, 1, x_1109);
return x_1111;
}
}
else
{
obj* x_1112; obj* x_1113; obj* x_1114; obj* x_1115; 
lean::dec(x_1085);
x_1112 = lean::cnstr_get(x_1092, 0);
lean::inc(x_1112);
x_1113 = lean::cnstr_get(x_1092, 1);
lean::inc(x_1113);
if (lean::is_exclusive(x_1092)) {
 lean::cnstr_release(x_1092, 0);
 lean::cnstr_release(x_1092, 1);
 x_1114 = x_1092;
} else {
 lean::dec_ref(x_1092);
 x_1114 = lean::box(0);
}
if (lean::is_scalar(x_1114)) {
 x_1115 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1115 = x_1114;
}
lean::cnstr_set(x_1115, 0, x_1112);
lean::cnstr_set(x_1115, 1, x_1113);
return x_1115;
}
}
else
{
obj* x_1116; obj* x_1117; obj* x_1118; obj* x_1119; 
lean::dec(x_1085);
x_1116 = lean::cnstr_get(x_1086, 0);
lean::inc(x_1116);
x_1117 = lean::cnstr_get(x_1086, 1);
lean::inc(x_1117);
if (lean::is_exclusive(x_1086)) {
 lean::cnstr_release(x_1086, 0);
 lean::cnstr_release(x_1086, 1);
 x_1118 = x_1086;
} else {
 lean::dec_ref(x_1086);
 x_1118 = lean::box(0);
}
if (lean::is_scalar(x_1118)) {
 x_1119 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1119 = x_1118;
}
lean::cnstr_set(x_1119, 0, x_1116);
lean::cnstr_set(x_1119, 1, x_1117);
return x_1119;
}
}
else
{
obj* x_1120; obj* x_1121; obj* x_1122; obj* x_1123; 
lean::dec(x_1078);
x_1120 = lean::cnstr_get(x_1081, 0);
lean::inc(x_1120);
x_1121 = lean::cnstr_get(x_1081, 1);
lean::inc(x_1121);
if (lean::is_exclusive(x_1081)) {
 lean::cnstr_release(x_1081, 0);
 lean::cnstr_release(x_1081, 1);
 x_1122 = x_1081;
} else {
 lean::dec_ref(x_1081);
 x_1122 = lean::box(0);
}
if (lean::is_scalar(x_1122)) {
 x_1123 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1123 = x_1122;
}
lean::cnstr_set(x_1123, 0, x_1120);
lean::cnstr_set(x_1123, 1, x_1121);
return x_1123;
}
}
else
{
obj* x_1124; obj* x_1125; obj* x_1126; obj* x_1127; 
lean::dec(x_1068);
x_1124 = lean::cnstr_get(x_1074, 0);
lean::inc(x_1124);
x_1125 = lean::cnstr_get(x_1074, 1);
lean::inc(x_1125);
if (lean::is_exclusive(x_1074)) {
 lean::cnstr_release(x_1074, 0);
 lean::cnstr_release(x_1074, 1);
 x_1126 = x_1074;
} else {
 lean::dec_ref(x_1074);
 x_1126 = lean::box(0);
}
if (lean::is_scalar(x_1126)) {
 x_1127 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1127 = x_1126;
}
lean::cnstr_set(x_1127, 0, x_1124);
lean::cnstr_set(x_1127, 1, x_1125);
return x_1127;
}
}
else
{
obj* x_1128; obj* x_1129; obj* x_1130; obj* x_1131; 
x_1128 = lean::cnstr_get(x_1067, 0);
lean::inc(x_1128);
x_1129 = lean::cnstr_get(x_1067, 1);
lean::inc(x_1129);
if (lean::is_exclusive(x_1067)) {
 lean::cnstr_release(x_1067, 0);
 lean::cnstr_release(x_1067, 1);
 x_1130 = x_1067;
} else {
 lean::dec_ref(x_1067);
 x_1130 = lean::box(0);
}
if (lean::is_scalar(x_1130)) {
 x_1131 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1131 = x_1130;
}
lean::cnstr_set(x_1131, 0, x_1128);
lean::cnstr_set(x_1131, 1, x_1129);
return x_1131;
}
}
else
{
obj* x_1132; obj* x_1133; obj* x_1134; obj* x_1135; 
lean::dec(x_1057);
x_1132 = lean::cnstr_get(x_1063, 0);
lean::inc(x_1132);
x_1133 = lean::cnstr_get(x_1063, 1);
lean::inc(x_1133);
if (lean::is_exclusive(x_1063)) {
 lean::cnstr_release(x_1063, 0);
 lean::cnstr_release(x_1063, 1);
 x_1134 = x_1063;
} else {
 lean::dec_ref(x_1063);
 x_1134 = lean::box(0);
}
if (lean::is_scalar(x_1134)) {
 x_1135 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1135 = x_1134;
}
lean::cnstr_set(x_1135, 0, x_1132);
lean::cnstr_set(x_1135, 1, x_1133);
return x_1135;
}
}
else
{
obj* x_1136; obj* x_1137; obj* x_1138; obj* x_1139; 
x_1136 = lean::cnstr_get(x_1056, 0);
lean::inc(x_1136);
x_1137 = lean::cnstr_get(x_1056, 1);
lean::inc(x_1137);
if (lean::is_exclusive(x_1056)) {
 lean::cnstr_release(x_1056, 0);
 lean::cnstr_release(x_1056, 1);
 x_1138 = x_1056;
} else {
 lean::dec_ref(x_1056);
 x_1138 = lean::box(0);
}
if (lean::is_scalar(x_1138)) {
 x_1139 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1139 = x_1138;
}
lean::cnstr_set(x_1139, 0, x_1136);
lean::cnstr_set(x_1139, 1, x_1137);
return x_1139;
}
}
else
{
obj* x_1140; obj* x_1141; obj* x_1142; obj* x_1143; 
lean::dec(x_1046);
x_1140 = lean::cnstr_get(x_1052, 0);
lean::inc(x_1140);
x_1141 = lean::cnstr_get(x_1052, 1);
lean::inc(x_1141);
if (lean::is_exclusive(x_1052)) {
 lean::cnstr_release(x_1052, 0);
 lean::cnstr_release(x_1052, 1);
 x_1142 = x_1052;
} else {
 lean::dec_ref(x_1052);
 x_1142 = lean::box(0);
}
if (lean::is_scalar(x_1142)) {
 x_1143 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1143 = x_1142;
}
lean::cnstr_set(x_1143, 0, x_1140);
lean::cnstr_set(x_1143, 1, x_1141);
return x_1143;
}
}
else
{
obj* x_1144; obj* x_1145; obj* x_1146; obj* x_1147; 
x_1144 = lean::cnstr_get(x_1045, 0);
lean::inc(x_1144);
x_1145 = lean::cnstr_get(x_1045, 1);
lean::inc(x_1145);
if (lean::is_exclusive(x_1045)) {
 lean::cnstr_release(x_1045, 0);
 lean::cnstr_release(x_1045, 1);
 x_1146 = x_1045;
} else {
 lean::dec_ref(x_1045);
 x_1146 = lean::box(0);
}
if (lean::is_scalar(x_1146)) {
 x_1147 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1147 = x_1146;
}
lean::cnstr_set(x_1147, 0, x_1144);
lean::cnstr_set(x_1147, 1, x_1145);
return x_1147;
}
}
else
{
obj* x_1148; obj* x_1149; obj* x_1150; obj* x_1151; 
lean::dec(x_1037);
x_1148 = lean::cnstr_get(x_1040, 0);
lean::inc(x_1148);
x_1149 = lean::cnstr_get(x_1040, 1);
lean::inc(x_1149);
if (lean::is_exclusive(x_1040)) {
 lean::cnstr_release(x_1040, 0);
 lean::cnstr_release(x_1040, 1);
 x_1150 = x_1040;
} else {
 lean::dec_ref(x_1040);
 x_1150 = lean::box(0);
}
if (lean::is_scalar(x_1150)) {
 x_1151 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1151 = x_1150;
}
lean::cnstr_set(x_1151, 0, x_1148);
lean::cnstr_set(x_1151, 1, x_1149);
return x_1151;
}
}
else
{
obj* x_1152; obj* x_1153; obj* x_1154; obj* x_1155; 
lean::dec(x_1030);
x_1152 = lean::cnstr_get(x_1033, 0);
lean::inc(x_1152);
x_1153 = lean::cnstr_get(x_1033, 1);
lean::inc(x_1153);
if (lean::is_exclusive(x_1033)) {
 lean::cnstr_release(x_1033, 0);
 lean::cnstr_release(x_1033, 1);
 x_1154 = x_1033;
} else {
 lean::dec_ref(x_1033);
 x_1154 = lean::box(0);
}
if (lean::is_scalar(x_1154)) {
 x_1155 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1155 = x_1154;
}
lean::cnstr_set(x_1155, 0, x_1152);
lean::cnstr_set(x_1155, 1, x_1153);
return x_1155;
}
}
else
{
obj* x_1156; obj* x_1157; obj* x_1158; obj* x_1159; 
lean::dec(x_1023);
x_1156 = lean::cnstr_get(x_1026, 0);
lean::inc(x_1156);
x_1157 = lean::cnstr_get(x_1026, 1);
lean::inc(x_1157);
if (lean::is_exclusive(x_1026)) {
 lean::cnstr_release(x_1026, 0);
 lean::cnstr_release(x_1026, 1);
 x_1158 = x_1026;
} else {
 lean::dec_ref(x_1026);
 x_1158 = lean::box(0);
}
if (lean::is_scalar(x_1158)) {
 x_1159 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1159 = x_1158;
}
lean::cnstr_set(x_1159, 0, x_1156);
lean::cnstr_set(x_1159, 1, x_1157);
return x_1159;
}
}
}
else
{
uint8 x_1160; 
lean::dec(x_14);
x_1160 = !lean::is_exclusive(x_17);
if (x_1160 == 0)
{
return x_17;
}
else
{
obj* x_1161; obj* x_1162; obj* x_1163; 
x_1161 = lean::cnstr_get(x_17, 0);
x_1162 = lean::cnstr_get(x_17, 1);
lean::inc(x_1162);
lean::inc(x_1161);
lean::dec(x_17);
x_1163 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_1163, 0, x_1161);
lean::cnstr_set(x_1163, 1, x_1162);
return x_1163;
}
}
}
else
{
obj* x_1164; obj* x_1165; obj* x_1166; obj* x_1167; obj* x_1168; obj* x_1169; 
x_1164 = lean::cnstr_get(x_11, 1);
lean::inc(x_1164);
lean::dec(x_11);
x_1165 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1165, 0, x_9);
lean::cnstr_set(x_1165, 1, x_1164);
x_1166 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_1);
x_1167 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__4;
x_1168 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
lean::inc(x_1166);
x_1169 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1167, x_1168, x_1166, x_2, x_1165);
if (lean::obj_tag(x_1169) == 0)
{
obj* x_1170; obj* x_1171; obj* x_1172; obj* x_1173; obj* x_1174; obj* x_1175; obj* x_1176; 
x_1170 = lean::cnstr_get(x_1169, 1);
lean::inc(x_1170);
if (lean::is_exclusive(x_1169)) {
 lean::cnstr_release(x_1169, 0);
 lean::cnstr_release(x_1169, 1);
 x_1171 = x_1169;
} else {
 lean::dec_ref(x_1169);
 x_1171 = lean::box(0);
}
if (lean::is_scalar(x_1171)) {
 x_1172 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1172 = x_1171;
}
lean::cnstr_set(x_1172, 0, x_9);
lean::cnstr_set(x_1172, 1, x_1170);
x_1173 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(x_10, x_1166);
x_1174 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__7;
x_1175 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
lean::inc(x_1173);
x_1176 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1174, x_1175, x_1173, x_2, x_1172);
if (lean::obj_tag(x_1176) == 0)
{
obj* x_1177; obj* x_1178; obj* x_1179; obj* x_1180; obj* x_1181; obj* x_1182; obj* x_1183; 
x_1177 = lean::cnstr_get(x_1176, 1);
lean::inc(x_1177);
if (lean::is_exclusive(x_1176)) {
 lean::cnstr_release(x_1176, 0);
 lean::cnstr_release(x_1176, 1);
 x_1178 = x_1176;
} else {
 lean::dec_ref(x_1176);
 x_1178 = lean::box(0);
}
if (lean::is_scalar(x_1178)) {
 x_1179 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1179 = x_1178;
}
lean::cnstr_set(x_1179, 0, x_9);
lean::cnstr_set(x_1179, 1, x_1177);
x_1180 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(x_10, x_1173);
x_1181 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
x_1182 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
lean::inc(x_1180);
x_1183 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1181, x_1182, x_1180, x_2, x_1179);
if (lean::obj_tag(x_1183) == 0)
{
obj* x_1184; obj* x_1185; obj* x_1186; obj* x_1187; obj* x_1188; obj* x_1189; obj* x_1190; 
x_1184 = lean::cnstr_get(x_1183, 1);
lean::inc(x_1184);
if (lean::is_exclusive(x_1183)) {
 lean::cnstr_release(x_1183, 0);
 lean::cnstr_release(x_1183, 1);
 x_1185 = x_1183;
} else {
 lean::dec_ref(x_1183);
 x_1185 = lean::box(0);
}
if (lean::is_scalar(x_1185)) {
 x_1186 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1186 = x_1185;
}
lean::cnstr_set(x_1186, 0, x_9);
lean::cnstr_set(x_1186, 1, x_1184);
x_1187 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(x_10, x_1180);
x_1188 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
x_1189 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean::inc(x_1187);
x_1190 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1188, x_1189, x_1187, x_2, x_1186);
if (lean::obj_tag(x_1190) == 0)
{
obj* x_1191; obj* x_1192; obj* x_1193; obj* x_1194; obj* x_1195; 
x_1191 = lean::cnstr_get(x_1190, 1);
lean::inc(x_1191);
if (lean::is_exclusive(x_1190)) {
 lean::cnstr_release(x_1190, 0);
 lean::cnstr_release(x_1190, 1);
 x_1192 = x_1190;
} else {
 lean::dec_ref(x_1190);
 x_1192 = lean::box(0);
}
if (lean::is_scalar(x_1192)) {
 x_1193 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1193 = x_1192;
}
lean::cnstr_set(x_1193, 0, x_9);
lean::cnstr_set(x_1193, 1, x_1191);
x_1194 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_1187);
x_1195 = l_Lean_IR_inferBorrow(x_1194, x_2, x_1193);
if (lean::obj_tag(x_1195) == 0)
{
obj* x_1196; obj* x_1197; obj* x_1198; obj* x_1199; obj* x_1200; obj* x_1201; obj* x_1202; 
x_1196 = lean::cnstr_get(x_1195, 0);
lean::inc(x_1196);
x_1197 = lean::cnstr_get(x_1195, 1);
lean::inc(x_1197);
if (lean::is_exclusive(x_1195)) {
 lean::cnstr_release(x_1195, 0);
 lean::cnstr_release(x_1195, 1);
 x_1198 = x_1195;
} else {
 lean::dec_ref(x_1195);
 x_1198 = lean::box(0);
}
if (lean::is_scalar(x_1198)) {
 x_1199 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1199 = x_1198;
}
lean::cnstr_set(x_1199, 0, x_9);
lean::cnstr_set(x_1199, 1, x_1197);
x_1200 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_1201 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean::inc(x_1196);
x_1202 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1200, x_1201, x_1196, x_2, x_1199);
if (lean::obj_tag(x_1202) == 0)
{
obj* x_1203; obj* x_1204; obj* x_1205; obj* x_1206; 
x_1203 = lean::cnstr_get(x_1202, 1);
lean::inc(x_1203);
if (lean::is_exclusive(x_1202)) {
 lean::cnstr_release(x_1202, 0);
 lean::cnstr_release(x_1202, 1);
 x_1204 = x_1202;
} else {
 lean::dec_ref(x_1202);
 x_1204 = lean::box(0);
}
if (lean::is_scalar(x_1204)) {
 x_1205 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1205 = x_1204;
}
lean::cnstr_set(x_1205, 0, x_9);
lean::cnstr_set(x_1205, 1, x_1203);
x_1206 = l_Lean_IR_explicitBoxing(x_1196, x_2, x_1205);
if (lean::obj_tag(x_1206) == 0)
{
obj* x_1207; obj* x_1208; obj* x_1209; obj* x_1210; obj* x_1211; obj* x_1212; obj* x_1213; 
x_1207 = lean::cnstr_get(x_1206, 0);
lean::inc(x_1207);
x_1208 = lean::cnstr_get(x_1206, 1);
lean::inc(x_1208);
if (lean::is_exclusive(x_1206)) {
 lean::cnstr_release(x_1206, 0);
 lean::cnstr_release(x_1206, 1);
 x_1209 = x_1206;
} else {
 lean::dec_ref(x_1206);
 x_1209 = lean::box(0);
}
if (lean::is_scalar(x_1209)) {
 x_1210 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1210 = x_1209;
}
lean::cnstr_set(x_1210, 0, x_9);
lean::cnstr_set(x_1210, 1, x_1208);
x_1211 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_1212 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean::inc(x_1207);
x_1213 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1211, x_1212, x_1207, x_2, x_1210);
if (lean::obj_tag(x_1213) == 0)
{
obj* x_1214; obj* x_1215; obj* x_1216; obj* x_1217; 
x_1214 = lean::cnstr_get(x_1213, 1);
lean::inc(x_1214);
if (lean::is_exclusive(x_1213)) {
 lean::cnstr_release(x_1213, 0);
 lean::cnstr_release(x_1213, 1);
 x_1215 = x_1213;
} else {
 lean::dec_ref(x_1213);
 x_1215 = lean::box(0);
}
if (lean::is_scalar(x_1215)) {
 x_1216 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1216 = x_1215;
}
lean::cnstr_set(x_1216, 0, x_9);
lean::cnstr_set(x_1216, 1, x_1214);
x_1217 = l_Lean_IR_explicitRC(x_1207, x_2, x_1216);
if (lean::obj_tag(x_1217) == 0)
{
obj* x_1218; obj* x_1219; obj* x_1220; obj* x_1221; obj* x_1222; obj* x_1223; obj* x_1224; 
x_1218 = lean::cnstr_get(x_1217, 0);
lean::inc(x_1218);
x_1219 = lean::cnstr_get(x_1217, 1);
lean::inc(x_1219);
if (lean::is_exclusive(x_1217)) {
 lean::cnstr_release(x_1217, 0);
 lean::cnstr_release(x_1217, 1);
 x_1220 = x_1217;
} else {
 lean::dec_ref(x_1217);
 x_1220 = lean::box(0);
}
if (lean::is_scalar(x_1220)) {
 x_1221 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1221 = x_1220;
}
lean::cnstr_set(x_1221, 0, x_9);
lean::cnstr_set(x_1221, 1, x_1219);
x_1222 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_1223 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean::inc(x_1218);
x_1224 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1222, x_1223, x_1218, x_2, x_1221);
if (lean::obj_tag(x_1224) == 0)
{
obj* x_1225; obj* x_1226; obj* x_1227; obj* x_1228; obj* x_1229; obj* x_1230; obj* x_1231; 
x_1225 = lean::cnstr_get(x_1224, 1);
lean::inc(x_1225);
if (lean::is_exclusive(x_1224)) {
 lean::cnstr_release(x_1224, 0);
 lean::cnstr_release(x_1224, 1);
 x_1226 = x_1224;
} else {
 lean::dec_ref(x_1224);
 x_1226 = lean::box(0);
}
if (lean::is_scalar(x_1226)) {
 x_1227 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1227 = x_1226;
}
lean::cnstr_set(x_1227, 0, x_9);
lean::cnstr_set(x_1227, 1, x_1225);
x_1228 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_1218);
x_1229 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_1230 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean::inc(x_1228);
x_1231 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1229, x_1230, x_1228, x_2, x_1227);
if (lean::obj_tag(x_1231) == 0)
{
obj* x_1232; obj* x_1233; obj* x_1234; obj* x_1235; obj* x_1236; 
x_1232 = lean::cnstr_get(x_1231, 1);
lean::inc(x_1232);
if (lean::is_exclusive(x_1231)) {
 lean::cnstr_release(x_1231, 0);
 lean::cnstr_release(x_1231, 1);
 x_1233 = x_1231;
} else {
 lean::dec_ref(x_1231);
 x_1233 = lean::box(0);
}
if (lean::is_scalar(x_1233)) {
 x_1234 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1234 = x_1233;
}
lean::cnstr_set(x_1234, 0, x_9);
lean::cnstr_set(x_1234, 1, x_1232);
x_1235 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_1228);
lean::inc(x_1235);
x_1236 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1167, x_1168, x_1235, x_2, x_1234);
if (lean::obj_tag(x_1236) == 0)
{
obj* x_1237; obj* x_1238; obj* x_1239; obj* x_1240; obj* x_1241; obj* x_1242; 
x_1237 = lean::cnstr_get(x_1236, 1);
lean::inc(x_1237);
if (lean::is_exclusive(x_1236)) {
 lean::cnstr_release(x_1236, 0);
 lean::cnstr_release(x_1236, 1);
 x_1238 = x_1236;
} else {
 lean::dec_ref(x_1236);
 x_1238 = lean::box(0);
}
if (lean::is_scalar(x_1238)) {
 x_1239 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1239 = x_1238;
}
lean::cnstr_set(x_1239, 0, x_9);
lean::cnstr_set(x_1239, 1, x_1237);
x_1240 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_1241 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_1235);
x_1242 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1240, x_1241, x_1235, x_2, x_1239);
if (lean::obj_tag(x_1242) == 0)
{
obj* x_1243; obj* x_1244; obj* x_1245; obj* x_1246; 
x_1243 = lean::cnstr_get(x_1242, 1);
lean::inc(x_1243);
if (lean::is_exclusive(x_1242)) {
 lean::cnstr_release(x_1242, 0);
 lean::cnstr_release(x_1242, 1);
 x_1244 = x_1242;
} else {
 lean::dec_ref(x_1242);
 x_1244 = lean::box(0);
}
if (lean::is_scalar(x_1244)) {
 x_1245 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1245 = x_1244;
}
lean::cnstr_set(x_1245, 0, x_9);
lean::cnstr_set(x_1245, 1, x_1243);
lean::inc(x_1235);
x_1246 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1235, x_1235, x_10, x_2, x_1245);
if (lean::obj_tag(x_1246) == 0)
{
obj* x_1247; obj* x_1248; obj* x_1249; obj* x_1250; 
x_1247 = lean::cnstr_get(x_1246, 1);
lean::inc(x_1247);
if (lean::is_exclusive(x_1246)) {
 lean::cnstr_release(x_1246, 0);
 lean::cnstr_release(x_1246, 1);
 x_1248 = x_1246;
} else {
 lean::dec_ref(x_1246);
 x_1248 = lean::box(0);
}
if (lean::is_scalar(x_1248)) {
 x_1249 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1249 = x_1248;
}
lean::cnstr_set(x_1249, 0, x_9);
lean::cnstr_set(x_1249, 1, x_1247);
x_1250 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_1235, x_10, x_2, x_1249);
lean::dec(x_1235);
if (lean::obj_tag(x_1250) == 0)
{
obj* x_1251; obj* x_1252; obj* x_1253; 
x_1251 = lean::cnstr_get(x_1250, 1);
lean::inc(x_1251);
if (lean::is_exclusive(x_1250)) {
 lean::cnstr_release(x_1250, 0);
 lean::cnstr_release(x_1250, 1);
 x_1252 = x_1250;
} else {
 lean::dec_ref(x_1250);
 x_1252 = lean::box(0);
}
if (lean::is_scalar(x_1252)) {
 x_1253 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1253 = x_1252;
}
lean::cnstr_set(x_1253, 0, x_9);
lean::cnstr_set(x_1253, 1, x_1251);
return x_1253;
}
else
{
obj* x_1254; obj* x_1255; obj* x_1256; obj* x_1257; 
x_1254 = lean::cnstr_get(x_1250, 0);
lean::inc(x_1254);
x_1255 = lean::cnstr_get(x_1250, 1);
lean::inc(x_1255);
if (lean::is_exclusive(x_1250)) {
 lean::cnstr_release(x_1250, 0);
 lean::cnstr_release(x_1250, 1);
 x_1256 = x_1250;
} else {
 lean::dec_ref(x_1250);
 x_1256 = lean::box(0);
}
if (lean::is_scalar(x_1256)) {
 x_1257 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1257 = x_1256;
}
lean::cnstr_set(x_1257, 0, x_1254);
lean::cnstr_set(x_1257, 1, x_1255);
return x_1257;
}
}
else
{
obj* x_1258; obj* x_1259; obj* x_1260; obj* x_1261; 
lean::dec(x_1235);
x_1258 = lean::cnstr_get(x_1246, 0);
lean::inc(x_1258);
x_1259 = lean::cnstr_get(x_1246, 1);
lean::inc(x_1259);
if (lean::is_exclusive(x_1246)) {
 lean::cnstr_release(x_1246, 0);
 lean::cnstr_release(x_1246, 1);
 x_1260 = x_1246;
} else {
 lean::dec_ref(x_1246);
 x_1260 = lean::box(0);
}
if (lean::is_scalar(x_1260)) {
 x_1261 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1261 = x_1260;
}
lean::cnstr_set(x_1261, 0, x_1258);
lean::cnstr_set(x_1261, 1, x_1259);
return x_1261;
}
}
else
{
obj* x_1262; obj* x_1263; obj* x_1264; obj* x_1265; 
lean::dec(x_1235);
x_1262 = lean::cnstr_get(x_1242, 0);
lean::inc(x_1262);
x_1263 = lean::cnstr_get(x_1242, 1);
lean::inc(x_1263);
if (lean::is_exclusive(x_1242)) {
 lean::cnstr_release(x_1242, 0);
 lean::cnstr_release(x_1242, 1);
 x_1264 = x_1242;
} else {
 lean::dec_ref(x_1242);
 x_1264 = lean::box(0);
}
if (lean::is_scalar(x_1264)) {
 x_1265 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1265 = x_1264;
}
lean::cnstr_set(x_1265, 0, x_1262);
lean::cnstr_set(x_1265, 1, x_1263);
return x_1265;
}
}
else
{
obj* x_1266; obj* x_1267; obj* x_1268; obj* x_1269; 
lean::dec(x_1235);
x_1266 = lean::cnstr_get(x_1236, 0);
lean::inc(x_1266);
x_1267 = lean::cnstr_get(x_1236, 1);
lean::inc(x_1267);
if (lean::is_exclusive(x_1236)) {
 lean::cnstr_release(x_1236, 0);
 lean::cnstr_release(x_1236, 1);
 x_1268 = x_1236;
} else {
 lean::dec_ref(x_1236);
 x_1268 = lean::box(0);
}
if (lean::is_scalar(x_1268)) {
 x_1269 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1269 = x_1268;
}
lean::cnstr_set(x_1269, 0, x_1266);
lean::cnstr_set(x_1269, 1, x_1267);
return x_1269;
}
}
else
{
obj* x_1270; obj* x_1271; obj* x_1272; obj* x_1273; 
lean::dec(x_1228);
x_1270 = lean::cnstr_get(x_1231, 0);
lean::inc(x_1270);
x_1271 = lean::cnstr_get(x_1231, 1);
lean::inc(x_1271);
if (lean::is_exclusive(x_1231)) {
 lean::cnstr_release(x_1231, 0);
 lean::cnstr_release(x_1231, 1);
 x_1272 = x_1231;
} else {
 lean::dec_ref(x_1231);
 x_1272 = lean::box(0);
}
if (lean::is_scalar(x_1272)) {
 x_1273 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1273 = x_1272;
}
lean::cnstr_set(x_1273, 0, x_1270);
lean::cnstr_set(x_1273, 1, x_1271);
return x_1273;
}
}
else
{
obj* x_1274; obj* x_1275; obj* x_1276; obj* x_1277; 
lean::dec(x_1218);
x_1274 = lean::cnstr_get(x_1224, 0);
lean::inc(x_1274);
x_1275 = lean::cnstr_get(x_1224, 1);
lean::inc(x_1275);
if (lean::is_exclusive(x_1224)) {
 lean::cnstr_release(x_1224, 0);
 lean::cnstr_release(x_1224, 1);
 x_1276 = x_1224;
} else {
 lean::dec_ref(x_1224);
 x_1276 = lean::box(0);
}
if (lean::is_scalar(x_1276)) {
 x_1277 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1277 = x_1276;
}
lean::cnstr_set(x_1277, 0, x_1274);
lean::cnstr_set(x_1277, 1, x_1275);
return x_1277;
}
}
else
{
obj* x_1278; obj* x_1279; obj* x_1280; obj* x_1281; 
x_1278 = lean::cnstr_get(x_1217, 0);
lean::inc(x_1278);
x_1279 = lean::cnstr_get(x_1217, 1);
lean::inc(x_1279);
if (lean::is_exclusive(x_1217)) {
 lean::cnstr_release(x_1217, 0);
 lean::cnstr_release(x_1217, 1);
 x_1280 = x_1217;
} else {
 lean::dec_ref(x_1217);
 x_1280 = lean::box(0);
}
if (lean::is_scalar(x_1280)) {
 x_1281 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1281 = x_1280;
}
lean::cnstr_set(x_1281, 0, x_1278);
lean::cnstr_set(x_1281, 1, x_1279);
return x_1281;
}
}
else
{
obj* x_1282; obj* x_1283; obj* x_1284; obj* x_1285; 
lean::dec(x_1207);
x_1282 = lean::cnstr_get(x_1213, 0);
lean::inc(x_1282);
x_1283 = lean::cnstr_get(x_1213, 1);
lean::inc(x_1283);
if (lean::is_exclusive(x_1213)) {
 lean::cnstr_release(x_1213, 0);
 lean::cnstr_release(x_1213, 1);
 x_1284 = x_1213;
} else {
 lean::dec_ref(x_1213);
 x_1284 = lean::box(0);
}
if (lean::is_scalar(x_1284)) {
 x_1285 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1285 = x_1284;
}
lean::cnstr_set(x_1285, 0, x_1282);
lean::cnstr_set(x_1285, 1, x_1283);
return x_1285;
}
}
else
{
obj* x_1286; obj* x_1287; obj* x_1288; obj* x_1289; 
x_1286 = lean::cnstr_get(x_1206, 0);
lean::inc(x_1286);
x_1287 = lean::cnstr_get(x_1206, 1);
lean::inc(x_1287);
if (lean::is_exclusive(x_1206)) {
 lean::cnstr_release(x_1206, 0);
 lean::cnstr_release(x_1206, 1);
 x_1288 = x_1206;
} else {
 lean::dec_ref(x_1206);
 x_1288 = lean::box(0);
}
if (lean::is_scalar(x_1288)) {
 x_1289 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1289 = x_1288;
}
lean::cnstr_set(x_1289, 0, x_1286);
lean::cnstr_set(x_1289, 1, x_1287);
return x_1289;
}
}
else
{
obj* x_1290; obj* x_1291; obj* x_1292; obj* x_1293; 
lean::dec(x_1196);
x_1290 = lean::cnstr_get(x_1202, 0);
lean::inc(x_1290);
x_1291 = lean::cnstr_get(x_1202, 1);
lean::inc(x_1291);
if (lean::is_exclusive(x_1202)) {
 lean::cnstr_release(x_1202, 0);
 lean::cnstr_release(x_1202, 1);
 x_1292 = x_1202;
} else {
 lean::dec_ref(x_1202);
 x_1292 = lean::box(0);
}
if (lean::is_scalar(x_1292)) {
 x_1293 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1293 = x_1292;
}
lean::cnstr_set(x_1293, 0, x_1290);
lean::cnstr_set(x_1293, 1, x_1291);
return x_1293;
}
}
else
{
obj* x_1294; obj* x_1295; obj* x_1296; obj* x_1297; 
x_1294 = lean::cnstr_get(x_1195, 0);
lean::inc(x_1294);
x_1295 = lean::cnstr_get(x_1195, 1);
lean::inc(x_1295);
if (lean::is_exclusive(x_1195)) {
 lean::cnstr_release(x_1195, 0);
 lean::cnstr_release(x_1195, 1);
 x_1296 = x_1195;
} else {
 lean::dec_ref(x_1195);
 x_1296 = lean::box(0);
}
if (lean::is_scalar(x_1296)) {
 x_1297 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1297 = x_1296;
}
lean::cnstr_set(x_1297, 0, x_1294);
lean::cnstr_set(x_1297, 1, x_1295);
return x_1297;
}
}
else
{
obj* x_1298; obj* x_1299; obj* x_1300; obj* x_1301; 
lean::dec(x_1187);
x_1298 = lean::cnstr_get(x_1190, 0);
lean::inc(x_1298);
x_1299 = lean::cnstr_get(x_1190, 1);
lean::inc(x_1299);
if (lean::is_exclusive(x_1190)) {
 lean::cnstr_release(x_1190, 0);
 lean::cnstr_release(x_1190, 1);
 x_1300 = x_1190;
} else {
 lean::dec_ref(x_1190);
 x_1300 = lean::box(0);
}
if (lean::is_scalar(x_1300)) {
 x_1301 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1301 = x_1300;
}
lean::cnstr_set(x_1301, 0, x_1298);
lean::cnstr_set(x_1301, 1, x_1299);
return x_1301;
}
}
else
{
obj* x_1302; obj* x_1303; obj* x_1304; obj* x_1305; 
lean::dec(x_1180);
x_1302 = lean::cnstr_get(x_1183, 0);
lean::inc(x_1302);
x_1303 = lean::cnstr_get(x_1183, 1);
lean::inc(x_1303);
if (lean::is_exclusive(x_1183)) {
 lean::cnstr_release(x_1183, 0);
 lean::cnstr_release(x_1183, 1);
 x_1304 = x_1183;
} else {
 lean::dec_ref(x_1183);
 x_1304 = lean::box(0);
}
if (lean::is_scalar(x_1304)) {
 x_1305 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1305 = x_1304;
}
lean::cnstr_set(x_1305, 0, x_1302);
lean::cnstr_set(x_1305, 1, x_1303);
return x_1305;
}
}
else
{
obj* x_1306; obj* x_1307; obj* x_1308; obj* x_1309; 
lean::dec(x_1173);
x_1306 = lean::cnstr_get(x_1176, 0);
lean::inc(x_1306);
x_1307 = lean::cnstr_get(x_1176, 1);
lean::inc(x_1307);
if (lean::is_exclusive(x_1176)) {
 lean::cnstr_release(x_1176, 0);
 lean::cnstr_release(x_1176, 1);
 x_1308 = x_1176;
} else {
 lean::dec_ref(x_1176);
 x_1308 = lean::box(0);
}
if (lean::is_scalar(x_1308)) {
 x_1309 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1309 = x_1308;
}
lean::cnstr_set(x_1309, 0, x_1306);
lean::cnstr_set(x_1309, 1, x_1307);
return x_1309;
}
}
else
{
obj* x_1310; obj* x_1311; obj* x_1312; obj* x_1313; 
lean::dec(x_1166);
x_1310 = lean::cnstr_get(x_1169, 0);
lean::inc(x_1310);
x_1311 = lean::cnstr_get(x_1169, 1);
lean::inc(x_1311);
if (lean::is_exclusive(x_1169)) {
 lean::cnstr_release(x_1169, 0);
 lean::cnstr_release(x_1169, 1);
 x_1312 = x_1169;
} else {
 lean::dec_ref(x_1169);
 x_1312 = lean::box(0);
}
if (lean::is_scalar(x_1312)) {
 x_1313 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1313 = x_1312;
}
lean::cnstr_set(x_1313, 0, x_1310);
lean::cnstr_set(x_1313, 1, x_1311);
return x_1313;
}
}
}
else
{
uint8 x_1314; 
lean::dec(x_1);
x_1314 = !lean::is_exclusive(x_11);
if (x_1314 == 0)
{
return x_11;
}
else
{
obj* x_1315; obj* x_1316; obj* x_1317; 
x_1315 = lean::cnstr_get(x_11, 0);
x_1316 = lean::cnstr_get(x_11, 1);
lean::inc(x_1316);
lean::inc(x_1315);
lean::dec(x_11);
x_1317 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_1317, 0, x_1315);
lean::cnstr_set(x_1317, 1, x_1316);
return x_1317;
}
}
}
else
{
obj* x_1318; obj* x_1319; obj* x_1320; obj* x_1321; obj* x_1322; 
x_1318 = lean::cnstr_get(x_6, 1);
lean::inc(x_1318);
lean::dec(x_6);
x_1319 = lean::box(0);
x_1320 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1320, 0, x_1319);
lean::cnstr_set(x_1320, 1, x_1318);
x_1321 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_1322 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1, x_1, x_1321, x_2, x_1320);
if (lean::obj_tag(x_1322) == 0)
{
obj* x_1323; obj* x_1324; obj* x_1325; obj* x_1326; obj* x_1327; obj* x_1328; obj* x_1329; 
x_1323 = lean::cnstr_get(x_1322, 1);
lean::inc(x_1323);
if (lean::is_exclusive(x_1322)) {
 lean::cnstr_release(x_1322, 0);
 lean::cnstr_release(x_1322, 1);
 x_1324 = x_1322;
} else {
 lean::dec_ref(x_1322);
 x_1324 = lean::box(0);
}
if (lean::is_scalar(x_1324)) {
 x_1325 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1325 = x_1324;
}
lean::cnstr_set(x_1325, 0, x_1319);
lean::cnstr_set(x_1325, 1, x_1323);
x_1326 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_1321, x_1);
x_1327 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__4;
x_1328 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
lean::inc(x_1326);
x_1329 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1327, x_1328, x_1326, x_2, x_1325);
if (lean::obj_tag(x_1329) == 0)
{
obj* x_1330; obj* x_1331; obj* x_1332; obj* x_1333; obj* x_1334; obj* x_1335; obj* x_1336; 
x_1330 = lean::cnstr_get(x_1329, 1);
lean::inc(x_1330);
if (lean::is_exclusive(x_1329)) {
 lean::cnstr_release(x_1329, 0);
 lean::cnstr_release(x_1329, 1);
 x_1331 = x_1329;
} else {
 lean::dec_ref(x_1329);
 x_1331 = lean::box(0);
}
if (lean::is_scalar(x_1331)) {
 x_1332 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1332 = x_1331;
}
lean::cnstr_set(x_1332, 0, x_1319);
lean::cnstr_set(x_1332, 1, x_1330);
x_1333 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(x_1321, x_1326);
x_1334 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__7;
x_1335 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
lean::inc(x_1333);
x_1336 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1334, x_1335, x_1333, x_2, x_1332);
if (lean::obj_tag(x_1336) == 0)
{
obj* x_1337; obj* x_1338; obj* x_1339; obj* x_1340; obj* x_1341; obj* x_1342; obj* x_1343; 
x_1337 = lean::cnstr_get(x_1336, 1);
lean::inc(x_1337);
if (lean::is_exclusive(x_1336)) {
 lean::cnstr_release(x_1336, 0);
 lean::cnstr_release(x_1336, 1);
 x_1338 = x_1336;
} else {
 lean::dec_ref(x_1336);
 x_1338 = lean::box(0);
}
if (lean::is_scalar(x_1338)) {
 x_1339 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1339 = x_1338;
}
lean::cnstr_set(x_1339, 0, x_1319);
lean::cnstr_set(x_1339, 1, x_1337);
x_1340 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(x_1321, x_1333);
x_1341 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
x_1342 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
lean::inc(x_1340);
x_1343 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1341, x_1342, x_1340, x_2, x_1339);
if (lean::obj_tag(x_1343) == 0)
{
obj* x_1344; obj* x_1345; obj* x_1346; obj* x_1347; obj* x_1348; obj* x_1349; obj* x_1350; 
x_1344 = lean::cnstr_get(x_1343, 1);
lean::inc(x_1344);
if (lean::is_exclusive(x_1343)) {
 lean::cnstr_release(x_1343, 0);
 lean::cnstr_release(x_1343, 1);
 x_1345 = x_1343;
} else {
 lean::dec_ref(x_1343);
 x_1345 = lean::box(0);
}
if (lean::is_scalar(x_1345)) {
 x_1346 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1346 = x_1345;
}
lean::cnstr_set(x_1346, 0, x_1319);
lean::cnstr_set(x_1346, 1, x_1344);
x_1347 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(x_1321, x_1340);
x_1348 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
x_1349 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean::inc(x_1347);
x_1350 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1348, x_1349, x_1347, x_2, x_1346);
if (lean::obj_tag(x_1350) == 0)
{
obj* x_1351; obj* x_1352; obj* x_1353; obj* x_1354; obj* x_1355; 
x_1351 = lean::cnstr_get(x_1350, 1);
lean::inc(x_1351);
if (lean::is_exclusive(x_1350)) {
 lean::cnstr_release(x_1350, 0);
 lean::cnstr_release(x_1350, 1);
 x_1352 = x_1350;
} else {
 lean::dec_ref(x_1350);
 x_1352 = lean::box(0);
}
if (lean::is_scalar(x_1352)) {
 x_1353 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1353 = x_1352;
}
lean::cnstr_set(x_1353, 0, x_1319);
lean::cnstr_set(x_1353, 1, x_1351);
x_1354 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_1321, x_1347);
x_1355 = l_Lean_IR_inferBorrow(x_1354, x_2, x_1353);
if (lean::obj_tag(x_1355) == 0)
{
obj* x_1356; obj* x_1357; obj* x_1358; obj* x_1359; obj* x_1360; obj* x_1361; obj* x_1362; 
x_1356 = lean::cnstr_get(x_1355, 0);
lean::inc(x_1356);
x_1357 = lean::cnstr_get(x_1355, 1);
lean::inc(x_1357);
if (lean::is_exclusive(x_1355)) {
 lean::cnstr_release(x_1355, 0);
 lean::cnstr_release(x_1355, 1);
 x_1358 = x_1355;
} else {
 lean::dec_ref(x_1355);
 x_1358 = lean::box(0);
}
if (lean::is_scalar(x_1358)) {
 x_1359 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1359 = x_1358;
}
lean::cnstr_set(x_1359, 0, x_1319);
lean::cnstr_set(x_1359, 1, x_1357);
x_1360 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_1361 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean::inc(x_1356);
x_1362 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1360, x_1361, x_1356, x_2, x_1359);
if (lean::obj_tag(x_1362) == 0)
{
obj* x_1363; obj* x_1364; obj* x_1365; obj* x_1366; 
x_1363 = lean::cnstr_get(x_1362, 1);
lean::inc(x_1363);
if (lean::is_exclusive(x_1362)) {
 lean::cnstr_release(x_1362, 0);
 lean::cnstr_release(x_1362, 1);
 x_1364 = x_1362;
} else {
 lean::dec_ref(x_1362);
 x_1364 = lean::box(0);
}
if (lean::is_scalar(x_1364)) {
 x_1365 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1365 = x_1364;
}
lean::cnstr_set(x_1365, 0, x_1319);
lean::cnstr_set(x_1365, 1, x_1363);
x_1366 = l_Lean_IR_explicitBoxing(x_1356, x_2, x_1365);
if (lean::obj_tag(x_1366) == 0)
{
obj* x_1367; obj* x_1368; obj* x_1369; obj* x_1370; obj* x_1371; obj* x_1372; obj* x_1373; 
x_1367 = lean::cnstr_get(x_1366, 0);
lean::inc(x_1367);
x_1368 = lean::cnstr_get(x_1366, 1);
lean::inc(x_1368);
if (lean::is_exclusive(x_1366)) {
 lean::cnstr_release(x_1366, 0);
 lean::cnstr_release(x_1366, 1);
 x_1369 = x_1366;
} else {
 lean::dec_ref(x_1366);
 x_1369 = lean::box(0);
}
if (lean::is_scalar(x_1369)) {
 x_1370 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1370 = x_1369;
}
lean::cnstr_set(x_1370, 0, x_1319);
lean::cnstr_set(x_1370, 1, x_1368);
x_1371 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_1372 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean::inc(x_1367);
x_1373 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1371, x_1372, x_1367, x_2, x_1370);
if (lean::obj_tag(x_1373) == 0)
{
obj* x_1374; obj* x_1375; obj* x_1376; obj* x_1377; 
x_1374 = lean::cnstr_get(x_1373, 1);
lean::inc(x_1374);
if (lean::is_exclusive(x_1373)) {
 lean::cnstr_release(x_1373, 0);
 lean::cnstr_release(x_1373, 1);
 x_1375 = x_1373;
} else {
 lean::dec_ref(x_1373);
 x_1375 = lean::box(0);
}
if (lean::is_scalar(x_1375)) {
 x_1376 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1376 = x_1375;
}
lean::cnstr_set(x_1376, 0, x_1319);
lean::cnstr_set(x_1376, 1, x_1374);
x_1377 = l_Lean_IR_explicitRC(x_1367, x_2, x_1376);
if (lean::obj_tag(x_1377) == 0)
{
obj* x_1378; obj* x_1379; obj* x_1380; obj* x_1381; obj* x_1382; obj* x_1383; obj* x_1384; 
x_1378 = lean::cnstr_get(x_1377, 0);
lean::inc(x_1378);
x_1379 = lean::cnstr_get(x_1377, 1);
lean::inc(x_1379);
if (lean::is_exclusive(x_1377)) {
 lean::cnstr_release(x_1377, 0);
 lean::cnstr_release(x_1377, 1);
 x_1380 = x_1377;
} else {
 lean::dec_ref(x_1377);
 x_1380 = lean::box(0);
}
if (lean::is_scalar(x_1380)) {
 x_1381 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1381 = x_1380;
}
lean::cnstr_set(x_1381, 0, x_1319);
lean::cnstr_set(x_1381, 1, x_1379);
x_1382 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_1383 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean::inc(x_1378);
x_1384 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1382, x_1383, x_1378, x_2, x_1381);
if (lean::obj_tag(x_1384) == 0)
{
obj* x_1385; obj* x_1386; obj* x_1387; obj* x_1388; obj* x_1389; obj* x_1390; obj* x_1391; 
x_1385 = lean::cnstr_get(x_1384, 1);
lean::inc(x_1385);
if (lean::is_exclusive(x_1384)) {
 lean::cnstr_release(x_1384, 0);
 lean::cnstr_release(x_1384, 1);
 x_1386 = x_1384;
} else {
 lean::dec_ref(x_1384);
 x_1386 = lean::box(0);
}
if (lean::is_scalar(x_1386)) {
 x_1387 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1387 = x_1386;
}
lean::cnstr_set(x_1387, 0, x_1319);
lean::cnstr_set(x_1387, 1, x_1385);
x_1388 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_1321, x_1378);
x_1389 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_1390 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean::inc(x_1388);
x_1391 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1389, x_1390, x_1388, x_2, x_1387);
if (lean::obj_tag(x_1391) == 0)
{
obj* x_1392; obj* x_1393; obj* x_1394; obj* x_1395; obj* x_1396; 
x_1392 = lean::cnstr_get(x_1391, 1);
lean::inc(x_1392);
if (lean::is_exclusive(x_1391)) {
 lean::cnstr_release(x_1391, 0);
 lean::cnstr_release(x_1391, 1);
 x_1393 = x_1391;
} else {
 lean::dec_ref(x_1391);
 x_1393 = lean::box(0);
}
if (lean::is_scalar(x_1393)) {
 x_1394 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1394 = x_1393;
}
lean::cnstr_set(x_1394, 0, x_1319);
lean::cnstr_set(x_1394, 1, x_1392);
x_1395 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_1321, x_1388);
lean::inc(x_1395);
x_1396 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1327, x_1328, x_1395, x_2, x_1394);
if (lean::obj_tag(x_1396) == 0)
{
obj* x_1397; obj* x_1398; obj* x_1399; obj* x_1400; obj* x_1401; obj* x_1402; 
x_1397 = lean::cnstr_get(x_1396, 1);
lean::inc(x_1397);
if (lean::is_exclusive(x_1396)) {
 lean::cnstr_release(x_1396, 0);
 lean::cnstr_release(x_1396, 1);
 x_1398 = x_1396;
} else {
 lean::dec_ref(x_1396);
 x_1398 = lean::box(0);
}
if (lean::is_scalar(x_1398)) {
 x_1399 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1399 = x_1398;
}
lean::cnstr_set(x_1399, 0, x_1319);
lean::cnstr_set(x_1399, 1, x_1397);
x_1400 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_1401 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean::inc(x_1395);
x_1402 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1400, x_1401, x_1395, x_2, x_1399);
if (lean::obj_tag(x_1402) == 0)
{
obj* x_1403; obj* x_1404; obj* x_1405; obj* x_1406; 
x_1403 = lean::cnstr_get(x_1402, 1);
lean::inc(x_1403);
if (lean::is_exclusive(x_1402)) {
 lean::cnstr_release(x_1402, 0);
 lean::cnstr_release(x_1402, 1);
 x_1404 = x_1402;
} else {
 lean::dec_ref(x_1402);
 x_1404 = lean::box(0);
}
if (lean::is_scalar(x_1404)) {
 x_1405 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1405 = x_1404;
}
lean::cnstr_set(x_1405, 0, x_1319);
lean::cnstr_set(x_1405, 1, x_1403);
lean::inc(x_1395);
x_1406 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1395, x_1395, x_1321, x_2, x_1405);
if (lean::obj_tag(x_1406) == 0)
{
obj* x_1407; obj* x_1408; obj* x_1409; obj* x_1410; 
x_1407 = lean::cnstr_get(x_1406, 1);
lean::inc(x_1407);
if (lean::is_exclusive(x_1406)) {
 lean::cnstr_release(x_1406, 0);
 lean::cnstr_release(x_1406, 1);
 x_1408 = x_1406;
} else {
 lean::dec_ref(x_1406);
 x_1408 = lean::box(0);
}
if (lean::is_scalar(x_1408)) {
 x_1409 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1409 = x_1408;
}
lean::cnstr_set(x_1409, 0, x_1319);
lean::cnstr_set(x_1409, 1, x_1407);
x_1410 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_1395, x_1321, x_2, x_1409);
lean::dec(x_1395);
if (lean::obj_tag(x_1410) == 0)
{
obj* x_1411; obj* x_1412; obj* x_1413; 
x_1411 = lean::cnstr_get(x_1410, 1);
lean::inc(x_1411);
if (lean::is_exclusive(x_1410)) {
 lean::cnstr_release(x_1410, 0);
 lean::cnstr_release(x_1410, 1);
 x_1412 = x_1410;
} else {
 lean::dec_ref(x_1410);
 x_1412 = lean::box(0);
}
if (lean::is_scalar(x_1412)) {
 x_1413 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1413 = x_1412;
}
lean::cnstr_set(x_1413, 0, x_1319);
lean::cnstr_set(x_1413, 1, x_1411);
return x_1413;
}
else
{
obj* x_1414; obj* x_1415; obj* x_1416; obj* x_1417; 
x_1414 = lean::cnstr_get(x_1410, 0);
lean::inc(x_1414);
x_1415 = lean::cnstr_get(x_1410, 1);
lean::inc(x_1415);
if (lean::is_exclusive(x_1410)) {
 lean::cnstr_release(x_1410, 0);
 lean::cnstr_release(x_1410, 1);
 x_1416 = x_1410;
} else {
 lean::dec_ref(x_1410);
 x_1416 = lean::box(0);
}
if (lean::is_scalar(x_1416)) {
 x_1417 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1417 = x_1416;
}
lean::cnstr_set(x_1417, 0, x_1414);
lean::cnstr_set(x_1417, 1, x_1415);
return x_1417;
}
}
else
{
obj* x_1418; obj* x_1419; obj* x_1420; obj* x_1421; 
lean::dec(x_1395);
x_1418 = lean::cnstr_get(x_1406, 0);
lean::inc(x_1418);
x_1419 = lean::cnstr_get(x_1406, 1);
lean::inc(x_1419);
if (lean::is_exclusive(x_1406)) {
 lean::cnstr_release(x_1406, 0);
 lean::cnstr_release(x_1406, 1);
 x_1420 = x_1406;
} else {
 lean::dec_ref(x_1406);
 x_1420 = lean::box(0);
}
if (lean::is_scalar(x_1420)) {
 x_1421 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1421 = x_1420;
}
lean::cnstr_set(x_1421, 0, x_1418);
lean::cnstr_set(x_1421, 1, x_1419);
return x_1421;
}
}
else
{
obj* x_1422; obj* x_1423; obj* x_1424; obj* x_1425; 
lean::dec(x_1395);
x_1422 = lean::cnstr_get(x_1402, 0);
lean::inc(x_1422);
x_1423 = lean::cnstr_get(x_1402, 1);
lean::inc(x_1423);
if (lean::is_exclusive(x_1402)) {
 lean::cnstr_release(x_1402, 0);
 lean::cnstr_release(x_1402, 1);
 x_1424 = x_1402;
} else {
 lean::dec_ref(x_1402);
 x_1424 = lean::box(0);
}
if (lean::is_scalar(x_1424)) {
 x_1425 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1425 = x_1424;
}
lean::cnstr_set(x_1425, 0, x_1422);
lean::cnstr_set(x_1425, 1, x_1423);
return x_1425;
}
}
else
{
obj* x_1426; obj* x_1427; obj* x_1428; obj* x_1429; 
lean::dec(x_1395);
x_1426 = lean::cnstr_get(x_1396, 0);
lean::inc(x_1426);
x_1427 = lean::cnstr_get(x_1396, 1);
lean::inc(x_1427);
if (lean::is_exclusive(x_1396)) {
 lean::cnstr_release(x_1396, 0);
 lean::cnstr_release(x_1396, 1);
 x_1428 = x_1396;
} else {
 lean::dec_ref(x_1396);
 x_1428 = lean::box(0);
}
if (lean::is_scalar(x_1428)) {
 x_1429 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1429 = x_1428;
}
lean::cnstr_set(x_1429, 0, x_1426);
lean::cnstr_set(x_1429, 1, x_1427);
return x_1429;
}
}
else
{
obj* x_1430; obj* x_1431; obj* x_1432; obj* x_1433; 
lean::dec(x_1388);
x_1430 = lean::cnstr_get(x_1391, 0);
lean::inc(x_1430);
x_1431 = lean::cnstr_get(x_1391, 1);
lean::inc(x_1431);
if (lean::is_exclusive(x_1391)) {
 lean::cnstr_release(x_1391, 0);
 lean::cnstr_release(x_1391, 1);
 x_1432 = x_1391;
} else {
 lean::dec_ref(x_1391);
 x_1432 = lean::box(0);
}
if (lean::is_scalar(x_1432)) {
 x_1433 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1433 = x_1432;
}
lean::cnstr_set(x_1433, 0, x_1430);
lean::cnstr_set(x_1433, 1, x_1431);
return x_1433;
}
}
else
{
obj* x_1434; obj* x_1435; obj* x_1436; obj* x_1437; 
lean::dec(x_1378);
x_1434 = lean::cnstr_get(x_1384, 0);
lean::inc(x_1434);
x_1435 = lean::cnstr_get(x_1384, 1);
lean::inc(x_1435);
if (lean::is_exclusive(x_1384)) {
 lean::cnstr_release(x_1384, 0);
 lean::cnstr_release(x_1384, 1);
 x_1436 = x_1384;
} else {
 lean::dec_ref(x_1384);
 x_1436 = lean::box(0);
}
if (lean::is_scalar(x_1436)) {
 x_1437 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1437 = x_1436;
}
lean::cnstr_set(x_1437, 0, x_1434);
lean::cnstr_set(x_1437, 1, x_1435);
return x_1437;
}
}
else
{
obj* x_1438; obj* x_1439; obj* x_1440; obj* x_1441; 
x_1438 = lean::cnstr_get(x_1377, 0);
lean::inc(x_1438);
x_1439 = lean::cnstr_get(x_1377, 1);
lean::inc(x_1439);
if (lean::is_exclusive(x_1377)) {
 lean::cnstr_release(x_1377, 0);
 lean::cnstr_release(x_1377, 1);
 x_1440 = x_1377;
} else {
 lean::dec_ref(x_1377);
 x_1440 = lean::box(0);
}
if (lean::is_scalar(x_1440)) {
 x_1441 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1441 = x_1440;
}
lean::cnstr_set(x_1441, 0, x_1438);
lean::cnstr_set(x_1441, 1, x_1439);
return x_1441;
}
}
else
{
obj* x_1442; obj* x_1443; obj* x_1444; obj* x_1445; 
lean::dec(x_1367);
x_1442 = lean::cnstr_get(x_1373, 0);
lean::inc(x_1442);
x_1443 = lean::cnstr_get(x_1373, 1);
lean::inc(x_1443);
if (lean::is_exclusive(x_1373)) {
 lean::cnstr_release(x_1373, 0);
 lean::cnstr_release(x_1373, 1);
 x_1444 = x_1373;
} else {
 lean::dec_ref(x_1373);
 x_1444 = lean::box(0);
}
if (lean::is_scalar(x_1444)) {
 x_1445 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1445 = x_1444;
}
lean::cnstr_set(x_1445, 0, x_1442);
lean::cnstr_set(x_1445, 1, x_1443);
return x_1445;
}
}
else
{
obj* x_1446; obj* x_1447; obj* x_1448; obj* x_1449; 
x_1446 = lean::cnstr_get(x_1366, 0);
lean::inc(x_1446);
x_1447 = lean::cnstr_get(x_1366, 1);
lean::inc(x_1447);
if (lean::is_exclusive(x_1366)) {
 lean::cnstr_release(x_1366, 0);
 lean::cnstr_release(x_1366, 1);
 x_1448 = x_1366;
} else {
 lean::dec_ref(x_1366);
 x_1448 = lean::box(0);
}
if (lean::is_scalar(x_1448)) {
 x_1449 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1449 = x_1448;
}
lean::cnstr_set(x_1449, 0, x_1446);
lean::cnstr_set(x_1449, 1, x_1447);
return x_1449;
}
}
else
{
obj* x_1450; obj* x_1451; obj* x_1452; obj* x_1453; 
lean::dec(x_1356);
x_1450 = lean::cnstr_get(x_1362, 0);
lean::inc(x_1450);
x_1451 = lean::cnstr_get(x_1362, 1);
lean::inc(x_1451);
if (lean::is_exclusive(x_1362)) {
 lean::cnstr_release(x_1362, 0);
 lean::cnstr_release(x_1362, 1);
 x_1452 = x_1362;
} else {
 lean::dec_ref(x_1362);
 x_1452 = lean::box(0);
}
if (lean::is_scalar(x_1452)) {
 x_1453 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1453 = x_1452;
}
lean::cnstr_set(x_1453, 0, x_1450);
lean::cnstr_set(x_1453, 1, x_1451);
return x_1453;
}
}
else
{
obj* x_1454; obj* x_1455; obj* x_1456; obj* x_1457; 
x_1454 = lean::cnstr_get(x_1355, 0);
lean::inc(x_1454);
x_1455 = lean::cnstr_get(x_1355, 1);
lean::inc(x_1455);
if (lean::is_exclusive(x_1355)) {
 lean::cnstr_release(x_1355, 0);
 lean::cnstr_release(x_1355, 1);
 x_1456 = x_1355;
} else {
 lean::dec_ref(x_1355);
 x_1456 = lean::box(0);
}
if (lean::is_scalar(x_1456)) {
 x_1457 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1457 = x_1456;
}
lean::cnstr_set(x_1457, 0, x_1454);
lean::cnstr_set(x_1457, 1, x_1455);
return x_1457;
}
}
else
{
obj* x_1458; obj* x_1459; obj* x_1460; obj* x_1461; 
lean::dec(x_1347);
x_1458 = lean::cnstr_get(x_1350, 0);
lean::inc(x_1458);
x_1459 = lean::cnstr_get(x_1350, 1);
lean::inc(x_1459);
if (lean::is_exclusive(x_1350)) {
 lean::cnstr_release(x_1350, 0);
 lean::cnstr_release(x_1350, 1);
 x_1460 = x_1350;
} else {
 lean::dec_ref(x_1350);
 x_1460 = lean::box(0);
}
if (lean::is_scalar(x_1460)) {
 x_1461 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1461 = x_1460;
}
lean::cnstr_set(x_1461, 0, x_1458);
lean::cnstr_set(x_1461, 1, x_1459);
return x_1461;
}
}
else
{
obj* x_1462; obj* x_1463; obj* x_1464; obj* x_1465; 
lean::dec(x_1340);
x_1462 = lean::cnstr_get(x_1343, 0);
lean::inc(x_1462);
x_1463 = lean::cnstr_get(x_1343, 1);
lean::inc(x_1463);
if (lean::is_exclusive(x_1343)) {
 lean::cnstr_release(x_1343, 0);
 lean::cnstr_release(x_1343, 1);
 x_1464 = x_1343;
} else {
 lean::dec_ref(x_1343);
 x_1464 = lean::box(0);
}
if (lean::is_scalar(x_1464)) {
 x_1465 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1465 = x_1464;
}
lean::cnstr_set(x_1465, 0, x_1462);
lean::cnstr_set(x_1465, 1, x_1463);
return x_1465;
}
}
else
{
obj* x_1466; obj* x_1467; obj* x_1468; obj* x_1469; 
lean::dec(x_1333);
x_1466 = lean::cnstr_get(x_1336, 0);
lean::inc(x_1466);
x_1467 = lean::cnstr_get(x_1336, 1);
lean::inc(x_1467);
if (lean::is_exclusive(x_1336)) {
 lean::cnstr_release(x_1336, 0);
 lean::cnstr_release(x_1336, 1);
 x_1468 = x_1336;
} else {
 lean::dec_ref(x_1336);
 x_1468 = lean::box(0);
}
if (lean::is_scalar(x_1468)) {
 x_1469 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1469 = x_1468;
}
lean::cnstr_set(x_1469, 0, x_1466);
lean::cnstr_set(x_1469, 1, x_1467);
return x_1469;
}
}
else
{
obj* x_1470; obj* x_1471; obj* x_1472; obj* x_1473; 
lean::dec(x_1326);
x_1470 = lean::cnstr_get(x_1329, 0);
lean::inc(x_1470);
x_1471 = lean::cnstr_get(x_1329, 1);
lean::inc(x_1471);
if (lean::is_exclusive(x_1329)) {
 lean::cnstr_release(x_1329, 0);
 lean::cnstr_release(x_1329, 1);
 x_1472 = x_1329;
} else {
 lean::dec_ref(x_1329);
 x_1472 = lean::box(0);
}
if (lean::is_scalar(x_1472)) {
 x_1473 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1473 = x_1472;
}
lean::cnstr_set(x_1473, 0, x_1470);
lean::cnstr_set(x_1473, 1, x_1471);
return x_1473;
}
}
else
{
obj* x_1474; obj* x_1475; obj* x_1476; obj* x_1477; 
lean::dec(x_1);
x_1474 = lean::cnstr_get(x_1322, 0);
lean::inc(x_1474);
x_1475 = lean::cnstr_get(x_1322, 1);
lean::inc(x_1475);
if (lean::is_exclusive(x_1322)) {
 lean::cnstr_release(x_1322, 0);
 lean::cnstr_release(x_1322, 1);
 x_1476 = x_1322;
} else {
 lean::dec_ref(x_1322);
 x_1476 = lean::box(0);
}
if (lean::is_scalar(x_1476)) {
 x_1477 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_1477 = x_1476;
}
lean::cnstr_set(x_1477, 0, x_1474);
lean::cnstr_set(x_1477, 1, x_1475);
return x_1477;
}
}
}
else
{
uint8 x_1478; 
lean::dec(x_1);
x_1478 = !lean::is_exclusive(x_6);
if (x_1478 == 0)
{
return x_6;
}
else
{
obj* x_1479; obj* x_1480; obj* x_1481; 
x_1479 = lean::cnstr_get(x_6, 0);
x_1480 = lean::cnstr_get(x_6, 1);
lean::inc(x_1480);
lean::inc(x_1479);
lean::dec(x_6);
x_1481 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_1481, 0, x_1479);
lean::cnstr_set(x_1481, 1, x_1480);
return x_1481;
}
}
}
}
obj* l___private_init_lean_compiler_ir_default_1__compileAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_default_1__compileAux(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* lean_ir_compile(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_Array_empty___closed__1;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
x_8 = l___private_init_lean_compiler_ir_default_1__compileAux(x_3, x_2, x_7);
lean::dec(x_2);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_10);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
lean::dec(x_8);
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
lean::dec(x_15);
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_14);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
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
obj* initialize_init_lean_compiler_ir_emitc(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_default(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_format(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_pushproj(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_elimdead(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_simpcase(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_resetreuse(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_normids(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_checker(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_borrow(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_boxing(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_rc(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_expandresetreuse(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_emitcpp(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_emitc(w);
if (lean::io_result_is_error(w)) return w;
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
l___private_init_lean_compiler_ir_default_1__compileAux___closed__21 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__21();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__21);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__22 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__22();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__22);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__23 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__23();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__23);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__24 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__24();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__24);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__25 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__25();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__25);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__26 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__26();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__26);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__27 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__27();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__27);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__28 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__28();
lean::mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__28);
return w;
}
