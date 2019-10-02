// Lean compiler output
// Module: init.lean.compiler.ir.default
// Imports: init.lean.compiler.ir.basic init.lean.compiler.ir.format init.lean.compiler.ir.compilerm init.lean.compiler.ir.pushproj init.lean.compiler.ir.elimdead init.lean.compiler.ir.simpcase init.lean.compiler.ir.resetreuse init.lean.compiler.ir.normids init.lean.compiler.ir.checker init.lean.compiler.ir.borrow init.lean.compiler.ir.boxing init.lean.compiler.ir.rc init.lean.compiler.ir.expandresetreuse init.lean.compiler.ir.unboxresult init.lean.compiler.ir.emitc
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_addBoxedVersionAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__5;
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__2;
lean_object* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_pushProj(lean_object*);
lean_object* l_Array_mkArray(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__20;
lean_object* l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
extern lean_object* l_Lean_Options_empty;
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__11;
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__14;
extern lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__23;
lean_object* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_object* l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_IR_inferBorrow(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
lean_object* l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__1;
extern lean_object* l_Lean_IR_declMapExt;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__8;
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__7;
lean_object* l_Lean_IR_Decl_simpCase(lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_main(lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__4;
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__26;
lean_object* l_Array_size(lean_object*, lean_object*);
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object*);
lean_object* lean_ir_compile(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__17;
lean_object* lean_ir_add_boxed_version(lean_object*, lean_object*);
lean_object* l_Array_set(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
extern lean_object* l_Lean_mkInitAttr___closed__2;
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_explicitRC(lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
lean_object* l_Lean_IR_addBoxedVersionAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_explicitBoxing(lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean_object* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
lean_inc(x_7);
x_11 = l_Lean_IR_Decl_pushProj(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
lean_inc(x_7);
x_11 = l_Lean_IR_Decl_insertResetReuse(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
lean_inc(x_7);
x_11 = l_Lean_IR_Decl_elimDead(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
lean_inc(x_7);
x_11 = l_Lean_IR_Decl_simpCase(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
lean_inc(x_7);
x_11 = l_Lean_IR_ExpandResetReuse_main(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l_Lean_mkInitAttr___closed__2;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("push_proj");
return x_1;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reset_reuse");
return x_1;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elim_dead");
return x_1;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simp_case");
return x_1;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("borrow");
return x_1;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("boxing");
return x_1;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rc");
return x_1;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__20;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expand_reset_reuse");
return x_1;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__23;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result");
return x_1;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__1;
x_5 = l_Lean_mkInitAttr___closed__2;
lean_inc(x_1);
x_6 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_4, x_5, x_1, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_6, 0, x_9);
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_11 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1, x_1, x_10, x_2, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_9);
x_14 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_1);
x_15 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__4;
x_16 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
lean_inc(x_14);
x_17 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_14, x_2, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_9);
x_20 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(x_10, x_14);
x_21 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__7;
x_22 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
lean_inc(x_20);
x_23 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_21, x_22, x_20, x_2, x_17);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_9);
x_26 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(x_10, x_20);
x_27 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
x_28 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
lean_inc(x_26);
x_29 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_27, x_28, x_26, x_2, x_23);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_9);
x_32 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(x_10, x_26);
x_33 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
x_34 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean_inc(x_32);
x_35 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_33, x_34, x_32, x_2, x_29);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_9);
x_38 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_32);
x_39 = l_Lean_IR_inferBorrow(x_38, x_2, x_35);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_39, 0);
lean_ctor_set(x_39, 0, x_9);
x_42 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_43 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean_inc(x_41);
x_44 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_42, x_43, x_41, x_2, x_39);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set(x_44, 0, x_9);
x_47 = l_Lean_IR_explicitBoxing(x_41, x_2, x_44);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_47, 0);
lean_ctor_set(x_47, 0, x_9);
x_50 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_51 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean_inc(x_49);
x_52 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_50, x_51, x_49, x_2, x_47);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_9);
x_55 = l_Lean_IR_explicitRC(x_49, x_2, x_52);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_55, 0);
lean_ctor_set(x_55, 0, x_9);
x_58 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_59 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean_inc(x_57);
x_60 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_58, x_59, x_57, x_2, x_55);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set(x_60, 0, x_9);
x_63 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_57);
x_64 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_65 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean_inc(x_63);
x_66 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_64, x_65, x_63, x_2, x_60);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_9);
x_69 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_63);
lean_inc(x_69);
x_70 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_69, x_2, x_66);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_9);
x_73 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_74 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_69);
x_75 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_73, x_74, x_69, x_2, x_70);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
lean_ctor_set(x_75, 0, x_9);
lean_inc(x_69);
x_78 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_69, x_69, x_10, x_2, x_75);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
lean_ctor_set(x_78, 0, x_9);
x_81 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_69, x_10, x_2, x_78);
lean_dec(x_69);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
lean_ctor_set(x_81, 0, x_9);
return x_81;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_9);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_81);
if (x_86 == 0)
{
return x_81;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_81, 0);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_81);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_78, 1);
lean_inc(x_90);
lean_dec(x_78);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_9);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_69, x_10, x_2, x_91);
lean_dec(x_69);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_9);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_98 = x_92;
} else {
 lean_dec_ref(x_92);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_69);
x_100 = !lean_is_exclusive(x_78);
if (x_100 == 0)
{
return x_78;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_78, 0);
x_102 = lean_ctor_get(x_78, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_78);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_75, 1);
lean_inc(x_104);
lean_dec(x_75);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_9);
lean_ctor_set(x_105, 1, x_104);
lean_inc(x_69);
x_106 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_69, x_69, x_10, x_2, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_9);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_69, x_10, x_2, x_109);
lean_dec(x_69);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_9);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_110, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_116 = x_110;
} else {
 lean_dec_ref(x_110);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_69);
x_118 = lean_ctor_get(x_106, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_120 = x_106;
} else {
 lean_dec_ref(x_106);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_69);
x_122 = !lean_is_exclusive(x_75);
if (x_122 == 0)
{
return x_75;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_75, 0);
x_124 = lean_ctor_get(x_75, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_75);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_70, 1);
lean_inc(x_126);
lean_dec(x_70);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_9);
lean_ctor_set(x_127, 1, x_126);
x_128 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_129 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_69);
x_130 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_128, x_129, x_69, x_2, x_127);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_9);
lean_ctor_set(x_133, 1, x_131);
lean_inc(x_69);
x_134 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_69, x_69, x_10, x_2, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_9);
lean_ctor_set(x_137, 1, x_135);
x_138 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_69, x_10, x_2, x_137);
lean_dec(x_69);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_9);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_138, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_144 = x_138;
} else {
 lean_dec_ref(x_138);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_69);
x_146 = lean_ctor_get(x_134, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_134, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_148 = x_134;
} else {
 lean_dec_ref(x_134);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_69);
x_150 = lean_ctor_get(x_130, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_130, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_152 = x_130;
} else {
 lean_dec_ref(x_130);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_69);
x_154 = !lean_is_exclusive(x_70);
if (x_154 == 0)
{
return x_70;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_70, 0);
x_156 = lean_ctor_get(x_70, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_70);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_66, 1);
lean_inc(x_158);
lean_dec(x_66);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_9);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_63);
lean_inc(x_160);
x_161 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_160, x_2, x_159);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_9);
lean_ctor_set(x_164, 1, x_162);
x_165 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_166 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_160);
x_167 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_165, x_166, x_160, x_2, x_164);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_9);
lean_ctor_set(x_170, 1, x_168);
lean_inc(x_160);
x_171 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_160, x_160, x_10, x_2, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_173 = x_171;
} else {
 lean_dec_ref(x_171);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_9);
lean_ctor_set(x_174, 1, x_172);
x_175 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_160, x_10, x_2, x_174);
lean_dec(x_160);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_177 = x_175;
} else {
 lean_dec_ref(x_175);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_9);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_175, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_175, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_181 = x_175;
} else {
 lean_dec_ref(x_175);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_160);
x_183 = lean_ctor_get(x_171, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_171, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_185 = x_171;
} else {
 lean_dec_ref(x_171);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_160);
x_187 = lean_ctor_get(x_167, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_167, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_189 = x_167;
} else {
 lean_dec_ref(x_167);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_160);
x_191 = lean_ctor_get(x_161, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_161, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_193 = x_161;
} else {
 lean_dec_ref(x_161);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_63);
x_195 = !lean_is_exclusive(x_66);
if (x_195 == 0)
{
return x_66;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_66, 0);
x_197 = lean_ctor_get(x_66, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_66);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_199 = lean_ctor_get(x_60, 1);
lean_inc(x_199);
lean_dec(x_60);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_9);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_57);
x_202 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_203 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean_inc(x_201);
x_204 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_202, x_203, x_201, x_2, x_200);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_9);
lean_ctor_set(x_207, 1, x_205);
x_208 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_201);
lean_inc(x_208);
x_209 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_208, x_2, x_207);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_211 = x_209;
} else {
 lean_dec_ref(x_209);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_9);
lean_ctor_set(x_212, 1, x_210);
x_213 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_214 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_208);
x_215 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_213, x_214, x_208, x_2, x_212);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_217 = x_215;
} else {
 lean_dec_ref(x_215);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_9);
lean_ctor_set(x_218, 1, x_216);
lean_inc(x_208);
x_219 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_208, x_208, x_10, x_2, x_218);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_221 = x_219;
} else {
 lean_dec_ref(x_219);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_9);
lean_ctor_set(x_222, 1, x_220);
x_223 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_208, x_10, x_2, x_222);
lean_dec(x_208);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_225 = x_223;
} else {
 lean_dec_ref(x_223);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_9);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_227 = lean_ctor_get(x_223, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_223, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_229 = x_223;
} else {
 lean_dec_ref(x_223);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_208);
x_231 = lean_ctor_get(x_219, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_219, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_233 = x_219;
} else {
 lean_dec_ref(x_219);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_208);
x_235 = lean_ctor_get(x_215, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_215, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_237 = x_215;
} else {
 lean_dec_ref(x_215);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(1, 2, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_236);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_208);
x_239 = lean_ctor_get(x_209, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_209, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_241 = x_209;
} else {
 lean_dec_ref(x_209);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_240);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_201);
x_243 = lean_ctor_get(x_204, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_204, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_245 = x_204;
} else {
 lean_dec_ref(x_204);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
}
else
{
uint8_t x_247; 
lean_dec(x_57);
x_247 = !lean_is_exclusive(x_60);
if (x_247 == 0)
{
return x_60;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_60, 0);
x_249 = lean_ctor_get(x_60, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_60);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_251 = lean_ctor_get(x_55, 0);
x_252 = lean_ctor_get(x_55, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_55);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_9);
lean_ctor_set(x_253, 1, x_252);
x_254 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_255 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean_inc(x_251);
x_256 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_254, x_255, x_251, x_2, x_253);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_258 = x_256;
} else {
 lean_dec_ref(x_256);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_9);
lean_ctor_set(x_259, 1, x_257);
x_260 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_251);
x_261 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_262 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean_inc(x_260);
x_263 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_261, x_262, x_260, x_2, x_259);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_265 = x_263;
} else {
 lean_dec_ref(x_263);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_9);
lean_ctor_set(x_266, 1, x_264);
x_267 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_260);
lean_inc(x_267);
x_268 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_267, x_2, x_266);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_270 = x_268;
} else {
 lean_dec_ref(x_268);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_9);
lean_ctor_set(x_271, 1, x_269);
x_272 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_273 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_267);
x_274 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_272, x_273, x_267, x_2, x_271);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_9);
lean_ctor_set(x_277, 1, x_275);
lean_inc(x_267);
x_278 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_267, x_267, x_10, x_2, x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_280 = x_278;
} else {
 lean_dec_ref(x_278);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_9);
lean_ctor_set(x_281, 1, x_279);
x_282 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_267, x_10, x_2, x_281);
lean_dec(x_267);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_284 = x_282;
} else {
 lean_dec_ref(x_282);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_9);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_286 = lean_ctor_get(x_282, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_282, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_288 = x_282;
} else {
 lean_dec_ref(x_282);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_267);
x_290 = lean_ctor_get(x_278, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_278, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_292 = x_278;
} else {
 lean_dec_ref(x_278);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_267);
x_294 = lean_ctor_get(x_274, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_274, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_296 = x_274;
} else {
 lean_dec_ref(x_274);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_296)) {
 x_297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_297 = x_296;
}
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_295);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_267);
x_298 = lean_ctor_get(x_268, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_268, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_300 = x_268;
} else {
 lean_dec_ref(x_268);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_299);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_260);
x_302 = lean_ctor_get(x_263, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_263, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_304 = x_263;
} else {
 lean_dec_ref(x_263);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_302);
lean_ctor_set(x_305, 1, x_303);
return x_305;
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_251);
x_306 = lean_ctor_get(x_256, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_256, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_308 = x_256;
} else {
 lean_dec_ref(x_256);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
}
else
{
uint8_t x_310; 
x_310 = !lean_is_exclusive(x_55);
if (x_310 == 0)
{
return x_55;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_55, 0);
x_312 = lean_ctor_get(x_55, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_55);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_52, 1);
lean_inc(x_314);
lean_dec(x_52);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_9);
lean_ctor_set(x_315, 1, x_314);
x_316 = l_Lean_IR_explicitRC(x_49, x_2, x_315);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_319 = x_316;
} else {
 lean_dec_ref(x_316);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_9);
lean_ctor_set(x_320, 1, x_318);
x_321 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_322 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean_inc(x_317);
x_323 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_321, x_322, x_317, x_2, x_320);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_324 = lean_ctor_get(x_323, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_325 = x_323;
} else {
 lean_dec_ref(x_323);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_9);
lean_ctor_set(x_326, 1, x_324);
x_327 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_317);
x_328 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_329 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean_inc(x_327);
x_330 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_328, x_329, x_327, x_2, x_326);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_332 = x_330;
} else {
 lean_dec_ref(x_330);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_9);
lean_ctor_set(x_333, 1, x_331);
x_334 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_327);
lean_inc(x_334);
x_335 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_334, x_2, x_333);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_336 = lean_ctor_get(x_335, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_337 = x_335;
} else {
 lean_dec_ref(x_335);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_9);
lean_ctor_set(x_338, 1, x_336);
x_339 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_340 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_334);
x_341 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_339, x_340, x_334, x_2, x_338);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_342 = lean_ctor_get(x_341, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_343 = x_341;
} else {
 lean_dec_ref(x_341);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_9);
lean_ctor_set(x_344, 1, x_342);
lean_inc(x_334);
x_345 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_334, x_334, x_10, x_2, x_344);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_346 = lean_ctor_get(x_345, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_347 = x_345;
} else {
 lean_dec_ref(x_345);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_9);
lean_ctor_set(x_348, 1, x_346);
x_349 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_334, x_10, x_2, x_348);
lean_dec(x_334);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_349, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_351 = x_349;
} else {
 lean_dec_ref(x_349);
 x_351 = lean_box(0);
}
if (lean_is_scalar(x_351)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_351;
}
lean_ctor_set(x_352, 0, x_9);
lean_ctor_set(x_352, 1, x_350);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_353 = lean_ctor_get(x_349, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_349, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_355 = x_349;
} else {
 lean_dec_ref(x_349);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_353);
lean_ctor_set(x_356, 1, x_354);
return x_356;
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_334);
x_357 = lean_ctor_get(x_345, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_345, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_359 = x_345;
} else {
 lean_dec_ref(x_345);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_334);
x_361 = lean_ctor_get(x_341, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_341, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_363 = x_341;
} else {
 lean_dec_ref(x_341);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(1, 2, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_361);
lean_ctor_set(x_364, 1, x_362);
return x_364;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_334);
x_365 = lean_ctor_get(x_335, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_335, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_367 = x_335;
} else {
 lean_dec_ref(x_335);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(1, 2, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_327);
x_369 = lean_ctor_get(x_330, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_330, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_371 = x_330;
} else {
 lean_dec_ref(x_330);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(1, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_317);
x_373 = lean_ctor_get(x_323, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_323, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_375 = x_323;
} else {
 lean_dec_ref(x_323);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_373);
lean_ctor_set(x_376, 1, x_374);
return x_376;
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_377 = lean_ctor_get(x_316, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_316, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_379 = x_316;
} else {
 lean_dec_ref(x_316);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(1, 2, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_378);
return x_380;
}
}
}
else
{
uint8_t x_381; 
lean_dec(x_49);
x_381 = !lean_is_exclusive(x_52);
if (x_381 == 0)
{
return x_52;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_52, 0);
x_383 = lean_ctor_get(x_52, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_52);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_385 = lean_ctor_get(x_47, 0);
x_386 = lean_ctor_get(x_47, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_47);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_9);
lean_ctor_set(x_387, 1, x_386);
x_388 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_389 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean_inc(x_385);
x_390 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_388, x_389, x_385, x_2, x_387);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_392 = x_390;
} else {
 lean_dec_ref(x_390);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_9);
lean_ctor_set(x_393, 1, x_391);
x_394 = l_Lean_IR_explicitRC(x_385, x_2, x_393);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_397 = x_394;
} else {
 lean_dec_ref(x_394);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_9);
lean_ctor_set(x_398, 1, x_396);
x_399 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_400 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean_inc(x_395);
x_401 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_399, x_400, x_395, x_2, x_398);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_402 = lean_ctor_get(x_401, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_403 = x_401;
} else {
 lean_dec_ref(x_401);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(0, 2, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_9);
lean_ctor_set(x_404, 1, x_402);
x_405 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_395);
x_406 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_407 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean_inc(x_405);
x_408 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_406, x_407, x_405, x_2, x_404);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_409 = lean_ctor_get(x_408, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_410 = x_408;
} else {
 lean_dec_ref(x_408);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(0, 2, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_9);
lean_ctor_set(x_411, 1, x_409);
x_412 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_405);
lean_inc(x_412);
x_413 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_412, x_2, x_411);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_415 = x_413;
} else {
 lean_dec_ref(x_413);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_9);
lean_ctor_set(x_416, 1, x_414);
x_417 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_418 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_412);
x_419 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_417, x_418, x_412, x_2, x_416);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_421 = x_419;
} else {
 lean_dec_ref(x_419);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_9);
lean_ctor_set(x_422, 1, x_420);
lean_inc(x_412);
x_423 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_412, x_412, x_10, x_2, x_422);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_425 = x_423;
} else {
 lean_dec_ref(x_423);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(0, 2, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_9);
lean_ctor_set(x_426, 1, x_424);
x_427 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_412, x_10, x_2, x_426);
lean_dec(x_412);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_427, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 x_429 = x_427;
} else {
 lean_dec_ref(x_427);
 x_429 = lean_box(0);
}
if (lean_is_scalar(x_429)) {
 x_430 = lean_alloc_ctor(0, 2, 0);
} else {
 x_430 = x_429;
}
lean_ctor_set(x_430, 0, x_9);
lean_ctor_set(x_430, 1, x_428);
return x_430;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_431 = lean_ctor_get(x_427, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_427, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 x_433 = x_427;
} else {
 lean_dec_ref(x_427);
 x_433 = lean_box(0);
}
if (lean_is_scalar(x_433)) {
 x_434 = lean_alloc_ctor(1, 2, 0);
} else {
 x_434 = x_433;
}
lean_ctor_set(x_434, 0, x_431);
lean_ctor_set(x_434, 1, x_432);
return x_434;
}
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_412);
x_435 = lean_ctor_get(x_423, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_423, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_437 = x_423;
} else {
 lean_dec_ref(x_423);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(1, 2, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_435);
lean_ctor_set(x_438, 1, x_436);
return x_438;
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_412);
x_439 = lean_ctor_get(x_419, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_419, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_441 = x_419;
} else {
 lean_dec_ref(x_419);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_439);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_412);
x_443 = lean_ctor_get(x_413, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_413, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_445 = x_413;
} else {
 lean_dec_ref(x_413);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(1, 2, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_443);
lean_ctor_set(x_446, 1, x_444);
return x_446;
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_405);
x_447 = lean_ctor_get(x_408, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_408, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_449 = x_408;
} else {
 lean_dec_ref(x_408);
 x_449 = lean_box(0);
}
if (lean_is_scalar(x_449)) {
 x_450 = lean_alloc_ctor(1, 2, 0);
} else {
 x_450 = x_449;
}
lean_ctor_set(x_450, 0, x_447);
lean_ctor_set(x_450, 1, x_448);
return x_450;
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_395);
x_451 = lean_ctor_get(x_401, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_401, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_453 = x_401;
} else {
 lean_dec_ref(x_401);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 2, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_451);
lean_ctor_set(x_454, 1, x_452);
return x_454;
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_455 = lean_ctor_get(x_394, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_394, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_457 = x_394;
} else {
 lean_dec_ref(x_394);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_458 = lean_alloc_ctor(1, 2, 0);
} else {
 x_458 = x_457;
}
lean_ctor_set(x_458, 0, x_455);
lean_ctor_set(x_458, 1, x_456);
return x_458;
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_385);
x_459 = lean_ctor_get(x_390, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_390, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_461 = x_390;
} else {
 lean_dec_ref(x_390);
 x_461 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 2, 0);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_459);
lean_ctor_set(x_462, 1, x_460);
return x_462;
}
}
}
else
{
uint8_t x_463; 
x_463 = !lean_is_exclusive(x_47);
if (x_463 == 0)
{
return x_47;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_47, 0);
x_465 = lean_ctor_get(x_47, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_47);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_44, 1);
lean_inc(x_467);
lean_dec(x_44);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_9);
lean_ctor_set(x_468, 1, x_467);
x_469 = l_Lean_IR_explicitBoxing(x_41, x_2, x_468);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_472 = x_469;
} else {
 lean_dec_ref(x_469);
 x_472 = lean_box(0);
}
if (lean_is_scalar(x_472)) {
 x_473 = lean_alloc_ctor(0, 2, 0);
} else {
 x_473 = x_472;
}
lean_ctor_set(x_473, 0, x_9);
lean_ctor_set(x_473, 1, x_471);
x_474 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_475 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean_inc(x_470);
x_476 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_474, x_475, x_470, x_2, x_473);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_477 = lean_ctor_get(x_476, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 x_478 = x_476;
} else {
 lean_dec_ref(x_476);
 x_478 = lean_box(0);
}
if (lean_is_scalar(x_478)) {
 x_479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_479 = x_478;
}
lean_ctor_set(x_479, 0, x_9);
lean_ctor_set(x_479, 1, x_477);
x_480 = l_Lean_IR_explicitRC(x_470, x_2, x_479);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_483 = x_480;
} else {
 lean_dec_ref(x_480);
 x_483 = lean_box(0);
}
if (lean_is_scalar(x_483)) {
 x_484 = lean_alloc_ctor(0, 2, 0);
} else {
 x_484 = x_483;
}
lean_ctor_set(x_484, 0, x_9);
lean_ctor_set(x_484, 1, x_482);
x_485 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_486 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean_inc(x_481);
x_487 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_485, x_486, x_481, x_2, x_484);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_488 = lean_ctor_get(x_487, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_489 = x_487;
} else {
 lean_dec_ref(x_487);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(0, 2, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_9);
lean_ctor_set(x_490, 1, x_488);
x_491 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_481);
x_492 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_493 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean_inc(x_491);
x_494 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_492, x_493, x_491, x_2, x_490);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_496 = x_494;
} else {
 lean_dec_ref(x_494);
 x_496 = lean_box(0);
}
if (lean_is_scalar(x_496)) {
 x_497 = lean_alloc_ctor(0, 2, 0);
} else {
 x_497 = x_496;
}
lean_ctor_set(x_497, 0, x_9);
lean_ctor_set(x_497, 1, x_495);
x_498 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_491);
lean_inc(x_498);
x_499 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_498, x_2, x_497);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_500 = lean_ctor_get(x_499, 1);
lean_inc(x_500);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_501 = x_499;
} else {
 lean_dec_ref(x_499);
 x_501 = lean_box(0);
}
if (lean_is_scalar(x_501)) {
 x_502 = lean_alloc_ctor(0, 2, 0);
} else {
 x_502 = x_501;
}
lean_ctor_set(x_502, 0, x_9);
lean_ctor_set(x_502, 1, x_500);
x_503 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_504 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_498);
x_505 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_503, x_504, x_498, x_2, x_502);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_507 = x_505;
} else {
 lean_dec_ref(x_505);
 x_507 = lean_box(0);
}
if (lean_is_scalar(x_507)) {
 x_508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_508 = x_507;
}
lean_ctor_set(x_508, 0, x_9);
lean_ctor_set(x_508, 1, x_506);
lean_inc(x_498);
x_509 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_498, x_498, x_10, x_2, x_508);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_510 = lean_ctor_get(x_509, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_511 = x_509;
} else {
 lean_dec_ref(x_509);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_512 = lean_alloc_ctor(0, 2, 0);
} else {
 x_512 = x_511;
}
lean_ctor_set(x_512, 0, x_9);
lean_ctor_set(x_512, 1, x_510);
x_513 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_498, x_10, x_2, x_512);
lean_dec(x_498);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_513, 1);
lean_inc(x_514);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_515 = x_513;
} else {
 lean_dec_ref(x_513);
 x_515 = lean_box(0);
}
if (lean_is_scalar(x_515)) {
 x_516 = lean_alloc_ctor(0, 2, 0);
} else {
 x_516 = x_515;
}
lean_ctor_set(x_516, 0, x_9);
lean_ctor_set(x_516, 1, x_514);
return x_516;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_517 = lean_ctor_get(x_513, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_513, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_519 = x_513;
} else {
 lean_dec_ref(x_513);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_519)) {
 x_520 = lean_alloc_ctor(1, 2, 0);
} else {
 x_520 = x_519;
}
lean_ctor_set(x_520, 0, x_517);
lean_ctor_set(x_520, 1, x_518);
return x_520;
}
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_498);
x_521 = lean_ctor_get(x_509, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_509, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_523 = x_509;
} else {
 lean_dec_ref(x_509);
 x_523 = lean_box(0);
}
if (lean_is_scalar(x_523)) {
 x_524 = lean_alloc_ctor(1, 2, 0);
} else {
 x_524 = x_523;
}
lean_ctor_set(x_524, 0, x_521);
lean_ctor_set(x_524, 1, x_522);
return x_524;
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_498);
x_525 = lean_ctor_get(x_505, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_505, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_527 = x_505;
} else {
 lean_dec_ref(x_505);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(1, 2, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_525);
lean_ctor_set(x_528, 1, x_526);
return x_528;
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_498);
x_529 = lean_ctor_get(x_499, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_499, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_531 = x_499;
} else {
 lean_dec_ref(x_499);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(1, 2, 0);
} else {
 x_532 = x_531;
}
lean_ctor_set(x_532, 0, x_529);
lean_ctor_set(x_532, 1, x_530);
return x_532;
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_dec(x_491);
x_533 = lean_ctor_get(x_494, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_494, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_535 = x_494;
} else {
 lean_dec_ref(x_494);
 x_535 = lean_box(0);
}
if (lean_is_scalar(x_535)) {
 x_536 = lean_alloc_ctor(1, 2, 0);
} else {
 x_536 = x_535;
}
lean_ctor_set(x_536, 0, x_533);
lean_ctor_set(x_536, 1, x_534);
return x_536;
}
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_481);
x_537 = lean_ctor_get(x_487, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_487, 1);
lean_inc(x_538);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_539 = x_487;
} else {
 lean_dec_ref(x_487);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 2, 0);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_537);
lean_ctor_set(x_540, 1, x_538);
return x_540;
}
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_541 = lean_ctor_get(x_480, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_480, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_543 = x_480;
} else {
 lean_dec_ref(x_480);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(1, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_541);
lean_ctor_set(x_544, 1, x_542);
return x_544;
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_470);
x_545 = lean_ctor_get(x_476, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_476, 1);
lean_inc(x_546);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 x_547 = x_476;
} else {
 lean_dec_ref(x_476);
 x_547 = lean_box(0);
}
if (lean_is_scalar(x_547)) {
 x_548 = lean_alloc_ctor(1, 2, 0);
} else {
 x_548 = x_547;
}
lean_ctor_set(x_548, 0, x_545);
lean_ctor_set(x_548, 1, x_546);
return x_548;
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_549 = lean_ctor_get(x_469, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_469, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 lean_ctor_release(x_469, 1);
 x_551 = x_469;
} else {
 lean_dec_ref(x_469);
 x_551 = lean_box(0);
}
if (lean_is_scalar(x_551)) {
 x_552 = lean_alloc_ctor(1, 2, 0);
} else {
 x_552 = x_551;
}
lean_ctor_set(x_552, 0, x_549);
lean_ctor_set(x_552, 1, x_550);
return x_552;
}
}
}
else
{
uint8_t x_553; 
lean_dec(x_41);
x_553 = !lean_is_exclusive(x_44);
if (x_553 == 0)
{
return x_44;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_554 = lean_ctor_get(x_44, 0);
x_555 = lean_ctor_get(x_44, 1);
lean_inc(x_555);
lean_inc(x_554);
lean_dec(x_44);
x_556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_556, 0, x_554);
lean_ctor_set(x_556, 1, x_555);
return x_556;
}
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_557 = lean_ctor_get(x_39, 0);
x_558 = lean_ctor_get(x_39, 1);
lean_inc(x_558);
lean_inc(x_557);
lean_dec(x_39);
x_559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_559, 0, x_9);
lean_ctor_set(x_559, 1, x_558);
x_560 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_561 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean_inc(x_557);
x_562 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_560, x_561, x_557, x_2, x_559);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_563 = lean_ctor_get(x_562, 1);
lean_inc(x_563);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_564 = x_562;
} else {
 lean_dec_ref(x_562);
 x_564 = lean_box(0);
}
if (lean_is_scalar(x_564)) {
 x_565 = lean_alloc_ctor(0, 2, 0);
} else {
 x_565 = x_564;
}
lean_ctor_set(x_565, 0, x_9);
lean_ctor_set(x_565, 1, x_563);
x_566 = l_Lean_IR_explicitBoxing(x_557, x_2, x_565);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_566, 1);
lean_inc(x_568);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_569 = x_566;
} else {
 lean_dec_ref(x_566);
 x_569 = lean_box(0);
}
if (lean_is_scalar(x_569)) {
 x_570 = lean_alloc_ctor(0, 2, 0);
} else {
 x_570 = x_569;
}
lean_ctor_set(x_570, 0, x_9);
lean_ctor_set(x_570, 1, x_568);
x_571 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_572 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean_inc(x_567);
x_573 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_571, x_572, x_567, x_2, x_570);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_574 = lean_ctor_get(x_573, 1);
lean_inc(x_574);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 lean_ctor_release(x_573, 1);
 x_575 = x_573;
} else {
 lean_dec_ref(x_573);
 x_575 = lean_box(0);
}
if (lean_is_scalar(x_575)) {
 x_576 = lean_alloc_ctor(0, 2, 0);
} else {
 x_576 = x_575;
}
lean_ctor_set(x_576, 0, x_9);
lean_ctor_set(x_576, 1, x_574);
x_577 = l_Lean_IR_explicitRC(x_567, x_2, x_576);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 lean_ctor_release(x_577, 1);
 x_580 = x_577;
} else {
 lean_dec_ref(x_577);
 x_580 = lean_box(0);
}
if (lean_is_scalar(x_580)) {
 x_581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_581 = x_580;
}
lean_ctor_set(x_581, 0, x_9);
lean_ctor_set(x_581, 1, x_579);
x_582 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_583 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean_inc(x_578);
x_584 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_582, x_583, x_578, x_2, x_581);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_585 = lean_ctor_get(x_584, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_584)) {
 lean_ctor_release(x_584, 0);
 lean_ctor_release(x_584, 1);
 x_586 = x_584;
} else {
 lean_dec_ref(x_584);
 x_586 = lean_box(0);
}
if (lean_is_scalar(x_586)) {
 x_587 = lean_alloc_ctor(0, 2, 0);
} else {
 x_587 = x_586;
}
lean_ctor_set(x_587, 0, x_9);
lean_ctor_set(x_587, 1, x_585);
x_588 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_578);
x_589 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_590 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean_inc(x_588);
x_591 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_589, x_590, x_588, x_2, x_587);
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_592 = lean_ctor_get(x_591, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 lean_ctor_release(x_591, 1);
 x_593 = x_591;
} else {
 lean_dec_ref(x_591);
 x_593 = lean_box(0);
}
if (lean_is_scalar(x_593)) {
 x_594 = lean_alloc_ctor(0, 2, 0);
} else {
 x_594 = x_593;
}
lean_ctor_set(x_594, 0, x_9);
lean_ctor_set(x_594, 1, x_592);
x_595 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_588);
lean_inc(x_595);
x_596 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_595, x_2, x_594);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_598 = x_596;
} else {
 lean_dec_ref(x_596);
 x_598 = lean_box(0);
}
if (lean_is_scalar(x_598)) {
 x_599 = lean_alloc_ctor(0, 2, 0);
} else {
 x_599 = x_598;
}
lean_ctor_set(x_599, 0, x_9);
lean_ctor_set(x_599, 1, x_597);
x_600 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_601 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_595);
x_602 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_600, x_601, x_595, x_2, x_599);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_603 = lean_ctor_get(x_602, 1);
lean_inc(x_603);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_604 = x_602;
} else {
 lean_dec_ref(x_602);
 x_604 = lean_box(0);
}
if (lean_is_scalar(x_604)) {
 x_605 = lean_alloc_ctor(0, 2, 0);
} else {
 x_605 = x_604;
}
lean_ctor_set(x_605, 0, x_9);
lean_ctor_set(x_605, 1, x_603);
lean_inc(x_595);
x_606 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_595, x_595, x_10, x_2, x_605);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_607 = lean_ctor_get(x_606, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_608 = x_606;
} else {
 lean_dec_ref(x_606);
 x_608 = lean_box(0);
}
if (lean_is_scalar(x_608)) {
 x_609 = lean_alloc_ctor(0, 2, 0);
} else {
 x_609 = x_608;
}
lean_ctor_set(x_609, 0, x_9);
lean_ctor_set(x_609, 1, x_607);
x_610 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_595, x_10, x_2, x_609);
lean_dec(x_595);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_611 = lean_ctor_get(x_610, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 lean_ctor_release(x_610, 1);
 x_612 = x_610;
} else {
 lean_dec_ref(x_610);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(0, 2, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_9);
lean_ctor_set(x_613, 1, x_611);
return x_613;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_614 = lean_ctor_get(x_610, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_610, 1);
lean_inc(x_615);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 lean_ctor_release(x_610, 1);
 x_616 = x_610;
} else {
 lean_dec_ref(x_610);
 x_616 = lean_box(0);
}
if (lean_is_scalar(x_616)) {
 x_617 = lean_alloc_ctor(1, 2, 0);
} else {
 x_617 = x_616;
}
lean_ctor_set(x_617, 0, x_614);
lean_ctor_set(x_617, 1, x_615);
return x_617;
}
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_595);
x_618 = lean_ctor_get(x_606, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_606, 1);
lean_inc(x_619);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_620 = x_606;
} else {
 lean_dec_ref(x_606);
 x_620 = lean_box(0);
}
if (lean_is_scalar(x_620)) {
 x_621 = lean_alloc_ctor(1, 2, 0);
} else {
 x_621 = x_620;
}
lean_ctor_set(x_621, 0, x_618);
lean_ctor_set(x_621, 1, x_619);
return x_621;
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_595);
x_622 = lean_ctor_get(x_602, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_602, 1);
lean_inc(x_623);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_624 = x_602;
} else {
 lean_dec_ref(x_602);
 x_624 = lean_box(0);
}
if (lean_is_scalar(x_624)) {
 x_625 = lean_alloc_ctor(1, 2, 0);
} else {
 x_625 = x_624;
}
lean_ctor_set(x_625, 0, x_622);
lean_ctor_set(x_625, 1, x_623);
return x_625;
}
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_595);
x_626 = lean_ctor_get(x_596, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_596, 1);
lean_inc(x_627);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_628 = x_596;
} else {
 lean_dec_ref(x_596);
 x_628 = lean_box(0);
}
if (lean_is_scalar(x_628)) {
 x_629 = lean_alloc_ctor(1, 2, 0);
} else {
 x_629 = x_628;
}
lean_ctor_set(x_629, 0, x_626);
lean_ctor_set(x_629, 1, x_627);
return x_629;
}
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
lean_dec(x_588);
x_630 = lean_ctor_get(x_591, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_591, 1);
lean_inc(x_631);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 lean_ctor_release(x_591, 1);
 x_632 = x_591;
} else {
 lean_dec_ref(x_591);
 x_632 = lean_box(0);
}
if (lean_is_scalar(x_632)) {
 x_633 = lean_alloc_ctor(1, 2, 0);
} else {
 x_633 = x_632;
}
lean_ctor_set(x_633, 0, x_630);
lean_ctor_set(x_633, 1, x_631);
return x_633;
}
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
lean_dec(x_578);
x_634 = lean_ctor_get(x_584, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_584, 1);
lean_inc(x_635);
if (lean_is_exclusive(x_584)) {
 lean_ctor_release(x_584, 0);
 lean_ctor_release(x_584, 1);
 x_636 = x_584;
} else {
 lean_dec_ref(x_584);
 x_636 = lean_box(0);
}
if (lean_is_scalar(x_636)) {
 x_637 = lean_alloc_ctor(1, 2, 0);
} else {
 x_637 = x_636;
}
lean_ctor_set(x_637, 0, x_634);
lean_ctor_set(x_637, 1, x_635);
return x_637;
}
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_638 = lean_ctor_get(x_577, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_577, 1);
lean_inc(x_639);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 lean_ctor_release(x_577, 1);
 x_640 = x_577;
} else {
 lean_dec_ref(x_577);
 x_640 = lean_box(0);
}
if (lean_is_scalar(x_640)) {
 x_641 = lean_alloc_ctor(1, 2, 0);
} else {
 x_641 = x_640;
}
lean_ctor_set(x_641, 0, x_638);
lean_ctor_set(x_641, 1, x_639);
return x_641;
}
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
lean_dec(x_567);
x_642 = lean_ctor_get(x_573, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_573, 1);
lean_inc(x_643);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 lean_ctor_release(x_573, 1);
 x_644 = x_573;
} else {
 lean_dec_ref(x_573);
 x_644 = lean_box(0);
}
if (lean_is_scalar(x_644)) {
 x_645 = lean_alloc_ctor(1, 2, 0);
} else {
 x_645 = x_644;
}
lean_ctor_set(x_645, 0, x_642);
lean_ctor_set(x_645, 1, x_643);
return x_645;
}
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_646 = lean_ctor_get(x_566, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_566, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_648 = x_566;
} else {
 lean_dec_ref(x_566);
 x_648 = lean_box(0);
}
if (lean_is_scalar(x_648)) {
 x_649 = lean_alloc_ctor(1, 2, 0);
} else {
 x_649 = x_648;
}
lean_ctor_set(x_649, 0, x_646);
lean_ctor_set(x_649, 1, x_647);
return x_649;
}
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_557);
x_650 = lean_ctor_get(x_562, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_562, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_652 = x_562;
} else {
 lean_dec_ref(x_562);
 x_652 = lean_box(0);
}
if (lean_is_scalar(x_652)) {
 x_653 = lean_alloc_ctor(1, 2, 0);
} else {
 x_653 = x_652;
}
lean_ctor_set(x_653, 0, x_650);
lean_ctor_set(x_653, 1, x_651);
return x_653;
}
}
}
else
{
uint8_t x_654; 
x_654 = !lean_is_exclusive(x_39);
if (x_654 == 0)
{
return x_39;
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_655 = lean_ctor_get(x_39, 0);
x_656 = lean_ctor_get(x_39, 1);
lean_inc(x_656);
lean_inc(x_655);
lean_dec(x_39);
x_657 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_657, 0, x_655);
lean_ctor_set(x_657, 1, x_656);
return x_657;
}
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_658 = lean_ctor_get(x_35, 1);
lean_inc(x_658);
lean_dec(x_35);
x_659 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_659, 0, x_9);
lean_ctor_set(x_659, 1, x_658);
x_660 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_32);
x_661 = l_Lean_IR_inferBorrow(x_660, x_2, x_659);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_661, 1);
lean_inc(x_663);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 x_664 = x_661;
} else {
 lean_dec_ref(x_661);
 x_664 = lean_box(0);
}
if (lean_is_scalar(x_664)) {
 x_665 = lean_alloc_ctor(0, 2, 0);
} else {
 x_665 = x_664;
}
lean_ctor_set(x_665, 0, x_9);
lean_ctor_set(x_665, 1, x_663);
x_666 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_667 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean_inc(x_662);
x_668 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_666, x_667, x_662, x_2, x_665);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_669 = lean_ctor_get(x_668, 1);
lean_inc(x_669);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_670 = x_668;
} else {
 lean_dec_ref(x_668);
 x_670 = lean_box(0);
}
if (lean_is_scalar(x_670)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_670;
}
lean_ctor_set(x_671, 0, x_9);
lean_ctor_set(x_671, 1, x_669);
x_672 = l_Lean_IR_explicitBoxing(x_662, x_2, x_671);
if (lean_obj_tag(x_672) == 0)
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
if (lean_is_exclusive(x_672)) {
 lean_ctor_release(x_672, 0);
 lean_ctor_release(x_672, 1);
 x_675 = x_672;
} else {
 lean_dec_ref(x_672);
 x_675 = lean_box(0);
}
if (lean_is_scalar(x_675)) {
 x_676 = lean_alloc_ctor(0, 2, 0);
} else {
 x_676 = x_675;
}
lean_ctor_set(x_676, 0, x_9);
lean_ctor_set(x_676, 1, x_674);
x_677 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_678 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean_inc(x_673);
x_679 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_677, x_678, x_673, x_2, x_676);
if (lean_obj_tag(x_679) == 0)
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_680 = lean_ctor_get(x_679, 1);
lean_inc(x_680);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 x_681 = x_679;
} else {
 lean_dec_ref(x_679);
 x_681 = lean_box(0);
}
if (lean_is_scalar(x_681)) {
 x_682 = lean_alloc_ctor(0, 2, 0);
} else {
 x_682 = x_681;
}
lean_ctor_set(x_682, 0, x_9);
lean_ctor_set(x_682, 1, x_680);
x_683 = l_Lean_IR_explicitRC(x_673, x_2, x_682);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_683, 1);
lean_inc(x_685);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 lean_ctor_release(x_683, 1);
 x_686 = x_683;
} else {
 lean_dec_ref(x_683);
 x_686 = lean_box(0);
}
if (lean_is_scalar(x_686)) {
 x_687 = lean_alloc_ctor(0, 2, 0);
} else {
 x_687 = x_686;
}
lean_ctor_set(x_687, 0, x_9);
lean_ctor_set(x_687, 1, x_685);
x_688 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_689 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean_inc(x_684);
x_690 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_688, x_689, x_684, x_2, x_687);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_691 = lean_ctor_get(x_690, 1);
lean_inc(x_691);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 x_692 = x_690;
} else {
 lean_dec_ref(x_690);
 x_692 = lean_box(0);
}
if (lean_is_scalar(x_692)) {
 x_693 = lean_alloc_ctor(0, 2, 0);
} else {
 x_693 = x_692;
}
lean_ctor_set(x_693, 0, x_9);
lean_ctor_set(x_693, 1, x_691);
x_694 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_684);
x_695 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_696 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean_inc(x_694);
x_697 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_695, x_696, x_694, x_2, x_693);
if (lean_obj_tag(x_697) == 0)
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_698 = lean_ctor_get(x_697, 1);
lean_inc(x_698);
if (lean_is_exclusive(x_697)) {
 lean_ctor_release(x_697, 0);
 lean_ctor_release(x_697, 1);
 x_699 = x_697;
} else {
 lean_dec_ref(x_697);
 x_699 = lean_box(0);
}
if (lean_is_scalar(x_699)) {
 x_700 = lean_alloc_ctor(0, 2, 0);
} else {
 x_700 = x_699;
}
lean_ctor_set(x_700, 0, x_9);
lean_ctor_set(x_700, 1, x_698);
x_701 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_694);
lean_inc(x_701);
x_702 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_701, x_2, x_700);
if (lean_obj_tag(x_702) == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_703 = lean_ctor_get(x_702, 1);
lean_inc(x_703);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_704 = x_702;
} else {
 lean_dec_ref(x_702);
 x_704 = lean_box(0);
}
if (lean_is_scalar(x_704)) {
 x_705 = lean_alloc_ctor(0, 2, 0);
} else {
 x_705 = x_704;
}
lean_ctor_set(x_705, 0, x_9);
lean_ctor_set(x_705, 1, x_703);
x_706 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_707 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_701);
x_708 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_706, x_707, x_701, x_2, x_705);
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_709 = lean_ctor_get(x_708, 1);
lean_inc(x_709);
if (lean_is_exclusive(x_708)) {
 lean_ctor_release(x_708, 0);
 lean_ctor_release(x_708, 1);
 x_710 = x_708;
} else {
 lean_dec_ref(x_708);
 x_710 = lean_box(0);
}
if (lean_is_scalar(x_710)) {
 x_711 = lean_alloc_ctor(0, 2, 0);
} else {
 x_711 = x_710;
}
lean_ctor_set(x_711, 0, x_9);
lean_ctor_set(x_711, 1, x_709);
lean_inc(x_701);
x_712 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_701, x_701, x_10, x_2, x_711);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_713 = lean_ctor_get(x_712, 1);
lean_inc(x_713);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 lean_ctor_release(x_712, 1);
 x_714 = x_712;
} else {
 lean_dec_ref(x_712);
 x_714 = lean_box(0);
}
if (lean_is_scalar(x_714)) {
 x_715 = lean_alloc_ctor(0, 2, 0);
} else {
 x_715 = x_714;
}
lean_ctor_set(x_715, 0, x_9);
lean_ctor_set(x_715, 1, x_713);
x_716 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_701, x_10, x_2, x_715);
lean_dec(x_701);
if (lean_obj_tag(x_716) == 0)
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_717 = lean_ctor_get(x_716, 1);
lean_inc(x_717);
if (lean_is_exclusive(x_716)) {
 lean_ctor_release(x_716, 0);
 lean_ctor_release(x_716, 1);
 x_718 = x_716;
} else {
 lean_dec_ref(x_716);
 x_718 = lean_box(0);
}
if (lean_is_scalar(x_718)) {
 x_719 = lean_alloc_ctor(0, 2, 0);
} else {
 x_719 = x_718;
}
lean_ctor_set(x_719, 0, x_9);
lean_ctor_set(x_719, 1, x_717);
return x_719;
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_720 = lean_ctor_get(x_716, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_716, 1);
lean_inc(x_721);
if (lean_is_exclusive(x_716)) {
 lean_ctor_release(x_716, 0);
 lean_ctor_release(x_716, 1);
 x_722 = x_716;
} else {
 lean_dec_ref(x_716);
 x_722 = lean_box(0);
}
if (lean_is_scalar(x_722)) {
 x_723 = lean_alloc_ctor(1, 2, 0);
} else {
 x_723 = x_722;
}
lean_ctor_set(x_723, 0, x_720);
lean_ctor_set(x_723, 1, x_721);
return x_723;
}
}
else
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
lean_dec(x_701);
x_724 = lean_ctor_get(x_712, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_712, 1);
lean_inc(x_725);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 lean_ctor_release(x_712, 1);
 x_726 = x_712;
} else {
 lean_dec_ref(x_712);
 x_726 = lean_box(0);
}
if (lean_is_scalar(x_726)) {
 x_727 = lean_alloc_ctor(1, 2, 0);
} else {
 x_727 = x_726;
}
lean_ctor_set(x_727, 0, x_724);
lean_ctor_set(x_727, 1, x_725);
return x_727;
}
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; 
lean_dec(x_701);
x_728 = lean_ctor_get(x_708, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_708, 1);
lean_inc(x_729);
if (lean_is_exclusive(x_708)) {
 lean_ctor_release(x_708, 0);
 lean_ctor_release(x_708, 1);
 x_730 = x_708;
} else {
 lean_dec_ref(x_708);
 x_730 = lean_box(0);
}
if (lean_is_scalar(x_730)) {
 x_731 = lean_alloc_ctor(1, 2, 0);
} else {
 x_731 = x_730;
}
lean_ctor_set(x_731, 0, x_728);
lean_ctor_set(x_731, 1, x_729);
return x_731;
}
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_701);
x_732 = lean_ctor_get(x_702, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_702, 1);
lean_inc(x_733);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_734 = x_702;
} else {
 lean_dec_ref(x_702);
 x_734 = lean_box(0);
}
if (lean_is_scalar(x_734)) {
 x_735 = lean_alloc_ctor(1, 2, 0);
} else {
 x_735 = x_734;
}
lean_ctor_set(x_735, 0, x_732);
lean_ctor_set(x_735, 1, x_733);
return x_735;
}
}
else
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; 
lean_dec(x_694);
x_736 = lean_ctor_get(x_697, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_697, 1);
lean_inc(x_737);
if (lean_is_exclusive(x_697)) {
 lean_ctor_release(x_697, 0);
 lean_ctor_release(x_697, 1);
 x_738 = x_697;
} else {
 lean_dec_ref(x_697);
 x_738 = lean_box(0);
}
if (lean_is_scalar(x_738)) {
 x_739 = lean_alloc_ctor(1, 2, 0);
} else {
 x_739 = x_738;
}
lean_ctor_set(x_739, 0, x_736);
lean_ctor_set(x_739, 1, x_737);
return x_739;
}
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
lean_dec(x_684);
x_740 = lean_ctor_get(x_690, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_690, 1);
lean_inc(x_741);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 x_742 = x_690;
} else {
 lean_dec_ref(x_690);
 x_742 = lean_box(0);
}
if (lean_is_scalar(x_742)) {
 x_743 = lean_alloc_ctor(1, 2, 0);
} else {
 x_743 = x_742;
}
lean_ctor_set(x_743, 0, x_740);
lean_ctor_set(x_743, 1, x_741);
return x_743;
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_744 = lean_ctor_get(x_683, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_683, 1);
lean_inc(x_745);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 lean_ctor_release(x_683, 1);
 x_746 = x_683;
} else {
 lean_dec_ref(x_683);
 x_746 = lean_box(0);
}
if (lean_is_scalar(x_746)) {
 x_747 = lean_alloc_ctor(1, 2, 0);
} else {
 x_747 = x_746;
}
lean_ctor_set(x_747, 0, x_744);
lean_ctor_set(x_747, 1, x_745);
return x_747;
}
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
lean_dec(x_673);
x_748 = lean_ctor_get(x_679, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_679, 1);
lean_inc(x_749);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 x_750 = x_679;
} else {
 lean_dec_ref(x_679);
 x_750 = lean_box(0);
}
if (lean_is_scalar(x_750)) {
 x_751 = lean_alloc_ctor(1, 2, 0);
} else {
 x_751 = x_750;
}
lean_ctor_set(x_751, 0, x_748);
lean_ctor_set(x_751, 1, x_749);
return x_751;
}
}
else
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_752 = lean_ctor_get(x_672, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_672, 1);
lean_inc(x_753);
if (lean_is_exclusive(x_672)) {
 lean_ctor_release(x_672, 0);
 lean_ctor_release(x_672, 1);
 x_754 = x_672;
} else {
 lean_dec_ref(x_672);
 x_754 = lean_box(0);
}
if (lean_is_scalar(x_754)) {
 x_755 = lean_alloc_ctor(1, 2, 0);
} else {
 x_755 = x_754;
}
lean_ctor_set(x_755, 0, x_752);
lean_ctor_set(x_755, 1, x_753);
return x_755;
}
}
else
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; 
lean_dec(x_662);
x_756 = lean_ctor_get(x_668, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_668, 1);
lean_inc(x_757);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_758 = x_668;
} else {
 lean_dec_ref(x_668);
 x_758 = lean_box(0);
}
if (lean_is_scalar(x_758)) {
 x_759 = lean_alloc_ctor(1, 2, 0);
} else {
 x_759 = x_758;
}
lean_ctor_set(x_759, 0, x_756);
lean_ctor_set(x_759, 1, x_757);
return x_759;
}
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; 
x_760 = lean_ctor_get(x_661, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_661, 1);
lean_inc(x_761);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 x_762 = x_661;
} else {
 lean_dec_ref(x_661);
 x_762 = lean_box(0);
}
if (lean_is_scalar(x_762)) {
 x_763 = lean_alloc_ctor(1, 2, 0);
} else {
 x_763 = x_762;
}
lean_ctor_set(x_763, 0, x_760);
lean_ctor_set(x_763, 1, x_761);
return x_763;
}
}
}
else
{
uint8_t x_764; 
lean_dec(x_32);
x_764 = !lean_is_exclusive(x_35);
if (x_764 == 0)
{
return x_35;
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; 
x_765 = lean_ctor_get(x_35, 0);
x_766 = lean_ctor_get(x_35, 1);
lean_inc(x_766);
lean_inc(x_765);
lean_dec(x_35);
x_767 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_767, 0, x_765);
lean_ctor_set(x_767, 1, x_766);
return x_767;
}
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_768 = lean_ctor_get(x_29, 1);
lean_inc(x_768);
lean_dec(x_29);
x_769 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_769, 0, x_9);
lean_ctor_set(x_769, 1, x_768);
x_770 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(x_10, x_26);
x_771 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
x_772 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean_inc(x_770);
x_773 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_771, x_772, x_770, x_2, x_769);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_774 = lean_ctor_get(x_773, 1);
lean_inc(x_774);
if (lean_is_exclusive(x_773)) {
 lean_ctor_release(x_773, 0);
 lean_ctor_release(x_773, 1);
 x_775 = x_773;
} else {
 lean_dec_ref(x_773);
 x_775 = lean_box(0);
}
if (lean_is_scalar(x_775)) {
 x_776 = lean_alloc_ctor(0, 2, 0);
} else {
 x_776 = x_775;
}
lean_ctor_set(x_776, 0, x_9);
lean_ctor_set(x_776, 1, x_774);
x_777 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_770);
x_778 = l_Lean_IR_inferBorrow(x_777, x_2, x_776);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_779 = lean_ctor_get(x_778, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_778, 1);
lean_inc(x_780);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_781 = x_778;
} else {
 lean_dec_ref(x_778);
 x_781 = lean_box(0);
}
if (lean_is_scalar(x_781)) {
 x_782 = lean_alloc_ctor(0, 2, 0);
} else {
 x_782 = x_781;
}
lean_ctor_set(x_782, 0, x_9);
lean_ctor_set(x_782, 1, x_780);
x_783 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_784 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean_inc(x_779);
x_785 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_783, x_784, x_779, x_2, x_782);
if (lean_obj_tag(x_785) == 0)
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_786 = lean_ctor_get(x_785, 1);
lean_inc(x_786);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_787 = x_785;
} else {
 lean_dec_ref(x_785);
 x_787 = lean_box(0);
}
if (lean_is_scalar(x_787)) {
 x_788 = lean_alloc_ctor(0, 2, 0);
} else {
 x_788 = x_787;
}
lean_ctor_set(x_788, 0, x_9);
lean_ctor_set(x_788, 1, x_786);
x_789 = l_Lean_IR_explicitBoxing(x_779, x_2, x_788);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_792 = x_789;
} else {
 lean_dec_ref(x_789);
 x_792 = lean_box(0);
}
if (lean_is_scalar(x_792)) {
 x_793 = lean_alloc_ctor(0, 2, 0);
} else {
 x_793 = x_792;
}
lean_ctor_set(x_793, 0, x_9);
lean_ctor_set(x_793, 1, x_791);
x_794 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_795 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean_inc(x_790);
x_796 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_794, x_795, x_790, x_2, x_793);
if (lean_obj_tag(x_796) == 0)
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; 
x_797 = lean_ctor_get(x_796, 1);
lean_inc(x_797);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 x_798 = x_796;
} else {
 lean_dec_ref(x_796);
 x_798 = lean_box(0);
}
if (lean_is_scalar(x_798)) {
 x_799 = lean_alloc_ctor(0, 2, 0);
} else {
 x_799 = x_798;
}
lean_ctor_set(x_799, 0, x_9);
lean_ctor_set(x_799, 1, x_797);
x_800 = l_Lean_IR_explicitRC(x_790, x_2, x_799);
if (lean_obj_tag(x_800) == 0)
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_801 = lean_ctor_get(x_800, 0);
lean_inc(x_801);
x_802 = lean_ctor_get(x_800, 1);
lean_inc(x_802);
if (lean_is_exclusive(x_800)) {
 lean_ctor_release(x_800, 0);
 lean_ctor_release(x_800, 1);
 x_803 = x_800;
} else {
 lean_dec_ref(x_800);
 x_803 = lean_box(0);
}
if (lean_is_scalar(x_803)) {
 x_804 = lean_alloc_ctor(0, 2, 0);
} else {
 x_804 = x_803;
}
lean_ctor_set(x_804, 0, x_9);
lean_ctor_set(x_804, 1, x_802);
x_805 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_806 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean_inc(x_801);
x_807 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_805, x_806, x_801, x_2, x_804);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_808 = lean_ctor_get(x_807, 1);
lean_inc(x_808);
if (lean_is_exclusive(x_807)) {
 lean_ctor_release(x_807, 0);
 lean_ctor_release(x_807, 1);
 x_809 = x_807;
} else {
 lean_dec_ref(x_807);
 x_809 = lean_box(0);
}
if (lean_is_scalar(x_809)) {
 x_810 = lean_alloc_ctor(0, 2, 0);
} else {
 x_810 = x_809;
}
lean_ctor_set(x_810, 0, x_9);
lean_ctor_set(x_810, 1, x_808);
x_811 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_801);
x_812 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_813 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean_inc(x_811);
x_814 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_812, x_813, x_811, x_2, x_810);
if (lean_obj_tag(x_814) == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_815 = lean_ctor_get(x_814, 1);
lean_inc(x_815);
if (lean_is_exclusive(x_814)) {
 lean_ctor_release(x_814, 0);
 lean_ctor_release(x_814, 1);
 x_816 = x_814;
} else {
 lean_dec_ref(x_814);
 x_816 = lean_box(0);
}
if (lean_is_scalar(x_816)) {
 x_817 = lean_alloc_ctor(0, 2, 0);
} else {
 x_817 = x_816;
}
lean_ctor_set(x_817, 0, x_9);
lean_ctor_set(x_817, 1, x_815);
x_818 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_811);
lean_inc(x_818);
x_819 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_818, x_2, x_817);
if (lean_obj_tag(x_819) == 0)
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_820 = lean_ctor_get(x_819, 1);
lean_inc(x_820);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_821 = x_819;
} else {
 lean_dec_ref(x_819);
 x_821 = lean_box(0);
}
if (lean_is_scalar(x_821)) {
 x_822 = lean_alloc_ctor(0, 2, 0);
} else {
 x_822 = x_821;
}
lean_ctor_set(x_822, 0, x_9);
lean_ctor_set(x_822, 1, x_820);
x_823 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_824 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_818);
x_825 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_823, x_824, x_818, x_2, x_822);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; 
x_826 = lean_ctor_get(x_825, 1);
lean_inc(x_826);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 x_827 = x_825;
} else {
 lean_dec_ref(x_825);
 x_827 = lean_box(0);
}
if (lean_is_scalar(x_827)) {
 x_828 = lean_alloc_ctor(0, 2, 0);
} else {
 x_828 = x_827;
}
lean_ctor_set(x_828, 0, x_9);
lean_ctor_set(x_828, 1, x_826);
lean_inc(x_818);
x_829 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_818, x_818, x_10, x_2, x_828);
if (lean_obj_tag(x_829) == 0)
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_830 = lean_ctor_get(x_829, 1);
lean_inc(x_830);
if (lean_is_exclusive(x_829)) {
 lean_ctor_release(x_829, 0);
 lean_ctor_release(x_829, 1);
 x_831 = x_829;
} else {
 lean_dec_ref(x_829);
 x_831 = lean_box(0);
}
if (lean_is_scalar(x_831)) {
 x_832 = lean_alloc_ctor(0, 2, 0);
} else {
 x_832 = x_831;
}
lean_ctor_set(x_832, 0, x_9);
lean_ctor_set(x_832, 1, x_830);
x_833 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_818, x_10, x_2, x_832);
lean_dec(x_818);
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_834 = lean_ctor_get(x_833, 1);
lean_inc(x_834);
if (lean_is_exclusive(x_833)) {
 lean_ctor_release(x_833, 0);
 lean_ctor_release(x_833, 1);
 x_835 = x_833;
} else {
 lean_dec_ref(x_833);
 x_835 = lean_box(0);
}
if (lean_is_scalar(x_835)) {
 x_836 = lean_alloc_ctor(0, 2, 0);
} else {
 x_836 = x_835;
}
lean_ctor_set(x_836, 0, x_9);
lean_ctor_set(x_836, 1, x_834);
return x_836;
}
else
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; 
x_837 = lean_ctor_get(x_833, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_833, 1);
lean_inc(x_838);
if (lean_is_exclusive(x_833)) {
 lean_ctor_release(x_833, 0);
 lean_ctor_release(x_833, 1);
 x_839 = x_833;
} else {
 lean_dec_ref(x_833);
 x_839 = lean_box(0);
}
if (lean_is_scalar(x_839)) {
 x_840 = lean_alloc_ctor(1, 2, 0);
} else {
 x_840 = x_839;
}
lean_ctor_set(x_840, 0, x_837);
lean_ctor_set(x_840, 1, x_838);
return x_840;
}
}
else
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
lean_dec(x_818);
x_841 = lean_ctor_get(x_829, 0);
lean_inc(x_841);
x_842 = lean_ctor_get(x_829, 1);
lean_inc(x_842);
if (lean_is_exclusive(x_829)) {
 lean_ctor_release(x_829, 0);
 lean_ctor_release(x_829, 1);
 x_843 = x_829;
} else {
 lean_dec_ref(x_829);
 x_843 = lean_box(0);
}
if (lean_is_scalar(x_843)) {
 x_844 = lean_alloc_ctor(1, 2, 0);
} else {
 x_844 = x_843;
}
lean_ctor_set(x_844, 0, x_841);
lean_ctor_set(x_844, 1, x_842);
return x_844;
}
}
else
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
lean_dec(x_818);
x_845 = lean_ctor_get(x_825, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_825, 1);
lean_inc(x_846);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 x_847 = x_825;
} else {
 lean_dec_ref(x_825);
 x_847 = lean_box(0);
}
if (lean_is_scalar(x_847)) {
 x_848 = lean_alloc_ctor(1, 2, 0);
} else {
 x_848 = x_847;
}
lean_ctor_set(x_848, 0, x_845);
lean_ctor_set(x_848, 1, x_846);
return x_848;
}
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; 
lean_dec(x_818);
x_849 = lean_ctor_get(x_819, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_819, 1);
lean_inc(x_850);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_851 = x_819;
} else {
 lean_dec_ref(x_819);
 x_851 = lean_box(0);
}
if (lean_is_scalar(x_851)) {
 x_852 = lean_alloc_ctor(1, 2, 0);
} else {
 x_852 = x_851;
}
lean_ctor_set(x_852, 0, x_849);
lean_ctor_set(x_852, 1, x_850);
return x_852;
}
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_811);
x_853 = lean_ctor_get(x_814, 0);
lean_inc(x_853);
x_854 = lean_ctor_get(x_814, 1);
lean_inc(x_854);
if (lean_is_exclusive(x_814)) {
 lean_ctor_release(x_814, 0);
 lean_ctor_release(x_814, 1);
 x_855 = x_814;
} else {
 lean_dec_ref(x_814);
 x_855 = lean_box(0);
}
if (lean_is_scalar(x_855)) {
 x_856 = lean_alloc_ctor(1, 2, 0);
} else {
 x_856 = x_855;
}
lean_ctor_set(x_856, 0, x_853);
lean_ctor_set(x_856, 1, x_854);
return x_856;
}
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
lean_dec(x_801);
x_857 = lean_ctor_get(x_807, 0);
lean_inc(x_857);
x_858 = lean_ctor_get(x_807, 1);
lean_inc(x_858);
if (lean_is_exclusive(x_807)) {
 lean_ctor_release(x_807, 0);
 lean_ctor_release(x_807, 1);
 x_859 = x_807;
} else {
 lean_dec_ref(x_807);
 x_859 = lean_box(0);
}
if (lean_is_scalar(x_859)) {
 x_860 = lean_alloc_ctor(1, 2, 0);
} else {
 x_860 = x_859;
}
lean_ctor_set(x_860, 0, x_857);
lean_ctor_set(x_860, 1, x_858);
return x_860;
}
}
else
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_861 = lean_ctor_get(x_800, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_800, 1);
lean_inc(x_862);
if (lean_is_exclusive(x_800)) {
 lean_ctor_release(x_800, 0);
 lean_ctor_release(x_800, 1);
 x_863 = x_800;
} else {
 lean_dec_ref(x_800);
 x_863 = lean_box(0);
}
if (lean_is_scalar(x_863)) {
 x_864 = lean_alloc_ctor(1, 2, 0);
} else {
 x_864 = x_863;
}
lean_ctor_set(x_864, 0, x_861);
lean_ctor_set(x_864, 1, x_862);
return x_864;
}
}
else
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_790);
x_865 = lean_ctor_get(x_796, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_796, 1);
lean_inc(x_866);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 x_867 = x_796;
} else {
 lean_dec_ref(x_796);
 x_867 = lean_box(0);
}
if (lean_is_scalar(x_867)) {
 x_868 = lean_alloc_ctor(1, 2, 0);
} else {
 x_868 = x_867;
}
lean_ctor_set(x_868, 0, x_865);
lean_ctor_set(x_868, 1, x_866);
return x_868;
}
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_869 = lean_ctor_get(x_789, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_789, 1);
lean_inc(x_870);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_871 = x_789;
} else {
 lean_dec_ref(x_789);
 x_871 = lean_box(0);
}
if (lean_is_scalar(x_871)) {
 x_872 = lean_alloc_ctor(1, 2, 0);
} else {
 x_872 = x_871;
}
lean_ctor_set(x_872, 0, x_869);
lean_ctor_set(x_872, 1, x_870);
return x_872;
}
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
lean_dec(x_779);
x_873 = lean_ctor_get(x_785, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_785, 1);
lean_inc(x_874);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_875 = x_785;
} else {
 lean_dec_ref(x_785);
 x_875 = lean_box(0);
}
if (lean_is_scalar(x_875)) {
 x_876 = lean_alloc_ctor(1, 2, 0);
} else {
 x_876 = x_875;
}
lean_ctor_set(x_876, 0, x_873);
lean_ctor_set(x_876, 1, x_874);
return x_876;
}
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_877 = lean_ctor_get(x_778, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_778, 1);
lean_inc(x_878);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_879 = x_778;
} else {
 lean_dec_ref(x_778);
 x_879 = lean_box(0);
}
if (lean_is_scalar(x_879)) {
 x_880 = lean_alloc_ctor(1, 2, 0);
} else {
 x_880 = x_879;
}
lean_ctor_set(x_880, 0, x_877);
lean_ctor_set(x_880, 1, x_878);
return x_880;
}
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
lean_dec(x_770);
x_881 = lean_ctor_get(x_773, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_773, 1);
lean_inc(x_882);
if (lean_is_exclusive(x_773)) {
 lean_ctor_release(x_773, 0);
 lean_ctor_release(x_773, 1);
 x_883 = x_773;
} else {
 lean_dec_ref(x_773);
 x_883 = lean_box(0);
}
if (lean_is_scalar(x_883)) {
 x_884 = lean_alloc_ctor(1, 2, 0);
} else {
 x_884 = x_883;
}
lean_ctor_set(x_884, 0, x_881);
lean_ctor_set(x_884, 1, x_882);
return x_884;
}
}
}
else
{
uint8_t x_885; 
lean_dec(x_26);
x_885 = !lean_is_exclusive(x_29);
if (x_885 == 0)
{
return x_29;
}
else
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; 
x_886 = lean_ctor_get(x_29, 0);
x_887 = lean_ctor_get(x_29, 1);
lean_inc(x_887);
lean_inc(x_886);
lean_dec(x_29);
x_888 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_888, 0, x_886);
lean_ctor_set(x_888, 1, x_887);
return x_888;
}
}
}
else
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_889 = lean_ctor_get(x_23, 1);
lean_inc(x_889);
lean_dec(x_23);
x_890 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_890, 0, x_9);
lean_ctor_set(x_890, 1, x_889);
x_891 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(x_10, x_20);
x_892 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
x_893 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
lean_inc(x_891);
x_894 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_892, x_893, x_891, x_2, x_890);
if (lean_obj_tag(x_894) == 0)
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; 
x_895 = lean_ctor_get(x_894, 1);
lean_inc(x_895);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 lean_ctor_release(x_894, 1);
 x_896 = x_894;
} else {
 lean_dec_ref(x_894);
 x_896 = lean_box(0);
}
if (lean_is_scalar(x_896)) {
 x_897 = lean_alloc_ctor(0, 2, 0);
} else {
 x_897 = x_896;
}
lean_ctor_set(x_897, 0, x_9);
lean_ctor_set(x_897, 1, x_895);
x_898 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(x_10, x_891);
x_899 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
x_900 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean_inc(x_898);
x_901 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_899, x_900, x_898, x_2, x_897);
if (lean_obj_tag(x_901) == 0)
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; 
x_902 = lean_ctor_get(x_901, 1);
lean_inc(x_902);
if (lean_is_exclusive(x_901)) {
 lean_ctor_release(x_901, 0);
 lean_ctor_release(x_901, 1);
 x_903 = x_901;
} else {
 lean_dec_ref(x_901);
 x_903 = lean_box(0);
}
if (lean_is_scalar(x_903)) {
 x_904 = lean_alloc_ctor(0, 2, 0);
} else {
 x_904 = x_903;
}
lean_ctor_set(x_904, 0, x_9);
lean_ctor_set(x_904, 1, x_902);
x_905 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_898);
x_906 = l_Lean_IR_inferBorrow(x_905, x_2, x_904);
if (lean_obj_tag(x_906) == 0)
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; 
x_907 = lean_ctor_get(x_906, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_906, 1);
lean_inc(x_908);
if (lean_is_exclusive(x_906)) {
 lean_ctor_release(x_906, 0);
 lean_ctor_release(x_906, 1);
 x_909 = x_906;
} else {
 lean_dec_ref(x_906);
 x_909 = lean_box(0);
}
if (lean_is_scalar(x_909)) {
 x_910 = lean_alloc_ctor(0, 2, 0);
} else {
 x_910 = x_909;
}
lean_ctor_set(x_910, 0, x_9);
lean_ctor_set(x_910, 1, x_908);
x_911 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_912 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean_inc(x_907);
x_913 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_911, x_912, x_907, x_2, x_910);
if (lean_obj_tag(x_913) == 0)
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
x_914 = lean_ctor_get(x_913, 1);
lean_inc(x_914);
if (lean_is_exclusive(x_913)) {
 lean_ctor_release(x_913, 0);
 lean_ctor_release(x_913, 1);
 x_915 = x_913;
} else {
 lean_dec_ref(x_913);
 x_915 = lean_box(0);
}
if (lean_is_scalar(x_915)) {
 x_916 = lean_alloc_ctor(0, 2, 0);
} else {
 x_916 = x_915;
}
lean_ctor_set(x_916, 0, x_9);
lean_ctor_set(x_916, 1, x_914);
x_917 = l_Lean_IR_explicitBoxing(x_907, x_2, x_916);
if (lean_obj_tag(x_917) == 0)
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
x_918 = lean_ctor_get(x_917, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_917, 1);
lean_inc(x_919);
if (lean_is_exclusive(x_917)) {
 lean_ctor_release(x_917, 0);
 lean_ctor_release(x_917, 1);
 x_920 = x_917;
} else {
 lean_dec_ref(x_917);
 x_920 = lean_box(0);
}
if (lean_is_scalar(x_920)) {
 x_921 = lean_alloc_ctor(0, 2, 0);
} else {
 x_921 = x_920;
}
lean_ctor_set(x_921, 0, x_9);
lean_ctor_set(x_921, 1, x_919);
x_922 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_923 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean_inc(x_918);
x_924 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_922, x_923, x_918, x_2, x_921);
if (lean_obj_tag(x_924) == 0)
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; 
x_925 = lean_ctor_get(x_924, 1);
lean_inc(x_925);
if (lean_is_exclusive(x_924)) {
 lean_ctor_release(x_924, 0);
 lean_ctor_release(x_924, 1);
 x_926 = x_924;
} else {
 lean_dec_ref(x_924);
 x_926 = lean_box(0);
}
if (lean_is_scalar(x_926)) {
 x_927 = lean_alloc_ctor(0, 2, 0);
} else {
 x_927 = x_926;
}
lean_ctor_set(x_927, 0, x_9);
lean_ctor_set(x_927, 1, x_925);
x_928 = l_Lean_IR_explicitRC(x_918, x_2, x_927);
if (lean_obj_tag(x_928) == 0)
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_929 = lean_ctor_get(x_928, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_928, 1);
lean_inc(x_930);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 lean_ctor_release(x_928, 1);
 x_931 = x_928;
} else {
 lean_dec_ref(x_928);
 x_931 = lean_box(0);
}
if (lean_is_scalar(x_931)) {
 x_932 = lean_alloc_ctor(0, 2, 0);
} else {
 x_932 = x_931;
}
lean_ctor_set(x_932, 0, x_9);
lean_ctor_set(x_932, 1, x_930);
x_933 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_934 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean_inc(x_929);
x_935 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_933, x_934, x_929, x_2, x_932);
if (lean_obj_tag(x_935) == 0)
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
x_936 = lean_ctor_get(x_935, 1);
lean_inc(x_936);
if (lean_is_exclusive(x_935)) {
 lean_ctor_release(x_935, 0);
 lean_ctor_release(x_935, 1);
 x_937 = x_935;
} else {
 lean_dec_ref(x_935);
 x_937 = lean_box(0);
}
if (lean_is_scalar(x_937)) {
 x_938 = lean_alloc_ctor(0, 2, 0);
} else {
 x_938 = x_937;
}
lean_ctor_set(x_938, 0, x_9);
lean_ctor_set(x_938, 1, x_936);
x_939 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_929);
x_940 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_941 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean_inc(x_939);
x_942 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_940, x_941, x_939, x_2, x_938);
if (lean_obj_tag(x_942) == 0)
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; 
x_943 = lean_ctor_get(x_942, 1);
lean_inc(x_943);
if (lean_is_exclusive(x_942)) {
 lean_ctor_release(x_942, 0);
 lean_ctor_release(x_942, 1);
 x_944 = x_942;
} else {
 lean_dec_ref(x_942);
 x_944 = lean_box(0);
}
if (lean_is_scalar(x_944)) {
 x_945 = lean_alloc_ctor(0, 2, 0);
} else {
 x_945 = x_944;
}
lean_ctor_set(x_945, 0, x_9);
lean_ctor_set(x_945, 1, x_943);
x_946 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_939);
lean_inc(x_946);
x_947 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_946, x_2, x_945);
if (lean_obj_tag(x_947) == 0)
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; 
x_948 = lean_ctor_get(x_947, 1);
lean_inc(x_948);
if (lean_is_exclusive(x_947)) {
 lean_ctor_release(x_947, 0);
 lean_ctor_release(x_947, 1);
 x_949 = x_947;
} else {
 lean_dec_ref(x_947);
 x_949 = lean_box(0);
}
if (lean_is_scalar(x_949)) {
 x_950 = lean_alloc_ctor(0, 2, 0);
} else {
 x_950 = x_949;
}
lean_ctor_set(x_950, 0, x_9);
lean_ctor_set(x_950, 1, x_948);
x_951 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_952 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_946);
x_953 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_951, x_952, x_946, x_2, x_950);
if (lean_obj_tag(x_953) == 0)
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; 
x_954 = lean_ctor_get(x_953, 1);
lean_inc(x_954);
if (lean_is_exclusive(x_953)) {
 lean_ctor_release(x_953, 0);
 lean_ctor_release(x_953, 1);
 x_955 = x_953;
} else {
 lean_dec_ref(x_953);
 x_955 = lean_box(0);
}
if (lean_is_scalar(x_955)) {
 x_956 = lean_alloc_ctor(0, 2, 0);
} else {
 x_956 = x_955;
}
lean_ctor_set(x_956, 0, x_9);
lean_ctor_set(x_956, 1, x_954);
lean_inc(x_946);
x_957 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_946, x_946, x_10, x_2, x_956);
if (lean_obj_tag(x_957) == 0)
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; 
x_958 = lean_ctor_get(x_957, 1);
lean_inc(x_958);
if (lean_is_exclusive(x_957)) {
 lean_ctor_release(x_957, 0);
 lean_ctor_release(x_957, 1);
 x_959 = x_957;
} else {
 lean_dec_ref(x_957);
 x_959 = lean_box(0);
}
if (lean_is_scalar(x_959)) {
 x_960 = lean_alloc_ctor(0, 2, 0);
} else {
 x_960 = x_959;
}
lean_ctor_set(x_960, 0, x_9);
lean_ctor_set(x_960, 1, x_958);
x_961 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_946, x_10, x_2, x_960);
lean_dec(x_946);
if (lean_obj_tag(x_961) == 0)
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_962 = lean_ctor_get(x_961, 1);
lean_inc(x_962);
if (lean_is_exclusive(x_961)) {
 lean_ctor_release(x_961, 0);
 lean_ctor_release(x_961, 1);
 x_963 = x_961;
} else {
 lean_dec_ref(x_961);
 x_963 = lean_box(0);
}
if (lean_is_scalar(x_963)) {
 x_964 = lean_alloc_ctor(0, 2, 0);
} else {
 x_964 = x_963;
}
lean_ctor_set(x_964, 0, x_9);
lean_ctor_set(x_964, 1, x_962);
return x_964;
}
else
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; 
x_965 = lean_ctor_get(x_961, 0);
lean_inc(x_965);
x_966 = lean_ctor_get(x_961, 1);
lean_inc(x_966);
if (lean_is_exclusive(x_961)) {
 lean_ctor_release(x_961, 0);
 lean_ctor_release(x_961, 1);
 x_967 = x_961;
} else {
 lean_dec_ref(x_961);
 x_967 = lean_box(0);
}
if (lean_is_scalar(x_967)) {
 x_968 = lean_alloc_ctor(1, 2, 0);
} else {
 x_968 = x_967;
}
lean_ctor_set(x_968, 0, x_965);
lean_ctor_set(x_968, 1, x_966);
return x_968;
}
}
else
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; 
lean_dec(x_946);
x_969 = lean_ctor_get(x_957, 0);
lean_inc(x_969);
x_970 = lean_ctor_get(x_957, 1);
lean_inc(x_970);
if (lean_is_exclusive(x_957)) {
 lean_ctor_release(x_957, 0);
 lean_ctor_release(x_957, 1);
 x_971 = x_957;
} else {
 lean_dec_ref(x_957);
 x_971 = lean_box(0);
}
if (lean_is_scalar(x_971)) {
 x_972 = lean_alloc_ctor(1, 2, 0);
} else {
 x_972 = x_971;
}
lean_ctor_set(x_972, 0, x_969);
lean_ctor_set(x_972, 1, x_970);
return x_972;
}
}
else
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; 
lean_dec(x_946);
x_973 = lean_ctor_get(x_953, 0);
lean_inc(x_973);
x_974 = lean_ctor_get(x_953, 1);
lean_inc(x_974);
if (lean_is_exclusive(x_953)) {
 lean_ctor_release(x_953, 0);
 lean_ctor_release(x_953, 1);
 x_975 = x_953;
} else {
 lean_dec_ref(x_953);
 x_975 = lean_box(0);
}
if (lean_is_scalar(x_975)) {
 x_976 = lean_alloc_ctor(1, 2, 0);
} else {
 x_976 = x_975;
}
lean_ctor_set(x_976, 0, x_973);
lean_ctor_set(x_976, 1, x_974);
return x_976;
}
}
else
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
lean_dec(x_946);
x_977 = lean_ctor_get(x_947, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_947, 1);
lean_inc(x_978);
if (lean_is_exclusive(x_947)) {
 lean_ctor_release(x_947, 0);
 lean_ctor_release(x_947, 1);
 x_979 = x_947;
} else {
 lean_dec_ref(x_947);
 x_979 = lean_box(0);
}
if (lean_is_scalar(x_979)) {
 x_980 = lean_alloc_ctor(1, 2, 0);
} else {
 x_980 = x_979;
}
lean_ctor_set(x_980, 0, x_977);
lean_ctor_set(x_980, 1, x_978);
return x_980;
}
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
lean_dec(x_939);
x_981 = lean_ctor_get(x_942, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_942, 1);
lean_inc(x_982);
if (lean_is_exclusive(x_942)) {
 lean_ctor_release(x_942, 0);
 lean_ctor_release(x_942, 1);
 x_983 = x_942;
} else {
 lean_dec_ref(x_942);
 x_983 = lean_box(0);
}
if (lean_is_scalar(x_983)) {
 x_984 = lean_alloc_ctor(1, 2, 0);
} else {
 x_984 = x_983;
}
lean_ctor_set(x_984, 0, x_981);
lean_ctor_set(x_984, 1, x_982);
return x_984;
}
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
lean_dec(x_929);
x_985 = lean_ctor_get(x_935, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_935, 1);
lean_inc(x_986);
if (lean_is_exclusive(x_935)) {
 lean_ctor_release(x_935, 0);
 lean_ctor_release(x_935, 1);
 x_987 = x_935;
} else {
 lean_dec_ref(x_935);
 x_987 = lean_box(0);
}
if (lean_is_scalar(x_987)) {
 x_988 = lean_alloc_ctor(1, 2, 0);
} else {
 x_988 = x_987;
}
lean_ctor_set(x_988, 0, x_985);
lean_ctor_set(x_988, 1, x_986);
return x_988;
}
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_989 = lean_ctor_get(x_928, 0);
lean_inc(x_989);
x_990 = lean_ctor_get(x_928, 1);
lean_inc(x_990);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 lean_ctor_release(x_928, 1);
 x_991 = x_928;
} else {
 lean_dec_ref(x_928);
 x_991 = lean_box(0);
}
if (lean_is_scalar(x_991)) {
 x_992 = lean_alloc_ctor(1, 2, 0);
} else {
 x_992 = x_991;
}
lean_ctor_set(x_992, 0, x_989);
lean_ctor_set(x_992, 1, x_990);
return x_992;
}
}
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; 
lean_dec(x_918);
x_993 = lean_ctor_get(x_924, 0);
lean_inc(x_993);
x_994 = lean_ctor_get(x_924, 1);
lean_inc(x_994);
if (lean_is_exclusive(x_924)) {
 lean_ctor_release(x_924, 0);
 lean_ctor_release(x_924, 1);
 x_995 = x_924;
} else {
 lean_dec_ref(x_924);
 x_995 = lean_box(0);
}
if (lean_is_scalar(x_995)) {
 x_996 = lean_alloc_ctor(1, 2, 0);
} else {
 x_996 = x_995;
}
lean_ctor_set(x_996, 0, x_993);
lean_ctor_set(x_996, 1, x_994);
return x_996;
}
}
else
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_997 = lean_ctor_get(x_917, 0);
lean_inc(x_997);
x_998 = lean_ctor_get(x_917, 1);
lean_inc(x_998);
if (lean_is_exclusive(x_917)) {
 lean_ctor_release(x_917, 0);
 lean_ctor_release(x_917, 1);
 x_999 = x_917;
} else {
 lean_dec_ref(x_917);
 x_999 = lean_box(0);
}
if (lean_is_scalar(x_999)) {
 x_1000 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1000 = x_999;
}
lean_ctor_set(x_1000, 0, x_997);
lean_ctor_set(x_1000, 1, x_998);
return x_1000;
}
}
else
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
lean_dec(x_907);
x_1001 = lean_ctor_get(x_913, 0);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_913, 1);
lean_inc(x_1002);
if (lean_is_exclusive(x_913)) {
 lean_ctor_release(x_913, 0);
 lean_ctor_release(x_913, 1);
 x_1003 = x_913;
} else {
 lean_dec_ref(x_913);
 x_1003 = lean_box(0);
}
if (lean_is_scalar(x_1003)) {
 x_1004 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1004 = x_1003;
}
lean_ctor_set(x_1004, 0, x_1001);
lean_ctor_set(x_1004, 1, x_1002);
return x_1004;
}
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
x_1005 = lean_ctor_get(x_906, 0);
lean_inc(x_1005);
x_1006 = lean_ctor_get(x_906, 1);
lean_inc(x_1006);
if (lean_is_exclusive(x_906)) {
 lean_ctor_release(x_906, 0);
 lean_ctor_release(x_906, 1);
 x_1007 = x_906;
} else {
 lean_dec_ref(x_906);
 x_1007 = lean_box(0);
}
if (lean_is_scalar(x_1007)) {
 x_1008 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1008 = x_1007;
}
lean_ctor_set(x_1008, 0, x_1005);
lean_ctor_set(x_1008, 1, x_1006);
return x_1008;
}
}
else
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
lean_dec(x_898);
x_1009 = lean_ctor_get(x_901, 0);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_901, 1);
lean_inc(x_1010);
if (lean_is_exclusive(x_901)) {
 lean_ctor_release(x_901, 0);
 lean_ctor_release(x_901, 1);
 x_1011 = x_901;
} else {
 lean_dec_ref(x_901);
 x_1011 = lean_box(0);
}
if (lean_is_scalar(x_1011)) {
 x_1012 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1012 = x_1011;
}
lean_ctor_set(x_1012, 0, x_1009);
lean_ctor_set(x_1012, 1, x_1010);
return x_1012;
}
}
else
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
lean_dec(x_891);
x_1013 = lean_ctor_get(x_894, 0);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_894, 1);
lean_inc(x_1014);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 lean_ctor_release(x_894, 1);
 x_1015 = x_894;
} else {
 lean_dec_ref(x_894);
 x_1015 = lean_box(0);
}
if (lean_is_scalar(x_1015)) {
 x_1016 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1016 = x_1015;
}
lean_ctor_set(x_1016, 0, x_1013);
lean_ctor_set(x_1016, 1, x_1014);
return x_1016;
}
}
}
else
{
uint8_t x_1017; 
lean_dec(x_20);
x_1017 = !lean_is_exclusive(x_23);
if (x_1017 == 0)
{
return x_23;
}
else
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
x_1018 = lean_ctor_get(x_23, 0);
x_1019 = lean_ctor_get(x_23, 1);
lean_inc(x_1019);
lean_inc(x_1018);
lean_dec(x_23);
x_1020 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1020, 0, x_1018);
lean_ctor_set(x_1020, 1, x_1019);
return x_1020;
}
}
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
x_1021 = lean_ctor_get(x_17, 1);
lean_inc(x_1021);
lean_dec(x_17);
x_1022 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1022, 0, x_9);
lean_ctor_set(x_1022, 1, x_1021);
x_1023 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(x_10, x_14);
x_1024 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__7;
x_1025 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
lean_inc(x_1023);
x_1026 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1024, x_1025, x_1023, x_2, x_1022);
if (lean_obj_tag(x_1026) == 0)
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
x_1027 = lean_ctor_get(x_1026, 1);
lean_inc(x_1027);
if (lean_is_exclusive(x_1026)) {
 lean_ctor_release(x_1026, 0);
 lean_ctor_release(x_1026, 1);
 x_1028 = x_1026;
} else {
 lean_dec_ref(x_1026);
 x_1028 = lean_box(0);
}
if (lean_is_scalar(x_1028)) {
 x_1029 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1029 = x_1028;
}
lean_ctor_set(x_1029, 0, x_9);
lean_ctor_set(x_1029, 1, x_1027);
x_1030 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(x_10, x_1023);
x_1031 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
x_1032 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
lean_inc(x_1030);
x_1033 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1031, x_1032, x_1030, x_2, x_1029);
if (lean_obj_tag(x_1033) == 0)
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
x_1034 = lean_ctor_get(x_1033, 1);
lean_inc(x_1034);
if (lean_is_exclusive(x_1033)) {
 lean_ctor_release(x_1033, 0);
 lean_ctor_release(x_1033, 1);
 x_1035 = x_1033;
} else {
 lean_dec_ref(x_1033);
 x_1035 = lean_box(0);
}
if (lean_is_scalar(x_1035)) {
 x_1036 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1036 = x_1035;
}
lean_ctor_set(x_1036, 0, x_9);
lean_ctor_set(x_1036, 1, x_1034);
x_1037 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(x_10, x_1030);
x_1038 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
x_1039 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean_inc(x_1037);
x_1040 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1038, x_1039, x_1037, x_2, x_1036);
if (lean_obj_tag(x_1040) == 0)
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
x_1041 = lean_ctor_get(x_1040, 1);
lean_inc(x_1041);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 lean_ctor_release(x_1040, 1);
 x_1042 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1042 = lean_box(0);
}
if (lean_is_scalar(x_1042)) {
 x_1043 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1043 = x_1042;
}
lean_ctor_set(x_1043, 0, x_9);
lean_ctor_set(x_1043, 1, x_1041);
x_1044 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_1037);
x_1045 = l_Lean_IR_inferBorrow(x_1044, x_2, x_1043);
if (lean_obj_tag(x_1045) == 0)
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
x_1046 = lean_ctor_get(x_1045, 0);
lean_inc(x_1046);
x_1047 = lean_ctor_get(x_1045, 1);
lean_inc(x_1047);
if (lean_is_exclusive(x_1045)) {
 lean_ctor_release(x_1045, 0);
 lean_ctor_release(x_1045, 1);
 x_1048 = x_1045;
} else {
 lean_dec_ref(x_1045);
 x_1048 = lean_box(0);
}
if (lean_is_scalar(x_1048)) {
 x_1049 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1049 = x_1048;
}
lean_ctor_set(x_1049, 0, x_9);
lean_ctor_set(x_1049, 1, x_1047);
x_1050 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_1051 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean_inc(x_1046);
x_1052 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1050, x_1051, x_1046, x_2, x_1049);
if (lean_obj_tag(x_1052) == 0)
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
x_1053 = lean_ctor_get(x_1052, 1);
lean_inc(x_1053);
if (lean_is_exclusive(x_1052)) {
 lean_ctor_release(x_1052, 0);
 lean_ctor_release(x_1052, 1);
 x_1054 = x_1052;
} else {
 lean_dec_ref(x_1052);
 x_1054 = lean_box(0);
}
if (lean_is_scalar(x_1054)) {
 x_1055 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1055 = x_1054;
}
lean_ctor_set(x_1055, 0, x_9);
lean_ctor_set(x_1055, 1, x_1053);
x_1056 = l_Lean_IR_explicitBoxing(x_1046, x_2, x_1055);
if (lean_obj_tag(x_1056) == 0)
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; 
x_1057 = lean_ctor_get(x_1056, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1056, 1);
lean_inc(x_1058);
if (lean_is_exclusive(x_1056)) {
 lean_ctor_release(x_1056, 0);
 lean_ctor_release(x_1056, 1);
 x_1059 = x_1056;
} else {
 lean_dec_ref(x_1056);
 x_1059 = lean_box(0);
}
if (lean_is_scalar(x_1059)) {
 x_1060 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1060 = x_1059;
}
lean_ctor_set(x_1060, 0, x_9);
lean_ctor_set(x_1060, 1, x_1058);
x_1061 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_1062 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean_inc(x_1057);
x_1063 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1061, x_1062, x_1057, x_2, x_1060);
if (lean_obj_tag(x_1063) == 0)
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; 
x_1064 = lean_ctor_get(x_1063, 1);
lean_inc(x_1064);
if (lean_is_exclusive(x_1063)) {
 lean_ctor_release(x_1063, 0);
 lean_ctor_release(x_1063, 1);
 x_1065 = x_1063;
} else {
 lean_dec_ref(x_1063);
 x_1065 = lean_box(0);
}
if (lean_is_scalar(x_1065)) {
 x_1066 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1066 = x_1065;
}
lean_ctor_set(x_1066, 0, x_9);
lean_ctor_set(x_1066, 1, x_1064);
x_1067 = l_Lean_IR_explicitRC(x_1057, x_2, x_1066);
if (lean_obj_tag(x_1067) == 0)
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
x_1068 = lean_ctor_get(x_1067, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1067, 1);
lean_inc(x_1069);
if (lean_is_exclusive(x_1067)) {
 lean_ctor_release(x_1067, 0);
 lean_ctor_release(x_1067, 1);
 x_1070 = x_1067;
} else {
 lean_dec_ref(x_1067);
 x_1070 = lean_box(0);
}
if (lean_is_scalar(x_1070)) {
 x_1071 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1071 = x_1070;
}
lean_ctor_set(x_1071, 0, x_9);
lean_ctor_set(x_1071, 1, x_1069);
x_1072 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_1073 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean_inc(x_1068);
x_1074 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1072, x_1073, x_1068, x_2, x_1071);
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
x_1075 = lean_ctor_get(x_1074, 1);
lean_inc(x_1075);
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 lean_ctor_release(x_1074, 1);
 x_1076 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1076 = lean_box(0);
}
if (lean_is_scalar(x_1076)) {
 x_1077 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1077 = x_1076;
}
lean_ctor_set(x_1077, 0, x_9);
lean_ctor_set(x_1077, 1, x_1075);
x_1078 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_1068);
x_1079 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_1080 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean_inc(x_1078);
x_1081 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1079, x_1080, x_1078, x_2, x_1077);
if (lean_obj_tag(x_1081) == 0)
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
x_1082 = lean_ctor_get(x_1081, 1);
lean_inc(x_1082);
if (lean_is_exclusive(x_1081)) {
 lean_ctor_release(x_1081, 0);
 lean_ctor_release(x_1081, 1);
 x_1083 = x_1081;
} else {
 lean_dec_ref(x_1081);
 x_1083 = lean_box(0);
}
if (lean_is_scalar(x_1083)) {
 x_1084 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1084 = x_1083;
}
lean_ctor_set(x_1084, 0, x_9);
lean_ctor_set(x_1084, 1, x_1082);
x_1085 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_1078);
lean_inc(x_1085);
x_1086 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_15, x_16, x_1085, x_2, x_1084);
if (lean_obj_tag(x_1086) == 0)
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
x_1087 = lean_ctor_get(x_1086, 1);
lean_inc(x_1087);
if (lean_is_exclusive(x_1086)) {
 lean_ctor_release(x_1086, 0);
 lean_ctor_release(x_1086, 1);
 x_1088 = x_1086;
} else {
 lean_dec_ref(x_1086);
 x_1088 = lean_box(0);
}
if (lean_is_scalar(x_1088)) {
 x_1089 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1089 = x_1088;
}
lean_ctor_set(x_1089, 0, x_9);
lean_ctor_set(x_1089, 1, x_1087);
x_1090 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_1091 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_1085);
x_1092 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1090, x_1091, x_1085, x_2, x_1089);
if (lean_obj_tag(x_1092) == 0)
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
x_1093 = lean_ctor_get(x_1092, 1);
lean_inc(x_1093);
if (lean_is_exclusive(x_1092)) {
 lean_ctor_release(x_1092, 0);
 lean_ctor_release(x_1092, 1);
 x_1094 = x_1092;
} else {
 lean_dec_ref(x_1092);
 x_1094 = lean_box(0);
}
if (lean_is_scalar(x_1094)) {
 x_1095 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1095 = x_1094;
}
lean_ctor_set(x_1095, 0, x_9);
lean_ctor_set(x_1095, 1, x_1093);
lean_inc(x_1085);
x_1096 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1085, x_1085, x_10, x_2, x_1095);
if (lean_obj_tag(x_1096) == 0)
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
x_1097 = lean_ctor_get(x_1096, 1);
lean_inc(x_1097);
if (lean_is_exclusive(x_1096)) {
 lean_ctor_release(x_1096, 0);
 lean_ctor_release(x_1096, 1);
 x_1098 = x_1096;
} else {
 lean_dec_ref(x_1096);
 x_1098 = lean_box(0);
}
if (lean_is_scalar(x_1098)) {
 x_1099 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1099 = x_1098;
}
lean_ctor_set(x_1099, 0, x_9);
lean_ctor_set(x_1099, 1, x_1097);
x_1100 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_1085, x_10, x_2, x_1099);
lean_dec(x_1085);
if (lean_obj_tag(x_1100) == 0)
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
x_1101 = lean_ctor_get(x_1100, 1);
lean_inc(x_1101);
if (lean_is_exclusive(x_1100)) {
 lean_ctor_release(x_1100, 0);
 lean_ctor_release(x_1100, 1);
 x_1102 = x_1100;
} else {
 lean_dec_ref(x_1100);
 x_1102 = lean_box(0);
}
if (lean_is_scalar(x_1102)) {
 x_1103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1103 = x_1102;
}
lean_ctor_set(x_1103, 0, x_9);
lean_ctor_set(x_1103, 1, x_1101);
return x_1103;
}
else
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; 
x_1104 = lean_ctor_get(x_1100, 0);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_1100, 1);
lean_inc(x_1105);
if (lean_is_exclusive(x_1100)) {
 lean_ctor_release(x_1100, 0);
 lean_ctor_release(x_1100, 1);
 x_1106 = x_1100;
} else {
 lean_dec_ref(x_1100);
 x_1106 = lean_box(0);
}
if (lean_is_scalar(x_1106)) {
 x_1107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1107 = x_1106;
}
lean_ctor_set(x_1107, 0, x_1104);
lean_ctor_set(x_1107, 1, x_1105);
return x_1107;
}
}
else
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
lean_dec(x_1085);
x_1108 = lean_ctor_get(x_1096, 0);
lean_inc(x_1108);
x_1109 = lean_ctor_get(x_1096, 1);
lean_inc(x_1109);
if (lean_is_exclusive(x_1096)) {
 lean_ctor_release(x_1096, 0);
 lean_ctor_release(x_1096, 1);
 x_1110 = x_1096;
} else {
 lean_dec_ref(x_1096);
 x_1110 = lean_box(0);
}
if (lean_is_scalar(x_1110)) {
 x_1111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1111 = x_1110;
}
lean_ctor_set(x_1111, 0, x_1108);
lean_ctor_set(x_1111, 1, x_1109);
return x_1111;
}
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
lean_dec(x_1085);
x_1112 = lean_ctor_get(x_1092, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1092, 1);
lean_inc(x_1113);
if (lean_is_exclusive(x_1092)) {
 lean_ctor_release(x_1092, 0);
 lean_ctor_release(x_1092, 1);
 x_1114 = x_1092;
} else {
 lean_dec_ref(x_1092);
 x_1114 = lean_box(0);
}
if (lean_is_scalar(x_1114)) {
 x_1115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1115 = x_1114;
}
lean_ctor_set(x_1115, 0, x_1112);
lean_ctor_set(x_1115, 1, x_1113);
return x_1115;
}
}
else
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
lean_dec(x_1085);
x_1116 = lean_ctor_get(x_1086, 0);
lean_inc(x_1116);
x_1117 = lean_ctor_get(x_1086, 1);
lean_inc(x_1117);
if (lean_is_exclusive(x_1086)) {
 lean_ctor_release(x_1086, 0);
 lean_ctor_release(x_1086, 1);
 x_1118 = x_1086;
} else {
 lean_dec_ref(x_1086);
 x_1118 = lean_box(0);
}
if (lean_is_scalar(x_1118)) {
 x_1119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1119 = x_1118;
}
lean_ctor_set(x_1119, 0, x_1116);
lean_ctor_set(x_1119, 1, x_1117);
return x_1119;
}
}
else
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
lean_dec(x_1078);
x_1120 = lean_ctor_get(x_1081, 0);
lean_inc(x_1120);
x_1121 = lean_ctor_get(x_1081, 1);
lean_inc(x_1121);
if (lean_is_exclusive(x_1081)) {
 lean_ctor_release(x_1081, 0);
 lean_ctor_release(x_1081, 1);
 x_1122 = x_1081;
} else {
 lean_dec_ref(x_1081);
 x_1122 = lean_box(0);
}
if (lean_is_scalar(x_1122)) {
 x_1123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1123 = x_1122;
}
lean_ctor_set(x_1123, 0, x_1120);
lean_ctor_set(x_1123, 1, x_1121);
return x_1123;
}
}
else
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
lean_dec(x_1068);
x_1124 = lean_ctor_get(x_1074, 0);
lean_inc(x_1124);
x_1125 = lean_ctor_get(x_1074, 1);
lean_inc(x_1125);
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 lean_ctor_release(x_1074, 1);
 x_1126 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1126 = lean_box(0);
}
if (lean_is_scalar(x_1126)) {
 x_1127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1127 = x_1126;
}
lean_ctor_set(x_1127, 0, x_1124);
lean_ctor_set(x_1127, 1, x_1125);
return x_1127;
}
}
else
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
x_1128 = lean_ctor_get(x_1067, 0);
lean_inc(x_1128);
x_1129 = lean_ctor_get(x_1067, 1);
lean_inc(x_1129);
if (lean_is_exclusive(x_1067)) {
 lean_ctor_release(x_1067, 0);
 lean_ctor_release(x_1067, 1);
 x_1130 = x_1067;
} else {
 lean_dec_ref(x_1067);
 x_1130 = lean_box(0);
}
if (lean_is_scalar(x_1130)) {
 x_1131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1131 = x_1130;
}
lean_ctor_set(x_1131, 0, x_1128);
lean_ctor_set(x_1131, 1, x_1129);
return x_1131;
}
}
else
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
lean_dec(x_1057);
x_1132 = lean_ctor_get(x_1063, 0);
lean_inc(x_1132);
x_1133 = lean_ctor_get(x_1063, 1);
lean_inc(x_1133);
if (lean_is_exclusive(x_1063)) {
 lean_ctor_release(x_1063, 0);
 lean_ctor_release(x_1063, 1);
 x_1134 = x_1063;
} else {
 lean_dec_ref(x_1063);
 x_1134 = lean_box(0);
}
if (lean_is_scalar(x_1134)) {
 x_1135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1135 = x_1134;
}
lean_ctor_set(x_1135, 0, x_1132);
lean_ctor_set(x_1135, 1, x_1133);
return x_1135;
}
}
else
{
lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; 
x_1136 = lean_ctor_get(x_1056, 0);
lean_inc(x_1136);
x_1137 = lean_ctor_get(x_1056, 1);
lean_inc(x_1137);
if (lean_is_exclusive(x_1056)) {
 lean_ctor_release(x_1056, 0);
 lean_ctor_release(x_1056, 1);
 x_1138 = x_1056;
} else {
 lean_dec_ref(x_1056);
 x_1138 = lean_box(0);
}
if (lean_is_scalar(x_1138)) {
 x_1139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1139 = x_1138;
}
lean_ctor_set(x_1139, 0, x_1136);
lean_ctor_set(x_1139, 1, x_1137);
return x_1139;
}
}
else
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
lean_dec(x_1046);
x_1140 = lean_ctor_get(x_1052, 0);
lean_inc(x_1140);
x_1141 = lean_ctor_get(x_1052, 1);
lean_inc(x_1141);
if (lean_is_exclusive(x_1052)) {
 lean_ctor_release(x_1052, 0);
 lean_ctor_release(x_1052, 1);
 x_1142 = x_1052;
} else {
 lean_dec_ref(x_1052);
 x_1142 = lean_box(0);
}
if (lean_is_scalar(x_1142)) {
 x_1143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1143 = x_1142;
}
lean_ctor_set(x_1143, 0, x_1140);
lean_ctor_set(x_1143, 1, x_1141);
return x_1143;
}
}
else
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
x_1144 = lean_ctor_get(x_1045, 0);
lean_inc(x_1144);
x_1145 = lean_ctor_get(x_1045, 1);
lean_inc(x_1145);
if (lean_is_exclusive(x_1045)) {
 lean_ctor_release(x_1045, 0);
 lean_ctor_release(x_1045, 1);
 x_1146 = x_1045;
} else {
 lean_dec_ref(x_1045);
 x_1146 = lean_box(0);
}
if (lean_is_scalar(x_1146)) {
 x_1147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1147 = x_1146;
}
lean_ctor_set(x_1147, 0, x_1144);
lean_ctor_set(x_1147, 1, x_1145);
return x_1147;
}
}
else
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
lean_dec(x_1037);
x_1148 = lean_ctor_get(x_1040, 0);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1040, 1);
lean_inc(x_1149);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 lean_ctor_release(x_1040, 1);
 x_1150 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1150 = lean_box(0);
}
if (lean_is_scalar(x_1150)) {
 x_1151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1151 = x_1150;
}
lean_ctor_set(x_1151, 0, x_1148);
lean_ctor_set(x_1151, 1, x_1149);
return x_1151;
}
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
lean_dec(x_1030);
x_1152 = lean_ctor_get(x_1033, 0);
lean_inc(x_1152);
x_1153 = lean_ctor_get(x_1033, 1);
lean_inc(x_1153);
if (lean_is_exclusive(x_1033)) {
 lean_ctor_release(x_1033, 0);
 lean_ctor_release(x_1033, 1);
 x_1154 = x_1033;
} else {
 lean_dec_ref(x_1033);
 x_1154 = lean_box(0);
}
if (lean_is_scalar(x_1154)) {
 x_1155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1155 = x_1154;
}
lean_ctor_set(x_1155, 0, x_1152);
lean_ctor_set(x_1155, 1, x_1153);
return x_1155;
}
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
lean_dec(x_1023);
x_1156 = lean_ctor_get(x_1026, 0);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1026, 1);
lean_inc(x_1157);
if (lean_is_exclusive(x_1026)) {
 lean_ctor_release(x_1026, 0);
 lean_ctor_release(x_1026, 1);
 x_1158 = x_1026;
} else {
 lean_dec_ref(x_1026);
 x_1158 = lean_box(0);
}
if (lean_is_scalar(x_1158)) {
 x_1159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1159 = x_1158;
}
lean_ctor_set(x_1159, 0, x_1156);
lean_ctor_set(x_1159, 1, x_1157);
return x_1159;
}
}
}
else
{
uint8_t x_1160; 
lean_dec(x_14);
x_1160 = !lean_is_exclusive(x_17);
if (x_1160 == 0)
{
return x_17;
}
else
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; 
x_1161 = lean_ctor_get(x_17, 0);
x_1162 = lean_ctor_get(x_17, 1);
lean_inc(x_1162);
lean_inc(x_1161);
lean_dec(x_17);
x_1163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1163, 0, x_1161);
lean_ctor_set(x_1163, 1, x_1162);
return x_1163;
}
}
}
else
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; 
x_1164 = lean_ctor_get(x_11, 1);
lean_inc(x_1164);
lean_dec(x_11);
x_1165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1165, 0, x_9);
lean_ctor_set(x_1165, 1, x_1164);
x_1166 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_1);
x_1167 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__4;
x_1168 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
lean_inc(x_1166);
x_1169 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1167, x_1168, x_1166, x_2, x_1165);
if (lean_obj_tag(x_1169) == 0)
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
x_1170 = lean_ctor_get(x_1169, 1);
lean_inc(x_1170);
if (lean_is_exclusive(x_1169)) {
 lean_ctor_release(x_1169, 0);
 lean_ctor_release(x_1169, 1);
 x_1171 = x_1169;
} else {
 lean_dec_ref(x_1169);
 x_1171 = lean_box(0);
}
if (lean_is_scalar(x_1171)) {
 x_1172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1172 = x_1171;
}
lean_ctor_set(x_1172, 0, x_9);
lean_ctor_set(x_1172, 1, x_1170);
x_1173 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(x_10, x_1166);
x_1174 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__7;
x_1175 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
lean_inc(x_1173);
x_1176 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1174, x_1175, x_1173, x_2, x_1172);
if (lean_obj_tag(x_1176) == 0)
{
lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
x_1177 = lean_ctor_get(x_1176, 1);
lean_inc(x_1177);
if (lean_is_exclusive(x_1176)) {
 lean_ctor_release(x_1176, 0);
 lean_ctor_release(x_1176, 1);
 x_1178 = x_1176;
} else {
 lean_dec_ref(x_1176);
 x_1178 = lean_box(0);
}
if (lean_is_scalar(x_1178)) {
 x_1179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1179 = x_1178;
}
lean_ctor_set(x_1179, 0, x_9);
lean_ctor_set(x_1179, 1, x_1177);
x_1180 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(x_10, x_1173);
x_1181 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
x_1182 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
lean_inc(x_1180);
x_1183 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1181, x_1182, x_1180, x_2, x_1179);
if (lean_obj_tag(x_1183) == 0)
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; 
x_1184 = lean_ctor_get(x_1183, 1);
lean_inc(x_1184);
if (lean_is_exclusive(x_1183)) {
 lean_ctor_release(x_1183, 0);
 lean_ctor_release(x_1183, 1);
 x_1185 = x_1183;
} else {
 lean_dec_ref(x_1183);
 x_1185 = lean_box(0);
}
if (lean_is_scalar(x_1185)) {
 x_1186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1186 = x_1185;
}
lean_ctor_set(x_1186, 0, x_9);
lean_ctor_set(x_1186, 1, x_1184);
x_1187 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(x_10, x_1180);
x_1188 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
x_1189 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean_inc(x_1187);
x_1190 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1188, x_1189, x_1187, x_2, x_1186);
if (lean_obj_tag(x_1190) == 0)
{
lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
x_1191 = lean_ctor_get(x_1190, 1);
lean_inc(x_1191);
if (lean_is_exclusive(x_1190)) {
 lean_ctor_release(x_1190, 0);
 lean_ctor_release(x_1190, 1);
 x_1192 = x_1190;
} else {
 lean_dec_ref(x_1190);
 x_1192 = lean_box(0);
}
if (lean_is_scalar(x_1192)) {
 x_1193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1193 = x_1192;
}
lean_ctor_set(x_1193, 0, x_9);
lean_ctor_set(x_1193, 1, x_1191);
x_1194 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_1187);
x_1195 = l_Lean_IR_inferBorrow(x_1194, x_2, x_1193);
if (lean_obj_tag(x_1195) == 0)
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1196 = lean_ctor_get(x_1195, 0);
lean_inc(x_1196);
x_1197 = lean_ctor_get(x_1195, 1);
lean_inc(x_1197);
if (lean_is_exclusive(x_1195)) {
 lean_ctor_release(x_1195, 0);
 lean_ctor_release(x_1195, 1);
 x_1198 = x_1195;
} else {
 lean_dec_ref(x_1195);
 x_1198 = lean_box(0);
}
if (lean_is_scalar(x_1198)) {
 x_1199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1199 = x_1198;
}
lean_ctor_set(x_1199, 0, x_9);
lean_ctor_set(x_1199, 1, x_1197);
x_1200 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_1201 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean_inc(x_1196);
x_1202 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1200, x_1201, x_1196, x_2, x_1199);
if (lean_obj_tag(x_1202) == 0)
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; 
x_1203 = lean_ctor_get(x_1202, 1);
lean_inc(x_1203);
if (lean_is_exclusive(x_1202)) {
 lean_ctor_release(x_1202, 0);
 lean_ctor_release(x_1202, 1);
 x_1204 = x_1202;
} else {
 lean_dec_ref(x_1202);
 x_1204 = lean_box(0);
}
if (lean_is_scalar(x_1204)) {
 x_1205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1205 = x_1204;
}
lean_ctor_set(x_1205, 0, x_9);
lean_ctor_set(x_1205, 1, x_1203);
x_1206 = l_Lean_IR_explicitBoxing(x_1196, x_2, x_1205);
if (lean_obj_tag(x_1206) == 0)
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; 
x_1207 = lean_ctor_get(x_1206, 0);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1206, 1);
lean_inc(x_1208);
if (lean_is_exclusive(x_1206)) {
 lean_ctor_release(x_1206, 0);
 lean_ctor_release(x_1206, 1);
 x_1209 = x_1206;
} else {
 lean_dec_ref(x_1206);
 x_1209 = lean_box(0);
}
if (lean_is_scalar(x_1209)) {
 x_1210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1210 = x_1209;
}
lean_ctor_set(x_1210, 0, x_9);
lean_ctor_set(x_1210, 1, x_1208);
x_1211 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_1212 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean_inc(x_1207);
x_1213 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1211, x_1212, x_1207, x_2, x_1210);
if (lean_obj_tag(x_1213) == 0)
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; 
x_1214 = lean_ctor_get(x_1213, 1);
lean_inc(x_1214);
if (lean_is_exclusive(x_1213)) {
 lean_ctor_release(x_1213, 0);
 lean_ctor_release(x_1213, 1);
 x_1215 = x_1213;
} else {
 lean_dec_ref(x_1213);
 x_1215 = lean_box(0);
}
if (lean_is_scalar(x_1215)) {
 x_1216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1216 = x_1215;
}
lean_ctor_set(x_1216, 0, x_9);
lean_ctor_set(x_1216, 1, x_1214);
x_1217 = l_Lean_IR_explicitRC(x_1207, x_2, x_1216);
if (lean_obj_tag(x_1217) == 0)
{
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
x_1218 = lean_ctor_get(x_1217, 0);
lean_inc(x_1218);
x_1219 = lean_ctor_get(x_1217, 1);
lean_inc(x_1219);
if (lean_is_exclusive(x_1217)) {
 lean_ctor_release(x_1217, 0);
 lean_ctor_release(x_1217, 1);
 x_1220 = x_1217;
} else {
 lean_dec_ref(x_1217);
 x_1220 = lean_box(0);
}
if (lean_is_scalar(x_1220)) {
 x_1221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1221 = x_1220;
}
lean_ctor_set(x_1221, 0, x_9);
lean_ctor_set(x_1221, 1, x_1219);
x_1222 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_1223 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean_inc(x_1218);
x_1224 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1222, x_1223, x_1218, x_2, x_1221);
if (lean_obj_tag(x_1224) == 0)
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; 
x_1225 = lean_ctor_get(x_1224, 1);
lean_inc(x_1225);
if (lean_is_exclusive(x_1224)) {
 lean_ctor_release(x_1224, 0);
 lean_ctor_release(x_1224, 1);
 x_1226 = x_1224;
} else {
 lean_dec_ref(x_1224);
 x_1226 = lean_box(0);
}
if (lean_is_scalar(x_1226)) {
 x_1227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1227 = x_1226;
}
lean_ctor_set(x_1227, 0, x_9);
lean_ctor_set(x_1227, 1, x_1225);
x_1228 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_10, x_1218);
x_1229 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_1230 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean_inc(x_1228);
x_1231 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1229, x_1230, x_1228, x_2, x_1227);
if (lean_obj_tag(x_1231) == 0)
{
lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
x_1232 = lean_ctor_get(x_1231, 1);
lean_inc(x_1232);
if (lean_is_exclusive(x_1231)) {
 lean_ctor_release(x_1231, 0);
 lean_ctor_release(x_1231, 1);
 x_1233 = x_1231;
} else {
 lean_dec_ref(x_1231);
 x_1233 = lean_box(0);
}
if (lean_is_scalar(x_1233)) {
 x_1234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1234 = x_1233;
}
lean_ctor_set(x_1234, 0, x_9);
lean_ctor_set(x_1234, 1, x_1232);
x_1235 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_10, x_1228);
lean_inc(x_1235);
x_1236 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1167, x_1168, x_1235, x_2, x_1234);
if (lean_obj_tag(x_1236) == 0)
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; 
x_1237 = lean_ctor_get(x_1236, 1);
lean_inc(x_1237);
if (lean_is_exclusive(x_1236)) {
 lean_ctor_release(x_1236, 0);
 lean_ctor_release(x_1236, 1);
 x_1238 = x_1236;
} else {
 lean_dec_ref(x_1236);
 x_1238 = lean_box(0);
}
if (lean_is_scalar(x_1238)) {
 x_1239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1239 = x_1238;
}
lean_ctor_set(x_1239, 0, x_9);
lean_ctor_set(x_1239, 1, x_1237);
x_1240 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_1241 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_1235);
x_1242 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1240, x_1241, x_1235, x_2, x_1239);
if (lean_obj_tag(x_1242) == 0)
{
lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; 
x_1243 = lean_ctor_get(x_1242, 1);
lean_inc(x_1243);
if (lean_is_exclusive(x_1242)) {
 lean_ctor_release(x_1242, 0);
 lean_ctor_release(x_1242, 1);
 x_1244 = x_1242;
} else {
 lean_dec_ref(x_1242);
 x_1244 = lean_box(0);
}
if (lean_is_scalar(x_1244)) {
 x_1245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1245 = x_1244;
}
lean_ctor_set(x_1245, 0, x_9);
lean_ctor_set(x_1245, 1, x_1243);
lean_inc(x_1235);
x_1246 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1235, x_1235, x_10, x_2, x_1245);
if (lean_obj_tag(x_1246) == 0)
{
lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; 
x_1247 = lean_ctor_get(x_1246, 1);
lean_inc(x_1247);
if (lean_is_exclusive(x_1246)) {
 lean_ctor_release(x_1246, 0);
 lean_ctor_release(x_1246, 1);
 x_1248 = x_1246;
} else {
 lean_dec_ref(x_1246);
 x_1248 = lean_box(0);
}
if (lean_is_scalar(x_1248)) {
 x_1249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1249 = x_1248;
}
lean_ctor_set(x_1249, 0, x_9);
lean_ctor_set(x_1249, 1, x_1247);
x_1250 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_1235, x_10, x_2, x_1249);
lean_dec(x_1235);
if (lean_obj_tag(x_1250) == 0)
{
lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; 
x_1251 = lean_ctor_get(x_1250, 1);
lean_inc(x_1251);
if (lean_is_exclusive(x_1250)) {
 lean_ctor_release(x_1250, 0);
 lean_ctor_release(x_1250, 1);
 x_1252 = x_1250;
} else {
 lean_dec_ref(x_1250);
 x_1252 = lean_box(0);
}
if (lean_is_scalar(x_1252)) {
 x_1253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1253 = x_1252;
}
lean_ctor_set(x_1253, 0, x_9);
lean_ctor_set(x_1253, 1, x_1251);
return x_1253;
}
else
{
lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; 
x_1254 = lean_ctor_get(x_1250, 0);
lean_inc(x_1254);
x_1255 = lean_ctor_get(x_1250, 1);
lean_inc(x_1255);
if (lean_is_exclusive(x_1250)) {
 lean_ctor_release(x_1250, 0);
 lean_ctor_release(x_1250, 1);
 x_1256 = x_1250;
} else {
 lean_dec_ref(x_1250);
 x_1256 = lean_box(0);
}
if (lean_is_scalar(x_1256)) {
 x_1257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1257 = x_1256;
}
lean_ctor_set(x_1257, 0, x_1254);
lean_ctor_set(x_1257, 1, x_1255);
return x_1257;
}
}
else
{
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
lean_dec(x_1235);
x_1258 = lean_ctor_get(x_1246, 0);
lean_inc(x_1258);
x_1259 = lean_ctor_get(x_1246, 1);
lean_inc(x_1259);
if (lean_is_exclusive(x_1246)) {
 lean_ctor_release(x_1246, 0);
 lean_ctor_release(x_1246, 1);
 x_1260 = x_1246;
} else {
 lean_dec_ref(x_1246);
 x_1260 = lean_box(0);
}
if (lean_is_scalar(x_1260)) {
 x_1261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1261 = x_1260;
}
lean_ctor_set(x_1261, 0, x_1258);
lean_ctor_set(x_1261, 1, x_1259);
return x_1261;
}
}
else
{
lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; 
lean_dec(x_1235);
x_1262 = lean_ctor_get(x_1242, 0);
lean_inc(x_1262);
x_1263 = lean_ctor_get(x_1242, 1);
lean_inc(x_1263);
if (lean_is_exclusive(x_1242)) {
 lean_ctor_release(x_1242, 0);
 lean_ctor_release(x_1242, 1);
 x_1264 = x_1242;
} else {
 lean_dec_ref(x_1242);
 x_1264 = lean_box(0);
}
if (lean_is_scalar(x_1264)) {
 x_1265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1265 = x_1264;
}
lean_ctor_set(x_1265, 0, x_1262);
lean_ctor_set(x_1265, 1, x_1263);
return x_1265;
}
}
else
{
lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
lean_dec(x_1235);
x_1266 = lean_ctor_get(x_1236, 0);
lean_inc(x_1266);
x_1267 = lean_ctor_get(x_1236, 1);
lean_inc(x_1267);
if (lean_is_exclusive(x_1236)) {
 lean_ctor_release(x_1236, 0);
 lean_ctor_release(x_1236, 1);
 x_1268 = x_1236;
} else {
 lean_dec_ref(x_1236);
 x_1268 = lean_box(0);
}
if (lean_is_scalar(x_1268)) {
 x_1269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1269 = x_1268;
}
lean_ctor_set(x_1269, 0, x_1266);
lean_ctor_set(x_1269, 1, x_1267);
return x_1269;
}
}
else
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; 
lean_dec(x_1228);
x_1270 = lean_ctor_get(x_1231, 0);
lean_inc(x_1270);
x_1271 = lean_ctor_get(x_1231, 1);
lean_inc(x_1271);
if (lean_is_exclusive(x_1231)) {
 lean_ctor_release(x_1231, 0);
 lean_ctor_release(x_1231, 1);
 x_1272 = x_1231;
} else {
 lean_dec_ref(x_1231);
 x_1272 = lean_box(0);
}
if (lean_is_scalar(x_1272)) {
 x_1273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1273 = x_1272;
}
lean_ctor_set(x_1273, 0, x_1270);
lean_ctor_set(x_1273, 1, x_1271);
return x_1273;
}
}
else
{
lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; 
lean_dec(x_1218);
x_1274 = lean_ctor_get(x_1224, 0);
lean_inc(x_1274);
x_1275 = lean_ctor_get(x_1224, 1);
lean_inc(x_1275);
if (lean_is_exclusive(x_1224)) {
 lean_ctor_release(x_1224, 0);
 lean_ctor_release(x_1224, 1);
 x_1276 = x_1224;
} else {
 lean_dec_ref(x_1224);
 x_1276 = lean_box(0);
}
if (lean_is_scalar(x_1276)) {
 x_1277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1277 = x_1276;
}
lean_ctor_set(x_1277, 0, x_1274);
lean_ctor_set(x_1277, 1, x_1275);
return x_1277;
}
}
else
{
lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; 
x_1278 = lean_ctor_get(x_1217, 0);
lean_inc(x_1278);
x_1279 = lean_ctor_get(x_1217, 1);
lean_inc(x_1279);
if (lean_is_exclusive(x_1217)) {
 lean_ctor_release(x_1217, 0);
 lean_ctor_release(x_1217, 1);
 x_1280 = x_1217;
} else {
 lean_dec_ref(x_1217);
 x_1280 = lean_box(0);
}
if (lean_is_scalar(x_1280)) {
 x_1281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1281 = x_1280;
}
lean_ctor_set(x_1281, 0, x_1278);
lean_ctor_set(x_1281, 1, x_1279);
return x_1281;
}
}
else
{
lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; 
lean_dec(x_1207);
x_1282 = lean_ctor_get(x_1213, 0);
lean_inc(x_1282);
x_1283 = lean_ctor_get(x_1213, 1);
lean_inc(x_1283);
if (lean_is_exclusive(x_1213)) {
 lean_ctor_release(x_1213, 0);
 lean_ctor_release(x_1213, 1);
 x_1284 = x_1213;
} else {
 lean_dec_ref(x_1213);
 x_1284 = lean_box(0);
}
if (lean_is_scalar(x_1284)) {
 x_1285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1285 = x_1284;
}
lean_ctor_set(x_1285, 0, x_1282);
lean_ctor_set(x_1285, 1, x_1283);
return x_1285;
}
}
else
{
lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; 
x_1286 = lean_ctor_get(x_1206, 0);
lean_inc(x_1286);
x_1287 = lean_ctor_get(x_1206, 1);
lean_inc(x_1287);
if (lean_is_exclusive(x_1206)) {
 lean_ctor_release(x_1206, 0);
 lean_ctor_release(x_1206, 1);
 x_1288 = x_1206;
} else {
 lean_dec_ref(x_1206);
 x_1288 = lean_box(0);
}
if (lean_is_scalar(x_1288)) {
 x_1289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1289 = x_1288;
}
lean_ctor_set(x_1289, 0, x_1286);
lean_ctor_set(x_1289, 1, x_1287);
return x_1289;
}
}
else
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; 
lean_dec(x_1196);
x_1290 = lean_ctor_get(x_1202, 0);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1202, 1);
lean_inc(x_1291);
if (lean_is_exclusive(x_1202)) {
 lean_ctor_release(x_1202, 0);
 lean_ctor_release(x_1202, 1);
 x_1292 = x_1202;
} else {
 lean_dec_ref(x_1202);
 x_1292 = lean_box(0);
}
if (lean_is_scalar(x_1292)) {
 x_1293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1293 = x_1292;
}
lean_ctor_set(x_1293, 0, x_1290);
lean_ctor_set(x_1293, 1, x_1291);
return x_1293;
}
}
else
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; 
x_1294 = lean_ctor_get(x_1195, 0);
lean_inc(x_1294);
x_1295 = lean_ctor_get(x_1195, 1);
lean_inc(x_1295);
if (lean_is_exclusive(x_1195)) {
 lean_ctor_release(x_1195, 0);
 lean_ctor_release(x_1195, 1);
 x_1296 = x_1195;
} else {
 lean_dec_ref(x_1195);
 x_1296 = lean_box(0);
}
if (lean_is_scalar(x_1296)) {
 x_1297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1297 = x_1296;
}
lean_ctor_set(x_1297, 0, x_1294);
lean_ctor_set(x_1297, 1, x_1295);
return x_1297;
}
}
else
{
lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; 
lean_dec(x_1187);
x_1298 = lean_ctor_get(x_1190, 0);
lean_inc(x_1298);
x_1299 = lean_ctor_get(x_1190, 1);
lean_inc(x_1299);
if (lean_is_exclusive(x_1190)) {
 lean_ctor_release(x_1190, 0);
 lean_ctor_release(x_1190, 1);
 x_1300 = x_1190;
} else {
 lean_dec_ref(x_1190);
 x_1300 = lean_box(0);
}
if (lean_is_scalar(x_1300)) {
 x_1301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1301 = x_1300;
}
lean_ctor_set(x_1301, 0, x_1298);
lean_ctor_set(x_1301, 1, x_1299);
return x_1301;
}
}
else
{
lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; 
lean_dec(x_1180);
x_1302 = lean_ctor_get(x_1183, 0);
lean_inc(x_1302);
x_1303 = lean_ctor_get(x_1183, 1);
lean_inc(x_1303);
if (lean_is_exclusive(x_1183)) {
 lean_ctor_release(x_1183, 0);
 lean_ctor_release(x_1183, 1);
 x_1304 = x_1183;
} else {
 lean_dec_ref(x_1183);
 x_1304 = lean_box(0);
}
if (lean_is_scalar(x_1304)) {
 x_1305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1305 = x_1304;
}
lean_ctor_set(x_1305, 0, x_1302);
lean_ctor_set(x_1305, 1, x_1303);
return x_1305;
}
}
else
{
lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; 
lean_dec(x_1173);
x_1306 = lean_ctor_get(x_1176, 0);
lean_inc(x_1306);
x_1307 = lean_ctor_get(x_1176, 1);
lean_inc(x_1307);
if (lean_is_exclusive(x_1176)) {
 lean_ctor_release(x_1176, 0);
 lean_ctor_release(x_1176, 1);
 x_1308 = x_1176;
} else {
 lean_dec_ref(x_1176);
 x_1308 = lean_box(0);
}
if (lean_is_scalar(x_1308)) {
 x_1309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1309 = x_1308;
}
lean_ctor_set(x_1309, 0, x_1306);
lean_ctor_set(x_1309, 1, x_1307);
return x_1309;
}
}
else
{
lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; 
lean_dec(x_1166);
x_1310 = lean_ctor_get(x_1169, 0);
lean_inc(x_1310);
x_1311 = lean_ctor_get(x_1169, 1);
lean_inc(x_1311);
if (lean_is_exclusive(x_1169)) {
 lean_ctor_release(x_1169, 0);
 lean_ctor_release(x_1169, 1);
 x_1312 = x_1169;
} else {
 lean_dec_ref(x_1169);
 x_1312 = lean_box(0);
}
if (lean_is_scalar(x_1312)) {
 x_1313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1313 = x_1312;
}
lean_ctor_set(x_1313, 0, x_1310);
lean_ctor_set(x_1313, 1, x_1311);
return x_1313;
}
}
}
else
{
uint8_t x_1314; 
lean_dec(x_1);
x_1314 = !lean_is_exclusive(x_11);
if (x_1314 == 0)
{
return x_11;
}
else
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; 
x_1315 = lean_ctor_get(x_11, 0);
x_1316 = lean_ctor_get(x_11, 1);
lean_inc(x_1316);
lean_inc(x_1315);
lean_dec(x_11);
x_1317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1317, 0, x_1315);
lean_ctor_set(x_1317, 1, x_1316);
return x_1317;
}
}
}
else
{
lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; 
x_1318 = lean_ctor_get(x_6, 1);
lean_inc(x_1318);
lean_dec(x_6);
x_1319 = lean_box(0);
x_1320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1320, 0, x_1319);
lean_ctor_set(x_1320, 1, x_1318);
x_1321 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_1322 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1, x_1, x_1321, x_2, x_1320);
if (lean_obj_tag(x_1322) == 0)
{
lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
x_1323 = lean_ctor_get(x_1322, 1);
lean_inc(x_1323);
if (lean_is_exclusive(x_1322)) {
 lean_ctor_release(x_1322, 0);
 lean_ctor_release(x_1322, 1);
 x_1324 = x_1322;
} else {
 lean_dec_ref(x_1322);
 x_1324 = lean_box(0);
}
if (lean_is_scalar(x_1324)) {
 x_1325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1325 = x_1324;
}
lean_ctor_set(x_1325, 0, x_1319);
lean_ctor_set(x_1325, 1, x_1323);
x_1326 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_1321, x_1);
x_1327 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__4;
x_1328 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__3;
lean_inc(x_1326);
x_1329 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1327, x_1328, x_1326, x_2, x_1325);
if (lean_obj_tag(x_1329) == 0)
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; 
x_1330 = lean_ctor_get(x_1329, 1);
lean_inc(x_1330);
if (lean_is_exclusive(x_1329)) {
 lean_ctor_release(x_1329, 0);
 lean_ctor_release(x_1329, 1);
 x_1331 = x_1329;
} else {
 lean_dec_ref(x_1329);
 x_1331 = lean_box(0);
}
if (lean_is_scalar(x_1331)) {
 x_1332 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1332 = x_1331;
}
lean_ctor_set(x_1332, 0, x_1319);
lean_ctor_set(x_1332, 1, x_1330);
x_1333 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__2(x_1321, x_1326);
x_1334 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__7;
x_1335 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__6;
lean_inc(x_1333);
x_1336 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1334, x_1335, x_1333, x_2, x_1332);
if (lean_obj_tag(x_1336) == 0)
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; 
x_1337 = lean_ctor_get(x_1336, 1);
lean_inc(x_1337);
if (lean_is_exclusive(x_1336)) {
 lean_ctor_release(x_1336, 0);
 lean_ctor_release(x_1336, 1);
 x_1338 = x_1336;
} else {
 lean_dec_ref(x_1336);
 x_1338 = lean_box(0);
}
if (lean_is_scalar(x_1338)) {
 x_1339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1339 = x_1338;
}
lean_ctor_set(x_1339, 0, x_1319);
lean_ctor_set(x_1339, 1, x_1337);
x_1340 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__3(x_1321, x_1333);
x_1341 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__10;
x_1342 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__9;
lean_inc(x_1340);
x_1343 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1341, x_1342, x_1340, x_2, x_1339);
if (lean_obj_tag(x_1343) == 0)
{
lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
x_1344 = lean_ctor_get(x_1343, 1);
lean_inc(x_1344);
if (lean_is_exclusive(x_1343)) {
 lean_ctor_release(x_1343, 0);
 lean_ctor_release(x_1343, 1);
 x_1345 = x_1343;
} else {
 lean_dec_ref(x_1343);
 x_1345 = lean_box(0);
}
if (lean_is_scalar(x_1345)) {
 x_1346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1346 = x_1345;
}
lean_ctor_set(x_1346, 0, x_1319);
lean_ctor_set(x_1346, 1, x_1344);
x_1347 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__4(x_1321, x_1340);
x_1348 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__13;
x_1349 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__12;
lean_inc(x_1347);
x_1350 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1348, x_1349, x_1347, x_2, x_1346);
if (lean_obj_tag(x_1350) == 0)
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; 
x_1351 = lean_ctor_get(x_1350, 1);
lean_inc(x_1351);
if (lean_is_exclusive(x_1350)) {
 lean_ctor_release(x_1350, 0);
 lean_ctor_release(x_1350, 1);
 x_1352 = x_1350;
} else {
 lean_dec_ref(x_1350);
 x_1352 = lean_box(0);
}
if (lean_is_scalar(x_1352)) {
 x_1353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1353 = x_1352;
}
lean_ctor_set(x_1353, 0, x_1319);
lean_ctor_set(x_1353, 1, x_1351);
x_1354 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_1321, x_1347);
x_1355 = l_Lean_IR_inferBorrow(x_1354, x_2, x_1353);
if (lean_obj_tag(x_1355) == 0)
{
lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; 
x_1356 = lean_ctor_get(x_1355, 0);
lean_inc(x_1356);
x_1357 = lean_ctor_get(x_1355, 1);
lean_inc(x_1357);
if (lean_is_exclusive(x_1355)) {
 lean_ctor_release(x_1355, 0);
 lean_ctor_release(x_1355, 1);
 x_1358 = x_1355;
} else {
 lean_dec_ref(x_1355);
 x_1358 = lean_box(0);
}
if (lean_is_scalar(x_1358)) {
 x_1359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1359 = x_1358;
}
lean_ctor_set(x_1359, 0, x_1319);
lean_ctor_set(x_1359, 1, x_1357);
x_1360 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__16;
x_1361 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__15;
lean_inc(x_1356);
x_1362 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1360, x_1361, x_1356, x_2, x_1359);
if (lean_obj_tag(x_1362) == 0)
{
lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; 
x_1363 = lean_ctor_get(x_1362, 1);
lean_inc(x_1363);
if (lean_is_exclusive(x_1362)) {
 lean_ctor_release(x_1362, 0);
 lean_ctor_release(x_1362, 1);
 x_1364 = x_1362;
} else {
 lean_dec_ref(x_1362);
 x_1364 = lean_box(0);
}
if (lean_is_scalar(x_1364)) {
 x_1365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1365 = x_1364;
}
lean_ctor_set(x_1365, 0, x_1319);
lean_ctor_set(x_1365, 1, x_1363);
x_1366 = l_Lean_IR_explicitBoxing(x_1356, x_2, x_1365);
if (lean_obj_tag(x_1366) == 0)
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; 
x_1367 = lean_ctor_get(x_1366, 0);
lean_inc(x_1367);
x_1368 = lean_ctor_get(x_1366, 1);
lean_inc(x_1368);
if (lean_is_exclusive(x_1366)) {
 lean_ctor_release(x_1366, 0);
 lean_ctor_release(x_1366, 1);
 x_1369 = x_1366;
} else {
 lean_dec_ref(x_1366);
 x_1369 = lean_box(0);
}
if (lean_is_scalar(x_1369)) {
 x_1370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1370 = x_1369;
}
lean_ctor_set(x_1370, 0, x_1319);
lean_ctor_set(x_1370, 1, x_1368);
x_1371 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__19;
x_1372 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__18;
lean_inc(x_1367);
x_1373 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1371, x_1372, x_1367, x_2, x_1370);
if (lean_obj_tag(x_1373) == 0)
{
lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
x_1374 = lean_ctor_get(x_1373, 1);
lean_inc(x_1374);
if (lean_is_exclusive(x_1373)) {
 lean_ctor_release(x_1373, 0);
 lean_ctor_release(x_1373, 1);
 x_1375 = x_1373;
} else {
 lean_dec_ref(x_1373);
 x_1375 = lean_box(0);
}
if (lean_is_scalar(x_1375)) {
 x_1376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1376 = x_1375;
}
lean_ctor_set(x_1376, 0, x_1319);
lean_ctor_set(x_1376, 1, x_1374);
x_1377 = l_Lean_IR_explicitRC(x_1367, x_2, x_1376);
if (lean_obj_tag(x_1377) == 0)
{
lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; 
x_1378 = lean_ctor_get(x_1377, 0);
lean_inc(x_1378);
x_1379 = lean_ctor_get(x_1377, 1);
lean_inc(x_1379);
if (lean_is_exclusive(x_1377)) {
 lean_ctor_release(x_1377, 0);
 lean_ctor_release(x_1377, 1);
 x_1380 = x_1377;
} else {
 lean_dec_ref(x_1377);
 x_1380 = lean_box(0);
}
if (lean_is_scalar(x_1380)) {
 x_1381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1381 = x_1380;
}
lean_ctor_set(x_1381, 0, x_1319);
lean_ctor_set(x_1381, 1, x_1379);
x_1382 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__22;
x_1383 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__21;
lean_inc(x_1378);
x_1384 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1382, x_1383, x_1378, x_2, x_1381);
if (lean_obj_tag(x_1384) == 0)
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; 
x_1385 = lean_ctor_get(x_1384, 1);
lean_inc(x_1385);
if (lean_is_exclusive(x_1384)) {
 lean_ctor_release(x_1384, 0);
 lean_ctor_release(x_1384, 1);
 x_1386 = x_1384;
} else {
 lean_dec_ref(x_1384);
 x_1386 = lean_box(0);
}
if (lean_is_scalar(x_1386)) {
 x_1387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1387 = x_1386;
}
lean_ctor_set(x_1387, 0, x_1319);
lean_ctor_set(x_1387, 1, x_1385);
x_1388 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__5(x_1321, x_1378);
x_1389 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__25;
x_1390 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__24;
lean_inc(x_1388);
x_1391 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1389, x_1390, x_1388, x_2, x_1387);
if (lean_obj_tag(x_1391) == 0)
{
lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; 
x_1392 = lean_ctor_get(x_1391, 1);
lean_inc(x_1392);
if (lean_is_exclusive(x_1391)) {
 lean_ctor_release(x_1391, 0);
 lean_ctor_release(x_1391, 1);
 x_1393 = x_1391;
} else {
 lean_dec_ref(x_1391);
 x_1393 = lean_box(0);
}
if (lean_is_scalar(x_1393)) {
 x_1394 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1394 = x_1393;
}
lean_ctor_set(x_1394, 0, x_1319);
lean_ctor_set(x_1394, 1, x_1392);
x_1395 = l_Array_ummapAux___main___at___private_init_lean_compiler_ir_default_1__compileAux___spec__1(x_1321, x_1388);
lean_inc(x_1395);
x_1396 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1327, x_1328, x_1395, x_2, x_1394);
if (lean_obj_tag(x_1396) == 0)
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; 
x_1397 = lean_ctor_get(x_1396, 1);
lean_inc(x_1397);
if (lean_is_exclusive(x_1396)) {
 lean_ctor_release(x_1396, 0);
 lean_ctor_release(x_1396, 1);
 x_1398 = x_1396;
} else {
 lean_dec_ref(x_1396);
 x_1398 = lean_box(0);
}
if (lean_is_scalar(x_1398)) {
 x_1399 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1399 = x_1398;
}
lean_ctor_set(x_1399, 0, x_1319);
lean_ctor_set(x_1399, 1, x_1397);
x_1400 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__28;
x_1401 = l___private_init_lean_compiler_ir_default_1__compileAux___closed__27;
lean_inc(x_1395);
x_1402 = l___private_init_lean_compiler_ir_compilerm_2__logDeclsAux(x_1400, x_1401, x_1395, x_2, x_1399);
if (lean_obj_tag(x_1402) == 0)
{
lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
x_1403 = lean_ctor_get(x_1402, 1);
lean_inc(x_1403);
if (lean_is_exclusive(x_1402)) {
 lean_ctor_release(x_1402, 0);
 lean_ctor_release(x_1402, 1);
 x_1404 = x_1402;
} else {
 lean_dec_ref(x_1402);
 x_1404 = lean_box(0);
}
if (lean_is_scalar(x_1404)) {
 x_1405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1405 = x_1404;
}
lean_ctor_set(x_1405, 0, x_1319);
lean_ctor_set(x_1405, 1, x_1403);
lean_inc(x_1395);
x_1406 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1395, x_1395, x_1321, x_2, x_1405);
if (lean_obj_tag(x_1406) == 0)
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; 
x_1407 = lean_ctor_get(x_1406, 1);
lean_inc(x_1407);
if (lean_is_exclusive(x_1406)) {
 lean_ctor_release(x_1406, 0);
 lean_ctor_release(x_1406, 1);
 x_1408 = x_1406;
} else {
 lean_dec_ref(x_1406);
 x_1408 = lean_box(0);
}
if (lean_is_scalar(x_1408)) {
 x_1409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1409 = x_1408;
}
lean_ctor_set(x_1409, 0, x_1319);
lean_ctor_set(x_1409, 1, x_1407);
x_1410 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_1395, x_1321, x_2, x_1409);
lean_dec(x_1395);
if (lean_obj_tag(x_1410) == 0)
{
lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; 
x_1411 = lean_ctor_get(x_1410, 1);
lean_inc(x_1411);
if (lean_is_exclusive(x_1410)) {
 lean_ctor_release(x_1410, 0);
 lean_ctor_release(x_1410, 1);
 x_1412 = x_1410;
} else {
 lean_dec_ref(x_1410);
 x_1412 = lean_box(0);
}
if (lean_is_scalar(x_1412)) {
 x_1413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1413 = x_1412;
}
lean_ctor_set(x_1413, 0, x_1319);
lean_ctor_set(x_1413, 1, x_1411);
return x_1413;
}
else
{
lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; 
x_1414 = lean_ctor_get(x_1410, 0);
lean_inc(x_1414);
x_1415 = lean_ctor_get(x_1410, 1);
lean_inc(x_1415);
if (lean_is_exclusive(x_1410)) {
 lean_ctor_release(x_1410, 0);
 lean_ctor_release(x_1410, 1);
 x_1416 = x_1410;
} else {
 lean_dec_ref(x_1410);
 x_1416 = lean_box(0);
}
if (lean_is_scalar(x_1416)) {
 x_1417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1417 = x_1416;
}
lean_ctor_set(x_1417, 0, x_1414);
lean_ctor_set(x_1417, 1, x_1415);
return x_1417;
}
}
else
{
lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; 
lean_dec(x_1395);
x_1418 = lean_ctor_get(x_1406, 0);
lean_inc(x_1418);
x_1419 = lean_ctor_get(x_1406, 1);
lean_inc(x_1419);
if (lean_is_exclusive(x_1406)) {
 lean_ctor_release(x_1406, 0);
 lean_ctor_release(x_1406, 1);
 x_1420 = x_1406;
} else {
 lean_dec_ref(x_1406);
 x_1420 = lean_box(0);
}
if (lean_is_scalar(x_1420)) {
 x_1421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1421 = x_1420;
}
lean_ctor_set(x_1421, 0, x_1418);
lean_ctor_set(x_1421, 1, x_1419);
return x_1421;
}
}
else
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; 
lean_dec(x_1395);
x_1422 = lean_ctor_get(x_1402, 0);
lean_inc(x_1422);
x_1423 = lean_ctor_get(x_1402, 1);
lean_inc(x_1423);
if (lean_is_exclusive(x_1402)) {
 lean_ctor_release(x_1402, 0);
 lean_ctor_release(x_1402, 1);
 x_1424 = x_1402;
} else {
 lean_dec_ref(x_1402);
 x_1424 = lean_box(0);
}
if (lean_is_scalar(x_1424)) {
 x_1425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1425 = x_1424;
}
lean_ctor_set(x_1425, 0, x_1422);
lean_ctor_set(x_1425, 1, x_1423);
return x_1425;
}
}
else
{
lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; 
lean_dec(x_1395);
x_1426 = lean_ctor_get(x_1396, 0);
lean_inc(x_1426);
x_1427 = lean_ctor_get(x_1396, 1);
lean_inc(x_1427);
if (lean_is_exclusive(x_1396)) {
 lean_ctor_release(x_1396, 0);
 lean_ctor_release(x_1396, 1);
 x_1428 = x_1396;
} else {
 lean_dec_ref(x_1396);
 x_1428 = lean_box(0);
}
if (lean_is_scalar(x_1428)) {
 x_1429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1429 = x_1428;
}
lean_ctor_set(x_1429, 0, x_1426);
lean_ctor_set(x_1429, 1, x_1427);
return x_1429;
}
}
else
{
lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; 
lean_dec(x_1388);
x_1430 = lean_ctor_get(x_1391, 0);
lean_inc(x_1430);
x_1431 = lean_ctor_get(x_1391, 1);
lean_inc(x_1431);
if (lean_is_exclusive(x_1391)) {
 lean_ctor_release(x_1391, 0);
 lean_ctor_release(x_1391, 1);
 x_1432 = x_1391;
} else {
 lean_dec_ref(x_1391);
 x_1432 = lean_box(0);
}
if (lean_is_scalar(x_1432)) {
 x_1433 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1433 = x_1432;
}
lean_ctor_set(x_1433, 0, x_1430);
lean_ctor_set(x_1433, 1, x_1431);
return x_1433;
}
}
else
{
lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; 
lean_dec(x_1378);
x_1434 = lean_ctor_get(x_1384, 0);
lean_inc(x_1434);
x_1435 = lean_ctor_get(x_1384, 1);
lean_inc(x_1435);
if (lean_is_exclusive(x_1384)) {
 lean_ctor_release(x_1384, 0);
 lean_ctor_release(x_1384, 1);
 x_1436 = x_1384;
} else {
 lean_dec_ref(x_1384);
 x_1436 = lean_box(0);
}
if (lean_is_scalar(x_1436)) {
 x_1437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1437 = x_1436;
}
lean_ctor_set(x_1437, 0, x_1434);
lean_ctor_set(x_1437, 1, x_1435);
return x_1437;
}
}
else
{
lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; 
x_1438 = lean_ctor_get(x_1377, 0);
lean_inc(x_1438);
x_1439 = lean_ctor_get(x_1377, 1);
lean_inc(x_1439);
if (lean_is_exclusive(x_1377)) {
 lean_ctor_release(x_1377, 0);
 lean_ctor_release(x_1377, 1);
 x_1440 = x_1377;
} else {
 lean_dec_ref(x_1377);
 x_1440 = lean_box(0);
}
if (lean_is_scalar(x_1440)) {
 x_1441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1441 = x_1440;
}
lean_ctor_set(x_1441, 0, x_1438);
lean_ctor_set(x_1441, 1, x_1439);
return x_1441;
}
}
else
{
lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; 
lean_dec(x_1367);
x_1442 = lean_ctor_get(x_1373, 0);
lean_inc(x_1442);
x_1443 = lean_ctor_get(x_1373, 1);
lean_inc(x_1443);
if (lean_is_exclusive(x_1373)) {
 lean_ctor_release(x_1373, 0);
 lean_ctor_release(x_1373, 1);
 x_1444 = x_1373;
} else {
 lean_dec_ref(x_1373);
 x_1444 = lean_box(0);
}
if (lean_is_scalar(x_1444)) {
 x_1445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1445 = x_1444;
}
lean_ctor_set(x_1445, 0, x_1442);
lean_ctor_set(x_1445, 1, x_1443);
return x_1445;
}
}
else
{
lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; 
x_1446 = lean_ctor_get(x_1366, 0);
lean_inc(x_1446);
x_1447 = lean_ctor_get(x_1366, 1);
lean_inc(x_1447);
if (lean_is_exclusive(x_1366)) {
 lean_ctor_release(x_1366, 0);
 lean_ctor_release(x_1366, 1);
 x_1448 = x_1366;
} else {
 lean_dec_ref(x_1366);
 x_1448 = lean_box(0);
}
if (lean_is_scalar(x_1448)) {
 x_1449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1449 = x_1448;
}
lean_ctor_set(x_1449, 0, x_1446);
lean_ctor_set(x_1449, 1, x_1447);
return x_1449;
}
}
else
{
lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; 
lean_dec(x_1356);
x_1450 = lean_ctor_get(x_1362, 0);
lean_inc(x_1450);
x_1451 = lean_ctor_get(x_1362, 1);
lean_inc(x_1451);
if (lean_is_exclusive(x_1362)) {
 lean_ctor_release(x_1362, 0);
 lean_ctor_release(x_1362, 1);
 x_1452 = x_1362;
} else {
 lean_dec_ref(x_1362);
 x_1452 = lean_box(0);
}
if (lean_is_scalar(x_1452)) {
 x_1453 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1453 = x_1452;
}
lean_ctor_set(x_1453, 0, x_1450);
lean_ctor_set(x_1453, 1, x_1451);
return x_1453;
}
}
else
{
lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; 
x_1454 = lean_ctor_get(x_1355, 0);
lean_inc(x_1454);
x_1455 = lean_ctor_get(x_1355, 1);
lean_inc(x_1455);
if (lean_is_exclusive(x_1355)) {
 lean_ctor_release(x_1355, 0);
 lean_ctor_release(x_1355, 1);
 x_1456 = x_1355;
} else {
 lean_dec_ref(x_1355);
 x_1456 = lean_box(0);
}
if (lean_is_scalar(x_1456)) {
 x_1457 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1457 = x_1456;
}
lean_ctor_set(x_1457, 0, x_1454);
lean_ctor_set(x_1457, 1, x_1455);
return x_1457;
}
}
else
{
lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; 
lean_dec(x_1347);
x_1458 = lean_ctor_get(x_1350, 0);
lean_inc(x_1458);
x_1459 = lean_ctor_get(x_1350, 1);
lean_inc(x_1459);
if (lean_is_exclusive(x_1350)) {
 lean_ctor_release(x_1350, 0);
 lean_ctor_release(x_1350, 1);
 x_1460 = x_1350;
} else {
 lean_dec_ref(x_1350);
 x_1460 = lean_box(0);
}
if (lean_is_scalar(x_1460)) {
 x_1461 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1461 = x_1460;
}
lean_ctor_set(x_1461, 0, x_1458);
lean_ctor_set(x_1461, 1, x_1459);
return x_1461;
}
}
else
{
lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; 
lean_dec(x_1340);
x_1462 = lean_ctor_get(x_1343, 0);
lean_inc(x_1462);
x_1463 = lean_ctor_get(x_1343, 1);
lean_inc(x_1463);
if (lean_is_exclusive(x_1343)) {
 lean_ctor_release(x_1343, 0);
 lean_ctor_release(x_1343, 1);
 x_1464 = x_1343;
} else {
 lean_dec_ref(x_1343);
 x_1464 = lean_box(0);
}
if (lean_is_scalar(x_1464)) {
 x_1465 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1465 = x_1464;
}
lean_ctor_set(x_1465, 0, x_1462);
lean_ctor_set(x_1465, 1, x_1463);
return x_1465;
}
}
else
{
lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; 
lean_dec(x_1333);
x_1466 = lean_ctor_get(x_1336, 0);
lean_inc(x_1466);
x_1467 = lean_ctor_get(x_1336, 1);
lean_inc(x_1467);
if (lean_is_exclusive(x_1336)) {
 lean_ctor_release(x_1336, 0);
 lean_ctor_release(x_1336, 1);
 x_1468 = x_1336;
} else {
 lean_dec_ref(x_1336);
 x_1468 = lean_box(0);
}
if (lean_is_scalar(x_1468)) {
 x_1469 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1469 = x_1468;
}
lean_ctor_set(x_1469, 0, x_1466);
lean_ctor_set(x_1469, 1, x_1467);
return x_1469;
}
}
else
{
lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; 
lean_dec(x_1326);
x_1470 = lean_ctor_get(x_1329, 0);
lean_inc(x_1470);
x_1471 = lean_ctor_get(x_1329, 1);
lean_inc(x_1471);
if (lean_is_exclusive(x_1329)) {
 lean_ctor_release(x_1329, 0);
 lean_ctor_release(x_1329, 1);
 x_1472 = x_1329;
} else {
 lean_dec_ref(x_1329);
 x_1472 = lean_box(0);
}
if (lean_is_scalar(x_1472)) {
 x_1473 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1473 = x_1472;
}
lean_ctor_set(x_1473, 0, x_1470);
lean_ctor_set(x_1473, 1, x_1471);
return x_1473;
}
}
else
{
lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; 
lean_dec(x_1);
x_1474 = lean_ctor_get(x_1322, 0);
lean_inc(x_1474);
x_1475 = lean_ctor_get(x_1322, 1);
lean_inc(x_1475);
if (lean_is_exclusive(x_1322)) {
 lean_ctor_release(x_1322, 0);
 lean_ctor_release(x_1322, 1);
 x_1476 = x_1322;
} else {
 lean_dec_ref(x_1322);
 x_1476 = lean_box(0);
}
if (lean_is_scalar(x_1476)) {
 x_1477 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1477 = x_1476;
}
lean_ctor_set(x_1477, 0, x_1474);
lean_ctor_set(x_1477, 1, x_1475);
return x_1477;
}
}
}
else
{
uint8_t x_1478; 
lean_dec(x_1);
x_1478 = !lean_is_exclusive(x_6);
if (x_1478 == 0)
{
return x_6;
}
else
{
lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; 
x_1479 = lean_ctor_get(x_6, 0);
x_1480 = lean_ctor_get(x_6, 1);
lean_inc(x_1480);
lean_inc(x_1479);
lean_dec(x_6);
x_1481 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1481, 0, x_1479);
lean_ctor_set(x_1481, 1, x_1480);
return x_1481;
}
}
}
}
lean_object* l___private_init_lean_compiler_ir_default_1__compileAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_init_lean_compiler_ir_default_1__compileAux(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* lean_ir_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_init_lean_compiler_ir_default_1__compileAux(x_3, x_2, x_7);
lean_dec(x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = lean_array_fget(x_1, x_2);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = l_Lean_IR_declMapExt;
x_22 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_21, x_20, x_16);
lean_ctor_set(x_14, 0, x_22);
x_23 = lean_box(0);
lean_ctor_set(x_4, 0, x_23);
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = l_Lean_IR_declMapExt;
x_28 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_27, x_25, x_16);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_box(0);
lean_ctor_set(x_4, 1, x_29);
lean_ctor_set(x_4, 0, x_30);
x_2 = x_18;
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_dec(x_4);
x_33 = lean_array_fget(x_1, x_2);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_2, x_34);
lean_dec(x_2);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_38 = x_32;
} else {
 lean_dec_ref(x_32);
 x_38 = lean_box(0);
}
x_39 = l_Lean_IR_declMapExt;
x_40 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_39, x_36, x_33);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_2 = x_35;
x_4 = x_43;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_addBoxedVersionAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_getEnv___rarg(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_box(0);
lean_inc(x_7);
lean_ctor_set(x_4, 0, x_8);
x_9 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_6, x_1);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_11 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_mk_array(x_12, x_11);
x_14 = l_Lean_IR_explicitRC(x_13, x_2, x_4);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_14, 0, x_8);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(x_16, x_17, x_2, x_14);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_8);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(x_27, x_30, x_2, x_29);
lean_dec(x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_8);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_37 = x_31;
} else {
 lean_dec_ref(x_31);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
return x_14;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_14, 0);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_4, 0);
x_44 = lean_ctor_get(x_4, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_4);
x_45 = lean_box(0);
lean_inc(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_43, x_1);
lean_dec(x_43);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_44);
x_49 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_mk_array(x_50, x_49);
x_52 = l_Lean_IR_explicitRC(x_51, x_2, x_46);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(x_53, x_57, x_2, x_56);
lean_dec(x_53);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_45);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_64 = x_58;
} else {
 lean_dec_ref(x_58);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_52, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_52, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_68 = x_52;
} else {
 lean_dec_ref(x_52);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_4);
if (x_70 == 0)
{
return x_4;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_4, 0);
x_72 = lean_ctor_get(x_4, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_4);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
lean_object* l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_addBoxedVersionAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_addBoxedVersionAux(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* lean_ir_add_boxed_version(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Lean_Options_empty;
x_8 = l_Lean_IR_addBoxedVersionAux(x_2, x_7, x_6);
lean_dec(x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
lean_object* initialize_init_lean_compiler_ir_basic(lean_object*);
lean_object* initialize_init_lean_compiler_ir_format(lean_object*);
lean_object* initialize_init_lean_compiler_ir_compilerm(lean_object*);
lean_object* initialize_init_lean_compiler_ir_pushproj(lean_object*);
lean_object* initialize_init_lean_compiler_ir_elimdead(lean_object*);
lean_object* initialize_init_lean_compiler_ir_simpcase(lean_object*);
lean_object* initialize_init_lean_compiler_ir_resetreuse(lean_object*);
lean_object* initialize_init_lean_compiler_ir_normids(lean_object*);
lean_object* initialize_init_lean_compiler_ir_checker(lean_object*);
lean_object* initialize_init_lean_compiler_ir_borrow(lean_object*);
lean_object* initialize_init_lean_compiler_ir_boxing(lean_object*);
lean_object* initialize_init_lean_compiler_ir_rc(lean_object*);
lean_object* initialize_init_lean_compiler_ir_expandresetreuse(lean_object*);
lean_object* initialize_init_lean_compiler_ir_unboxresult(lean_object*);
lean_object* initialize_init_lean_compiler_ir_emitc(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_compiler_ir_default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_format(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_pushproj(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_elimdead(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_simpcase(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_resetreuse(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_normids(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_checker(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_borrow(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_boxing(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_rc(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_expandresetreuse(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_unboxresult(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_emitc(w);
if (lean_io_result_is_error(w)) return w;
l___private_init_lean_compiler_ir_default_1__compileAux___closed__1 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__1();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__1);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__2 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__2();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__2);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__3 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__3();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__3);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__4 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__4();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__4);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__5 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__5();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__5);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__6 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__6();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__6);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__7 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__7();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__7);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__8 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__8();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__8);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__9 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__9();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__9);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__10 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__10();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__10);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__11 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__11();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__11);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__12 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__12();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__12);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__13 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__13();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__13);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__14 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__14();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__14);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__15 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__15();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__15);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__16 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__16();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__16);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__17 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__17();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__17);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__18 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__18();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__18);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__19 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__19();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__19);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__20 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__20();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__20);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__21 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__21();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__21);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__22 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__22();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__22);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__23 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__23();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__23);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__24 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__24();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__24);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__25 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__25();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__25);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__26 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__26();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__26);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__27 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__27();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__27);
l___private_init_lean_compiler_ir_default_1__compileAux___closed__28 = _init_l___private_init_lean_compiler_ir_default_1__compileAux___closed__28();
lean_mark_persistent(l___private_init_lean_compiler_ir_default_1__compileAux___closed__28);
return w;
}
#ifdef __cplusplus
}
#endif
