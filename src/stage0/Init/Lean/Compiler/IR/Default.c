// Lean compiler output
// Module: Init.Lean.Compiler.IR.Default
// Imports: Init.Lean.Compiler.IR.Basic Init.Lean.Compiler.IR.Format Init.Lean.Compiler.IR.CompilerM Init.Lean.Compiler.IR.PushProj Init.Lean.Compiler.IR.ElimDead Init.Lean.Compiler.IR.SimpCase Init.Lean.Compiler.IR.ResetReuse Init.Lean.Compiler.IR.NormIds Init.Lean.Compiler.IR.Checker Init.Lean.Compiler.IR.Borrow Init.Lean.Compiler.IR.Boxing Init.Lean.Compiler.IR.RC Init.Lean.Compiler.IR.ExpandResetReuse Init.Lean.Compiler.IR.UnboxResult Init.Lean.Compiler.IR.UnreachBranches Init.Lean.Compiler.IR.EmitC
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
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__23;
lean_object* l_Lean_IR_addBoxedVersionAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_object* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_pushProj(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__14;
lean_object* l_Array_mkArray(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__20;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3;
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
extern lean_object* l_Lean_Options_empty;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__26;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__17;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__5;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
extern lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__4;
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_IR_inferBorrow(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
lean_object* l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_declMapExt;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
lean_object* l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_simpCase(lean_object*);
lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_main(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__8;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__2;
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_object* l_Array_size(lean_object*, lean_object*);
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object*);
lean_object* lean_ir_compile(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7;
lean_object* lean_ir_add_boxed_version(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__11;
lean_object* l_Array_set(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkInitAttr___closed__2;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_explicitRC(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_inferCtorSummaries(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_addBoxedVersionAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_IR_explicitBoxing(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l_Lean_mkInitAttr___closed__2;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("push_proj");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reset_reuse");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elim_dead");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simp_case");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("borrow");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("boxing");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rc");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__20;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expand_reset_reuse");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__23;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__1;
x_5 = l_Lean_mkInitAttr___closed__2;
lean_inc(x_1);
x_6 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_4, x_5, x_1, x_2, x_3);
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
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_9);
lean_inc(x_1);
x_14 = l_Lean_IR_inferCtorSummaries(x_1, x_2, x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_9);
x_17 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_1);
x_18 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__4;
x_19 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3;
lean_inc(x_17);
x_20 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_18, x_19, x_17, x_2, x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_9);
x_23 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__2(x_10, x_17);
x_24 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7;
x_25 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6;
lean_inc(x_23);
x_26 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_24, x_25, x_23, x_2, x_20);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_9);
x_29 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(x_10, x_23);
x_30 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10;
x_31 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
lean_inc(x_29);
x_32 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_30, x_31, x_29, x_2, x_26);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_9);
x_35 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_10, x_29);
x_36 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
x_37 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_inc(x_35);
x_38 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_36, x_37, x_35, x_2, x_32);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_9);
x_41 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_35);
x_42 = l_Lean_IR_inferBorrow(x_41, x_2, x_38);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_42, 0);
lean_ctor_set(x_42, 0, x_9);
x_45 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_46 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_44);
x_47 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_45, x_46, x_44, x_2, x_42);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_9);
x_50 = l_Lean_IR_explicitBoxing(x_44, x_2, x_47);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_50, 0);
lean_ctor_set(x_50, 0, x_9);
x_53 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_54 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_52);
x_55 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_53, x_54, x_52, x_2, x_50);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_9);
x_58 = l_Lean_IR_explicitRC(x_52, x_2, x_55);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_58, 0);
lean_ctor_set(x_58, 0, x_9);
x_61 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_62 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_60);
x_63 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_61, x_62, x_60, x_2, x_58);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
lean_ctor_set(x_63, 0, x_9);
x_66 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_60);
x_67 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_68 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_66);
x_69 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_67, x_68, x_66, x_2, x_63);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
lean_ctor_set(x_69, 0, x_9);
x_72 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_66);
lean_inc(x_72);
x_73 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_18, x_19, x_72, x_2, x_69);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
lean_ctor_set(x_73, 0, x_9);
x_76 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_77 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_72);
x_78 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_76, x_77, x_72, x_2, x_73);
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
lean_inc(x_72);
x_81 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_72, x_72, x_10, x_2, x_78);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
lean_ctor_set(x_81, 0, x_9);
x_84 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_72, x_10, x_2, x_81);
lean_dec(x_72);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
lean_ctor_set(x_84, 0, x_9);
return x_84;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_9);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_84);
if (x_89 == 0)
{
return x_84;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_84, 0);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_84);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_81, 1);
lean_inc(x_93);
lean_dec(x_81);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_9);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_72, x_10, x_2, x_94);
lean_dec(x_72);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_9);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_95, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_101 = x_95;
} else {
 lean_dec_ref(x_95);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_72);
x_103 = !lean_is_exclusive(x_81);
if (x_103 == 0)
{
return x_81;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_81, 0);
x_105 = lean_ctor_get(x_81, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_81);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_78, 1);
lean_inc(x_107);
lean_dec(x_78);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_9);
lean_ctor_set(x_108, 1, x_107);
lean_inc(x_72);
x_109 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_72, x_72, x_10, x_2, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_9);
lean_ctor_set(x_112, 1, x_110);
x_113 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_72, x_10, x_2, x_112);
lean_dec(x_72);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_9);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_113, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_113, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_119 = x_113;
} else {
 lean_dec_ref(x_113);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_72);
x_121 = lean_ctor_get(x_109, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_109, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_123 = x_109;
} else {
 lean_dec_ref(x_109);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_72);
x_125 = !lean_is_exclusive(x_78);
if (x_125 == 0)
{
return x_78;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_78, 0);
x_127 = lean_ctor_get(x_78, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_78);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_73, 1);
lean_inc(x_129);
lean_dec(x_73);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_9);
lean_ctor_set(x_130, 1, x_129);
x_131 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_132 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_72);
x_133 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_131, x_132, x_72, x_2, x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_9);
lean_ctor_set(x_136, 1, x_134);
lean_inc(x_72);
x_137 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_72, x_72, x_10, x_2, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_9);
lean_ctor_set(x_140, 1, x_138);
x_141 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_72, x_10, x_2, x_140);
lean_dec(x_72);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_9);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_141, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_147 = x_141;
} else {
 lean_dec_ref(x_141);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_72);
x_149 = lean_ctor_get(x_137, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_137, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_151 = x_137;
} else {
 lean_dec_ref(x_137);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_72);
x_153 = lean_ctor_get(x_133, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_133, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_155 = x_133;
} else {
 lean_dec_ref(x_133);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_72);
x_157 = !lean_is_exclusive(x_73);
if (x_157 == 0)
{
return x_73;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_73, 0);
x_159 = lean_ctor_get(x_73, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_73);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_69, 1);
lean_inc(x_161);
lean_dec(x_69);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_9);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_66);
lean_inc(x_163);
x_164 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_18, x_19, x_163, x_2, x_162);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_166 = x_164;
} else {
 lean_dec_ref(x_164);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_9);
lean_ctor_set(x_167, 1, x_165);
x_168 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_169 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_163);
x_170 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_168, x_169, x_163, x_2, x_167);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_9);
lean_ctor_set(x_173, 1, x_171);
lean_inc(x_163);
x_174 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_163, x_163, x_10, x_2, x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_176 = x_174;
} else {
 lean_dec_ref(x_174);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_9);
lean_ctor_set(x_177, 1, x_175);
x_178 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_163, x_10, x_2, x_177);
lean_dec(x_163);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_180 = x_178;
} else {
 lean_dec_ref(x_178);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_9);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_178, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_178, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_184 = x_178;
} else {
 lean_dec_ref(x_178);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_163);
x_186 = lean_ctor_get(x_174, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_174, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_188 = x_174;
} else {
 lean_dec_ref(x_174);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_163);
x_190 = lean_ctor_get(x_170, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_170, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_192 = x_170;
} else {
 lean_dec_ref(x_170);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_163);
x_194 = lean_ctor_get(x_164, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_164, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_196 = x_164;
} else {
 lean_dec_ref(x_164);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_66);
x_198 = !lean_is_exclusive(x_69);
if (x_198 == 0)
{
return x_69;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_69, 0);
x_200 = lean_ctor_get(x_69, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_69);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_202 = lean_ctor_get(x_63, 1);
lean_inc(x_202);
lean_dec(x_63);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_9);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_60);
x_205 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_206 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_204);
x_207 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_205, x_206, x_204, x_2, x_203);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_209 = x_207;
} else {
 lean_dec_ref(x_207);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_9);
lean_ctor_set(x_210, 1, x_208);
x_211 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_204);
lean_inc(x_211);
x_212 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_18, x_19, x_211, x_2, x_210);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_9);
lean_ctor_set(x_215, 1, x_213);
x_216 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_217 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_211);
x_218 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_216, x_217, x_211, x_2, x_215);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_220 = x_218;
} else {
 lean_dec_ref(x_218);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_9);
lean_ctor_set(x_221, 1, x_219);
lean_inc(x_211);
x_222 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_211, x_211, x_10, x_2, x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_224 = x_222;
} else {
 lean_dec_ref(x_222);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_9);
lean_ctor_set(x_225, 1, x_223);
x_226 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_211, x_10, x_2, x_225);
lean_dec(x_211);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_228 = x_226;
} else {
 lean_dec_ref(x_226);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_9);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_226, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_226, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_232 = x_226;
} else {
 lean_dec_ref(x_226);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_211);
x_234 = lean_ctor_get(x_222, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_222, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_236 = x_222;
} else {
 lean_dec_ref(x_222);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_211);
x_238 = lean_ctor_get(x_218, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_218, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_240 = x_218;
} else {
 lean_dec_ref(x_218);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_211);
x_242 = lean_ctor_get(x_212, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_212, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_244 = x_212;
} else {
 lean_dec_ref(x_212);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_204);
x_246 = lean_ctor_get(x_207, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_207, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_248 = x_207;
} else {
 lean_dec_ref(x_207);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_60);
x_250 = !lean_is_exclusive(x_63);
if (x_250 == 0)
{
return x_63;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_63, 0);
x_252 = lean_ctor_get(x_63, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_63);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_254 = lean_ctor_get(x_58, 0);
x_255 = lean_ctor_get(x_58, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_58);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_9);
lean_ctor_set(x_256, 1, x_255);
x_257 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_258 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_254);
x_259 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_257, x_258, x_254, x_2, x_256);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_261 = x_259;
} else {
 lean_dec_ref(x_259);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_9);
lean_ctor_set(x_262, 1, x_260);
x_263 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_254);
x_264 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_265 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_263);
x_266 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_264, x_265, x_263, x_2, x_262);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_268 = x_266;
} else {
 lean_dec_ref(x_266);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_9);
lean_ctor_set(x_269, 1, x_267);
x_270 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_263);
lean_inc(x_270);
x_271 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_18, x_19, x_270, x_2, x_269);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_9);
lean_ctor_set(x_274, 1, x_272);
x_275 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_276 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_270);
x_277 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_275, x_276, x_270, x_2, x_274);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_279 = x_277;
} else {
 lean_dec_ref(x_277);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_9);
lean_ctor_set(x_280, 1, x_278);
lean_inc(x_270);
x_281 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_270, x_270, x_10, x_2, x_280);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_283 = x_281;
} else {
 lean_dec_ref(x_281);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_9);
lean_ctor_set(x_284, 1, x_282);
x_285 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_270, x_10, x_2, x_284);
lean_dec(x_270);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_287 = x_285;
} else {
 lean_dec_ref(x_285);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_9);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_285, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_285, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_291 = x_285;
} else {
 lean_dec_ref(x_285);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_290);
return x_292;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_270);
x_293 = lean_ctor_get(x_281, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_281, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_295 = x_281;
} else {
 lean_dec_ref(x_281);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_294);
return x_296;
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_270);
x_297 = lean_ctor_get(x_277, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_277, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_299 = x_277;
} else {
 lean_dec_ref(x_277);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_270);
x_301 = lean_ctor_get(x_271, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_271, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_303 = x_271;
} else {
 lean_dec_ref(x_271);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_302);
return x_304;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_263);
x_305 = lean_ctor_get(x_266, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_266, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_307 = x_266;
} else {
 lean_dec_ref(x_266);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_305);
lean_ctor_set(x_308, 1, x_306);
return x_308;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_254);
x_309 = lean_ctor_get(x_259, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_259, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_311 = x_259;
} else {
 lean_dec_ref(x_259);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
}
else
{
uint8_t x_313; 
x_313 = !lean_is_exclusive(x_58);
if (x_313 == 0)
{
return x_58;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_58, 0);
x_315 = lean_ctor_get(x_58, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_58);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_55, 1);
lean_inc(x_317);
lean_dec(x_55);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_9);
lean_ctor_set(x_318, 1, x_317);
x_319 = l_Lean_IR_explicitRC(x_52, x_2, x_318);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_322 = x_319;
} else {
 lean_dec_ref(x_319);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_9);
lean_ctor_set(x_323, 1, x_321);
x_324 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_325 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_320);
x_326 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_324, x_325, x_320, x_2, x_323);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_327 = lean_ctor_get(x_326, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_328 = x_326;
} else {
 lean_dec_ref(x_326);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_9);
lean_ctor_set(x_329, 1, x_327);
x_330 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_320);
x_331 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_332 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_330);
x_333 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_331, x_332, x_330, x_2, x_329);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_335 = x_333;
} else {
 lean_dec_ref(x_333);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_9);
lean_ctor_set(x_336, 1, x_334);
x_337 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_330);
lean_inc(x_337);
x_338 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_18, x_19, x_337, x_2, x_336);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_339 = lean_ctor_get(x_338, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_340 = x_338;
} else {
 lean_dec_ref(x_338);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_9);
lean_ctor_set(x_341, 1, x_339);
x_342 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_343 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_337);
x_344 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_342, x_343, x_337, x_2, x_341);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_346 = x_344;
} else {
 lean_dec_ref(x_344);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_9);
lean_ctor_set(x_347, 1, x_345);
lean_inc(x_337);
x_348 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_337, x_337, x_10, x_2, x_347);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_350 = x_348;
} else {
 lean_dec_ref(x_348);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_9);
lean_ctor_set(x_351, 1, x_349);
x_352 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_337, x_10, x_2, x_351);
lean_dec(x_337);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_354 = x_352;
} else {
 lean_dec_ref(x_352);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_9);
lean_ctor_set(x_355, 1, x_353);
return x_355;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_356 = lean_ctor_get(x_352, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_352, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_358 = x_352;
} else {
 lean_dec_ref(x_352);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_356);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_337);
x_360 = lean_ctor_get(x_348, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_348, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_362 = x_348;
} else {
 lean_dec_ref(x_348);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_337);
x_364 = lean_ctor_get(x_344, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_344, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_366 = x_344;
} else {
 lean_dec_ref(x_344);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(1, 2, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_364);
lean_ctor_set(x_367, 1, x_365);
return x_367;
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec(x_337);
x_368 = lean_ctor_get(x_338, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_338, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_370 = x_338;
} else {
 lean_dec_ref(x_338);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_369);
return x_371;
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_330);
x_372 = lean_ctor_get(x_333, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_333, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_374 = x_333;
} else {
 lean_dec_ref(x_333);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_320);
x_376 = lean_ctor_get(x_326, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_326, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_378 = x_326;
} else {
 lean_dec_ref(x_326);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_376);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_380 = lean_ctor_get(x_319, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_319, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_382 = x_319;
} else {
 lean_dec_ref(x_319);
 x_382 = lean_box(0);
}
if (lean_is_scalar(x_382)) {
 x_383 = lean_alloc_ctor(1, 2, 0);
} else {
 x_383 = x_382;
}
lean_ctor_set(x_383, 0, x_380);
lean_ctor_set(x_383, 1, x_381);
return x_383;
}
}
}
else
{
uint8_t x_384; 
lean_dec(x_52);
x_384 = !lean_is_exclusive(x_55);
if (x_384 == 0)
{
return x_55;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_55, 0);
x_386 = lean_ctor_get(x_55, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_55);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
return x_387;
}
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_388 = lean_ctor_get(x_50, 0);
x_389 = lean_ctor_get(x_50, 1);
lean_inc(x_389);
lean_inc(x_388);
lean_dec(x_50);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_9);
lean_ctor_set(x_390, 1, x_389);
x_391 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_392 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_388);
x_393 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_391, x_392, x_388, x_2, x_390);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_395 = x_393;
} else {
 lean_dec_ref(x_393);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(0, 2, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_9);
lean_ctor_set(x_396, 1, x_394);
x_397 = l_Lean_IR_explicitRC(x_388, x_2, x_396);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_400 = x_397;
} else {
 lean_dec_ref(x_397);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_9);
lean_ctor_set(x_401, 1, x_399);
x_402 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_403 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_398);
x_404 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_402, x_403, x_398, x_2, x_401);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_405 = lean_ctor_get(x_404, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_406 = x_404;
} else {
 lean_dec_ref(x_404);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_9);
lean_ctor_set(x_407, 1, x_405);
x_408 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_398);
x_409 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_410 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_408);
x_411 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_409, x_410, x_408, x_2, x_407);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_412 = lean_ctor_get(x_411, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_413 = x_411;
} else {
 lean_dec_ref(x_411);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(0, 2, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_9);
lean_ctor_set(x_414, 1, x_412);
x_415 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_408);
lean_inc(x_415);
x_416 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_18, x_19, x_415, x_2, x_414);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_417 = lean_ctor_get(x_416, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_418 = x_416;
} else {
 lean_dec_ref(x_416);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_9);
lean_ctor_set(x_419, 1, x_417);
x_420 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_421 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_415);
x_422 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_420, x_421, x_415, x_2, x_419);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_423 = lean_ctor_get(x_422, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_424 = x_422;
} else {
 lean_dec_ref(x_422);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(0, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_9);
lean_ctor_set(x_425, 1, x_423);
lean_inc(x_415);
x_426 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_415, x_415, x_10, x_2, x_425);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_427 = lean_ctor_get(x_426, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_428 = x_426;
} else {
 lean_dec_ref(x_426);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(0, 2, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_9);
lean_ctor_set(x_429, 1, x_427);
x_430 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_415, x_10, x_2, x_429);
lean_dec(x_415);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_430, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_432 = x_430;
} else {
 lean_dec_ref(x_430);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(0, 2, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_9);
lean_ctor_set(x_433, 1, x_431);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = lean_ctor_get(x_430, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_430, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_436 = x_430;
} else {
 lean_dec_ref(x_430);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_434);
lean_ctor_set(x_437, 1, x_435);
return x_437;
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_415);
x_438 = lean_ctor_get(x_426, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_426, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_440 = x_426;
} else {
 lean_dec_ref(x_426);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_439);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_415);
x_442 = lean_ctor_get(x_422, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_422, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_444 = x_422;
} else {
 lean_dec_ref(x_422);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_415);
x_446 = lean_ctor_get(x_416, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_416, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_448 = x_416;
} else {
 lean_dec_ref(x_416);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_408);
x_450 = lean_ctor_get(x_411, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_411, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_452 = x_411;
} else {
 lean_dec_ref(x_411);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 2, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_450);
lean_ctor_set(x_453, 1, x_451);
return x_453;
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_398);
x_454 = lean_ctor_get(x_404, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_404, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_456 = x_404;
} else {
 lean_dec_ref(x_404);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(1, 2, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_454);
lean_ctor_set(x_457, 1, x_455);
return x_457;
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_458 = lean_ctor_get(x_397, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_397, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_460 = x_397;
} else {
 lean_dec_ref(x_397);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(1, 2, 0);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_458);
lean_ctor_set(x_461, 1, x_459);
return x_461;
}
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_388);
x_462 = lean_ctor_get(x_393, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_393, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_464 = x_393;
} else {
 lean_dec_ref(x_393);
 x_464 = lean_box(0);
}
if (lean_is_scalar(x_464)) {
 x_465 = lean_alloc_ctor(1, 2, 0);
} else {
 x_465 = x_464;
}
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_463);
return x_465;
}
}
}
else
{
uint8_t x_466; 
x_466 = !lean_is_exclusive(x_50);
if (x_466 == 0)
{
return x_50;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_50, 0);
x_468 = lean_ctor_get(x_50, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_50);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
return x_469;
}
}
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_47, 1);
lean_inc(x_470);
lean_dec(x_47);
x_471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_471, 0, x_9);
lean_ctor_set(x_471, 1, x_470);
x_472 = l_Lean_IR_explicitBoxing(x_44, x_2, x_471);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_475 = x_472;
} else {
 lean_dec_ref(x_472);
 x_475 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(0, 2, 0);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_9);
lean_ctor_set(x_476, 1, x_474);
x_477 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_478 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_473);
x_479 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_477, x_478, x_473, x_2, x_476);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_480 = lean_ctor_get(x_479, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 x_481 = x_479;
} else {
 lean_dec_ref(x_479);
 x_481 = lean_box(0);
}
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(0, 2, 0);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_9);
lean_ctor_set(x_482, 1, x_480);
x_483 = l_Lean_IR_explicitRC(x_473, x_2, x_482);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_483, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_486 = x_483;
} else {
 lean_dec_ref(x_483);
 x_486 = lean_box(0);
}
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(0, 2, 0);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_9);
lean_ctor_set(x_487, 1, x_485);
x_488 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_489 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_484);
x_490 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_488, x_489, x_484, x_2, x_487);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_491 = lean_ctor_get(x_490, 1);
lean_inc(x_491);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_492 = x_490;
} else {
 lean_dec_ref(x_490);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(0, 2, 0);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_9);
lean_ctor_set(x_493, 1, x_491);
x_494 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_484);
x_495 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_496 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_494);
x_497 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_495, x_496, x_494, x_2, x_493);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_498 = lean_ctor_get(x_497, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_499 = x_497;
} else {
 lean_dec_ref(x_497);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_9);
lean_ctor_set(x_500, 1, x_498);
x_501 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_494);
lean_inc(x_501);
x_502 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_18, x_19, x_501, x_2, x_500);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_503 = lean_ctor_get(x_502, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_504 = x_502;
} else {
 lean_dec_ref(x_502);
 x_504 = lean_box(0);
}
if (lean_is_scalar(x_504)) {
 x_505 = lean_alloc_ctor(0, 2, 0);
} else {
 x_505 = x_504;
}
lean_ctor_set(x_505, 0, x_9);
lean_ctor_set(x_505, 1, x_503);
x_506 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_507 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_501);
x_508 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_506, x_507, x_501, x_2, x_505);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_510 = x_508;
} else {
 lean_dec_ref(x_508);
 x_510 = lean_box(0);
}
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_9);
lean_ctor_set(x_511, 1, x_509);
lean_inc(x_501);
x_512 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_501, x_501, x_10, x_2, x_511);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_513 = lean_ctor_get(x_512, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 lean_ctor_release(x_512, 1);
 x_514 = x_512;
} else {
 lean_dec_ref(x_512);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_9);
lean_ctor_set(x_515, 1, x_513);
x_516 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_501, x_10, x_2, x_515);
lean_dec(x_501);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_516, 1);
lean_inc(x_517);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_518 = x_516;
} else {
 lean_dec_ref(x_516);
 x_518 = lean_box(0);
}
if (lean_is_scalar(x_518)) {
 x_519 = lean_alloc_ctor(0, 2, 0);
} else {
 x_519 = x_518;
}
lean_ctor_set(x_519, 0, x_9);
lean_ctor_set(x_519, 1, x_517);
return x_519;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_520 = lean_ctor_get(x_516, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_516, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 lean_ctor_release(x_516, 1);
 x_522 = x_516;
} else {
 lean_dec_ref(x_516);
 x_522 = lean_box(0);
}
if (lean_is_scalar(x_522)) {
 x_523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_523 = x_522;
}
lean_ctor_set(x_523, 0, x_520);
lean_ctor_set(x_523, 1, x_521);
return x_523;
}
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_501);
x_524 = lean_ctor_get(x_512, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_512, 1);
lean_inc(x_525);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 lean_ctor_release(x_512, 1);
 x_526 = x_512;
} else {
 lean_dec_ref(x_512);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_527 = lean_alloc_ctor(1, 2, 0);
} else {
 x_527 = x_526;
}
lean_ctor_set(x_527, 0, x_524);
lean_ctor_set(x_527, 1, x_525);
return x_527;
}
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_501);
x_528 = lean_ctor_get(x_508, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_508, 1);
lean_inc(x_529);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_530 = x_508;
} else {
 lean_dec_ref(x_508);
 x_530 = lean_box(0);
}
if (lean_is_scalar(x_530)) {
 x_531 = lean_alloc_ctor(1, 2, 0);
} else {
 x_531 = x_530;
}
lean_ctor_set(x_531, 0, x_528);
lean_ctor_set(x_531, 1, x_529);
return x_531;
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_501);
x_532 = lean_ctor_get(x_502, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_502, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_534 = x_502;
} else {
 lean_dec_ref(x_502);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(1, 2, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_532);
lean_ctor_set(x_535, 1, x_533);
return x_535;
}
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_494);
x_536 = lean_ctor_get(x_497, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_497, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_538 = x_497;
} else {
 lean_dec_ref(x_497);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(1, 2, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_536);
lean_ctor_set(x_539, 1, x_537);
return x_539;
}
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_484);
x_540 = lean_ctor_get(x_490, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_490, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_542 = x_490;
} else {
 lean_dec_ref(x_490);
 x_542 = lean_box(0);
}
if (lean_is_scalar(x_542)) {
 x_543 = lean_alloc_ctor(1, 2, 0);
} else {
 x_543 = x_542;
}
lean_ctor_set(x_543, 0, x_540);
lean_ctor_set(x_543, 1, x_541);
return x_543;
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_544 = lean_ctor_get(x_483, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_483, 1);
lean_inc(x_545);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_546 = x_483;
} else {
 lean_dec_ref(x_483);
 x_546 = lean_box(0);
}
if (lean_is_scalar(x_546)) {
 x_547 = lean_alloc_ctor(1, 2, 0);
} else {
 x_547 = x_546;
}
lean_ctor_set(x_547, 0, x_544);
lean_ctor_set(x_547, 1, x_545);
return x_547;
}
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
lean_dec(x_473);
x_548 = lean_ctor_get(x_479, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_479, 1);
lean_inc(x_549);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 x_550 = x_479;
} else {
 lean_dec_ref(x_479);
 x_550 = lean_box(0);
}
if (lean_is_scalar(x_550)) {
 x_551 = lean_alloc_ctor(1, 2, 0);
} else {
 x_551 = x_550;
}
lean_ctor_set(x_551, 0, x_548);
lean_ctor_set(x_551, 1, x_549);
return x_551;
}
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_552 = lean_ctor_get(x_472, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_472, 1);
lean_inc(x_553);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_554 = x_472;
} else {
 lean_dec_ref(x_472);
 x_554 = lean_box(0);
}
if (lean_is_scalar(x_554)) {
 x_555 = lean_alloc_ctor(1, 2, 0);
} else {
 x_555 = x_554;
}
lean_ctor_set(x_555, 0, x_552);
lean_ctor_set(x_555, 1, x_553);
return x_555;
}
}
}
else
{
uint8_t x_556; 
lean_dec(x_44);
x_556 = !lean_is_exclusive(x_47);
if (x_556 == 0)
{
return x_47;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_557 = lean_ctor_get(x_47, 0);
x_558 = lean_ctor_get(x_47, 1);
lean_inc(x_558);
lean_inc(x_557);
lean_dec(x_47);
x_559 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_559, 0, x_557);
lean_ctor_set(x_559, 1, x_558);
return x_559;
}
}
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_560 = lean_ctor_get(x_42, 0);
x_561 = lean_ctor_get(x_42, 1);
lean_inc(x_561);
lean_inc(x_560);
lean_dec(x_42);
x_562 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_562, 0, x_9);
lean_ctor_set(x_562, 1, x_561);
x_563 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_564 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_560);
x_565 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_563, x_564, x_560, x_2, x_562);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_566 = lean_ctor_get(x_565, 1);
lean_inc(x_566);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_567 = x_565;
} else {
 lean_dec_ref(x_565);
 x_567 = lean_box(0);
}
if (lean_is_scalar(x_567)) {
 x_568 = lean_alloc_ctor(0, 2, 0);
} else {
 x_568 = x_567;
}
lean_ctor_set(x_568, 0, x_9);
lean_ctor_set(x_568, 1, x_566);
x_569 = l_Lean_IR_explicitBoxing(x_560, x_2, x_568);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_572 = x_569;
} else {
 lean_dec_ref(x_569);
 x_572 = lean_box(0);
}
if (lean_is_scalar(x_572)) {
 x_573 = lean_alloc_ctor(0, 2, 0);
} else {
 x_573 = x_572;
}
lean_ctor_set(x_573, 0, x_9);
lean_ctor_set(x_573, 1, x_571);
x_574 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_575 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_570);
x_576 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_574, x_575, x_570, x_2, x_573);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_577 = lean_ctor_get(x_576, 1);
lean_inc(x_577);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_578 = x_576;
} else {
 lean_dec_ref(x_576);
 x_578 = lean_box(0);
}
if (lean_is_scalar(x_578)) {
 x_579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_579 = x_578;
}
lean_ctor_set(x_579, 0, x_9);
lean_ctor_set(x_579, 1, x_577);
x_580 = l_Lean_IR_explicitRC(x_570, x_2, x_579);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_583 = x_580;
} else {
 lean_dec_ref(x_580);
 x_583 = lean_box(0);
}
if (lean_is_scalar(x_583)) {
 x_584 = lean_alloc_ctor(0, 2, 0);
} else {
 x_584 = x_583;
}
lean_ctor_set(x_584, 0, x_9);
lean_ctor_set(x_584, 1, x_582);
x_585 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_586 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_581);
x_587 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_585, x_586, x_581, x_2, x_584);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_588 = lean_ctor_get(x_587, 1);
lean_inc(x_588);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_589 = x_587;
} else {
 lean_dec_ref(x_587);
 x_589 = lean_box(0);
}
if (lean_is_scalar(x_589)) {
 x_590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_590 = x_589;
}
lean_ctor_set(x_590, 0, x_9);
lean_ctor_set(x_590, 1, x_588);
x_591 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_581);
x_592 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_593 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_591);
x_594 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_592, x_593, x_591, x_2, x_590);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_595 = lean_ctor_get(x_594, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_596 = x_594;
} else {
 lean_dec_ref(x_594);
 x_596 = lean_box(0);
}
if (lean_is_scalar(x_596)) {
 x_597 = lean_alloc_ctor(0, 2, 0);
} else {
 x_597 = x_596;
}
lean_ctor_set(x_597, 0, x_9);
lean_ctor_set(x_597, 1, x_595);
x_598 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_591);
lean_inc(x_598);
x_599 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_18, x_19, x_598, x_2, x_597);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_600 = lean_ctor_get(x_599, 1);
lean_inc(x_600);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 lean_ctor_release(x_599, 1);
 x_601 = x_599;
} else {
 lean_dec_ref(x_599);
 x_601 = lean_box(0);
}
if (lean_is_scalar(x_601)) {
 x_602 = lean_alloc_ctor(0, 2, 0);
} else {
 x_602 = x_601;
}
lean_ctor_set(x_602, 0, x_9);
lean_ctor_set(x_602, 1, x_600);
x_603 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_604 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_598);
x_605 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_603, x_604, x_598, x_2, x_602);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_606 = lean_ctor_get(x_605, 1);
lean_inc(x_606);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 lean_ctor_release(x_605, 1);
 x_607 = x_605;
} else {
 lean_dec_ref(x_605);
 x_607 = lean_box(0);
}
if (lean_is_scalar(x_607)) {
 x_608 = lean_alloc_ctor(0, 2, 0);
} else {
 x_608 = x_607;
}
lean_ctor_set(x_608, 0, x_9);
lean_ctor_set(x_608, 1, x_606);
lean_inc(x_598);
x_609 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_598, x_598, x_10, x_2, x_608);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_610 = lean_ctor_get(x_609, 1);
lean_inc(x_610);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_611 = x_609;
} else {
 lean_dec_ref(x_609);
 x_611 = lean_box(0);
}
if (lean_is_scalar(x_611)) {
 x_612 = lean_alloc_ctor(0, 2, 0);
} else {
 x_612 = x_611;
}
lean_ctor_set(x_612, 0, x_9);
lean_ctor_set(x_612, 1, x_610);
x_613 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_598, x_10, x_2, x_612);
lean_dec(x_598);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_613, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_615 = x_613;
} else {
 lean_dec_ref(x_613);
 x_615 = lean_box(0);
}
if (lean_is_scalar(x_615)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_615;
}
lean_ctor_set(x_616, 0, x_9);
lean_ctor_set(x_616, 1, x_614);
return x_616;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_617 = lean_ctor_get(x_613, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_613, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_619 = x_613;
} else {
 lean_dec_ref(x_613);
 x_619 = lean_box(0);
}
if (lean_is_scalar(x_619)) {
 x_620 = lean_alloc_ctor(1, 2, 0);
} else {
 x_620 = x_619;
}
lean_ctor_set(x_620, 0, x_617);
lean_ctor_set(x_620, 1, x_618);
return x_620;
}
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_598);
x_621 = lean_ctor_get(x_609, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_609, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_623 = x_609;
} else {
 lean_dec_ref(x_609);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(1, 2, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_621);
lean_ctor_set(x_624, 1, x_622);
return x_624;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_598);
x_625 = lean_ctor_get(x_605, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_605, 1);
lean_inc(x_626);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 lean_ctor_release(x_605, 1);
 x_627 = x_605;
} else {
 lean_dec_ref(x_605);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(1, 2, 0);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_625);
lean_ctor_set(x_628, 1, x_626);
return x_628;
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_598);
x_629 = lean_ctor_get(x_599, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_599, 1);
lean_inc(x_630);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 lean_ctor_release(x_599, 1);
 x_631 = x_599;
} else {
 lean_dec_ref(x_599);
 x_631 = lean_box(0);
}
if (lean_is_scalar(x_631)) {
 x_632 = lean_alloc_ctor(1, 2, 0);
} else {
 x_632 = x_631;
}
lean_ctor_set(x_632, 0, x_629);
lean_ctor_set(x_632, 1, x_630);
return x_632;
}
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_dec(x_591);
x_633 = lean_ctor_get(x_594, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_594, 1);
lean_inc(x_634);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_635 = x_594;
} else {
 lean_dec_ref(x_594);
 x_635 = lean_box(0);
}
if (lean_is_scalar(x_635)) {
 x_636 = lean_alloc_ctor(1, 2, 0);
} else {
 x_636 = x_635;
}
lean_ctor_set(x_636, 0, x_633);
lean_ctor_set(x_636, 1, x_634);
return x_636;
}
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
lean_dec(x_581);
x_637 = lean_ctor_get(x_587, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_587, 1);
lean_inc(x_638);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_639 = x_587;
} else {
 lean_dec_ref(x_587);
 x_639 = lean_box(0);
}
if (lean_is_scalar(x_639)) {
 x_640 = lean_alloc_ctor(1, 2, 0);
} else {
 x_640 = x_639;
}
lean_ctor_set(x_640, 0, x_637);
lean_ctor_set(x_640, 1, x_638);
return x_640;
}
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_641 = lean_ctor_get(x_580, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_580, 1);
lean_inc(x_642);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_643 = x_580;
} else {
 lean_dec_ref(x_580);
 x_643 = lean_box(0);
}
if (lean_is_scalar(x_643)) {
 x_644 = lean_alloc_ctor(1, 2, 0);
} else {
 x_644 = x_643;
}
lean_ctor_set(x_644, 0, x_641);
lean_ctor_set(x_644, 1, x_642);
return x_644;
}
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
lean_dec(x_570);
x_645 = lean_ctor_get(x_576, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_576, 1);
lean_inc(x_646);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_647 = x_576;
} else {
 lean_dec_ref(x_576);
 x_647 = lean_box(0);
}
if (lean_is_scalar(x_647)) {
 x_648 = lean_alloc_ctor(1, 2, 0);
} else {
 x_648 = x_647;
}
lean_ctor_set(x_648, 0, x_645);
lean_ctor_set(x_648, 1, x_646);
return x_648;
}
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_649 = lean_ctor_get(x_569, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_569, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_651 = x_569;
} else {
 lean_dec_ref(x_569);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_651)) {
 x_652 = lean_alloc_ctor(1, 2, 0);
} else {
 x_652 = x_651;
}
lean_ctor_set(x_652, 0, x_649);
lean_ctor_set(x_652, 1, x_650);
return x_652;
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_560);
x_653 = lean_ctor_get(x_565, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_565, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_655 = x_565;
} else {
 lean_dec_ref(x_565);
 x_655 = lean_box(0);
}
if (lean_is_scalar(x_655)) {
 x_656 = lean_alloc_ctor(1, 2, 0);
} else {
 x_656 = x_655;
}
lean_ctor_set(x_656, 0, x_653);
lean_ctor_set(x_656, 1, x_654);
return x_656;
}
}
}
else
{
uint8_t x_657; 
x_657 = !lean_is_exclusive(x_42);
if (x_657 == 0)
{
return x_42;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_658 = lean_ctor_get(x_42, 0);
x_659 = lean_ctor_get(x_42, 1);
lean_inc(x_659);
lean_inc(x_658);
lean_dec(x_42);
x_660 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_659);
return x_660;
}
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_661 = lean_ctor_get(x_38, 1);
lean_inc(x_661);
lean_dec(x_38);
x_662 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_662, 0, x_9);
lean_ctor_set(x_662, 1, x_661);
x_663 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_35);
x_664 = l_Lean_IR_inferBorrow(x_663, x_2, x_662);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 x_667 = x_664;
} else {
 lean_dec_ref(x_664);
 x_667 = lean_box(0);
}
if (lean_is_scalar(x_667)) {
 x_668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_668 = x_667;
}
lean_ctor_set(x_668, 0, x_9);
lean_ctor_set(x_668, 1, x_666);
x_669 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_670 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_665);
x_671 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_669, x_670, x_665, x_2, x_668);
if (lean_obj_tag(x_671) == 0)
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_672 = lean_ctor_get(x_671, 1);
lean_inc(x_672);
if (lean_is_exclusive(x_671)) {
 lean_ctor_release(x_671, 0);
 lean_ctor_release(x_671, 1);
 x_673 = x_671;
} else {
 lean_dec_ref(x_671);
 x_673 = lean_box(0);
}
if (lean_is_scalar(x_673)) {
 x_674 = lean_alloc_ctor(0, 2, 0);
} else {
 x_674 = x_673;
}
lean_ctor_set(x_674, 0, x_9);
lean_ctor_set(x_674, 1, x_672);
x_675 = l_Lean_IR_explicitBoxing(x_665, x_2, x_674);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_675, 1);
lean_inc(x_677);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 x_678 = x_675;
} else {
 lean_dec_ref(x_675);
 x_678 = lean_box(0);
}
if (lean_is_scalar(x_678)) {
 x_679 = lean_alloc_ctor(0, 2, 0);
} else {
 x_679 = x_678;
}
lean_ctor_set(x_679, 0, x_9);
lean_ctor_set(x_679, 1, x_677);
x_680 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_681 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_676);
x_682 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_680, x_681, x_676, x_2, x_679);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_683 = lean_ctor_get(x_682, 1);
lean_inc(x_683);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_684 = x_682;
} else {
 lean_dec_ref(x_682);
 x_684 = lean_box(0);
}
if (lean_is_scalar(x_684)) {
 x_685 = lean_alloc_ctor(0, 2, 0);
} else {
 x_685 = x_684;
}
lean_ctor_set(x_685, 0, x_9);
lean_ctor_set(x_685, 1, x_683);
x_686 = l_Lean_IR_explicitRC(x_676, x_2, x_685);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_689 = x_686;
} else {
 lean_dec_ref(x_686);
 x_689 = lean_box(0);
}
if (lean_is_scalar(x_689)) {
 x_690 = lean_alloc_ctor(0, 2, 0);
} else {
 x_690 = x_689;
}
lean_ctor_set(x_690, 0, x_9);
lean_ctor_set(x_690, 1, x_688);
x_691 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_692 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_687);
x_693 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_691, x_692, x_687, x_2, x_690);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_694 = lean_ctor_get(x_693, 1);
lean_inc(x_694);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_695 = x_693;
} else {
 lean_dec_ref(x_693);
 x_695 = lean_box(0);
}
if (lean_is_scalar(x_695)) {
 x_696 = lean_alloc_ctor(0, 2, 0);
} else {
 x_696 = x_695;
}
lean_ctor_set(x_696, 0, x_9);
lean_ctor_set(x_696, 1, x_694);
x_697 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_687);
x_698 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_699 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_697);
x_700 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_698, x_699, x_697, x_2, x_696);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
x_701 = lean_ctor_get(x_700, 1);
lean_inc(x_701);
if (lean_is_exclusive(x_700)) {
 lean_ctor_release(x_700, 0);
 lean_ctor_release(x_700, 1);
 x_702 = x_700;
} else {
 lean_dec_ref(x_700);
 x_702 = lean_box(0);
}
if (lean_is_scalar(x_702)) {
 x_703 = lean_alloc_ctor(0, 2, 0);
} else {
 x_703 = x_702;
}
lean_ctor_set(x_703, 0, x_9);
lean_ctor_set(x_703, 1, x_701);
x_704 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_697);
lean_inc(x_704);
x_705 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_18, x_19, x_704, x_2, x_703);
if (lean_obj_tag(x_705) == 0)
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_706 = lean_ctor_get(x_705, 1);
lean_inc(x_706);
if (lean_is_exclusive(x_705)) {
 lean_ctor_release(x_705, 0);
 lean_ctor_release(x_705, 1);
 x_707 = x_705;
} else {
 lean_dec_ref(x_705);
 x_707 = lean_box(0);
}
if (lean_is_scalar(x_707)) {
 x_708 = lean_alloc_ctor(0, 2, 0);
} else {
 x_708 = x_707;
}
lean_ctor_set(x_708, 0, x_9);
lean_ctor_set(x_708, 1, x_706);
x_709 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_710 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_704);
x_711 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_709, x_710, x_704, x_2, x_708);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_712 = lean_ctor_get(x_711, 1);
lean_inc(x_712);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_713 = x_711;
} else {
 lean_dec_ref(x_711);
 x_713 = lean_box(0);
}
if (lean_is_scalar(x_713)) {
 x_714 = lean_alloc_ctor(0, 2, 0);
} else {
 x_714 = x_713;
}
lean_ctor_set(x_714, 0, x_9);
lean_ctor_set(x_714, 1, x_712);
lean_inc(x_704);
x_715 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_704, x_704, x_10, x_2, x_714);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_716 = lean_ctor_get(x_715, 1);
lean_inc(x_716);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_717 = x_715;
} else {
 lean_dec_ref(x_715);
 x_717 = lean_box(0);
}
if (lean_is_scalar(x_717)) {
 x_718 = lean_alloc_ctor(0, 2, 0);
} else {
 x_718 = x_717;
}
lean_ctor_set(x_718, 0, x_9);
lean_ctor_set(x_718, 1, x_716);
x_719 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_704, x_10, x_2, x_718);
lean_dec(x_704);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_720 = lean_ctor_get(x_719, 1);
lean_inc(x_720);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_721 = x_719;
} else {
 lean_dec_ref(x_719);
 x_721 = lean_box(0);
}
if (lean_is_scalar(x_721)) {
 x_722 = lean_alloc_ctor(0, 2, 0);
} else {
 x_722 = x_721;
}
lean_ctor_set(x_722, 0, x_9);
lean_ctor_set(x_722, 1, x_720);
return x_722;
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_723 = lean_ctor_get(x_719, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_719, 1);
lean_inc(x_724);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_725 = x_719;
} else {
 lean_dec_ref(x_719);
 x_725 = lean_box(0);
}
if (lean_is_scalar(x_725)) {
 x_726 = lean_alloc_ctor(1, 2, 0);
} else {
 x_726 = x_725;
}
lean_ctor_set(x_726, 0, x_723);
lean_ctor_set(x_726, 1, x_724);
return x_726;
}
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
lean_dec(x_704);
x_727 = lean_ctor_get(x_715, 0);
lean_inc(x_727);
x_728 = lean_ctor_get(x_715, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_729 = x_715;
} else {
 lean_dec_ref(x_715);
 x_729 = lean_box(0);
}
if (lean_is_scalar(x_729)) {
 x_730 = lean_alloc_ctor(1, 2, 0);
} else {
 x_730 = x_729;
}
lean_ctor_set(x_730, 0, x_727);
lean_ctor_set(x_730, 1, x_728);
return x_730;
}
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
lean_dec(x_704);
x_731 = lean_ctor_get(x_711, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_711, 1);
lean_inc(x_732);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_733 = x_711;
} else {
 lean_dec_ref(x_711);
 x_733 = lean_box(0);
}
if (lean_is_scalar(x_733)) {
 x_734 = lean_alloc_ctor(1, 2, 0);
} else {
 x_734 = x_733;
}
lean_ctor_set(x_734, 0, x_731);
lean_ctor_set(x_734, 1, x_732);
return x_734;
}
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
lean_dec(x_704);
x_735 = lean_ctor_get(x_705, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_705, 1);
lean_inc(x_736);
if (lean_is_exclusive(x_705)) {
 lean_ctor_release(x_705, 0);
 lean_ctor_release(x_705, 1);
 x_737 = x_705;
} else {
 lean_dec_ref(x_705);
 x_737 = lean_box(0);
}
if (lean_is_scalar(x_737)) {
 x_738 = lean_alloc_ctor(1, 2, 0);
} else {
 x_738 = x_737;
}
lean_ctor_set(x_738, 0, x_735);
lean_ctor_set(x_738, 1, x_736);
return x_738;
}
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
lean_dec(x_697);
x_739 = lean_ctor_get(x_700, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_700, 1);
lean_inc(x_740);
if (lean_is_exclusive(x_700)) {
 lean_ctor_release(x_700, 0);
 lean_ctor_release(x_700, 1);
 x_741 = x_700;
} else {
 lean_dec_ref(x_700);
 x_741 = lean_box(0);
}
if (lean_is_scalar(x_741)) {
 x_742 = lean_alloc_ctor(1, 2, 0);
} else {
 x_742 = x_741;
}
lean_ctor_set(x_742, 0, x_739);
lean_ctor_set(x_742, 1, x_740);
return x_742;
}
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; 
lean_dec(x_687);
x_743 = lean_ctor_get(x_693, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_693, 1);
lean_inc(x_744);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_745 = x_693;
} else {
 lean_dec_ref(x_693);
 x_745 = lean_box(0);
}
if (lean_is_scalar(x_745)) {
 x_746 = lean_alloc_ctor(1, 2, 0);
} else {
 x_746 = x_745;
}
lean_ctor_set(x_746, 0, x_743);
lean_ctor_set(x_746, 1, x_744);
return x_746;
}
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_747 = lean_ctor_get(x_686, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_686, 1);
lean_inc(x_748);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_749 = x_686;
} else {
 lean_dec_ref(x_686);
 x_749 = lean_box(0);
}
if (lean_is_scalar(x_749)) {
 x_750 = lean_alloc_ctor(1, 2, 0);
} else {
 x_750 = x_749;
}
lean_ctor_set(x_750, 0, x_747);
lean_ctor_set(x_750, 1, x_748);
return x_750;
}
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; 
lean_dec(x_676);
x_751 = lean_ctor_get(x_682, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_682, 1);
lean_inc(x_752);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_753 = x_682;
} else {
 lean_dec_ref(x_682);
 x_753 = lean_box(0);
}
if (lean_is_scalar(x_753)) {
 x_754 = lean_alloc_ctor(1, 2, 0);
} else {
 x_754 = x_753;
}
lean_ctor_set(x_754, 0, x_751);
lean_ctor_set(x_754, 1, x_752);
return x_754;
}
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_755 = lean_ctor_get(x_675, 0);
lean_inc(x_755);
x_756 = lean_ctor_get(x_675, 1);
lean_inc(x_756);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 x_757 = x_675;
} else {
 lean_dec_ref(x_675);
 x_757 = lean_box(0);
}
if (lean_is_scalar(x_757)) {
 x_758 = lean_alloc_ctor(1, 2, 0);
} else {
 x_758 = x_757;
}
lean_ctor_set(x_758, 0, x_755);
lean_ctor_set(x_758, 1, x_756);
return x_758;
}
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
lean_dec(x_665);
x_759 = lean_ctor_get(x_671, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_671, 1);
lean_inc(x_760);
if (lean_is_exclusive(x_671)) {
 lean_ctor_release(x_671, 0);
 lean_ctor_release(x_671, 1);
 x_761 = x_671;
} else {
 lean_dec_ref(x_671);
 x_761 = lean_box(0);
}
if (lean_is_scalar(x_761)) {
 x_762 = lean_alloc_ctor(1, 2, 0);
} else {
 x_762 = x_761;
}
lean_ctor_set(x_762, 0, x_759);
lean_ctor_set(x_762, 1, x_760);
return x_762;
}
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_763 = lean_ctor_get(x_664, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_664, 1);
lean_inc(x_764);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 x_765 = x_664;
} else {
 lean_dec_ref(x_664);
 x_765 = lean_box(0);
}
if (lean_is_scalar(x_765)) {
 x_766 = lean_alloc_ctor(1, 2, 0);
} else {
 x_766 = x_765;
}
lean_ctor_set(x_766, 0, x_763);
lean_ctor_set(x_766, 1, x_764);
return x_766;
}
}
}
else
{
uint8_t x_767; 
lean_dec(x_35);
x_767 = !lean_is_exclusive(x_38);
if (x_767 == 0)
{
return x_38;
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_768 = lean_ctor_get(x_38, 0);
x_769 = lean_ctor_get(x_38, 1);
lean_inc(x_769);
lean_inc(x_768);
lean_dec(x_38);
x_770 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_770, 0, x_768);
lean_ctor_set(x_770, 1, x_769);
return x_770;
}
}
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_771 = lean_ctor_get(x_32, 1);
lean_inc(x_771);
lean_dec(x_32);
x_772 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_772, 0, x_9);
lean_ctor_set(x_772, 1, x_771);
x_773 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_10, x_29);
x_774 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
x_775 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_inc(x_773);
x_776 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_774, x_775, x_773, x_2, x_772);
if (lean_obj_tag(x_776) == 0)
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_777 = lean_ctor_get(x_776, 1);
lean_inc(x_777);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_778 = x_776;
} else {
 lean_dec_ref(x_776);
 x_778 = lean_box(0);
}
if (lean_is_scalar(x_778)) {
 x_779 = lean_alloc_ctor(0, 2, 0);
} else {
 x_779 = x_778;
}
lean_ctor_set(x_779, 0, x_9);
lean_ctor_set(x_779, 1, x_777);
x_780 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_773);
x_781 = l_Lean_IR_inferBorrow(x_780, x_2, x_779);
if (lean_obj_tag(x_781) == 0)
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_782 = lean_ctor_get(x_781, 0);
lean_inc(x_782);
x_783 = lean_ctor_get(x_781, 1);
lean_inc(x_783);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 lean_ctor_release(x_781, 1);
 x_784 = x_781;
} else {
 lean_dec_ref(x_781);
 x_784 = lean_box(0);
}
if (lean_is_scalar(x_784)) {
 x_785 = lean_alloc_ctor(0, 2, 0);
} else {
 x_785 = x_784;
}
lean_ctor_set(x_785, 0, x_9);
lean_ctor_set(x_785, 1, x_783);
x_786 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_787 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_782);
x_788 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_786, x_787, x_782, x_2, x_785);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_789 = lean_ctor_get(x_788, 1);
lean_inc(x_789);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 lean_ctor_release(x_788, 1);
 x_790 = x_788;
} else {
 lean_dec_ref(x_788);
 x_790 = lean_box(0);
}
if (lean_is_scalar(x_790)) {
 x_791 = lean_alloc_ctor(0, 2, 0);
} else {
 x_791 = x_790;
}
lean_ctor_set(x_791, 0, x_9);
lean_ctor_set(x_791, 1, x_789);
x_792 = l_Lean_IR_explicitBoxing(x_782, x_2, x_791);
if (lean_obj_tag(x_792) == 0)
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_792, 1);
lean_inc(x_794);
if (lean_is_exclusive(x_792)) {
 lean_ctor_release(x_792, 0);
 lean_ctor_release(x_792, 1);
 x_795 = x_792;
} else {
 lean_dec_ref(x_792);
 x_795 = lean_box(0);
}
if (lean_is_scalar(x_795)) {
 x_796 = lean_alloc_ctor(0, 2, 0);
} else {
 x_796 = x_795;
}
lean_ctor_set(x_796, 0, x_9);
lean_ctor_set(x_796, 1, x_794);
x_797 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_798 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_793);
x_799 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_797, x_798, x_793, x_2, x_796);
if (lean_obj_tag(x_799) == 0)
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; 
x_800 = lean_ctor_get(x_799, 1);
lean_inc(x_800);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_801 = x_799;
} else {
 lean_dec_ref(x_799);
 x_801 = lean_box(0);
}
if (lean_is_scalar(x_801)) {
 x_802 = lean_alloc_ctor(0, 2, 0);
} else {
 x_802 = x_801;
}
lean_ctor_set(x_802, 0, x_9);
lean_ctor_set(x_802, 1, x_800);
x_803 = l_Lean_IR_explicitRC(x_793, x_2, x_802);
if (lean_obj_tag(x_803) == 0)
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_804 = lean_ctor_get(x_803, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_803, 1);
lean_inc(x_805);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_806 = x_803;
} else {
 lean_dec_ref(x_803);
 x_806 = lean_box(0);
}
if (lean_is_scalar(x_806)) {
 x_807 = lean_alloc_ctor(0, 2, 0);
} else {
 x_807 = x_806;
}
lean_ctor_set(x_807, 0, x_9);
lean_ctor_set(x_807, 1, x_805);
x_808 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_809 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_804);
x_810 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_808, x_809, x_804, x_2, x_807);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_811 = lean_ctor_get(x_810, 1);
lean_inc(x_811);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 x_812 = x_810;
} else {
 lean_dec_ref(x_810);
 x_812 = lean_box(0);
}
if (lean_is_scalar(x_812)) {
 x_813 = lean_alloc_ctor(0, 2, 0);
} else {
 x_813 = x_812;
}
lean_ctor_set(x_813, 0, x_9);
lean_ctor_set(x_813, 1, x_811);
x_814 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_804);
x_815 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_816 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_814);
x_817 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_815, x_816, x_814, x_2, x_813);
if (lean_obj_tag(x_817) == 0)
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_818 = lean_ctor_get(x_817, 1);
lean_inc(x_818);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 x_819 = x_817;
} else {
 lean_dec_ref(x_817);
 x_819 = lean_box(0);
}
if (lean_is_scalar(x_819)) {
 x_820 = lean_alloc_ctor(0, 2, 0);
} else {
 x_820 = x_819;
}
lean_ctor_set(x_820, 0, x_9);
lean_ctor_set(x_820, 1, x_818);
x_821 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_814);
lean_inc(x_821);
x_822 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_18, x_19, x_821, x_2, x_820);
if (lean_obj_tag(x_822) == 0)
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_823 = lean_ctor_get(x_822, 1);
lean_inc(x_823);
if (lean_is_exclusive(x_822)) {
 lean_ctor_release(x_822, 0);
 lean_ctor_release(x_822, 1);
 x_824 = x_822;
} else {
 lean_dec_ref(x_822);
 x_824 = lean_box(0);
}
if (lean_is_scalar(x_824)) {
 x_825 = lean_alloc_ctor(0, 2, 0);
} else {
 x_825 = x_824;
}
lean_ctor_set(x_825, 0, x_9);
lean_ctor_set(x_825, 1, x_823);
x_826 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_827 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_821);
x_828 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_826, x_827, x_821, x_2, x_825);
if (lean_obj_tag(x_828) == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_829 = lean_ctor_get(x_828, 1);
lean_inc(x_829);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 x_830 = x_828;
} else {
 lean_dec_ref(x_828);
 x_830 = lean_box(0);
}
if (lean_is_scalar(x_830)) {
 x_831 = lean_alloc_ctor(0, 2, 0);
} else {
 x_831 = x_830;
}
lean_ctor_set(x_831, 0, x_9);
lean_ctor_set(x_831, 1, x_829);
lean_inc(x_821);
x_832 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_821, x_821, x_10, x_2, x_831);
if (lean_obj_tag(x_832) == 0)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_833 = lean_ctor_get(x_832, 1);
lean_inc(x_833);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 lean_ctor_release(x_832, 1);
 x_834 = x_832;
} else {
 lean_dec_ref(x_832);
 x_834 = lean_box(0);
}
if (lean_is_scalar(x_834)) {
 x_835 = lean_alloc_ctor(0, 2, 0);
} else {
 x_835 = x_834;
}
lean_ctor_set(x_835, 0, x_9);
lean_ctor_set(x_835, 1, x_833);
x_836 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_821, x_10, x_2, x_835);
lean_dec(x_821);
if (lean_obj_tag(x_836) == 0)
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; 
x_837 = lean_ctor_get(x_836, 1);
lean_inc(x_837);
if (lean_is_exclusive(x_836)) {
 lean_ctor_release(x_836, 0);
 lean_ctor_release(x_836, 1);
 x_838 = x_836;
} else {
 lean_dec_ref(x_836);
 x_838 = lean_box(0);
}
if (lean_is_scalar(x_838)) {
 x_839 = lean_alloc_ctor(0, 2, 0);
} else {
 x_839 = x_838;
}
lean_ctor_set(x_839, 0, x_9);
lean_ctor_set(x_839, 1, x_837);
return x_839;
}
else
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
x_840 = lean_ctor_get(x_836, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_836, 1);
lean_inc(x_841);
if (lean_is_exclusive(x_836)) {
 lean_ctor_release(x_836, 0);
 lean_ctor_release(x_836, 1);
 x_842 = x_836;
} else {
 lean_dec_ref(x_836);
 x_842 = lean_box(0);
}
if (lean_is_scalar(x_842)) {
 x_843 = lean_alloc_ctor(1, 2, 0);
} else {
 x_843 = x_842;
}
lean_ctor_set(x_843, 0, x_840);
lean_ctor_set(x_843, 1, x_841);
return x_843;
}
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
lean_dec(x_821);
x_844 = lean_ctor_get(x_832, 0);
lean_inc(x_844);
x_845 = lean_ctor_get(x_832, 1);
lean_inc(x_845);
if (lean_is_exclusive(x_832)) {
 lean_ctor_release(x_832, 0);
 lean_ctor_release(x_832, 1);
 x_846 = x_832;
} else {
 lean_dec_ref(x_832);
 x_846 = lean_box(0);
}
if (lean_is_scalar(x_846)) {
 x_847 = lean_alloc_ctor(1, 2, 0);
} else {
 x_847 = x_846;
}
lean_ctor_set(x_847, 0, x_844);
lean_ctor_set(x_847, 1, x_845);
return x_847;
}
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
lean_dec(x_821);
x_848 = lean_ctor_get(x_828, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_828, 1);
lean_inc(x_849);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 x_850 = x_828;
} else {
 lean_dec_ref(x_828);
 x_850 = lean_box(0);
}
if (lean_is_scalar(x_850)) {
 x_851 = lean_alloc_ctor(1, 2, 0);
} else {
 x_851 = x_850;
}
lean_ctor_set(x_851, 0, x_848);
lean_ctor_set(x_851, 1, x_849);
return x_851;
}
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; 
lean_dec(x_821);
x_852 = lean_ctor_get(x_822, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_822, 1);
lean_inc(x_853);
if (lean_is_exclusive(x_822)) {
 lean_ctor_release(x_822, 0);
 lean_ctor_release(x_822, 1);
 x_854 = x_822;
} else {
 lean_dec_ref(x_822);
 x_854 = lean_box(0);
}
if (lean_is_scalar(x_854)) {
 x_855 = lean_alloc_ctor(1, 2, 0);
} else {
 x_855 = x_854;
}
lean_ctor_set(x_855, 0, x_852);
lean_ctor_set(x_855, 1, x_853);
return x_855;
}
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
lean_dec(x_814);
x_856 = lean_ctor_get(x_817, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_817, 1);
lean_inc(x_857);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 x_858 = x_817;
} else {
 lean_dec_ref(x_817);
 x_858 = lean_box(0);
}
if (lean_is_scalar(x_858)) {
 x_859 = lean_alloc_ctor(1, 2, 0);
} else {
 x_859 = x_858;
}
lean_ctor_set(x_859, 0, x_856);
lean_ctor_set(x_859, 1, x_857);
return x_859;
}
}
else
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
lean_dec(x_804);
x_860 = lean_ctor_get(x_810, 0);
lean_inc(x_860);
x_861 = lean_ctor_get(x_810, 1);
lean_inc(x_861);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 x_862 = x_810;
} else {
 lean_dec_ref(x_810);
 x_862 = lean_box(0);
}
if (lean_is_scalar(x_862)) {
 x_863 = lean_alloc_ctor(1, 2, 0);
} else {
 x_863 = x_862;
}
lean_ctor_set(x_863, 0, x_860);
lean_ctor_set(x_863, 1, x_861);
return x_863;
}
}
else
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_864 = lean_ctor_get(x_803, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_803, 1);
lean_inc(x_865);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_866 = x_803;
} else {
 lean_dec_ref(x_803);
 x_866 = lean_box(0);
}
if (lean_is_scalar(x_866)) {
 x_867 = lean_alloc_ctor(1, 2, 0);
} else {
 x_867 = x_866;
}
lean_ctor_set(x_867, 0, x_864);
lean_ctor_set(x_867, 1, x_865);
return x_867;
}
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; 
lean_dec(x_793);
x_868 = lean_ctor_get(x_799, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_799, 1);
lean_inc(x_869);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_870 = x_799;
} else {
 lean_dec_ref(x_799);
 x_870 = lean_box(0);
}
if (lean_is_scalar(x_870)) {
 x_871 = lean_alloc_ctor(1, 2, 0);
} else {
 x_871 = x_870;
}
lean_ctor_set(x_871, 0, x_868);
lean_ctor_set(x_871, 1, x_869);
return x_871;
}
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_872 = lean_ctor_get(x_792, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_792, 1);
lean_inc(x_873);
if (lean_is_exclusive(x_792)) {
 lean_ctor_release(x_792, 0);
 lean_ctor_release(x_792, 1);
 x_874 = x_792;
} else {
 lean_dec_ref(x_792);
 x_874 = lean_box(0);
}
if (lean_is_scalar(x_874)) {
 x_875 = lean_alloc_ctor(1, 2, 0);
} else {
 x_875 = x_874;
}
lean_ctor_set(x_875, 0, x_872);
lean_ctor_set(x_875, 1, x_873);
return x_875;
}
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; 
lean_dec(x_782);
x_876 = lean_ctor_get(x_788, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_788, 1);
lean_inc(x_877);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 lean_ctor_release(x_788, 1);
 x_878 = x_788;
} else {
 lean_dec_ref(x_788);
 x_878 = lean_box(0);
}
if (lean_is_scalar(x_878)) {
 x_879 = lean_alloc_ctor(1, 2, 0);
} else {
 x_879 = x_878;
}
lean_ctor_set(x_879, 0, x_876);
lean_ctor_set(x_879, 1, x_877);
return x_879;
}
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_880 = lean_ctor_get(x_781, 0);
lean_inc(x_880);
x_881 = lean_ctor_get(x_781, 1);
lean_inc(x_881);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 lean_ctor_release(x_781, 1);
 x_882 = x_781;
} else {
 lean_dec_ref(x_781);
 x_882 = lean_box(0);
}
if (lean_is_scalar(x_882)) {
 x_883 = lean_alloc_ctor(1, 2, 0);
} else {
 x_883 = x_882;
}
lean_ctor_set(x_883, 0, x_880);
lean_ctor_set(x_883, 1, x_881);
return x_883;
}
}
else
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; 
lean_dec(x_773);
x_884 = lean_ctor_get(x_776, 0);
lean_inc(x_884);
x_885 = lean_ctor_get(x_776, 1);
lean_inc(x_885);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_886 = x_776;
} else {
 lean_dec_ref(x_776);
 x_886 = lean_box(0);
}
if (lean_is_scalar(x_886)) {
 x_887 = lean_alloc_ctor(1, 2, 0);
} else {
 x_887 = x_886;
}
lean_ctor_set(x_887, 0, x_884);
lean_ctor_set(x_887, 1, x_885);
return x_887;
}
}
}
else
{
uint8_t x_888; 
lean_dec(x_29);
x_888 = !lean_is_exclusive(x_32);
if (x_888 == 0)
{
return x_32;
}
else
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; 
x_889 = lean_ctor_get(x_32, 0);
x_890 = lean_ctor_get(x_32, 1);
lean_inc(x_890);
lean_inc(x_889);
lean_dec(x_32);
x_891 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_891, 0, x_889);
lean_ctor_set(x_891, 1, x_890);
return x_891;
}
}
}
else
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; 
x_892 = lean_ctor_get(x_26, 1);
lean_inc(x_892);
lean_dec(x_26);
x_893 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_893, 0, x_9);
lean_ctor_set(x_893, 1, x_892);
x_894 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(x_10, x_23);
x_895 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10;
x_896 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
lean_inc(x_894);
x_897 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_895, x_896, x_894, x_2, x_893);
if (lean_obj_tag(x_897) == 0)
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_898 = lean_ctor_get(x_897, 1);
lean_inc(x_898);
if (lean_is_exclusive(x_897)) {
 lean_ctor_release(x_897, 0);
 lean_ctor_release(x_897, 1);
 x_899 = x_897;
} else {
 lean_dec_ref(x_897);
 x_899 = lean_box(0);
}
if (lean_is_scalar(x_899)) {
 x_900 = lean_alloc_ctor(0, 2, 0);
} else {
 x_900 = x_899;
}
lean_ctor_set(x_900, 0, x_9);
lean_ctor_set(x_900, 1, x_898);
x_901 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_10, x_894);
x_902 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
x_903 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_inc(x_901);
x_904 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_902, x_903, x_901, x_2, x_900);
if (lean_obj_tag(x_904) == 0)
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_905 = lean_ctor_get(x_904, 1);
lean_inc(x_905);
if (lean_is_exclusive(x_904)) {
 lean_ctor_release(x_904, 0);
 lean_ctor_release(x_904, 1);
 x_906 = x_904;
} else {
 lean_dec_ref(x_904);
 x_906 = lean_box(0);
}
if (lean_is_scalar(x_906)) {
 x_907 = lean_alloc_ctor(0, 2, 0);
} else {
 x_907 = x_906;
}
lean_ctor_set(x_907, 0, x_9);
lean_ctor_set(x_907, 1, x_905);
x_908 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_901);
x_909 = l_Lean_IR_inferBorrow(x_908, x_2, x_907);
if (lean_obj_tag(x_909) == 0)
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; 
x_910 = lean_ctor_get(x_909, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_909, 1);
lean_inc(x_911);
if (lean_is_exclusive(x_909)) {
 lean_ctor_release(x_909, 0);
 lean_ctor_release(x_909, 1);
 x_912 = x_909;
} else {
 lean_dec_ref(x_909);
 x_912 = lean_box(0);
}
if (lean_is_scalar(x_912)) {
 x_913 = lean_alloc_ctor(0, 2, 0);
} else {
 x_913 = x_912;
}
lean_ctor_set(x_913, 0, x_9);
lean_ctor_set(x_913, 1, x_911);
x_914 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_915 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_910);
x_916 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_914, x_915, x_910, x_2, x_913);
if (lean_obj_tag(x_916) == 0)
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; 
x_917 = lean_ctor_get(x_916, 1);
lean_inc(x_917);
if (lean_is_exclusive(x_916)) {
 lean_ctor_release(x_916, 0);
 lean_ctor_release(x_916, 1);
 x_918 = x_916;
} else {
 lean_dec_ref(x_916);
 x_918 = lean_box(0);
}
if (lean_is_scalar(x_918)) {
 x_919 = lean_alloc_ctor(0, 2, 0);
} else {
 x_919 = x_918;
}
lean_ctor_set(x_919, 0, x_9);
lean_ctor_set(x_919, 1, x_917);
x_920 = l_Lean_IR_explicitBoxing(x_910, x_2, x_919);
if (lean_obj_tag(x_920) == 0)
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; 
x_921 = lean_ctor_get(x_920, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_920, 1);
lean_inc(x_922);
if (lean_is_exclusive(x_920)) {
 lean_ctor_release(x_920, 0);
 lean_ctor_release(x_920, 1);
 x_923 = x_920;
} else {
 lean_dec_ref(x_920);
 x_923 = lean_box(0);
}
if (lean_is_scalar(x_923)) {
 x_924 = lean_alloc_ctor(0, 2, 0);
} else {
 x_924 = x_923;
}
lean_ctor_set(x_924, 0, x_9);
lean_ctor_set(x_924, 1, x_922);
x_925 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_926 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_921);
x_927 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_925, x_926, x_921, x_2, x_924);
if (lean_obj_tag(x_927) == 0)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; 
x_928 = lean_ctor_get(x_927, 1);
lean_inc(x_928);
if (lean_is_exclusive(x_927)) {
 lean_ctor_release(x_927, 0);
 lean_ctor_release(x_927, 1);
 x_929 = x_927;
} else {
 lean_dec_ref(x_927);
 x_929 = lean_box(0);
}
if (lean_is_scalar(x_929)) {
 x_930 = lean_alloc_ctor(0, 2, 0);
} else {
 x_930 = x_929;
}
lean_ctor_set(x_930, 0, x_9);
lean_ctor_set(x_930, 1, x_928);
x_931 = l_Lean_IR_explicitRC(x_921, x_2, x_930);
if (lean_obj_tag(x_931) == 0)
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_932 = lean_ctor_get(x_931, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_931, 1);
lean_inc(x_933);
if (lean_is_exclusive(x_931)) {
 lean_ctor_release(x_931, 0);
 lean_ctor_release(x_931, 1);
 x_934 = x_931;
} else {
 lean_dec_ref(x_931);
 x_934 = lean_box(0);
}
if (lean_is_scalar(x_934)) {
 x_935 = lean_alloc_ctor(0, 2, 0);
} else {
 x_935 = x_934;
}
lean_ctor_set(x_935, 0, x_9);
lean_ctor_set(x_935, 1, x_933);
x_936 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_937 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_932);
x_938 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_936, x_937, x_932, x_2, x_935);
if (lean_obj_tag(x_938) == 0)
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; 
x_939 = lean_ctor_get(x_938, 1);
lean_inc(x_939);
if (lean_is_exclusive(x_938)) {
 lean_ctor_release(x_938, 0);
 lean_ctor_release(x_938, 1);
 x_940 = x_938;
} else {
 lean_dec_ref(x_938);
 x_940 = lean_box(0);
}
if (lean_is_scalar(x_940)) {
 x_941 = lean_alloc_ctor(0, 2, 0);
} else {
 x_941 = x_940;
}
lean_ctor_set(x_941, 0, x_9);
lean_ctor_set(x_941, 1, x_939);
x_942 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_932);
x_943 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_944 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_942);
x_945 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_943, x_944, x_942, x_2, x_941);
if (lean_obj_tag(x_945) == 0)
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; 
x_946 = lean_ctor_get(x_945, 1);
lean_inc(x_946);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_947 = x_945;
} else {
 lean_dec_ref(x_945);
 x_947 = lean_box(0);
}
if (lean_is_scalar(x_947)) {
 x_948 = lean_alloc_ctor(0, 2, 0);
} else {
 x_948 = x_947;
}
lean_ctor_set(x_948, 0, x_9);
lean_ctor_set(x_948, 1, x_946);
x_949 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_942);
lean_inc(x_949);
x_950 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_18, x_19, x_949, x_2, x_948);
if (lean_obj_tag(x_950) == 0)
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; 
x_951 = lean_ctor_get(x_950, 1);
lean_inc(x_951);
if (lean_is_exclusive(x_950)) {
 lean_ctor_release(x_950, 0);
 lean_ctor_release(x_950, 1);
 x_952 = x_950;
} else {
 lean_dec_ref(x_950);
 x_952 = lean_box(0);
}
if (lean_is_scalar(x_952)) {
 x_953 = lean_alloc_ctor(0, 2, 0);
} else {
 x_953 = x_952;
}
lean_ctor_set(x_953, 0, x_9);
lean_ctor_set(x_953, 1, x_951);
x_954 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_955 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_949);
x_956 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_954, x_955, x_949, x_2, x_953);
if (lean_obj_tag(x_956) == 0)
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_957 = lean_ctor_get(x_956, 1);
lean_inc(x_957);
if (lean_is_exclusive(x_956)) {
 lean_ctor_release(x_956, 0);
 lean_ctor_release(x_956, 1);
 x_958 = x_956;
} else {
 lean_dec_ref(x_956);
 x_958 = lean_box(0);
}
if (lean_is_scalar(x_958)) {
 x_959 = lean_alloc_ctor(0, 2, 0);
} else {
 x_959 = x_958;
}
lean_ctor_set(x_959, 0, x_9);
lean_ctor_set(x_959, 1, x_957);
lean_inc(x_949);
x_960 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_949, x_949, x_10, x_2, x_959);
if (lean_obj_tag(x_960) == 0)
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_961 = lean_ctor_get(x_960, 1);
lean_inc(x_961);
if (lean_is_exclusive(x_960)) {
 lean_ctor_release(x_960, 0);
 lean_ctor_release(x_960, 1);
 x_962 = x_960;
} else {
 lean_dec_ref(x_960);
 x_962 = lean_box(0);
}
if (lean_is_scalar(x_962)) {
 x_963 = lean_alloc_ctor(0, 2, 0);
} else {
 x_963 = x_962;
}
lean_ctor_set(x_963, 0, x_9);
lean_ctor_set(x_963, 1, x_961);
x_964 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_949, x_10, x_2, x_963);
lean_dec(x_949);
if (lean_obj_tag(x_964) == 0)
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; 
x_965 = lean_ctor_get(x_964, 1);
lean_inc(x_965);
if (lean_is_exclusive(x_964)) {
 lean_ctor_release(x_964, 0);
 lean_ctor_release(x_964, 1);
 x_966 = x_964;
} else {
 lean_dec_ref(x_964);
 x_966 = lean_box(0);
}
if (lean_is_scalar(x_966)) {
 x_967 = lean_alloc_ctor(0, 2, 0);
} else {
 x_967 = x_966;
}
lean_ctor_set(x_967, 0, x_9);
lean_ctor_set(x_967, 1, x_965);
return x_967;
}
else
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; 
x_968 = lean_ctor_get(x_964, 0);
lean_inc(x_968);
x_969 = lean_ctor_get(x_964, 1);
lean_inc(x_969);
if (lean_is_exclusive(x_964)) {
 lean_ctor_release(x_964, 0);
 lean_ctor_release(x_964, 1);
 x_970 = x_964;
} else {
 lean_dec_ref(x_964);
 x_970 = lean_box(0);
}
if (lean_is_scalar(x_970)) {
 x_971 = lean_alloc_ctor(1, 2, 0);
} else {
 x_971 = x_970;
}
lean_ctor_set(x_971, 0, x_968);
lean_ctor_set(x_971, 1, x_969);
return x_971;
}
}
else
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; 
lean_dec(x_949);
x_972 = lean_ctor_get(x_960, 0);
lean_inc(x_972);
x_973 = lean_ctor_get(x_960, 1);
lean_inc(x_973);
if (lean_is_exclusive(x_960)) {
 lean_ctor_release(x_960, 0);
 lean_ctor_release(x_960, 1);
 x_974 = x_960;
} else {
 lean_dec_ref(x_960);
 x_974 = lean_box(0);
}
if (lean_is_scalar(x_974)) {
 x_975 = lean_alloc_ctor(1, 2, 0);
} else {
 x_975 = x_974;
}
lean_ctor_set(x_975, 0, x_972);
lean_ctor_set(x_975, 1, x_973);
return x_975;
}
}
else
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; 
lean_dec(x_949);
x_976 = lean_ctor_get(x_956, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_956, 1);
lean_inc(x_977);
if (lean_is_exclusive(x_956)) {
 lean_ctor_release(x_956, 0);
 lean_ctor_release(x_956, 1);
 x_978 = x_956;
} else {
 lean_dec_ref(x_956);
 x_978 = lean_box(0);
}
if (lean_is_scalar(x_978)) {
 x_979 = lean_alloc_ctor(1, 2, 0);
} else {
 x_979 = x_978;
}
lean_ctor_set(x_979, 0, x_976);
lean_ctor_set(x_979, 1, x_977);
return x_979;
}
}
else
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
lean_dec(x_949);
x_980 = lean_ctor_get(x_950, 0);
lean_inc(x_980);
x_981 = lean_ctor_get(x_950, 1);
lean_inc(x_981);
if (lean_is_exclusive(x_950)) {
 lean_ctor_release(x_950, 0);
 lean_ctor_release(x_950, 1);
 x_982 = x_950;
} else {
 lean_dec_ref(x_950);
 x_982 = lean_box(0);
}
if (lean_is_scalar(x_982)) {
 x_983 = lean_alloc_ctor(1, 2, 0);
} else {
 x_983 = x_982;
}
lean_ctor_set(x_983, 0, x_980);
lean_ctor_set(x_983, 1, x_981);
return x_983;
}
}
else
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
lean_dec(x_942);
x_984 = lean_ctor_get(x_945, 0);
lean_inc(x_984);
x_985 = lean_ctor_get(x_945, 1);
lean_inc(x_985);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_986 = x_945;
} else {
 lean_dec_ref(x_945);
 x_986 = lean_box(0);
}
if (lean_is_scalar(x_986)) {
 x_987 = lean_alloc_ctor(1, 2, 0);
} else {
 x_987 = x_986;
}
lean_ctor_set(x_987, 0, x_984);
lean_ctor_set(x_987, 1, x_985);
return x_987;
}
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; 
lean_dec(x_932);
x_988 = lean_ctor_get(x_938, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_938, 1);
lean_inc(x_989);
if (lean_is_exclusive(x_938)) {
 lean_ctor_release(x_938, 0);
 lean_ctor_release(x_938, 1);
 x_990 = x_938;
} else {
 lean_dec_ref(x_938);
 x_990 = lean_box(0);
}
if (lean_is_scalar(x_990)) {
 x_991 = lean_alloc_ctor(1, 2, 0);
} else {
 x_991 = x_990;
}
lean_ctor_set(x_991, 0, x_988);
lean_ctor_set(x_991, 1, x_989);
return x_991;
}
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_992 = lean_ctor_get(x_931, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_931, 1);
lean_inc(x_993);
if (lean_is_exclusive(x_931)) {
 lean_ctor_release(x_931, 0);
 lean_ctor_release(x_931, 1);
 x_994 = x_931;
} else {
 lean_dec_ref(x_931);
 x_994 = lean_box(0);
}
if (lean_is_scalar(x_994)) {
 x_995 = lean_alloc_ctor(1, 2, 0);
} else {
 x_995 = x_994;
}
lean_ctor_set(x_995, 0, x_992);
lean_ctor_set(x_995, 1, x_993);
return x_995;
}
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; 
lean_dec(x_921);
x_996 = lean_ctor_get(x_927, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_927, 1);
lean_inc(x_997);
if (lean_is_exclusive(x_927)) {
 lean_ctor_release(x_927, 0);
 lean_ctor_release(x_927, 1);
 x_998 = x_927;
} else {
 lean_dec_ref(x_927);
 x_998 = lean_box(0);
}
if (lean_is_scalar(x_998)) {
 x_999 = lean_alloc_ctor(1, 2, 0);
} else {
 x_999 = x_998;
}
lean_ctor_set(x_999, 0, x_996);
lean_ctor_set(x_999, 1, x_997);
return x_999;
}
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; 
x_1000 = lean_ctor_get(x_920, 0);
lean_inc(x_1000);
x_1001 = lean_ctor_get(x_920, 1);
lean_inc(x_1001);
if (lean_is_exclusive(x_920)) {
 lean_ctor_release(x_920, 0);
 lean_ctor_release(x_920, 1);
 x_1002 = x_920;
} else {
 lean_dec_ref(x_920);
 x_1002 = lean_box(0);
}
if (lean_is_scalar(x_1002)) {
 x_1003 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1003 = x_1002;
}
lean_ctor_set(x_1003, 0, x_1000);
lean_ctor_set(x_1003, 1, x_1001);
return x_1003;
}
}
else
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; 
lean_dec(x_910);
x_1004 = lean_ctor_get(x_916, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_916, 1);
lean_inc(x_1005);
if (lean_is_exclusive(x_916)) {
 lean_ctor_release(x_916, 0);
 lean_ctor_release(x_916, 1);
 x_1006 = x_916;
} else {
 lean_dec_ref(x_916);
 x_1006 = lean_box(0);
}
if (lean_is_scalar(x_1006)) {
 x_1007 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1007 = x_1006;
}
lean_ctor_set(x_1007, 0, x_1004);
lean_ctor_set(x_1007, 1, x_1005);
return x_1007;
}
}
else
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
x_1008 = lean_ctor_get(x_909, 0);
lean_inc(x_1008);
x_1009 = lean_ctor_get(x_909, 1);
lean_inc(x_1009);
if (lean_is_exclusive(x_909)) {
 lean_ctor_release(x_909, 0);
 lean_ctor_release(x_909, 1);
 x_1010 = x_909;
} else {
 lean_dec_ref(x_909);
 x_1010 = lean_box(0);
}
if (lean_is_scalar(x_1010)) {
 x_1011 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1011 = x_1010;
}
lean_ctor_set(x_1011, 0, x_1008);
lean_ctor_set(x_1011, 1, x_1009);
return x_1011;
}
}
else
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
lean_dec(x_901);
x_1012 = lean_ctor_get(x_904, 0);
lean_inc(x_1012);
x_1013 = lean_ctor_get(x_904, 1);
lean_inc(x_1013);
if (lean_is_exclusive(x_904)) {
 lean_ctor_release(x_904, 0);
 lean_ctor_release(x_904, 1);
 x_1014 = x_904;
} else {
 lean_dec_ref(x_904);
 x_1014 = lean_box(0);
}
if (lean_is_scalar(x_1014)) {
 x_1015 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1015 = x_1014;
}
lean_ctor_set(x_1015, 0, x_1012);
lean_ctor_set(x_1015, 1, x_1013);
return x_1015;
}
}
else
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
lean_dec(x_894);
x_1016 = lean_ctor_get(x_897, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_897, 1);
lean_inc(x_1017);
if (lean_is_exclusive(x_897)) {
 lean_ctor_release(x_897, 0);
 lean_ctor_release(x_897, 1);
 x_1018 = x_897;
} else {
 lean_dec_ref(x_897);
 x_1018 = lean_box(0);
}
if (lean_is_scalar(x_1018)) {
 x_1019 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1019 = x_1018;
}
lean_ctor_set(x_1019, 0, x_1016);
lean_ctor_set(x_1019, 1, x_1017);
return x_1019;
}
}
}
else
{
uint8_t x_1020; 
lean_dec(x_23);
x_1020 = !lean_is_exclusive(x_26);
if (x_1020 == 0)
{
return x_26;
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1021 = lean_ctor_get(x_26, 0);
x_1022 = lean_ctor_get(x_26, 1);
lean_inc(x_1022);
lean_inc(x_1021);
lean_dec(x_26);
x_1023 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1023, 0, x_1021);
lean_ctor_set(x_1023, 1, x_1022);
return x_1023;
}
}
}
else
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
x_1024 = lean_ctor_get(x_20, 1);
lean_inc(x_1024);
lean_dec(x_20);
x_1025 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1025, 0, x_9);
lean_ctor_set(x_1025, 1, x_1024);
x_1026 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__2(x_10, x_17);
x_1027 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7;
x_1028 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6;
lean_inc(x_1026);
x_1029 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1027, x_1028, x_1026, x_2, x_1025);
if (lean_obj_tag(x_1029) == 0)
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
x_1030 = lean_ctor_get(x_1029, 1);
lean_inc(x_1030);
if (lean_is_exclusive(x_1029)) {
 lean_ctor_release(x_1029, 0);
 lean_ctor_release(x_1029, 1);
 x_1031 = x_1029;
} else {
 lean_dec_ref(x_1029);
 x_1031 = lean_box(0);
}
if (lean_is_scalar(x_1031)) {
 x_1032 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1032 = x_1031;
}
lean_ctor_set(x_1032, 0, x_9);
lean_ctor_set(x_1032, 1, x_1030);
x_1033 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(x_10, x_1026);
x_1034 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10;
x_1035 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
lean_inc(x_1033);
x_1036 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1034, x_1035, x_1033, x_2, x_1032);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1037 = lean_ctor_get(x_1036, 1);
lean_inc(x_1037);
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 lean_ctor_release(x_1036, 1);
 x_1038 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1038 = lean_box(0);
}
if (lean_is_scalar(x_1038)) {
 x_1039 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1039 = x_1038;
}
lean_ctor_set(x_1039, 0, x_9);
lean_ctor_set(x_1039, 1, x_1037);
x_1040 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_10, x_1033);
x_1041 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
x_1042 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_inc(x_1040);
x_1043 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1041, x_1042, x_1040, x_2, x_1039);
if (lean_obj_tag(x_1043) == 0)
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; 
x_1044 = lean_ctor_get(x_1043, 1);
lean_inc(x_1044);
if (lean_is_exclusive(x_1043)) {
 lean_ctor_release(x_1043, 0);
 lean_ctor_release(x_1043, 1);
 x_1045 = x_1043;
} else {
 lean_dec_ref(x_1043);
 x_1045 = lean_box(0);
}
if (lean_is_scalar(x_1045)) {
 x_1046 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1046 = x_1045;
}
lean_ctor_set(x_1046, 0, x_9);
lean_ctor_set(x_1046, 1, x_1044);
x_1047 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_1040);
x_1048 = l_Lean_IR_inferBorrow(x_1047, x_2, x_1046);
if (lean_obj_tag(x_1048) == 0)
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
x_1049 = lean_ctor_get(x_1048, 0);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_1048, 1);
lean_inc(x_1050);
if (lean_is_exclusive(x_1048)) {
 lean_ctor_release(x_1048, 0);
 lean_ctor_release(x_1048, 1);
 x_1051 = x_1048;
} else {
 lean_dec_ref(x_1048);
 x_1051 = lean_box(0);
}
if (lean_is_scalar(x_1051)) {
 x_1052 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1052 = x_1051;
}
lean_ctor_set(x_1052, 0, x_9);
lean_ctor_set(x_1052, 1, x_1050);
x_1053 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_1054 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_1049);
x_1055 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1053, x_1054, x_1049, x_2, x_1052);
if (lean_obj_tag(x_1055) == 0)
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
x_1056 = lean_ctor_get(x_1055, 1);
lean_inc(x_1056);
if (lean_is_exclusive(x_1055)) {
 lean_ctor_release(x_1055, 0);
 lean_ctor_release(x_1055, 1);
 x_1057 = x_1055;
} else {
 lean_dec_ref(x_1055);
 x_1057 = lean_box(0);
}
if (lean_is_scalar(x_1057)) {
 x_1058 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1058 = x_1057;
}
lean_ctor_set(x_1058, 0, x_9);
lean_ctor_set(x_1058, 1, x_1056);
x_1059 = l_Lean_IR_explicitBoxing(x_1049, x_2, x_1058);
if (lean_obj_tag(x_1059) == 0)
{
lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
x_1060 = lean_ctor_get(x_1059, 0);
lean_inc(x_1060);
x_1061 = lean_ctor_get(x_1059, 1);
lean_inc(x_1061);
if (lean_is_exclusive(x_1059)) {
 lean_ctor_release(x_1059, 0);
 lean_ctor_release(x_1059, 1);
 x_1062 = x_1059;
} else {
 lean_dec_ref(x_1059);
 x_1062 = lean_box(0);
}
if (lean_is_scalar(x_1062)) {
 x_1063 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1063 = x_1062;
}
lean_ctor_set(x_1063, 0, x_9);
lean_ctor_set(x_1063, 1, x_1061);
x_1064 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_1065 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_1060);
x_1066 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1064, x_1065, x_1060, x_2, x_1063);
if (lean_obj_tag(x_1066) == 0)
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
x_1067 = lean_ctor_get(x_1066, 1);
lean_inc(x_1067);
if (lean_is_exclusive(x_1066)) {
 lean_ctor_release(x_1066, 0);
 lean_ctor_release(x_1066, 1);
 x_1068 = x_1066;
} else {
 lean_dec_ref(x_1066);
 x_1068 = lean_box(0);
}
if (lean_is_scalar(x_1068)) {
 x_1069 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1069 = x_1068;
}
lean_ctor_set(x_1069, 0, x_9);
lean_ctor_set(x_1069, 1, x_1067);
x_1070 = l_Lean_IR_explicitRC(x_1060, x_2, x_1069);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; 
x_1071 = lean_ctor_get(x_1070, 0);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1070, 1);
lean_inc(x_1072);
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 lean_ctor_release(x_1070, 1);
 x_1073 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1073 = lean_box(0);
}
if (lean_is_scalar(x_1073)) {
 x_1074 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1074 = x_1073;
}
lean_ctor_set(x_1074, 0, x_9);
lean_ctor_set(x_1074, 1, x_1072);
x_1075 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_1076 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_1071);
x_1077 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1075, x_1076, x_1071, x_2, x_1074);
if (lean_obj_tag(x_1077) == 0)
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
x_1078 = lean_ctor_get(x_1077, 1);
lean_inc(x_1078);
if (lean_is_exclusive(x_1077)) {
 lean_ctor_release(x_1077, 0);
 lean_ctor_release(x_1077, 1);
 x_1079 = x_1077;
} else {
 lean_dec_ref(x_1077);
 x_1079 = lean_box(0);
}
if (lean_is_scalar(x_1079)) {
 x_1080 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1080 = x_1079;
}
lean_ctor_set(x_1080, 0, x_9);
lean_ctor_set(x_1080, 1, x_1078);
x_1081 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_1071);
x_1082 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_1083 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_1081);
x_1084 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1082, x_1083, x_1081, x_2, x_1080);
if (lean_obj_tag(x_1084) == 0)
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; 
x_1085 = lean_ctor_get(x_1084, 1);
lean_inc(x_1085);
if (lean_is_exclusive(x_1084)) {
 lean_ctor_release(x_1084, 0);
 lean_ctor_release(x_1084, 1);
 x_1086 = x_1084;
} else {
 lean_dec_ref(x_1084);
 x_1086 = lean_box(0);
}
if (lean_is_scalar(x_1086)) {
 x_1087 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1087 = x_1086;
}
lean_ctor_set(x_1087, 0, x_9);
lean_ctor_set(x_1087, 1, x_1085);
x_1088 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_1081);
lean_inc(x_1088);
x_1089 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_18, x_19, x_1088, x_2, x_1087);
if (lean_obj_tag(x_1089) == 0)
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; 
x_1090 = lean_ctor_get(x_1089, 1);
lean_inc(x_1090);
if (lean_is_exclusive(x_1089)) {
 lean_ctor_release(x_1089, 0);
 lean_ctor_release(x_1089, 1);
 x_1091 = x_1089;
} else {
 lean_dec_ref(x_1089);
 x_1091 = lean_box(0);
}
if (lean_is_scalar(x_1091)) {
 x_1092 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1092 = x_1091;
}
lean_ctor_set(x_1092, 0, x_9);
lean_ctor_set(x_1092, 1, x_1090);
x_1093 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_1094 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_1088);
x_1095 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1093, x_1094, x_1088, x_2, x_1092);
if (lean_obj_tag(x_1095) == 0)
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
x_1096 = lean_ctor_get(x_1095, 1);
lean_inc(x_1096);
if (lean_is_exclusive(x_1095)) {
 lean_ctor_release(x_1095, 0);
 lean_ctor_release(x_1095, 1);
 x_1097 = x_1095;
} else {
 lean_dec_ref(x_1095);
 x_1097 = lean_box(0);
}
if (lean_is_scalar(x_1097)) {
 x_1098 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1098 = x_1097;
}
lean_ctor_set(x_1098, 0, x_9);
lean_ctor_set(x_1098, 1, x_1096);
lean_inc(x_1088);
x_1099 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1088, x_1088, x_10, x_2, x_1098);
if (lean_obj_tag(x_1099) == 0)
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
x_1100 = lean_ctor_get(x_1099, 1);
lean_inc(x_1100);
if (lean_is_exclusive(x_1099)) {
 lean_ctor_release(x_1099, 0);
 lean_ctor_release(x_1099, 1);
 x_1101 = x_1099;
} else {
 lean_dec_ref(x_1099);
 x_1101 = lean_box(0);
}
if (lean_is_scalar(x_1101)) {
 x_1102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1102 = x_1101;
}
lean_ctor_set(x_1102, 0, x_9);
lean_ctor_set(x_1102, 1, x_1100);
x_1103 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_1088, x_10, x_2, x_1102);
lean_dec(x_1088);
if (lean_obj_tag(x_1103) == 0)
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; 
x_1104 = lean_ctor_get(x_1103, 1);
lean_inc(x_1104);
if (lean_is_exclusive(x_1103)) {
 lean_ctor_release(x_1103, 0);
 lean_ctor_release(x_1103, 1);
 x_1105 = x_1103;
} else {
 lean_dec_ref(x_1103);
 x_1105 = lean_box(0);
}
if (lean_is_scalar(x_1105)) {
 x_1106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1106 = x_1105;
}
lean_ctor_set(x_1106, 0, x_9);
lean_ctor_set(x_1106, 1, x_1104);
return x_1106;
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; 
x_1107 = lean_ctor_get(x_1103, 0);
lean_inc(x_1107);
x_1108 = lean_ctor_get(x_1103, 1);
lean_inc(x_1108);
if (lean_is_exclusive(x_1103)) {
 lean_ctor_release(x_1103, 0);
 lean_ctor_release(x_1103, 1);
 x_1109 = x_1103;
} else {
 lean_dec_ref(x_1103);
 x_1109 = lean_box(0);
}
if (lean_is_scalar(x_1109)) {
 x_1110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1110 = x_1109;
}
lean_ctor_set(x_1110, 0, x_1107);
lean_ctor_set(x_1110, 1, x_1108);
return x_1110;
}
}
else
{
lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
lean_dec(x_1088);
x_1111 = lean_ctor_get(x_1099, 0);
lean_inc(x_1111);
x_1112 = lean_ctor_get(x_1099, 1);
lean_inc(x_1112);
if (lean_is_exclusive(x_1099)) {
 lean_ctor_release(x_1099, 0);
 lean_ctor_release(x_1099, 1);
 x_1113 = x_1099;
} else {
 lean_dec_ref(x_1099);
 x_1113 = lean_box(0);
}
if (lean_is_scalar(x_1113)) {
 x_1114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1114 = x_1113;
}
lean_ctor_set(x_1114, 0, x_1111);
lean_ctor_set(x_1114, 1, x_1112);
return x_1114;
}
}
else
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
lean_dec(x_1088);
x_1115 = lean_ctor_get(x_1095, 0);
lean_inc(x_1115);
x_1116 = lean_ctor_get(x_1095, 1);
lean_inc(x_1116);
if (lean_is_exclusive(x_1095)) {
 lean_ctor_release(x_1095, 0);
 lean_ctor_release(x_1095, 1);
 x_1117 = x_1095;
} else {
 lean_dec_ref(x_1095);
 x_1117 = lean_box(0);
}
if (lean_is_scalar(x_1117)) {
 x_1118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1118 = x_1117;
}
lean_ctor_set(x_1118, 0, x_1115);
lean_ctor_set(x_1118, 1, x_1116);
return x_1118;
}
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
lean_dec(x_1088);
x_1119 = lean_ctor_get(x_1089, 0);
lean_inc(x_1119);
x_1120 = lean_ctor_get(x_1089, 1);
lean_inc(x_1120);
if (lean_is_exclusive(x_1089)) {
 lean_ctor_release(x_1089, 0);
 lean_ctor_release(x_1089, 1);
 x_1121 = x_1089;
} else {
 lean_dec_ref(x_1089);
 x_1121 = lean_box(0);
}
if (lean_is_scalar(x_1121)) {
 x_1122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1122 = x_1121;
}
lean_ctor_set(x_1122, 0, x_1119);
lean_ctor_set(x_1122, 1, x_1120);
return x_1122;
}
}
else
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
lean_dec(x_1081);
x_1123 = lean_ctor_get(x_1084, 0);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_1084, 1);
lean_inc(x_1124);
if (lean_is_exclusive(x_1084)) {
 lean_ctor_release(x_1084, 0);
 lean_ctor_release(x_1084, 1);
 x_1125 = x_1084;
} else {
 lean_dec_ref(x_1084);
 x_1125 = lean_box(0);
}
if (lean_is_scalar(x_1125)) {
 x_1126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1126 = x_1125;
}
lean_ctor_set(x_1126, 0, x_1123);
lean_ctor_set(x_1126, 1, x_1124);
return x_1126;
}
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
lean_dec(x_1071);
x_1127 = lean_ctor_get(x_1077, 0);
lean_inc(x_1127);
x_1128 = lean_ctor_get(x_1077, 1);
lean_inc(x_1128);
if (lean_is_exclusive(x_1077)) {
 lean_ctor_release(x_1077, 0);
 lean_ctor_release(x_1077, 1);
 x_1129 = x_1077;
} else {
 lean_dec_ref(x_1077);
 x_1129 = lean_box(0);
}
if (lean_is_scalar(x_1129)) {
 x_1130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1130 = x_1129;
}
lean_ctor_set(x_1130, 0, x_1127);
lean_ctor_set(x_1130, 1, x_1128);
return x_1130;
}
}
else
{
lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; 
x_1131 = lean_ctor_get(x_1070, 0);
lean_inc(x_1131);
x_1132 = lean_ctor_get(x_1070, 1);
lean_inc(x_1132);
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 lean_ctor_release(x_1070, 1);
 x_1133 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1133 = lean_box(0);
}
if (lean_is_scalar(x_1133)) {
 x_1134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1134 = x_1133;
}
lean_ctor_set(x_1134, 0, x_1131);
lean_ctor_set(x_1134, 1, x_1132);
return x_1134;
}
}
else
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; 
lean_dec(x_1060);
x_1135 = lean_ctor_get(x_1066, 0);
lean_inc(x_1135);
x_1136 = lean_ctor_get(x_1066, 1);
lean_inc(x_1136);
if (lean_is_exclusive(x_1066)) {
 lean_ctor_release(x_1066, 0);
 lean_ctor_release(x_1066, 1);
 x_1137 = x_1066;
} else {
 lean_dec_ref(x_1066);
 x_1137 = lean_box(0);
}
if (lean_is_scalar(x_1137)) {
 x_1138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1138 = x_1137;
}
lean_ctor_set(x_1138, 0, x_1135);
lean_ctor_set(x_1138, 1, x_1136);
return x_1138;
}
}
else
{
lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; 
x_1139 = lean_ctor_get(x_1059, 0);
lean_inc(x_1139);
x_1140 = lean_ctor_get(x_1059, 1);
lean_inc(x_1140);
if (lean_is_exclusive(x_1059)) {
 lean_ctor_release(x_1059, 0);
 lean_ctor_release(x_1059, 1);
 x_1141 = x_1059;
} else {
 lean_dec_ref(x_1059);
 x_1141 = lean_box(0);
}
if (lean_is_scalar(x_1141)) {
 x_1142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1142 = x_1141;
}
lean_ctor_set(x_1142, 0, x_1139);
lean_ctor_set(x_1142, 1, x_1140);
return x_1142;
}
}
else
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; 
lean_dec(x_1049);
x_1143 = lean_ctor_get(x_1055, 0);
lean_inc(x_1143);
x_1144 = lean_ctor_get(x_1055, 1);
lean_inc(x_1144);
if (lean_is_exclusive(x_1055)) {
 lean_ctor_release(x_1055, 0);
 lean_ctor_release(x_1055, 1);
 x_1145 = x_1055;
} else {
 lean_dec_ref(x_1055);
 x_1145 = lean_box(0);
}
if (lean_is_scalar(x_1145)) {
 x_1146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1146 = x_1145;
}
lean_ctor_set(x_1146, 0, x_1143);
lean_ctor_set(x_1146, 1, x_1144);
return x_1146;
}
}
else
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1147 = lean_ctor_get(x_1048, 0);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1048, 1);
lean_inc(x_1148);
if (lean_is_exclusive(x_1048)) {
 lean_ctor_release(x_1048, 0);
 lean_ctor_release(x_1048, 1);
 x_1149 = x_1048;
} else {
 lean_dec_ref(x_1048);
 x_1149 = lean_box(0);
}
if (lean_is_scalar(x_1149)) {
 x_1150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1150 = x_1149;
}
lean_ctor_set(x_1150, 0, x_1147);
lean_ctor_set(x_1150, 1, x_1148);
return x_1150;
}
}
else
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; 
lean_dec(x_1040);
x_1151 = lean_ctor_get(x_1043, 0);
lean_inc(x_1151);
x_1152 = lean_ctor_get(x_1043, 1);
lean_inc(x_1152);
if (lean_is_exclusive(x_1043)) {
 lean_ctor_release(x_1043, 0);
 lean_ctor_release(x_1043, 1);
 x_1153 = x_1043;
} else {
 lean_dec_ref(x_1043);
 x_1153 = lean_box(0);
}
if (lean_is_scalar(x_1153)) {
 x_1154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1154 = x_1153;
}
lean_ctor_set(x_1154, 0, x_1151);
lean_ctor_set(x_1154, 1, x_1152);
return x_1154;
}
}
else
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
lean_dec(x_1033);
x_1155 = lean_ctor_get(x_1036, 0);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1036, 1);
lean_inc(x_1156);
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 lean_ctor_release(x_1036, 1);
 x_1157 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1157 = lean_box(0);
}
if (lean_is_scalar(x_1157)) {
 x_1158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1158 = x_1157;
}
lean_ctor_set(x_1158, 0, x_1155);
lean_ctor_set(x_1158, 1, x_1156);
return x_1158;
}
}
else
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; 
lean_dec(x_1026);
x_1159 = lean_ctor_get(x_1029, 0);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_1029, 1);
lean_inc(x_1160);
if (lean_is_exclusive(x_1029)) {
 lean_ctor_release(x_1029, 0);
 lean_ctor_release(x_1029, 1);
 x_1161 = x_1029;
} else {
 lean_dec_ref(x_1029);
 x_1161 = lean_box(0);
}
if (lean_is_scalar(x_1161)) {
 x_1162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1162 = x_1161;
}
lean_ctor_set(x_1162, 0, x_1159);
lean_ctor_set(x_1162, 1, x_1160);
return x_1162;
}
}
}
else
{
uint8_t x_1163; 
lean_dec(x_17);
x_1163 = !lean_is_exclusive(x_20);
if (x_1163 == 0)
{
return x_20;
}
else
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; 
x_1164 = lean_ctor_get(x_20, 0);
x_1165 = lean_ctor_get(x_20, 1);
lean_inc(x_1165);
lean_inc(x_1164);
lean_dec(x_20);
x_1166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1166, 0, x_1164);
lean_ctor_set(x_1166, 1, x_1165);
return x_1166;
}
}
}
else
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
x_1167 = lean_ctor_get(x_14, 1);
lean_inc(x_1167);
lean_dec(x_14);
x_1168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1168, 0, x_9);
lean_ctor_set(x_1168, 1, x_1167);
x_1169 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_1);
x_1170 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__4;
x_1171 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3;
lean_inc(x_1169);
x_1172 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1170, x_1171, x_1169, x_2, x_1168);
if (lean_obj_tag(x_1172) == 0)
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; 
x_1173 = lean_ctor_get(x_1172, 1);
lean_inc(x_1173);
if (lean_is_exclusive(x_1172)) {
 lean_ctor_release(x_1172, 0);
 lean_ctor_release(x_1172, 1);
 x_1174 = x_1172;
} else {
 lean_dec_ref(x_1172);
 x_1174 = lean_box(0);
}
if (lean_is_scalar(x_1174)) {
 x_1175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1175 = x_1174;
}
lean_ctor_set(x_1175, 0, x_9);
lean_ctor_set(x_1175, 1, x_1173);
x_1176 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__2(x_10, x_1169);
x_1177 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7;
x_1178 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6;
lean_inc(x_1176);
x_1179 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1177, x_1178, x_1176, x_2, x_1175);
if (lean_obj_tag(x_1179) == 0)
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1180 = lean_ctor_get(x_1179, 1);
lean_inc(x_1180);
if (lean_is_exclusive(x_1179)) {
 lean_ctor_release(x_1179, 0);
 lean_ctor_release(x_1179, 1);
 x_1181 = x_1179;
} else {
 lean_dec_ref(x_1179);
 x_1181 = lean_box(0);
}
if (lean_is_scalar(x_1181)) {
 x_1182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1182 = x_1181;
}
lean_ctor_set(x_1182, 0, x_9);
lean_ctor_set(x_1182, 1, x_1180);
x_1183 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(x_10, x_1176);
x_1184 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10;
x_1185 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
lean_inc(x_1183);
x_1186 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1184, x_1185, x_1183, x_2, x_1182);
if (lean_obj_tag(x_1186) == 0)
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; 
x_1187 = lean_ctor_get(x_1186, 1);
lean_inc(x_1187);
if (lean_is_exclusive(x_1186)) {
 lean_ctor_release(x_1186, 0);
 lean_ctor_release(x_1186, 1);
 x_1188 = x_1186;
} else {
 lean_dec_ref(x_1186);
 x_1188 = lean_box(0);
}
if (lean_is_scalar(x_1188)) {
 x_1189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1189 = x_1188;
}
lean_ctor_set(x_1189, 0, x_9);
lean_ctor_set(x_1189, 1, x_1187);
x_1190 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_10, x_1183);
x_1191 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
x_1192 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_inc(x_1190);
x_1193 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1191, x_1192, x_1190, x_2, x_1189);
if (lean_obj_tag(x_1193) == 0)
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; 
x_1194 = lean_ctor_get(x_1193, 1);
lean_inc(x_1194);
if (lean_is_exclusive(x_1193)) {
 lean_ctor_release(x_1193, 0);
 lean_ctor_release(x_1193, 1);
 x_1195 = x_1193;
} else {
 lean_dec_ref(x_1193);
 x_1195 = lean_box(0);
}
if (lean_is_scalar(x_1195)) {
 x_1196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1196 = x_1195;
}
lean_ctor_set(x_1196, 0, x_9);
lean_ctor_set(x_1196, 1, x_1194);
x_1197 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_1190);
x_1198 = l_Lean_IR_inferBorrow(x_1197, x_2, x_1196);
if (lean_obj_tag(x_1198) == 0)
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1198, 1);
lean_inc(x_1200);
if (lean_is_exclusive(x_1198)) {
 lean_ctor_release(x_1198, 0);
 lean_ctor_release(x_1198, 1);
 x_1201 = x_1198;
} else {
 lean_dec_ref(x_1198);
 x_1201 = lean_box(0);
}
if (lean_is_scalar(x_1201)) {
 x_1202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1202 = x_1201;
}
lean_ctor_set(x_1202, 0, x_9);
lean_ctor_set(x_1202, 1, x_1200);
x_1203 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_1204 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_1199);
x_1205 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1203, x_1204, x_1199, x_2, x_1202);
if (lean_obj_tag(x_1205) == 0)
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; 
x_1206 = lean_ctor_get(x_1205, 1);
lean_inc(x_1206);
if (lean_is_exclusive(x_1205)) {
 lean_ctor_release(x_1205, 0);
 lean_ctor_release(x_1205, 1);
 x_1207 = x_1205;
} else {
 lean_dec_ref(x_1205);
 x_1207 = lean_box(0);
}
if (lean_is_scalar(x_1207)) {
 x_1208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1208 = x_1207;
}
lean_ctor_set(x_1208, 0, x_9);
lean_ctor_set(x_1208, 1, x_1206);
x_1209 = l_Lean_IR_explicitBoxing(x_1199, x_2, x_1208);
if (lean_obj_tag(x_1209) == 0)
{
lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
x_1210 = lean_ctor_get(x_1209, 0);
lean_inc(x_1210);
x_1211 = lean_ctor_get(x_1209, 1);
lean_inc(x_1211);
if (lean_is_exclusive(x_1209)) {
 lean_ctor_release(x_1209, 0);
 lean_ctor_release(x_1209, 1);
 x_1212 = x_1209;
} else {
 lean_dec_ref(x_1209);
 x_1212 = lean_box(0);
}
if (lean_is_scalar(x_1212)) {
 x_1213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1213 = x_1212;
}
lean_ctor_set(x_1213, 0, x_9);
lean_ctor_set(x_1213, 1, x_1211);
x_1214 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_1215 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_1210);
x_1216 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1214, x_1215, x_1210, x_2, x_1213);
if (lean_obj_tag(x_1216) == 0)
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; 
x_1217 = lean_ctor_get(x_1216, 1);
lean_inc(x_1217);
if (lean_is_exclusive(x_1216)) {
 lean_ctor_release(x_1216, 0);
 lean_ctor_release(x_1216, 1);
 x_1218 = x_1216;
} else {
 lean_dec_ref(x_1216);
 x_1218 = lean_box(0);
}
if (lean_is_scalar(x_1218)) {
 x_1219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1219 = x_1218;
}
lean_ctor_set(x_1219, 0, x_9);
lean_ctor_set(x_1219, 1, x_1217);
x_1220 = l_Lean_IR_explicitRC(x_1210, x_2, x_1219);
if (lean_obj_tag(x_1220) == 0)
{
lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; 
x_1221 = lean_ctor_get(x_1220, 0);
lean_inc(x_1221);
x_1222 = lean_ctor_get(x_1220, 1);
lean_inc(x_1222);
if (lean_is_exclusive(x_1220)) {
 lean_ctor_release(x_1220, 0);
 lean_ctor_release(x_1220, 1);
 x_1223 = x_1220;
} else {
 lean_dec_ref(x_1220);
 x_1223 = lean_box(0);
}
if (lean_is_scalar(x_1223)) {
 x_1224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1224 = x_1223;
}
lean_ctor_set(x_1224, 0, x_9);
lean_ctor_set(x_1224, 1, x_1222);
x_1225 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_1226 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_1221);
x_1227 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1225, x_1226, x_1221, x_2, x_1224);
if (lean_obj_tag(x_1227) == 0)
{
lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; 
x_1228 = lean_ctor_get(x_1227, 1);
lean_inc(x_1228);
if (lean_is_exclusive(x_1227)) {
 lean_ctor_release(x_1227, 0);
 lean_ctor_release(x_1227, 1);
 x_1229 = x_1227;
} else {
 lean_dec_ref(x_1227);
 x_1229 = lean_box(0);
}
if (lean_is_scalar(x_1229)) {
 x_1230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1230 = x_1229;
}
lean_ctor_set(x_1230, 0, x_9);
lean_ctor_set(x_1230, 1, x_1228);
x_1231 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_1221);
x_1232 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_1233 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_1231);
x_1234 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1232, x_1233, x_1231, x_2, x_1230);
if (lean_obj_tag(x_1234) == 0)
{
lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; 
x_1235 = lean_ctor_get(x_1234, 1);
lean_inc(x_1235);
if (lean_is_exclusive(x_1234)) {
 lean_ctor_release(x_1234, 0);
 lean_ctor_release(x_1234, 1);
 x_1236 = x_1234;
} else {
 lean_dec_ref(x_1234);
 x_1236 = lean_box(0);
}
if (lean_is_scalar(x_1236)) {
 x_1237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1237 = x_1236;
}
lean_ctor_set(x_1237, 0, x_9);
lean_ctor_set(x_1237, 1, x_1235);
x_1238 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_1231);
lean_inc(x_1238);
x_1239 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1170, x_1171, x_1238, x_2, x_1237);
if (lean_obj_tag(x_1239) == 0)
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; 
x_1240 = lean_ctor_get(x_1239, 1);
lean_inc(x_1240);
if (lean_is_exclusive(x_1239)) {
 lean_ctor_release(x_1239, 0);
 lean_ctor_release(x_1239, 1);
 x_1241 = x_1239;
} else {
 lean_dec_ref(x_1239);
 x_1241 = lean_box(0);
}
if (lean_is_scalar(x_1241)) {
 x_1242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1242 = x_1241;
}
lean_ctor_set(x_1242, 0, x_9);
lean_ctor_set(x_1242, 1, x_1240);
x_1243 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_1244 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_1238);
x_1245 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1243, x_1244, x_1238, x_2, x_1242);
if (lean_obj_tag(x_1245) == 0)
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; 
x_1246 = lean_ctor_get(x_1245, 1);
lean_inc(x_1246);
if (lean_is_exclusive(x_1245)) {
 lean_ctor_release(x_1245, 0);
 lean_ctor_release(x_1245, 1);
 x_1247 = x_1245;
} else {
 lean_dec_ref(x_1245);
 x_1247 = lean_box(0);
}
if (lean_is_scalar(x_1247)) {
 x_1248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1248 = x_1247;
}
lean_ctor_set(x_1248, 0, x_9);
lean_ctor_set(x_1248, 1, x_1246);
lean_inc(x_1238);
x_1249 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1238, x_1238, x_10, x_2, x_1248);
if (lean_obj_tag(x_1249) == 0)
{
lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; 
x_1250 = lean_ctor_get(x_1249, 1);
lean_inc(x_1250);
if (lean_is_exclusive(x_1249)) {
 lean_ctor_release(x_1249, 0);
 lean_ctor_release(x_1249, 1);
 x_1251 = x_1249;
} else {
 lean_dec_ref(x_1249);
 x_1251 = lean_box(0);
}
if (lean_is_scalar(x_1251)) {
 x_1252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1252 = x_1251;
}
lean_ctor_set(x_1252, 0, x_9);
lean_ctor_set(x_1252, 1, x_1250);
x_1253 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_1238, x_10, x_2, x_1252);
lean_dec(x_1238);
if (lean_obj_tag(x_1253) == 0)
{
lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
x_1254 = lean_ctor_get(x_1253, 1);
lean_inc(x_1254);
if (lean_is_exclusive(x_1253)) {
 lean_ctor_release(x_1253, 0);
 lean_ctor_release(x_1253, 1);
 x_1255 = x_1253;
} else {
 lean_dec_ref(x_1253);
 x_1255 = lean_box(0);
}
if (lean_is_scalar(x_1255)) {
 x_1256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1256 = x_1255;
}
lean_ctor_set(x_1256, 0, x_9);
lean_ctor_set(x_1256, 1, x_1254);
return x_1256;
}
else
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
x_1257 = lean_ctor_get(x_1253, 0);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_1253, 1);
lean_inc(x_1258);
if (lean_is_exclusive(x_1253)) {
 lean_ctor_release(x_1253, 0);
 lean_ctor_release(x_1253, 1);
 x_1259 = x_1253;
} else {
 lean_dec_ref(x_1253);
 x_1259 = lean_box(0);
}
if (lean_is_scalar(x_1259)) {
 x_1260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1260 = x_1259;
}
lean_ctor_set(x_1260, 0, x_1257);
lean_ctor_set(x_1260, 1, x_1258);
return x_1260;
}
}
else
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
lean_dec(x_1238);
x_1261 = lean_ctor_get(x_1249, 0);
lean_inc(x_1261);
x_1262 = lean_ctor_get(x_1249, 1);
lean_inc(x_1262);
if (lean_is_exclusive(x_1249)) {
 lean_ctor_release(x_1249, 0);
 lean_ctor_release(x_1249, 1);
 x_1263 = x_1249;
} else {
 lean_dec_ref(x_1249);
 x_1263 = lean_box(0);
}
if (lean_is_scalar(x_1263)) {
 x_1264 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1264 = x_1263;
}
lean_ctor_set(x_1264, 0, x_1261);
lean_ctor_set(x_1264, 1, x_1262);
return x_1264;
}
}
else
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; 
lean_dec(x_1238);
x_1265 = lean_ctor_get(x_1245, 0);
lean_inc(x_1265);
x_1266 = lean_ctor_get(x_1245, 1);
lean_inc(x_1266);
if (lean_is_exclusive(x_1245)) {
 lean_ctor_release(x_1245, 0);
 lean_ctor_release(x_1245, 1);
 x_1267 = x_1245;
} else {
 lean_dec_ref(x_1245);
 x_1267 = lean_box(0);
}
if (lean_is_scalar(x_1267)) {
 x_1268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1268 = x_1267;
}
lean_ctor_set(x_1268, 0, x_1265);
lean_ctor_set(x_1268, 1, x_1266);
return x_1268;
}
}
else
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
lean_dec(x_1238);
x_1269 = lean_ctor_get(x_1239, 0);
lean_inc(x_1269);
x_1270 = lean_ctor_get(x_1239, 1);
lean_inc(x_1270);
if (lean_is_exclusive(x_1239)) {
 lean_ctor_release(x_1239, 0);
 lean_ctor_release(x_1239, 1);
 x_1271 = x_1239;
} else {
 lean_dec_ref(x_1239);
 x_1271 = lean_box(0);
}
if (lean_is_scalar(x_1271)) {
 x_1272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1272 = x_1271;
}
lean_ctor_set(x_1272, 0, x_1269);
lean_ctor_set(x_1272, 1, x_1270);
return x_1272;
}
}
else
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; 
lean_dec(x_1231);
x_1273 = lean_ctor_get(x_1234, 0);
lean_inc(x_1273);
x_1274 = lean_ctor_get(x_1234, 1);
lean_inc(x_1274);
if (lean_is_exclusive(x_1234)) {
 lean_ctor_release(x_1234, 0);
 lean_ctor_release(x_1234, 1);
 x_1275 = x_1234;
} else {
 lean_dec_ref(x_1234);
 x_1275 = lean_box(0);
}
if (lean_is_scalar(x_1275)) {
 x_1276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1276 = x_1275;
}
lean_ctor_set(x_1276, 0, x_1273);
lean_ctor_set(x_1276, 1, x_1274);
return x_1276;
}
}
else
{
lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; 
lean_dec(x_1221);
x_1277 = lean_ctor_get(x_1227, 0);
lean_inc(x_1277);
x_1278 = lean_ctor_get(x_1227, 1);
lean_inc(x_1278);
if (lean_is_exclusive(x_1227)) {
 lean_ctor_release(x_1227, 0);
 lean_ctor_release(x_1227, 1);
 x_1279 = x_1227;
} else {
 lean_dec_ref(x_1227);
 x_1279 = lean_box(0);
}
if (lean_is_scalar(x_1279)) {
 x_1280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1280 = x_1279;
}
lean_ctor_set(x_1280, 0, x_1277);
lean_ctor_set(x_1280, 1, x_1278);
return x_1280;
}
}
else
{
lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; 
x_1281 = lean_ctor_get(x_1220, 0);
lean_inc(x_1281);
x_1282 = lean_ctor_get(x_1220, 1);
lean_inc(x_1282);
if (lean_is_exclusive(x_1220)) {
 lean_ctor_release(x_1220, 0);
 lean_ctor_release(x_1220, 1);
 x_1283 = x_1220;
} else {
 lean_dec_ref(x_1220);
 x_1283 = lean_box(0);
}
if (lean_is_scalar(x_1283)) {
 x_1284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1284 = x_1283;
}
lean_ctor_set(x_1284, 0, x_1281);
lean_ctor_set(x_1284, 1, x_1282);
return x_1284;
}
}
else
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; 
lean_dec(x_1210);
x_1285 = lean_ctor_get(x_1216, 0);
lean_inc(x_1285);
x_1286 = lean_ctor_get(x_1216, 1);
lean_inc(x_1286);
if (lean_is_exclusive(x_1216)) {
 lean_ctor_release(x_1216, 0);
 lean_ctor_release(x_1216, 1);
 x_1287 = x_1216;
} else {
 lean_dec_ref(x_1216);
 x_1287 = lean_box(0);
}
if (lean_is_scalar(x_1287)) {
 x_1288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1288 = x_1287;
}
lean_ctor_set(x_1288, 0, x_1285);
lean_ctor_set(x_1288, 1, x_1286);
return x_1288;
}
}
else
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; 
x_1289 = lean_ctor_get(x_1209, 0);
lean_inc(x_1289);
x_1290 = lean_ctor_get(x_1209, 1);
lean_inc(x_1290);
if (lean_is_exclusive(x_1209)) {
 lean_ctor_release(x_1209, 0);
 lean_ctor_release(x_1209, 1);
 x_1291 = x_1209;
} else {
 lean_dec_ref(x_1209);
 x_1291 = lean_box(0);
}
if (lean_is_scalar(x_1291)) {
 x_1292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1292 = x_1291;
}
lean_ctor_set(x_1292, 0, x_1289);
lean_ctor_set(x_1292, 1, x_1290);
return x_1292;
}
}
else
{
lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; 
lean_dec(x_1199);
x_1293 = lean_ctor_get(x_1205, 0);
lean_inc(x_1293);
x_1294 = lean_ctor_get(x_1205, 1);
lean_inc(x_1294);
if (lean_is_exclusive(x_1205)) {
 lean_ctor_release(x_1205, 0);
 lean_ctor_release(x_1205, 1);
 x_1295 = x_1205;
} else {
 lean_dec_ref(x_1205);
 x_1295 = lean_box(0);
}
if (lean_is_scalar(x_1295)) {
 x_1296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1296 = x_1295;
}
lean_ctor_set(x_1296, 0, x_1293);
lean_ctor_set(x_1296, 1, x_1294);
return x_1296;
}
}
else
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; 
x_1297 = lean_ctor_get(x_1198, 0);
lean_inc(x_1297);
x_1298 = lean_ctor_get(x_1198, 1);
lean_inc(x_1298);
if (lean_is_exclusive(x_1198)) {
 lean_ctor_release(x_1198, 0);
 lean_ctor_release(x_1198, 1);
 x_1299 = x_1198;
} else {
 lean_dec_ref(x_1198);
 x_1299 = lean_box(0);
}
if (lean_is_scalar(x_1299)) {
 x_1300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1300 = x_1299;
}
lean_ctor_set(x_1300, 0, x_1297);
lean_ctor_set(x_1300, 1, x_1298);
return x_1300;
}
}
else
{
lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; 
lean_dec(x_1190);
x_1301 = lean_ctor_get(x_1193, 0);
lean_inc(x_1301);
x_1302 = lean_ctor_get(x_1193, 1);
lean_inc(x_1302);
if (lean_is_exclusive(x_1193)) {
 lean_ctor_release(x_1193, 0);
 lean_ctor_release(x_1193, 1);
 x_1303 = x_1193;
} else {
 lean_dec_ref(x_1193);
 x_1303 = lean_box(0);
}
if (lean_is_scalar(x_1303)) {
 x_1304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1304 = x_1303;
}
lean_ctor_set(x_1304, 0, x_1301);
lean_ctor_set(x_1304, 1, x_1302);
return x_1304;
}
}
else
{
lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; 
lean_dec(x_1183);
x_1305 = lean_ctor_get(x_1186, 0);
lean_inc(x_1305);
x_1306 = lean_ctor_get(x_1186, 1);
lean_inc(x_1306);
if (lean_is_exclusive(x_1186)) {
 lean_ctor_release(x_1186, 0);
 lean_ctor_release(x_1186, 1);
 x_1307 = x_1186;
} else {
 lean_dec_ref(x_1186);
 x_1307 = lean_box(0);
}
if (lean_is_scalar(x_1307)) {
 x_1308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1308 = x_1307;
}
lean_ctor_set(x_1308, 0, x_1305);
lean_ctor_set(x_1308, 1, x_1306);
return x_1308;
}
}
else
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; 
lean_dec(x_1176);
x_1309 = lean_ctor_get(x_1179, 0);
lean_inc(x_1309);
x_1310 = lean_ctor_get(x_1179, 1);
lean_inc(x_1310);
if (lean_is_exclusive(x_1179)) {
 lean_ctor_release(x_1179, 0);
 lean_ctor_release(x_1179, 1);
 x_1311 = x_1179;
} else {
 lean_dec_ref(x_1179);
 x_1311 = lean_box(0);
}
if (lean_is_scalar(x_1311)) {
 x_1312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1312 = x_1311;
}
lean_ctor_set(x_1312, 0, x_1309);
lean_ctor_set(x_1312, 1, x_1310);
return x_1312;
}
}
else
{
lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; 
lean_dec(x_1169);
x_1313 = lean_ctor_get(x_1172, 0);
lean_inc(x_1313);
x_1314 = lean_ctor_get(x_1172, 1);
lean_inc(x_1314);
if (lean_is_exclusive(x_1172)) {
 lean_ctor_release(x_1172, 0);
 lean_ctor_release(x_1172, 1);
 x_1315 = x_1172;
} else {
 lean_dec_ref(x_1172);
 x_1315 = lean_box(0);
}
if (lean_is_scalar(x_1315)) {
 x_1316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1316 = x_1315;
}
lean_ctor_set(x_1316, 0, x_1313);
lean_ctor_set(x_1316, 1, x_1314);
return x_1316;
}
}
}
else
{
uint8_t x_1317; 
lean_dec(x_1);
x_1317 = !lean_is_exclusive(x_14);
if (x_1317 == 0)
{
return x_14;
}
else
{
lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; 
x_1318 = lean_ctor_get(x_14, 0);
x_1319 = lean_ctor_get(x_14, 1);
lean_inc(x_1319);
lean_inc(x_1318);
lean_dec(x_14);
x_1320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1320, 0, x_1318);
lean_ctor_set(x_1320, 1, x_1319);
return x_1320;
}
}
}
else
{
lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; 
x_1321 = lean_ctor_get(x_11, 1);
lean_inc(x_1321);
lean_dec(x_11);
x_1322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1322, 0, x_9);
lean_ctor_set(x_1322, 1, x_1321);
lean_inc(x_1);
x_1323 = l_Lean_IR_inferCtorSummaries(x_1, x_2, x_1322);
if (lean_obj_tag(x_1323) == 0)
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; 
x_1324 = lean_ctor_get(x_1323, 1);
lean_inc(x_1324);
if (lean_is_exclusive(x_1323)) {
 lean_ctor_release(x_1323, 0);
 lean_ctor_release(x_1323, 1);
 x_1325 = x_1323;
} else {
 lean_dec_ref(x_1323);
 x_1325 = lean_box(0);
}
if (lean_is_scalar(x_1325)) {
 x_1326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1326 = x_1325;
}
lean_ctor_set(x_1326, 0, x_9);
lean_ctor_set(x_1326, 1, x_1324);
x_1327 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_1);
x_1328 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__4;
x_1329 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3;
lean_inc(x_1327);
x_1330 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1328, x_1329, x_1327, x_2, x_1326);
if (lean_obj_tag(x_1330) == 0)
{
lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; 
x_1331 = lean_ctor_get(x_1330, 1);
lean_inc(x_1331);
if (lean_is_exclusive(x_1330)) {
 lean_ctor_release(x_1330, 0);
 lean_ctor_release(x_1330, 1);
 x_1332 = x_1330;
} else {
 lean_dec_ref(x_1330);
 x_1332 = lean_box(0);
}
if (lean_is_scalar(x_1332)) {
 x_1333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1333 = x_1332;
}
lean_ctor_set(x_1333, 0, x_9);
lean_ctor_set(x_1333, 1, x_1331);
x_1334 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__2(x_10, x_1327);
x_1335 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7;
x_1336 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6;
lean_inc(x_1334);
x_1337 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1335, x_1336, x_1334, x_2, x_1333);
if (lean_obj_tag(x_1337) == 0)
{
lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
x_1338 = lean_ctor_get(x_1337, 1);
lean_inc(x_1338);
if (lean_is_exclusive(x_1337)) {
 lean_ctor_release(x_1337, 0);
 lean_ctor_release(x_1337, 1);
 x_1339 = x_1337;
} else {
 lean_dec_ref(x_1337);
 x_1339 = lean_box(0);
}
if (lean_is_scalar(x_1339)) {
 x_1340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1340 = x_1339;
}
lean_ctor_set(x_1340, 0, x_9);
lean_ctor_set(x_1340, 1, x_1338);
x_1341 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(x_10, x_1334);
x_1342 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10;
x_1343 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
lean_inc(x_1341);
x_1344 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1342, x_1343, x_1341, x_2, x_1340);
if (lean_obj_tag(x_1344) == 0)
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; 
x_1345 = lean_ctor_get(x_1344, 1);
lean_inc(x_1345);
if (lean_is_exclusive(x_1344)) {
 lean_ctor_release(x_1344, 0);
 lean_ctor_release(x_1344, 1);
 x_1346 = x_1344;
} else {
 lean_dec_ref(x_1344);
 x_1346 = lean_box(0);
}
if (lean_is_scalar(x_1346)) {
 x_1347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1347 = x_1346;
}
lean_ctor_set(x_1347, 0, x_9);
lean_ctor_set(x_1347, 1, x_1345);
x_1348 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_10, x_1341);
x_1349 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
x_1350 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_inc(x_1348);
x_1351 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1349, x_1350, x_1348, x_2, x_1347);
if (lean_obj_tag(x_1351) == 0)
{
lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; 
x_1352 = lean_ctor_get(x_1351, 1);
lean_inc(x_1352);
if (lean_is_exclusive(x_1351)) {
 lean_ctor_release(x_1351, 0);
 lean_ctor_release(x_1351, 1);
 x_1353 = x_1351;
} else {
 lean_dec_ref(x_1351);
 x_1353 = lean_box(0);
}
if (lean_is_scalar(x_1353)) {
 x_1354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1354 = x_1353;
}
lean_ctor_set(x_1354, 0, x_9);
lean_ctor_set(x_1354, 1, x_1352);
x_1355 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_10, x_1348);
x_1356 = l_Lean_IR_inferBorrow(x_1355, x_2, x_1354);
if (lean_obj_tag(x_1356) == 0)
{
lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
x_1357 = lean_ctor_get(x_1356, 0);
lean_inc(x_1357);
x_1358 = lean_ctor_get(x_1356, 1);
lean_inc(x_1358);
if (lean_is_exclusive(x_1356)) {
 lean_ctor_release(x_1356, 0);
 lean_ctor_release(x_1356, 1);
 x_1359 = x_1356;
} else {
 lean_dec_ref(x_1356);
 x_1359 = lean_box(0);
}
if (lean_is_scalar(x_1359)) {
 x_1360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1360 = x_1359;
}
lean_ctor_set(x_1360, 0, x_9);
lean_ctor_set(x_1360, 1, x_1358);
x_1361 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_1362 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_1357);
x_1363 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1361, x_1362, x_1357, x_2, x_1360);
if (lean_obj_tag(x_1363) == 0)
{
lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; 
x_1364 = lean_ctor_get(x_1363, 1);
lean_inc(x_1364);
if (lean_is_exclusive(x_1363)) {
 lean_ctor_release(x_1363, 0);
 lean_ctor_release(x_1363, 1);
 x_1365 = x_1363;
} else {
 lean_dec_ref(x_1363);
 x_1365 = lean_box(0);
}
if (lean_is_scalar(x_1365)) {
 x_1366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1366 = x_1365;
}
lean_ctor_set(x_1366, 0, x_9);
lean_ctor_set(x_1366, 1, x_1364);
x_1367 = l_Lean_IR_explicitBoxing(x_1357, x_2, x_1366);
if (lean_obj_tag(x_1367) == 0)
{
lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
x_1368 = lean_ctor_get(x_1367, 0);
lean_inc(x_1368);
x_1369 = lean_ctor_get(x_1367, 1);
lean_inc(x_1369);
if (lean_is_exclusive(x_1367)) {
 lean_ctor_release(x_1367, 0);
 lean_ctor_release(x_1367, 1);
 x_1370 = x_1367;
} else {
 lean_dec_ref(x_1367);
 x_1370 = lean_box(0);
}
if (lean_is_scalar(x_1370)) {
 x_1371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1371 = x_1370;
}
lean_ctor_set(x_1371, 0, x_9);
lean_ctor_set(x_1371, 1, x_1369);
x_1372 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_1373 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_1368);
x_1374 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1372, x_1373, x_1368, x_2, x_1371);
if (lean_obj_tag(x_1374) == 0)
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; 
x_1375 = lean_ctor_get(x_1374, 1);
lean_inc(x_1375);
if (lean_is_exclusive(x_1374)) {
 lean_ctor_release(x_1374, 0);
 lean_ctor_release(x_1374, 1);
 x_1376 = x_1374;
} else {
 lean_dec_ref(x_1374);
 x_1376 = lean_box(0);
}
if (lean_is_scalar(x_1376)) {
 x_1377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1377 = x_1376;
}
lean_ctor_set(x_1377, 0, x_9);
lean_ctor_set(x_1377, 1, x_1375);
x_1378 = l_Lean_IR_explicitRC(x_1368, x_2, x_1377);
if (lean_obj_tag(x_1378) == 0)
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; 
x_1379 = lean_ctor_get(x_1378, 0);
lean_inc(x_1379);
x_1380 = lean_ctor_get(x_1378, 1);
lean_inc(x_1380);
if (lean_is_exclusive(x_1378)) {
 lean_ctor_release(x_1378, 0);
 lean_ctor_release(x_1378, 1);
 x_1381 = x_1378;
} else {
 lean_dec_ref(x_1378);
 x_1381 = lean_box(0);
}
if (lean_is_scalar(x_1381)) {
 x_1382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1382 = x_1381;
}
lean_ctor_set(x_1382, 0, x_9);
lean_ctor_set(x_1382, 1, x_1380);
x_1383 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_1384 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_1379);
x_1385 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1383, x_1384, x_1379, x_2, x_1382);
if (lean_obj_tag(x_1385) == 0)
{
lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; 
x_1386 = lean_ctor_get(x_1385, 1);
lean_inc(x_1386);
if (lean_is_exclusive(x_1385)) {
 lean_ctor_release(x_1385, 0);
 lean_ctor_release(x_1385, 1);
 x_1387 = x_1385;
} else {
 lean_dec_ref(x_1385);
 x_1387 = lean_box(0);
}
if (lean_is_scalar(x_1387)) {
 x_1388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1388 = x_1387;
}
lean_ctor_set(x_1388, 0, x_9);
lean_ctor_set(x_1388, 1, x_1386);
x_1389 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_1379);
x_1390 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_1391 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_1389);
x_1392 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1390, x_1391, x_1389, x_2, x_1388);
if (lean_obj_tag(x_1392) == 0)
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; 
x_1393 = lean_ctor_get(x_1392, 1);
lean_inc(x_1393);
if (lean_is_exclusive(x_1392)) {
 lean_ctor_release(x_1392, 0);
 lean_ctor_release(x_1392, 1);
 x_1394 = x_1392;
} else {
 lean_dec_ref(x_1392);
 x_1394 = lean_box(0);
}
if (lean_is_scalar(x_1394)) {
 x_1395 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1395 = x_1394;
}
lean_ctor_set(x_1395, 0, x_9);
lean_ctor_set(x_1395, 1, x_1393);
x_1396 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_1389);
lean_inc(x_1396);
x_1397 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1328, x_1329, x_1396, x_2, x_1395);
if (lean_obj_tag(x_1397) == 0)
{
lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1398 = lean_ctor_get(x_1397, 1);
lean_inc(x_1398);
if (lean_is_exclusive(x_1397)) {
 lean_ctor_release(x_1397, 0);
 lean_ctor_release(x_1397, 1);
 x_1399 = x_1397;
} else {
 lean_dec_ref(x_1397);
 x_1399 = lean_box(0);
}
if (lean_is_scalar(x_1399)) {
 x_1400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1400 = x_1399;
}
lean_ctor_set(x_1400, 0, x_9);
lean_ctor_set(x_1400, 1, x_1398);
x_1401 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_1402 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_1396);
x_1403 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1401, x_1402, x_1396, x_2, x_1400);
if (lean_obj_tag(x_1403) == 0)
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; 
x_1404 = lean_ctor_get(x_1403, 1);
lean_inc(x_1404);
if (lean_is_exclusive(x_1403)) {
 lean_ctor_release(x_1403, 0);
 lean_ctor_release(x_1403, 1);
 x_1405 = x_1403;
} else {
 lean_dec_ref(x_1403);
 x_1405 = lean_box(0);
}
if (lean_is_scalar(x_1405)) {
 x_1406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1406 = x_1405;
}
lean_ctor_set(x_1406, 0, x_9);
lean_ctor_set(x_1406, 1, x_1404);
lean_inc(x_1396);
x_1407 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1396, x_1396, x_10, x_2, x_1406);
if (lean_obj_tag(x_1407) == 0)
{
lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; 
x_1408 = lean_ctor_get(x_1407, 1);
lean_inc(x_1408);
if (lean_is_exclusive(x_1407)) {
 lean_ctor_release(x_1407, 0);
 lean_ctor_release(x_1407, 1);
 x_1409 = x_1407;
} else {
 lean_dec_ref(x_1407);
 x_1409 = lean_box(0);
}
if (lean_is_scalar(x_1409)) {
 x_1410 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1410 = x_1409;
}
lean_ctor_set(x_1410, 0, x_9);
lean_ctor_set(x_1410, 1, x_1408);
x_1411 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_1396, x_10, x_2, x_1410);
lean_dec(x_1396);
if (lean_obj_tag(x_1411) == 0)
{
lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; 
x_1412 = lean_ctor_get(x_1411, 1);
lean_inc(x_1412);
if (lean_is_exclusive(x_1411)) {
 lean_ctor_release(x_1411, 0);
 lean_ctor_release(x_1411, 1);
 x_1413 = x_1411;
} else {
 lean_dec_ref(x_1411);
 x_1413 = lean_box(0);
}
if (lean_is_scalar(x_1413)) {
 x_1414 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1414 = x_1413;
}
lean_ctor_set(x_1414, 0, x_9);
lean_ctor_set(x_1414, 1, x_1412);
return x_1414;
}
else
{
lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; 
x_1415 = lean_ctor_get(x_1411, 0);
lean_inc(x_1415);
x_1416 = lean_ctor_get(x_1411, 1);
lean_inc(x_1416);
if (lean_is_exclusive(x_1411)) {
 lean_ctor_release(x_1411, 0);
 lean_ctor_release(x_1411, 1);
 x_1417 = x_1411;
} else {
 lean_dec_ref(x_1411);
 x_1417 = lean_box(0);
}
if (lean_is_scalar(x_1417)) {
 x_1418 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1418 = x_1417;
}
lean_ctor_set(x_1418, 0, x_1415);
lean_ctor_set(x_1418, 1, x_1416);
return x_1418;
}
}
else
{
lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; 
lean_dec(x_1396);
x_1419 = lean_ctor_get(x_1407, 0);
lean_inc(x_1419);
x_1420 = lean_ctor_get(x_1407, 1);
lean_inc(x_1420);
if (lean_is_exclusive(x_1407)) {
 lean_ctor_release(x_1407, 0);
 lean_ctor_release(x_1407, 1);
 x_1421 = x_1407;
} else {
 lean_dec_ref(x_1407);
 x_1421 = lean_box(0);
}
if (lean_is_scalar(x_1421)) {
 x_1422 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1422 = x_1421;
}
lean_ctor_set(x_1422, 0, x_1419);
lean_ctor_set(x_1422, 1, x_1420);
return x_1422;
}
}
else
{
lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; 
lean_dec(x_1396);
x_1423 = lean_ctor_get(x_1403, 0);
lean_inc(x_1423);
x_1424 = lean_ctor_get(x_1403, 1);
lean_inc(x_1424);
if (lean_is_exclusive(x_1403)) {
 lean_ctor_release(x_1403, 0);
 lean_ctor_release(x_1403, 1);
 x_1425 = x_1403;
} else {
 lean_dec_ref(x_1403);
 x_1425 = lean_box(0);
}
if (lean_is_scalar(x_1425)) {
 x_1426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1426 = x_1425;
}
lean_ctor_set(x_1426, 0, x_1423);
lean_ctor_set(x_1426, 1, x_1424);
return x_1426;
}
}
else
{
lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; 
lean_dec(x_1396);
x_1427 = lean_ctor_get(x_1397, 0);
lean_inc(x_1427);
x_1428 = lean_ctor_get(x_1397, 1);
lean_inc(x_1428);
if (lean_is_exclusive(x_1397)) {
 lean_ctor_release(x_1397, 0);
 lean_ctor_release(x_1397, 1);
 x_1429 = x_1397;
} else {
 lean_dec_ref(x_1397);
 x_1429 = lean_box(0);
}
if (lean_is_scalar(x_1429)) {
 x_1430 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1430 = x_1429;
}
lean_ctor_set(x_1430, 0, x_1427);
lean_ctor_set(x_1430, 1, x_1428);
return x_1430;
}
}
else
{
lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; 
lean_dec(x_1389);
x_1431 = lean_ctor_get(x_1392, 0);
lean_inc(x_1431);
x_1432 = lean_ctor_get(x_1392, 1);
lean_inc(x_1432);
if (lean_is_exclusive(x_1392)) {
 lean_ctor_release(x_1392, 0);
 lean_ctor_release(x_1392, 1);
 x_1433 = x_1392;
} else {
 lean_dec_ref(x_1392);
 x_1433 = lean_box(0);
}
if (lean_is_scalar(x_1433)) {
 x_1434 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1434 = x_1433;
}
lean_ctor_set(x_1434, 0, x_1431);
lean_ctor_set(x_1434, 1, x_1432);
return x_1434;
}
}
else
{
lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; 
lean_dec(x_1379);
x_1435 = lean_ctor_get(x_1385, 0);
lean_inc(x_1435);
x_1436 = lean_ctor_get(x_1385, 1);
lean_inc(x_1436);
if (lean_is_exclusive(x_1385)) {
 lean_ctor_release(x_1385, 0);
 lean_ctor_release(x_1385, 1);
 x_1437 = x_1385;
} else {
 lean_dec_ref(x_1385);
 x_1437 = lean_box(0);
}
if (lean_is_scalar(x_1437)) {
 x_1438 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1438 = x_1437;
}
lean_ctor_set(x_1438, 0, x_1435);
lean_ctor_set(x_1438, 1, x_1436);
return x_1438;
}
}
else
{
lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; 
x_1439 = lean_ctor_get(x_1378, 0);
lean_inc(x_1439);
x_1440 = lean_ctor_get(x_1378, 1);
lean_inc(x_1440);
if (lean_is_exclusive(x_1378)) {
 lean_ctor_release(x_1378, 0);
 lean_ctor_release(x_1378, 1);
 x_1441 = x_1378;
} else {
 lean_dec_ref(x_1378);
 x_1441 = lean_box(0);
}
if (lean_is_scalar(x_1441)) {
 x_1442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1442 = x_1441;
}
lean_ctor_set(x_1442, 0, x_1439);
lean_ctor_set(x_1442, 1, x_1440);
return x_1442;
}
}
else
{
lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; 
lean_dec(x_1368);
x_1443 = lean_ctor_get(x_1374, 0);
lean_inc(x_1443);
x_1444 = lean_ctor_get(x_1374, 1);
lean_inc(x_1444);
if (lean_is_exclusive(x_1374)) {
 lean_ctor_release(x_1374, 0);
 lean_ctor_release(x_1374, 1);
 x_1445 = x_1374;
} else {
 lean_dec_ref(x_1374);
 x_1445 = lean_box(0);
}
if (lean_is_scalar(x_1445)) {
 x_1446 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1446 = x_1445;
}
lean_ctor_set(x_1446, 0, x_1443);
lean_ctor_set(x_1446, 1, x_1444);
return x_1446;
}
}
else
{
lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; 
x_1447 = lean_ctor_get(x_1367, 0);
lean_inc(x_1447);
x_1448 = lean_ctor_get(x_1367, 1);
lean_inc(x_1448);
if (lean_is_exclusive(x_1367)) {
 lean_ctor_release(x_1367, 0);
 lean_ctor_release(x_1367, 1);
 x_1449 = x_1367;
} else {
 lean_dec_ref(x_1367);
 x_1449 = lean_box(0);
}
if (lean_is_scalar(x_1449)) {
 x_1450 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1450 = x_1449;
}
lean_ctor_set(x_1450, 0, x_1447);
lean_ctor_set(x_1450, 1, x_1448);
return x_1450;
}
}
else
{
lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; 
lean_dec(x_1357);
x_1451 = lean_ctor_get(x_1363, 0);
lean_inc(x_1451);
x_1452 = lean_ctor_get(x_1363, 1);
lean_inc(x_1452);
if (lean_is_exclusive(x_1363)) {
 lean_ctor_release(x_1363, 0);
 lean_ctor_release(x_1363, 1);
 x_1453 = x_1363;
} else {
 lean_dec_ref(x_1363);
 x_1453 = lean_box(0);
}
if (lean_is_scalar(x_1453)) {
 x_1454 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1454 = x_1453;
}
lean_ctor_set(x_1454, 0, x_1451);
lean_ctor_set(x_1454, 1, x_1452);
return x_1454;
}
}
else
{
lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; 
x_1455 = lean_ctor_get(x_1356, 0);
lean_inc(x_1455);
x_1456 = lean_ctor_get(x_1356, 1);
lean_inc(x_1456);
if (lean_is_exclusive(x_1356)) {
 lean_ctor_release(x_1356, 0);
 lean_ctor_release(x_1356, 1);
 x_1457 = x_1356;
} else {
 lean_dec_ref(x_1356);
 x_1457 = lean_box(0);
}
if (lean_is_scalar(x_1457)) {
 x_1458 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1458 = x_1457;
}
lean_ctor_set(x_1458, 0, x_1455);
lean_ctor_set(x_1458, 1, x_1456);
return x_1458;
}
}
else
{
lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; 
lean_dec(x_1348);
x_1459 = lean_ctor_get(x_1351, 0);
lean_inc(x_1459);
x_1460 = lean_ctor_get(x_1351, 1);
lean_inc(x_1460);
if (lean_is_exclusive(x_1351)) {
 lean_ctor_release(x_1351, 0);
 lean_ctor_release(x_1351, 1);
 x_1461 = x_1351;
} else {
 lean_dec_ref(x_1351);
 x_1461 = lean_box(0);
}
if (lean_is_scalar(x_1461)) {
 x_1462 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1462 = x_1461;
}
lean_ctor_set(x_1462, 0, x_1459);
lean_ctor_set(x_1462, 1, x_1460);
return x_1462;
}
}
else
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; 
lean_dec(x_1341);
x_1463 = lean_ctor_get(x_1344, 0);
lean_inc(x_1463);
x_1464 = lean_ctor_get(x_1344, 1);
lean_inc(x_1464);
if (lean_is_exclusive(x_1344)) {
 lean_ctor_release(x_1344, 0);
 lean_ctor_release(x_1344, 1);
 x_1465 = x_1344;
} else {
 lean_dec_ref(x_1344);
 x_1465 = lean_box(0);
}
if (lean_is_scalar(x_1465)) {
 x_1466 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1466 = x_1465;
}
lean_ctor_set(x_1466, 0, x_1463);
lean_ctor_set(x_1466, 1, x_1464);
return x_1466;
}
}
else
{
lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; 
lean_dec(x_1334);
x_1467 = lean_ctor_get(x_1337, 0);
lean_inc(x_1467);
x_1468 = lean_ctor_get(x_1337, 1);
lean_inc(x_1468);
if (lean_is_exclusive(x_1337)) {
 lean_ctor_release(x_1337, 0);
 lean_ctor_release(x_1337, 1);
 x_1469 = x_1337;
} else {
 lean_dec_ref(x_1337);
 x_1469 = lean_box(0);
}
if (lean_is_scalar(x_1469)) {
 x_1470 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1470 = x_1469;
}
lean_ctor_set(x_1470, 0, x_1467);
lean_ctor_set(x_1470, 1, x_1468);
return x_1470;
}
}
else
{
lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; 
lean_dec(x_1327);
x_1471 = lean_ctor_get(x_1330, 0);
lean_inc(x_1471);
x_1472 = lean_ctor_get(x_1330, 1);
lean_inc(x_1472);
if (lean_is_exclusive(x_1330)) {
 lean_ctor_release(x_1330, 0);
 lean_ctor_release(x_1330, 1);
 x_1473 = x_1330;
} else {
 lean_dec_ref(x_1330);
 x_1473 = lean_box(0);
}
if (lean_is_scalar(x_1473)) {
 x_1474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1474 = x_1473;
}
lean_ctor_set(x_1474, 0, x_1471);
lean_ctor_set(x_1474, 1, x_1472);
return x_1474;
}
}
else
{
lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; 
lean_dec(x_1);
x_1475 = lean_ctor_get(x_1323, 0);
lean_inc(x_1475);
x_1476 = lean_ctor_get(x_1323, 1);
lean_inc(x_1476);
if (lean_is_exclusive(x_1323)) {
 lean_ctor_release(x_1323, 0);
 lean_ctor_release(x_1323, 1);
 x_1477 = x_1323;
} else {
 lean_dec_ref(x_1323);
 x_1477 = lean_box(0);
}
if (lean_is_scalar(x_1477)) {
 x_1478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1478 = x_1477;
}
lean_ctor_set(x_1478, 0, x_1475);
lean_ctor_set(x_1478, 1, x_1476);
return x_1478;
}
}
}
else
{
uint8_t x_1479; 
lean_dec(x_1);
x_1479 = !lean_is_exclusive(x_11);
if (x_1479 == 0)
{
return x_11;
}
else
{
lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; 
x_1480 = lean_ctor_get(x_11, 0);
x_1481 = lean_ctor_get(x_11, 1);
lean_inc(x_1481);
lean_inc(x_1480);
lean_dec(x_11);
x_1482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1482, 0, x_1480);
lean_ctor_set(x_1482, 1, x_1481);
return x_1482;
}
}
}
else
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; 
x_1483 = lean_ctor_get(x_6, 1);
lean_inc(x_1483);
lean_dec(x_6);
x_1484 = lean_box(0);
x_1485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1485, 0, x_1484);
lean_ctor_set(x_1485, 1, x_1483);
x_1486 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_1487 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1, x_1, x_1486, x_2, x_1485);
if (lean_obj_tag(x_1487) == 0)
{
lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; 
x_1488 = lean_ctor_get(x_1487, 1);
lean_inc(x_1488);
if (lean_is_exclusive(x_1487)) {
 lean_ctor_release(x_1487, 0);
 lean_ctor_release(x_1487, 1);
 x_1489 = x_1487;
} else {
 lean_dec_ref(x_1487);
 x_1489 = lean_box(0);
}
if (lean_is_scalar(x_1489)) {
 x_1490 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1490 = x_1489;
}
lean_ctor_set(x_1490, 0, x_1484);
lean_ctor_set(x_1490, 1, x_1488);
lean_inc(x_1);
x_1491 = l_Lean_IR_inferCtorSummaries(x_1, x_2, x_1490);
if (lean_obj_tag(x_1491) == 0)
{
lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; 
x_1492 = lean_ctor_get(x_1491, 1);
lean_inc(x_1492);
if (lean_is_exclusive(x_1491)) {
 lean_ctor_release(x_1491, 0);
 lean_ctor_release(x_1491, 1);
 x_1493 = x_1491;
} else {
 lean_dec_ref(x_1491);
 x_1493 = lean_box(0);
}
if (lean_is_scalar(x_1493)) {
 x_1494 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1494 = x_1493;
}
lean_ctor_set(x_1494, 0, x_1484);
lean_ctor_set(x_1494, 1, x_1492);
x_1495 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_1486, x_1);
x_1496 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__4;
x_1497 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3;
lean_inc(x_1495);
x_1498 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1496, x_1497, x_1495, x_2, x_1494);
if (lean_obj_tag(x_1498) == 0)
{
lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; 
x_1499 = lean_ctor_get(x_1498, 1);
lean_inc(x_1499);
if (lean_is_exclusive(x_1498)) {
 lean_ctor_release(x_1498, 0);
 lean_ctor_release(x_1498, 1);
 x_1500 = x_1498;
} else {
 lean_dec_ref(x_1498);
 x_1500 = lean_box(0);
}
if (lean_is_scalar(x_1500)) {
 x_1501 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1501 = x_1500;
}
lean_ctor_set(x_1501, 0, x_1484);
lean_ctor_set(x_1501, 1, x_1499);
x_1502 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__2(x_1486, x_1495);
x_1503 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7;
x_1504 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6;
lean_inc(x_1502);
x_1505 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1503, x_1504, x_1502, x_2, x_1501);
if (lean_obj_tag(x_1505) == 0)
{
lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; 
x_1506 = lean_ctor_get(x_1505, 1);
lean_inc(x_1506);
if (lean_is_exclusive(x_1505)) {
 lean_ctor_release(x_1505, 0);
 lean_ctor_release(x_1505, 1);
 x_1507 = x_1505;
} else {
 lean_dec_ref(x_1505);
 x_1507 = lean_box(0);
}
if (lean_is_scalar(x_1507)) {
 x_1508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1508 = x_1507;
}
lean_ctor_set(x_1508, 0, x_1484);
lean_ctor_set(x_1508, 1, x_1506);
x_1509 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(x_1486, x_1502);
x_1510 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10;
x_1511 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
lean_inc(x_1509);
x_1512 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1510, x_1511, x_1509, x_2, x_1508);
if (lean_obj_tag(x_1512) == 0)
{
lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; 
x_1513 = lean_ctor_get(x_1512, 1);
lean_inc(x_1513);
if (lean_is_exclusive(x_1512)) {
 lean_ctor_release(x_1512, 0);
 lean_ctor_release(x_1512, 1);
 x_1514 = x_1512;
} else {
 lean_dec_ref(x_1512);
 x_1514 = lean_box(0);
}
if (lean_is_scalar(x_1514)) {
 x_1515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1515 = x_1514;
}
lean_ctor_set(x_1515, 0, x_1484);
lean_ctor_set(x_1515, 1, x_1513);
x_1516 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_1486, x_1509);
x_1517 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
x_1518 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_inc(x_1516);
x_1519 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1517, x_1518, x_1516, x_2, x_1515);
if (lean_obj_tag(x_1519) == 0)
{
lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; 
x_1520 = lean_ctor_get(x_1519, 1);
lean_inc(x_1520);
if (lean_is_exclusive(x_1519)) {
 lean_ctor_release(x_1519, 0);
 lean_ctor_release(x_1519, 1);
 x_1521 = x_1519;
} else {
 lean_dec_ref(x_1519);
 x_1521 = lean_box(0);
}
if (lean_is_scalar(x_1521)) {
 x_1522 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1522 = x_1521;
}
lean_ctor_set(x_1522, 0, x_1484);
lean_ctor_set(x_1522, 1, x_1520);
x_1523 = l_Array_ummapAux___main___at_Lean_IR_inferBorrow___spec__1(x_1486, x_1516);
x_1524 = l_Lean_IR_inferBorrow(x_1523, x_2, x_1522);
if (lean_obj_tag(x_1524) == 0)
{
lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; 
x_1525 = lean_ctor_get(x_1524, 0);
lean_inc(x_1525);
x_1526 = lean_ctor_get(x_1524, 1);
lean_inc(x_1526);
if (lean_is_exclusive(x_1524)) {
 lean_ctor_release(x_1524, 0);
 lean_ctor_release(x_1524, 1);
 x_1527 = x_1524;
} else {
 lean_dec_ref(x_1524);
 x_1527 = lean_box(0);
}
if (lean_is_scalar(x_1527)) {
 x_1528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1528 = x_1527;
}
lean_ctor_set(x_1528, 0, x_1484);
lean_ctor_set(x_1528, 1, x_1526);
x_1529 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_1530 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_1525);
x_1531 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1529, x_1530, x_1525, x_2, x_1528);
if (lean_obj_tag(x_1531) == 0)
{
lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; 
x_1532 = lean_ctor_get(x_1531, 1);
lean_inc(x_1532);
if (lean_is_exclusive(x_1531)) {
 lean_ctor_release(x_1531, 0);
 lean_ctor_release(x_1531, 1);
 x_1533 = x_1531;
} else {
 lean_dec_ref(x_1531);
 x_1533 = lean_box(0);
}
if (lean_is_scalar(x_1533)) {
 x_1534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1534 = x_1533;
}
lean_ctor_set(x_1534, 0, x_1484);
lean_ctor_set(x_1534, 1, x_1532);
x_1535 = l_Lean_IR_explicitBoxing(x_1525, x_2, x_1534);
if (lean_obj_tag(x_1535) == 0)
{
lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; 
x_1536 = lean_ctor_get(x_1535, 0);
lean_inc(x_1536);
x_1537 = lean_ctor_get(x_1535, 1);
lean_inc(x_1537);
if (lean_is_exclusive(x_1535)) {
 lean_ctor_release(x_1535, 0);
 lean_ctor_release(x_1535, 1);
 x_1538 = x_1535;
} else {
 lean_dec_ref(x_1535);
 x_1538 = lean_box(0);
}
if (lean_is_scalar(x_1538)) {
 x_1539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1539 = x_1538;
}
lean_ctor_set(x_1539, 0, x_1484);
lean_ctor_set(x_1539, 1, x_1537);
x_1540 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_1541 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_1536);
x_1542 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1540, x_1541, x_1536, x_2, x_1539);
if (lean_obj_tag(x_1542) == 0)
{
lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; 
x_1543 = lean_ctor_get(x_1542, 1);
lean_inc(x_1543);
if (lean_is_exclusive(x_1542)) {
 lean_ctor_release(x_1542, 0);
 lean_ctor_release(x_1542, 1);
 x_1544 = x_1542;
} else {
 lean_dec_ref(x_1542);
 x_1544 = lean_box(0);
}
if (lean_is_scalar(x_1544)) {
 x_1545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1545 = x_1544;
}
lean_ctor_set(x_1545, 0, x_1484);
lean_ctor_set(x_1545, 1, x_1543);
x_1546 = l_Lean_IR_explicitRC(x_1536, x_2, x_1545);
if (lean_obj_tag(x_1546) == 0)
{
lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; 
x_1547 = lean_ctor_get(x_1546, 0);
lean_inc(x_1547);
x_1548 = lean_ctor_get(x_1546, 1);
lean_inc(x_1548);
if (lean_is_exclusive(x_1546)) {
 lean_ctor_release(x_1546, 0);
 lean_ctor_release(x_1546, 1);
 x_1549 = x_1546;
} else {
 lean_dec_ref(x_1546);
 x_1549 = lean_box(0);
}
if (lean_is_scalar(x_1549)) {
 x_1550 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1550 = x_1549;
}
lean_ctor_set(x_1550, 0, x_1484);
lean_ctor_set(x_1550, 1, x_1548);
x_1551 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_1552 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_1547);
x_1553 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1551, x_1552, x_1547, x_2, x_1550);
if (lean_obj_tag(x_1553) == 0)
{
lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; 
x_1554 = lean_ctor_get(x_1553, 1);
lean_inc(x_1554);
if (lean_is_exclusive(x_1553)) {
 lean_ctor_release(x_1553, 0);
 lean_ctor_release(x_1553, 1);
 x_1555 = x_1553;
} else {
 lean_dec_ref(x_1553);
 x_1555 = lean_box(0);
}
if (lean_is_scalar(x_1555)) {
 x_1556 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1556 = x_1555;
}
lean_ctor_set(x_1556, 0, x_1484);
lean_ctor_set(x_1556, 1, x_1554);
x_1557 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_1486, x_1547);
x_1558 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_1559 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_1557);
x_1560 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1558, x_1559, x_1557, x_2, x_1556);
if (lean_obj_tag(x_1560) == 0)
{
lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; 
x_1561 = lean_ctor_get(x_1560, 1);
lean_inc(x_1561);
if (lean_is_exclusive(x_1560)) {
 lean_ctor_release(x_1560, 0);
 lean_ctor_release(x_1560, 1);
 x_1562 = x_1560;
} else {
 lean_dec_ref(x_1560);
 x_1562 = lean_box(0);
}
if (lean_is_scalar(x_1562)) {
 x_1563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1563 = x_1562;
}
lean_ctor_set(x_1563, 0, x_1484);
lean_ctor_set(x_1563, 1, x_1561);
x_1564 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_1486, x_1557);
lean_inc(x_1564);
x_1565 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1496, x_1497, x_1564, x_2, x_1563);
if (lean_obj_tag(x_1565) == 0)
{
lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; 
x_1566 = lean_ctor_get(x_1565, 1);
lean_inc(x_1566);
if (lean_is_exclusive(x_1565)) {
 lean_ctor_release(x_1565, 0);
 lean_ctor_release(x_1565, 1);
 x_1567 = x_1565;
} else {
 lean_dec_ref(x_1565);
 x_1567 = lean_box(0);
}
if (lean_is_scalar(x_1567)) {
 x_1568 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1568 = x_1567;
}
lean_ctor_set(x_1568, 0, x_1484);
lean_ctor_set(x_1568, 1, x_1566);
x_1569 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_1570 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_1564);
x_1571 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1569, x_1570, x_1564, x_2, x_1568);
if (lean_obj_tag(x_1571) == 0)
{
lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; 
x_1572 = lean_ctor_get(x_1571, 1);
lean_inc(x_1572);
if (lean_is_exclusive(x_1571)) {
 lean_ctor_release(x_1571, 0);
 lean_ctor_release(x_1571, 1);
 x_1573 = x_1571;
} else {
 lean_dec_ref(x_1571);
 x_1573 = lean_box(0);
}
if (lean_is_scalar(x_1573)) {
 x_1574 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1574 = x_1573;
}
lean_ctor_set(x_1574, 0, x_1484);
lean_ctor_set(x_1574, 1, x_1572);
lean_inc(x_1564);
x_1575 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1564, x_1564, x_1486, x_2, x_1574);
if (lean_obj_tag(x_1575) == 0)
{
lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; 
x_1576 = lean_ctor_get(x_1575, 1);
lean_inc(x_1576);
if (lean_is_exclusive(x_1575)) {
 lean_ctor_release(x_1575, 0);
 lean_ctor_release(x_1575, 1);
 x_1577 = x_1575;
} else {
 lean_dec_ref(x_1575);
 x_1577 = lean_box(0);
}
if (lean_is_scalar(x_1577)) {
 x_1578 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1578 = x_1577;
}
lean_ctor_set(x_1578, 0, x_1484);
lean_ctor_set(x_1578, 1, x_1576);
x_1579 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_1564, x_1486, x_2, x_1578);
lean_dec(x_1564);
if (lean_obj_tag(x_1579) == 0)
{
lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; 
x_1580 = lean_ctor_get(x_1579, 1);
lean_inc(x_1580);
if (lean_is_exclusive(x_1579)) {
 lean_ctor_release(x_1579, 0);
 lean_ctor_release(x_1579, 1);
 x_1581 = x_1579;
} else {
 lean_dec_ref(x_1579);
 x_1581 = lean_box(0);
}
if (lean_is_scalar(x_1581)) {
 x_1582 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1582 = x_1581;
}
lean_ctor_set(x_1582, 0, x_1484);
lean_ctor_set(x_1582, 1, x_1580);
return x_1582;
}
else
{
lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; 
x_1583 = lean_ctor_get(x_1579, 0);
lean_inc(x_1583);
x_1584 = lean_ctor_get(x_1579, 1);
lean_inc(x_1584);
if (lean_is_exclusive(x_1579)) {
 lean_ctor_release(x_1579, 0);
 lean_ctor_release(x_1579, 1);
 x_1585 = x_1579;
} else {
 lean_dec_ref(x_1579);
 x_1585 = lean_box(0);
}
if (lean_is_scalar(x_1585)) {
 x_1586 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1586 = x_1585;
}
lean_ctor_set(x_1586, 0, x_1583);
lean_ctor_set(x_1586, 1, x_1584);
return x_1586;
}
}
else
{
lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; 
lean_dec(x_1564);
x_1587 = lean_ctor_get(x_1575, 0);
lean_inc(x_1587);
x_1588 = lean_ctor_get(x_1575, 1);
lean_inc(x_1588);
if (lean_is_exclusive(x_1575)) {
 lean_ctor_release(x_1575, 0);
 lean_ctor_release(x_1575, 1);
 x_1589 = x_1575;
} else {
 lean_dec_ref(x_1575);
 x_1589 = lean_box(0);
}
if (lean_is_scalar(x_1589)) {
 x_1590 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1590 = x_1589;
}
lean_ctor_set(x_1590, 0, x_1587);
lean_ctor_set(x_1590, 1, x_1588);
return x_1590;
}
}
else
{
lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; 
lean_dec(x_1564);
x_1591 = lean_ctor_get(x_1571, 0);
lean_inc(x_1591);
x_1592 = lean_ctor_get(x_1571, 1);
lean_inc(x_1592);
if (lean_is_exclusive(x_1571)) {
 lean_ctor_release(x_1571, 0);
 lean_ctor_release(x_1571, 1);
 x_1593 = x_1571;
} else {
 lean_dec_ref(x_1571);
 x_1593 = lean_box(0);
}
if (lean_is_scalar(x_1593)) {
 x_1594 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1594 = x_1593;
}
lean_ctor_set(x_1594, 0, x_1591);
lean_ctor_set(x_1594, 1, x_1592);
return x_1594;
}
}
else
{
lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; 
lean_dec(x_1564);
x_1595 = lean_ctor_get(x_1565, 0);
lean_inc(x_1595);
x_1596 = lean_ctor_get(x_1565, 1);
lean_inc(x_1596);
if (lean_is_exclusive(x_1565)) {
 lean_ctor_release(x_1565, 0);
 lean_ctor_release(x_1565, 1);
 x_1597 = x_1565;
} else {
 lean_dec_ref(x_1565);
 x_1597 = lean_box(0);
}
if (lean_is_scalar(x_1597)) {
 x_1598 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1598 = x_1597;
}
lean_ctor_set(x_1598, 0, x_1595);
lean_ctor_set(x_1598, 1, x_1596);
return x_1598;
}
}
else
{
lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; 
lean_dec(x_1557);
x_1599 = lean_ctor_get(x_1560, 0);
lean_inc(x_1599);
x_1600 = lean_ctor_get(x_1560, 1);
lean_inc(x_1600);
if (lean_is_exclusive(x_1560)) {
 lean_ctor_release(x_1560, 0);
 lean_ctor_release(x_1560, 1);
 x_1601 = x_1560;
} else {
 lean_dec_ref(x_1560);
 x_1601 = lean_box(0);
}
if (lean_is_scalar(x_1601)) {
 x_1602 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1602 = x_1601;
}
lean_ctor_set(x_1602, 0, x_1599);
lean_ctor_set(x_1602, 1, x_1600);
return x_1602;
}
}
else
{
lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; 
lean_dec(x_1547);
x_1603 = lean_ctor_get(x_1553, 0);
lean_inc(x_1603);
x_1604 = lean_ctor_get(x_1553, 1);
lean_inc(x_1604);
if (lean_is_exclusive(x_1553)) {
 lean_ctor_release(x_1553, 0);
 lean_ctor_release(x_1553, 1);
 x_1605 = x_1553;
} else {
 lean_dec_ref(x_1553);
 x_1605 = lean_box(0);
}
if (lean_is_scalar(x_1605)) {
 x_1606 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1606 = x_1605;
}
lean_ctor_set(x_1606, 0, x_1603);
lean_ctor_set(x_1606, 1, x_1604);
return x_1606;
}
}
else
{
lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; 
x_1607 = lean_ctor_get(x_1546, 0);
lean_inc(x_1607);
x_1608 = lean_ctor_get(x_1546, 1);
lean_inc(x_1608);
if (lean_is_exclusive(x_1546)) {
 lean_ctor_release(x_1546, 0);
 lean_ctor_release(x_1546, 1);
 x_1609 = x_1546;
} else {
 lean_dec_ref(x_1546);
 x_1609 = lean_box(0);
}
if (lean_is_scalar(x_1609)) {
 x_1610 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1610 = x_1609;
}
lean_ctor_set(x_1610, 0, x_1607);
lean_ctor_set(x_1610, 1, x_1608);
return x_1610;
}
}
else
{
lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; 
lean_dec(x_1536);
x_1611 = lean_ctor_get(x_1542, 0);
lean_inc(x_1611);
x_1612 = lean_ctor_get(x_1542, 1);
lean_inc(x_1612);
if (lean_is_exclusive(x_1542)) {
 lean_ctor_release(x_1542, 0);
 lean_ctor_release(x_1542, 1);
 x_1613 = x_1542;
} else {
 lean_dec_ref(x_1542);
 x_1613 = lean_box(0);
}
if (lean_is_scalar(x_1613)) {
 x_1614 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1614 = x_1613;
}
lean_ctor_set(x_1614, 0, x_1611);
lean_ctor_set(x_1614, 1, x_1612);
return x_1614;
}
}
else
{
lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; 
x_1615 = lean_ctor_get(x_1535, 0);
lean_inc(x_1615);
x_1616 = lean_ctor_get(x_1535, 1);
lean_inc(x_1616);
if (lean_is_exclusive(x_1535)) {
 lean_ctor_release(x_1535, 0);
 lean_ctor_release(x_1535, 1);
 x_1617 = x_1535;
} else {
 lean_dec_ref(x_1535);
 x_1617 = lean_box(0);
}
if (lean_is_scalar(x_1617)) {
 x_1618 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1618 = x_1617;
}
lean_ctor_set(x_1618, 0, x_1615);
lean_ctor_set(x_1618, 1, x_1616);
return x_1618;
}
}
else
{
lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; 
lean_dec(x_1525);
x_1619 = lean_ctor_get(x_1531, 0);
lean_inc(x_1619);
x_1620 = lean_ctor_get(x_1531, 1);
lean_inc(x_1620);
if (lean_is_exclusive(x_1531)) {
 lean_ctor_release(x_1531, 0);
 lean_ctor_release(x_1531, 1);
 x_1621 = x_1531;
} else {
 lean_dec_ref(x_1531);
 x_1621 = lean_box(0);
}
if (lean_is_scalar(x_1621)) {
 x_1622 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1622 = x_1621;
}
lean_ctor_set(x_1622, 0, x_1619);
lean_ctor_set(x_1622, 1, x_1620);
return x_1622;
}
}
else
{
lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; 
x_1623 = lean_ctor_get(x_1524, 0);
lean_inc(x_1623);
x_1624 = lean_ctor_get(x_1524, 1);
lean_inc(x_1624);
if (lean_is_exclusive(x_1524)) {
 lean_ctor_release(x_1524, 0);
 lean_ctor_release(x_1524, 1);
 x_1625 = x_1524;
} else {
 lean_dec_ref(x_1524);
 x_1625 = lean_box(0);
}
if (lean_is_scalar(x_1625)) {
 x_1626 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1626 = x_1625;
}
lean_ctor_set(x_1626, 0, x_1623);
lean_ctor_set(x_1626, 1, x_1624);
return x_1626;
}
}
else
{
lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; 
lean_dec(x_1516);
x_1627 = lean_ctor_get(x_1519, 0);
lean_inc(x_1627);
x_1628 = lean_ctor_get(x_1519, 1);
lean_inc(x_1628);
if (lean_is_exclusive(x_1519)) {
 lean_ctor_release(x_1519, 0);
 lean_ctor_release(x_1519, 1);
 x_1629 = x_1519;
} else {
 lean_dec_ref(x_1519);
 x_1629 = lean_box(0);
}
if (lean_is_scalar(x_1629)) {
 x_1630 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1630 = x_1629;
}
lean_ctor_set(x_1630, 0, x_1627);
lean_ctor_set(x_1630, 1, x_1628);
return x_1630;
}
}
else
{
lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; 
lean_dec(x_1509);
x_1631 = lean_ctor_get(x_1512, 0);
lean_inc(x_1631);
x_1632 = lean_ctor_get(x_1512, 1);
lean_inc(x_1632);
if (lean_is_exclusive(x_1512)) {
 lean_ctor_release(x_1512, 0);
 lean_ctor_release(x_1512, 1);
 x_1633 = x_1512;
} else {
 lean_dec_ref(x_1512);
 x_1633 = lean_box(0);
}
if (lean_is_scalar(x_1633)) {
 x_1634 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1634 = x_1633;
}
lean_ctor_set(x_1634, 0, x_1631);
lean_ctor_set(x_1634, 1, x_1632);
return x_1634;
}
}
else
{
lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; 
lean_dec(x_1502);
x_1635 = lean_ctor_get(x_1505, 0);
lean_inc(x_1635);
x_1636 = lean_ctor_get(x_1505, 1);
lean_inc(x_1636);
if (lean_is_exclusive(x_1505)) {
 lean_ctor_release(x_1505, 0);
 lean_ctor_release(x_1505, 1);
 x_1637 = x_1505;
} else {
 lean_dec_ref(x_1505);
 x_1637 = lean_box(0);
}
if (lean_is_scalar(x_1637)) {
 x_1638 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1638 = x_1637;
}
lean_ctor_set(x_1638, 0, x_1635);
lean_ctor_set(x_1638, 1, x_1636);
return x_1638;
}
}
else
{
lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; 
lean_dec(x_1495);
x_1639 = lean_ctor_get(x_1498, 0);
lean_inc(x_1639);
x_1640 = lean_ctor_get(x_1498, 1);
lean_inc(x_1640);
if (lean_is_exclusive(x_1498)) {
 lean_ctor_release(x_1498, 0);
 lean_ctor_release(x_1498, 1);
 x_1641 = x_1498;
} else {
 lean_dec_ref(x_1498);
 x_1641 = lean_box(0);
}
if (lean_is_scalar(x_1641)) {
 x_1642 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1642 = x_1641;
}
lean_ctor_set(x_1642, 0, x_1639);
lean_ctor_set(x_1642, 1, x_1640);
return x_1642;
}
}
else
{
lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; 
lean_dec(x_1);
x_1643 = lean_ctor_get(x_1491, 0);
lean_inc(x_1643);
x_1644 = lean_ctor_get(x_1491, 1);
lean_inc(x_1644);
if (lean_is_exclusive(x_1491)) {
 lean_ctor_release(x_1491, 0);
 lean_ctor_release(x_1491, 1);
 x_1645 = x_1491;
} else {
 lean_dec_ref(x_1491);
 x_1645 = lean_box(0);
}
if (lean_is_scalar(x_1645)) {
 x_1646 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1646 = x_1645;
}
lean_ctor_set(x_1646, 0, x_1643);
lean_ctor_set(x_1646, 1, x_1644);
return x_1646;
}
}
else
{
lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; 
lean_dec(x_1);
x_1647 = lean_ctor_get(x_1487, 0);
lean_inc(x_1647);
x_1648 = lean_ctor_get(x_1487, 1);
lean_inc(x_1648);
if (lean_is_exclusive(x_1487)) {
 lean_ctor_release(x_1487, 0);
 lean_ctor_release(x_1487, 1);
 x_1649 = x_1487;
} else {
 lean_dec_ref(x_1487);
 x_1649 = lean_box(0);
}
if (lean_is_scalar(x_1649)) {
 x_1650 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1650 = x_1649;
}
lean_ctor_set(x_1650, 0, x_1647);
lean_ctor_set(x_1650, 1, x_1648);
return x_1650;
}
}
}
else
{
uint8_t x_1651; 
lean_dec(x_1);
x_1651 = !lean_is_exclusive(x_6);
if (x_1651 == 0)
{
return x_6;
}
else
{
lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; 
x_1652 = lean_ctor_get(x_6, 0);
x_1653 = lean_ctor_get(x_6, 1);
lean_inc(x_1653);
lean_inc(x_1652);
lean_dec(x_6);
x_1654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1654, 0, x_1652);
lean_ctor_set(x_1654, 1, x_1653);
return x_1654;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux(x_1, x_2, x_3);
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
x_8 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux(x_3, x_2, x_7);
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
lean_object* initialize_Init_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Format(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_CompilerM(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_PushProj(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_ElimDead(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_SimpCase(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_ResetReuse(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_NormIds(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Checker(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Borrow(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Boxing(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_RC(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_ExpandResetReuse(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_UnboxResult(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_UnreachBranches(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_EmitC(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_Default(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_Basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_Format(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_CompilerM(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_PushProj(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_ElimDead(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_SimpCase(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_ResetReuse(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_NormIds(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_Checker(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_Borrow(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_Boxing(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_RC(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_ExpandResetReuse(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_UnboxResult(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_UnreachBranches(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Compiler_IR_EmitC(w);
if (lean_io_result_is_error(w)) return w;
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__1 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__1();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__1);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__2 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__2();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__2);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__4 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__4();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__4);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__5 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__5();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__5);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__8 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__8();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__8);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__11 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__11();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__11);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__14 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__14();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__14);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__17 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__17();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__17);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__20 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__20();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__20);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__23 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__23();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__23);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__26 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__26();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__26);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28);
return w;
}
#ifdef __cplusplus
}
#endif
