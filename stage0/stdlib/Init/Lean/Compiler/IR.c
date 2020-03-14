// Lean compiler output
// Module: Init.Lean.Compiler.IR
// Imports: Init.Lean.Compiler.IR.Basic Init.Lean.Compiler.IR.Format Init.Lean.Compiler.IR.CompilerM Init.Lean.Compiler.IR.PushProj Init.Lean.Compiler.IR.ElimDeadVars Init.Lean.Compiler.IR.SimpCase Init.Lean.Compiler.IR.ResetReuse Init.Lean.Compiler.IR.NormIds Init.Lean.Compiler.IR.Checker Init.Lean.Compiler.IR.Borrow Init.Lean.Compiler.IR.Boxing Init.Lean.Compiler.IR.RC Init.Lean.Compiler.IR.ExpandResetReuse Init.Lean.Compiler.IR.UnboxResult Init.Lean.Compiler.IR.ElimDeadBranches Init.Lean.Compiler.IR.EmitC Init.Lean.Compiler.IR.CtorLayout
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
uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__12;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__5(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__11;
lean_object* lean_ir_add_boxed_version(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__26;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_IR_addBoxedVersionAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__31;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
lean_object* l_Lean_IR_explicitRC(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__24;
lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__10;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__3(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_addDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__16;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__30;
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__18;
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__15;
lean_object* lean_ir_compile(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__5;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__20;
lean_object* l_Array_forMAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__4(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__3;
lean_object* l_Lean_IR_explicitBoxing(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__25;
lean_object* l_Lean_IR_addBoxedVersionAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_checkDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__28;
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__14;
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__7;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__29;
extern lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__21;
lean_object* l_Lean_IR_Decl_simpCase(lean_object*);
lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object*);
lean_object* l_Lean_IR_elimDeadBranches(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__6;
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__22;
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__23;
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__13;
lean_object* l_Lean_IR_inferBorrow(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__27;
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__4;
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__9;
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_pushProj(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__8;
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__17;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_declMapExt;
extern lean_object* l_Lean_mkInitAttr___closed__2;
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__2;
lean_object* l_Array_forMAux___main___at_Lean_IR_addBoxedVersionAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__6(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___closed__19;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_array_fget(x_2, x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_fset(x_2, x_1, x_6);
x_8 = x_5;
x_9 = l_Lean_IR_Decl_pushProj(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = x_9;
x_13 = lean_array_fset(x_7, x_1, x_12);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_array_fget(x_2, x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_fset(x_2, x_1, x_6);
x_8 = x_5;
x_9 = l_Lean_IR_Decl_insertResetReuse(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = x_9;
x_13 = lean_array_fset(x_7, x_1, x_12);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_array_fget(x_2, x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_fset(x_2, x_1, x_6);
x_8 = x_5;
x_9 = l_Lean_IR_Decl_elimDead(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = x_9;
x_13 = lean_array_fset(x_7, x_1, x_12);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_array_fget(x_2, x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_fset(x_2, x_1, x_6);
x_8 = x_5;
x_9 = l_Lean_IR_Decl_simpCase(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = x_9;
x_13 = lean_array_fset(x_7, x_1, x_12);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_array_fget(x_2, x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_fset(x_2, x_1, x_6);
x_8 = x_5;
x_9 = l_Lean_IR_Decl_normalizeIds(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = x_9;
x_13 = lean_array_fset(x_7, x_1, x_12);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_array_fget(x_2, x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_fset(x_2, x_1, x_6);
x_8 = x_5;
x_9 = l_Lean_IR_Decl_expandResetReuse(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = x_9;
x_13 = lean_array_fset(x_7, x_1, x_12);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l_Lean_mkInitAttr___closed__2;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elim_dead_branches");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__3;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("push_proj");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__6;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reset_reuse");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__9;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elim_dead");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__12;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simp_case");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__15;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("borrow");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__18;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("boxing");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__20;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__21;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rc");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__23;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__24;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expand_reset_reuse");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__27;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__29;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__30;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__1;
x_5 = l_Lean_mkInitAttr___closed__2;
lean_inc(x_1);
x_6 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_4, x_5, x_1, x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_9 = l_Array_forMAux___main___at_Lean_IR_checkDecls___spec__1(x_1, x_1, x_8, x_2, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_IR_elimDeadBranches(x_1, x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__4;
x_15 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__3;
lean_inc(x_12);
x_16 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_14, x_15, x_12, x_2, x_13);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = x_12;
x_19 = l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__1(x_8, x_18);
x_20 = x_19;
x_21 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__7;
x_22 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__6;
lean_inc(x_20);
x_23 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_21, x_22, x_20, x_2, x_17);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = x_20;
x_26 = l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__2(x_8, x_25);
x_27 = x_26;
x_28 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__10;
x_29 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__9;
lean_inc(x_27);
x_30 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_28, x_29, x_27, x_2, x_24);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = x_27;
x_33 = l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__3(x_8, x_32);
x_34 = x_33;
x_35 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__13;
x_36 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__12;
lean_inc(x_34);
x_37 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_35, x_36, x_34, x_2, x_31);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = x_34;
x_40 = l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__4(x_8, x_39);
x_41 = x_40;
x_42 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__16;
x_43 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__15;
lean_inc(x_41);
x_44 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_42, x_43, x_41, x_2, x_38);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = x_41;
x_47 = l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__5(x_8, x_46);
x_48 = x_47;
x_49 = l_Lean_IR_inferBorrow(x_48, x_2, x_45);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__19;
x_53 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__18;
lean_inc(x_50);
x_54 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_52, x_53, x_50, x_2, x_51);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_IR_explicitBoxing(x_50, x_2, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__22;
x_60 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__21;
lean_inc(x_57);
x_61 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_59, x_60, x_57, x_2, x_58);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_IR_explicitRC(x_57, x_2, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__25;
x_67 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__24;
lean_inc(x_64);
x_68 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_66, x_67, x_64, x_2, x_65);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = x_64;
x_71 = l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__6(x_8, x_70);
x_72 = x_71;
x_73 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__28;
x_74 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__27;
lean_inc(x_72);
x_75 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_73, x_74, x_72, x_2, x_69);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = x_72;
x_78 = l_Array_umapMAux___main___at___private_Init_Lean_Compiler_IR_1__compileAux___spec__1(x_8, x_77);
x_79 = x_78;
lean_inc(x_79);
x_80 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_21, x_22, x_79, x_2, x_76);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__31;
x_83 = l___private_Init_Lean_Compiler_IR_1__compileAux___closed__30;
lean_inc(x_79);
x_84 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_82, x_83, x_79, x_2, x_81);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
lean_inc(x_79);
x_86 = l_Array_forMAux___main___at_Lean_IR_checkDecls___spec__1(x_79, x_79, x_8, x_2, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Array_forMAux___main___at_Lean_IR_addDecls___spec__1(x_79, x_8, x_2, x_87);
lean_dec(x_79);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 0);
lean_dec(x_90);
x_91 = lean_box(0);
lean_ctor_set(x_88, 0, x_91);
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec(x_79);
x_95 = !lean_is_exclusive(x_86);
if (x_95 == 0)
{
return x_86;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_86, 0);
x_97 = lean_ctor_get(x_86, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_86);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_9);
if (x_99 == 0)
{
return x_9;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_9, 0);
x_101 = lean_ctor_get(x_9, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_9);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_1__compileAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Compiler_IR_1__compileAux(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* lean_ir_compile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_Init_Lean_Compiler_IR_1__compileAux(x_3, x_2, x_5);
lean_dec(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = l_Lean_IR_declMapExt;
x_13 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_12, x_11, x_9);
lean_ctor_set(x_4, 0, x_13);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = l_Lean_IR_declMapExt;
x_20 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_19, x_17, x_9);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
lean_dec(x_2);
x_2 = x_23;
x_4 = x_21;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_addBoxedVersionAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_getEnv___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_6, x_1);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_free_object(x_4);
x_10 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
x_11 = l_Lean_mkOptionalNode___closed__2;
x_12 = lean_array_push(x_11, x_10);
x_13 = l_Lean_IR_explicitRC(x_12, x_2, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_forMAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(x_14, x_16, x_2, x_15);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_4);
x_26 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_24, x_1);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
x_30 = l_Lean_mkOptionalNode___closed__2;
x_31 = lean_array_push(x_30, x_29);
x_32 = l_Lean_IR_explicitRC(x_31, x_2, x_25);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Array_forMAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(x_33, x_35, x_2, x_34);
lean_dec(x_33);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_addBoxedVersionAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(x_1, x_2, x_3, x_4);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_Options_empty;
x_6 = l_Lean_IR_addBoxedVersionAux(x_2, x_5, x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
lean_object* initialize_Init_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Format(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_CompilerM(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_PushProj(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_ElimDeadVars(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_SimpCase(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_ResetReuse(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_NormIds(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Checker(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Borrow(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Boxing(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_RC(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_ExpandResetReuse(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_UnboxResult(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_ElimDeadBranches(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_EmitC(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_CtorLayout(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_CompilerM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_PushProj(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_ElimDeadVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_SimpCase(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_ResetReuse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_NormIds(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Checker(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Borrow(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Boxing(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_RC(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_ExpandResetReuse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_UnboxResult(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_ElimDeadBranches(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_EmitC(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_CtorLayout(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__1 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__1();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__1);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__2 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__2();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__2);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__3 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__3();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__3);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__4 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__4();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__4);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__5 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__5();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__5);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__6 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__6();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__6);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__7 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__7();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__7);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__8 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__8();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__8);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__9 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__9();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__9);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__10 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__10();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__10);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__11 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__11();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__11);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__12 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__12();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__12);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__13 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__13();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__13);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__14 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__14();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__14);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__15 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__15();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__15);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__16 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__16();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__16);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__17 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__17();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__17);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__18 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__18();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__18);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__19 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__19();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__19);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__20 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__20();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__20);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__21 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__21();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__21);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__22 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__22();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__22);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__23 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__23();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__23);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__24 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__24();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__24);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__25 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__25();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__25);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__26 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__26();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__26);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__27 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__27();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__27);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__28 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__28();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__28);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__29 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__29();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__29);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__30 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__30();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__30);
l___private_Init_Lean_Compiler_IR_1__compileAux___closed__31 = _init_l___private_Init_Lean_Compiler_IR_1__compileAux___closed__31();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_1__compileAux___closed__31);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
