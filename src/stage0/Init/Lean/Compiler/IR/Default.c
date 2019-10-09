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
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_IR_addBoxedVersionAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_object* l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_pushProj(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__14;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__20;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3;
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__2(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__29;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
extern lean_object* l_Lean_Options_empty;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__26;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__17;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__5;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
lean_object* l_Lean_IR_elimDeadBranches(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
extern lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__4;
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___rarg___closed__1;
lean_object* l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_IR_inferBorrow(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
extern lean_object* l_Lean_IR_declMapExt;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
lean_object* l_Array_push(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_simpCase(lean_object*);
lean_object* l_Lean_IR_Decl_insertResetReuse(lean_object*);
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
x_11 = l_Lean_IR_Decl_normalizeIds(x_7);
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
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_11 = l_Lean_IR_Decl_expandResetReuse(x_7);
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
x_1 = lean_mk_string("elim_dead_branches");
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
x_1 = lean_mk_string("push_proj");
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
x_1 = lean_mk_string("reset_reuse");
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
x_1 = lean_mk_string("elim_dead");
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
x_1 = lean_mk_string("simp_case");
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
x_1 = lean_mk_string("borrow");
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
x_1 = lean_mk_string("boxing");
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
x_1 = lean_mk_string("rc");
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
x_1 = lean_mk_string("expand_reset_reuse");
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
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__29;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_tracePrefixOptionName;
x_2 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Default_1__compileAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__1;
x_5 = l_Lean_mkInitAttr___closed__2;
lean_inc(x_1);
x_6 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_4, x_5, x_1, x_2, x_3);
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
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_9);
x_14 = l_Lean_IR_elimDeadBranches(x_1, x_2, x_11);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_14, 0, x_9);
x_17 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__4;
x_18 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3;
lean_inc(x_16);
x_19 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_17, x_18, x_16, x_2, x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_9);
x_22 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_16);
x_23 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7;
x_24 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6;
lean_inc(x_22);
x_25 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_23, x_24, x_22, x_2, x_19);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_9);
x_28 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__2(x_10, x_22);
x_29 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10;
x_30 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
lean_inc(x_28);
x_31 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_29, x_30, x_28, x_2, x_25);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_9);
x_34 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(x_10, x_28);
x_35 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
x_36 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_inc(x_34);
x_37 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_35, x_36, x_34, x_2, x_31);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_9);
x_40 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_10, x_34);
x_41 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_42 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_40);
x_43 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_41, x_42, x_40, x_2, x_37);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_9);
x_46 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_40);
x_47 = l_Lean_IR_inferBorrow(x_46, x_2, x_43);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_47, 0);
lean_ctor_set(x_47, 0, x_9);
x_50 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_51 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_49);
x_52 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_50, x_51, x_49, x_2, x_47);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_9);
x_55 = l_Lean_IR_explicitBoxing(x_49, x_2, x_52);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_55, 0);
lean_ctor_set(x_55, 0, x_9);
x_58 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_59 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_57);
x_60 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_58, x_59, x_57, x_2, x_55);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set(x_60, 0, x_9);
x_63 = l_Lean_IR_explicitRC(x_57, x_2, x_60);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_63, 0);
lean_ctor_set(x_63, 0, x_9);
x_66 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_67 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_65);
x_68 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_66, x_67, x_65, x_2, x_63);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
lean_ctor_set(x_68, 0, x_9);
x_71 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_10, x_65);
x_72 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_73 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_71);
x_74 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_72, x_73, x_71, x_2, x_68);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
lean_ctor_set(x_74, 0, x_9);
x_77 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_71);
lean_inc(x_77);
x_78 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_23, x_24, x_77, x_2, x_74);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
lean_ctor_set(x_78, 0, x_9);
x_81 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_82 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_77);
x_83 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_81, x_82, x_77, x_2, x_78);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
lean_ctor_set(x_83, 0, x_9);
lean_inc(x_77);
x_86 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_77, x_77, x_10, x_2, x_83);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
lean_ctor_set(x_86, 0, x_9);
x_89 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_77, x_10, x_2, x_86);
lean_dec(x_77);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
lean_ctor_set(x_89, 0, x_9);
return x_89;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_9);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_86, 1);
lean_inc(x_94);
lean_dec(x_86);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_9);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_77, x_10, x_2, x_95);
lean_dec(x_77);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_9);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_77);
x_100 = !lean_is_exclusive(x_86);
if (x_100 == 0)
{
return x_86;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_86, 0);
x_102 = lean_ctor_get(x_86, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_86);
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
x_104 = lean_ctor_get(x_83, 1);
lean_inc(x_104);
lean_dec(x_83);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_9);
lean_ctor_set(x_105, 1, x_104);
lean_inc(x_77);
x_106 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_77, x_77, x_10, x_2, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
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
x_110 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_77, x_10, x_2, x_109);
lean_dec(x_77);
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
lean_dec(x_77);
x_114 = lean_ctor_get(x_106, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_106, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_116 = x_106;
} else {
 lean_dec_ref(x_106);
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
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_118 = lean_ctor_get(x_78, 1);
lean_inc(x_118);
lean_dec(x_78);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_9);
lean_ctor_set(x_119, 1, x_118);
x_120 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_121 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_77);
x_122 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_120, x_121, x_77, x_2, x_119);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_9);
lean_ctor_set(x_125, 1, x_123);
lean_inc(x_77);
x_126 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_77, x_77, x_10, x_2, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_9);
lean_ctor_set(x_129, 1, x_127);
x_130 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_77, x_10, x_2, x_129);
lean_dec(x_77);
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
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_77);
x_134 = lean_ctor_get(x_126, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_126, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_136 = x_126;
} else {
 lean_dec_ref(x_126);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_138 = lean_ctor_get(x_74, 1);
lean_inc(x_138);
lean_dec(x_74);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_9);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_71);
lean_inc(x_140);
x_141 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_23, x_24, x_140, x_2, x_139);
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
x_145 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_146 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_140);
x_147 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_145, x_146, x_140, x_2, x_144);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_9);
lean_ctor_set(x_150, 1, x_148);
lean_inc(x_140);
x_151 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_140, x_140, x_10, x_2, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_9);
lean_ctor_set(x_154, 1, x_152);
x_155 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_140, x_10, x_2, x_154);
lean_dec(x_140);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_9);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_140);
x_159 = lean_ctor_get(x_151, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_151, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_161 = x_151;
} else {
 lean_dec_ref(x_151);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_163 = lean_ctor_get(x_68, 1);
lean_inc(x_163);
lean_dec(x_68);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_9);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_10, x_65);
x_166 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_167 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_165);
x_168 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_166, x_167, x_165, x_2, x_164);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_9);
lean_ctor_set(x_171, 1, x_169);
x_172 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_165);
lean_inc(x_172);
x_173 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_23, x_24, x_172, x_2, x_171);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_9);
lean_ctor_set(x_176, 1, x_174);
x_177 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_178 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_172);
x_179 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_177, x_178, x_172, x_2, x_176);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_9);
lean_ctor_set(x_182, 1, x_180);
lean_inc(x_172);
x_183 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_172, x_172, x_10, x_2, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_185 = x_183;
} else {
 lean_dec_ref(x_183);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_9);
lean_ctor_set(x_186, 1, x_184);
x_187 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_172, x_10, x_2, x_186);
lean_dec(x_172);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_189 = x_187;
} else {
 lean_dec_ref(x_187);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_9);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_172);
x_191 = lean_ctor_get(x_183, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_183, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_193 = x_183;
} else {
 lean_dec_ref(x_183);
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
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_195 = lean_ctor_get(x_63, 0);
x_196 = lean_ctor_get(x_63, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_63);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_9);
lean_ctor_set(x_197, 1, x_196);
x_198 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_199 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_195);
x_200 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_198, x_199, x_195, x_2, x_197);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_202 = x_200;
} else {
 lean_dec_ref(x_200);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_9);
lean_ctor_set(x_203, 1, x_201);
x_204 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_10, x_195);
x_205 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_206 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_204);
x_207 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_205, x_206, x_204, x_2, x_203);
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
x_212 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_23, x_24, x_211, x_2, x_210);
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
x_216 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_217 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_211);
x_218 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_216, x_217, x_211, x_2, x_215);
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
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
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
lean_dec(x_211);
x_230 = lean_ctor_get(x_222, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_222, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_232 = x_222;
} else {
 lean_dec_ref(x_222);
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
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_234 = lean_ctor_get(x_60, 1);
lean_inc(x_234);
lean_dec(x_60);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_9);
lean_ctor_set(x_235, 1, x_234);
x_236 = l_Lean_IR_explicitRC(x_57, x_2, x_235);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_239 = x_236;
} else {
 lean_dec_ref(x_236);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_9);
lean_ctor_set(x_240, 1, x_238);
x_241 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_242 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_237);
x_243 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_241, x_242, x_237, x_2, x_240);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_245 = x_243;
} else {
 lean_dec_ref(x_243);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_9);
lean_ctor_set(x_246, 1, x_244);
x_247 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_10, x_237);
x_248 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_249 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_247);
x_250 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_248, x_249, x_247, x_2, x_246);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_9);
lean_ctor_set(x_253, 1, x_251);
x_254 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_247);
lean_inc(x_254);
x_255 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_23, x_24, x_254, x_2, x_253);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_257 = x_255;
} else {
 lean_dec_ref(x_255);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_9);
lean_ctor_set(x_258, 1, x_256);
x_259 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_260 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_254);
x_261 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_259, x_260, x_254, x_2, x_258);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_263 = x_261;
} else {
 lean_dec_ref(x_261);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_9);
lean_ctor_set(x_264, 1, x_262);
lean_inc(x_254);
x_265 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_254, x_254, x_10, x_2, x_264);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_267 = x_265;
} else {
 lean_dec_ref(x_265);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_9);
lean_ctor_set(x_268, 1, x_266);
x_269 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_254, x_10, x_2, x_268);
lean_dec(x_254);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_271 = x_269;
} else {
 lean_dec_ref(x_269);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_9);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_254);
x_273 = lean_ctor_get(x_265, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_265, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_275 = x_265;
} else {
 lean_dec_ref(x_265);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_277 = lean_ctor_get(x_55, 0);
x_278 = lean_ctor_get(x_55, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_55);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_9);
lean_ctor_set(x_279, 1, x_278);
x_280 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_281 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_277);
x_282 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_280, x_281, x_277, x_2, x_279);
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
x_286 = l_Lean_IR_explicitRC(x_277, x_2, x_285);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_289 = x_286;
} else {
 lean_dec_ref(x_286);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_9);
lean_ctor_set(x_290, 1, x_288);
x_291 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_292 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_287);
x_293 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_291, x_292, x_287, x_2, x_290);
x_294 = lean_ctor_get(x_293, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_295 = x_293;
} else {
 lean_dec_ref(x_293);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_9);
lean_ctor_set(x_296, 1, x_294);
x_297 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_10, x_287);
x_298 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_299 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_297);
x_300 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_298, x_299, x_297, x_2, x_296);
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_302 = x_300;
} else {
 lean_dec_ref(x_300);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_9);
lean_ctor_set(x_303, 1, x_301);
x_304 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_297);
lean_inc(x_304);
x_305 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_23, x_24, x_304, x_2, x_303);
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_307 = x_305;
} else {
 lean_dec_ref(x_305);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_9);
lean_ctor_set(x_308, 1, x_306);
x_309 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_310 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_304);
x_311 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_309, x_310, x_304, x_2, x_308);
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_313 = x_311;
} else {
 lean_dec_ref(x_311);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_9);
lean_ctor_set(x_314, 1, x_312);
lean_inc(x_304);
x_315 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_304, x_304, x_10, x_2, x_314);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_317 = x_315;
} else {
 lean_dec_ref(x_315);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_9);
lean_ctor_set(x_318, 1, x_316);
x_319 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_304, x_10, x_2, x_318);
lean_dec(x_304);
x_320 = lean_ctor_get(x_319, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_321 = x_319;
} else {
 lean_dec_ref(x_319);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_9);
lean_ctor_set(x_322, 1, x_320);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_304);
x_323 = lean_ctor_get(x_315, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_315, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_325 = x_315;
} else {
 lean_dec_ref(x_315);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_323);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_327 = lean_ctor_get(x_52, 1);
lean_inc(x_327);
lean_dec(x_52);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_9);
lean_ctor_set(x_328, 1, x_327);
x_329 = l_Lean_IR_explicitBoxing(x_49, x_2, x_328);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_332 = x_329;
} else {
 lean_dec_ref(x_329);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_9);
lean_ctor_set(x_333, 1, x_331);
x_334 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_335 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_330);
x_336 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_334, x_335, x_330, x_2, x_333);
x_337 = lean_ctor_get(x_336, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_338 = x_336;
} else {
 lean_dec_ref(x_336);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_9);
lean_ctor_set(x_339, 1, x_337);
x_340 = l_Lean_IR_explicitRC(x_330, x_2, x_339);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_343 = x_340;
} else {
 lean_dec_ref(x_340);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_9);
lean_ctor_set(x_344, 1, x_342);
x_345 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_346 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_341);
x_347 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_345, x_346, x_341, x_2, x_344);
x_348 = lean_ctor_get(x_347, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_349 = x_347;
} else {
 lean_dec_ref(x_347);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_9);
lean_ctor_set(x_350, 1, x_348);
x_351 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_10, x_341);
x_352 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_353 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_351);
x_354 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_352, x_353, x_351, x_2, x_350);
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_356 = x_354;
} else {
 lean_dec_ref(x_354);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_9);
lean_ctor_set(x_357, 1, x_355);
x_358 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_351);
lean_inc(x_358);
x_359 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_23, x_24, x_358, x_2, x_357);
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_361 = x_359;
} else {
 lean_dec_ref(x_359);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_9);
lean_ctor_set(x_362, 1, x_360);
x_363 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_364 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_358);
x_365 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_363, x_364, x_358, x_2, x_362);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_367 = x_365;
} else {
 lean_dec_ref(x_365);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_9);
lean_ctor_set(x_368, 1, x_366);
lean_inc(x_358);
x_369 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_358, x_358, x_10, x_2, x_368);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_371 = x_369;
} else {
 lean_dec_ref(x_369);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_9);
lean_ctor_set(x_372, 1, x_370);
x_373 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_358, x_10, x_2, x_372);
lean_dec(x_358);
x_374 = lean_ctor_get(x_373, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_375 = x_373;
} else {
 lean_dec_ref(x_373);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_9);
lean_ctor_set(x_376, 1, x_374);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_358);
x_377 = lean_ctor_get(x_369, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_369, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_379 = x_369;
} else {
 lean_dec_ref(x_369);
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
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_381 = lean_ctor_get(x_47, 0);
x_382 = lean_ctor_get(x_47, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_47);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_9);
lean_ctor_set(x_383, 1, x_382);
x_384 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_385 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_381);
x_386 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_384, x_385, x_381, x_2, x_383);
x_387 = lean_ctor_get(x_386, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_386)) {
 lean_ctor_release(x_386, 0);
 lean_ctor_release(x_386, 1);
 x_388 = x_386;
} else {
 lean_dec_ref(x_386);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_9);
lean_ctor_set(x_389, 1, x_387);
x_390 = l_Lean_IR_explicitBoxing(x_381, x_2, x_389);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_393 = x_390;
} else {
 lean_dec_ref(x_390);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(0, 2, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_9);
lean_ctor_set(x_394, 1, x_392);
x_395 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_396 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_391);
x_397 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_395, x_396, x_391, x_2, x_394);
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_399 = x_397;
} else {
 lean_dec_ref(x_397);
 x_399 = lean_box(0);
}
if (lean_is_scalar(x_399)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_399;
}
lean_ctor_set(x_400, 0, x_9);
lean_ctor_set(x_400, 1, x_398);
x_401 = l_Lean_IR_explicitRC(x_391, x_2, x_400);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_404 = x_401;
} else {
 lean_dec_ref(x_401);
 x_404 = lean_box(0);
}
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_9);
lean_ctor_set(x_405, 1, x_403);
x_406 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_407 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_402);
x_408 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_406, x_407, x_402, x_2, x_405);
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
x_412 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_10, x_402);
x_413 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_414 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_412);
x_415 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_413, x_414, x_412, x_2, x_411);
x_416 = lean_ctor_get(x_415, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_417 = x_415;
} else {
 lean_dec_ref(x_415);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_9);
lean_ctor_set(x_418, 1, x_416);
x_419 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_412);
lean_inc(x_419);
x_420 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_23, x_24, x_419, x_2, x_418);
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_422 = x_420;
} else {
 lean_dec_ref(x_420);
 x_422 = lean_box(0);
}
if (lean_is_scalar(x_422)) {
 x_423 = lean_alloc_ctor(0, 2, 0);
} else {
 x_423 = x_422;
}
lean_ctor_set(x_423, 0, x_9);
lean_ctor_set(x_423, 1, x_421);
x_424 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_425 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_419);
x_426 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_424, x_425, x_419, x_2, x_423);
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
lean_inc(x_419);
x_430 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_419, x_419, x_10, x_2, x_429);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
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
x_434 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_419, x_10, x_2, x_433);
lean_dec(x_419);
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_436 = x_434;
} else {
 lean_dec_ref(x_434);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_9);
lean_ctor_set(x_437, 1, x_435);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_419);
x_438 = lean_ctor_get(x_430, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_430, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 x_440 = x_430;
} else {
 lean_dec_ref(x_430);
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
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_442 = lean_ctor_get(x_43, 1);
lean_inc(x_442);
lean_dec(x_43);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_9);
lean_ctor_set(x_443, 1, x_442);
x_444 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_40);
x_445 = l_Lean_IR_inferBorrow(x_444, x_2, x_443);
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_448 = x_445;
} else {
 lean_dec_ref(x_445);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_9);
lean_ctor_set(x_449, 1, x_447);
x_450 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_451 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_446);
x_452 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_450, x_451, x_446, x_2, x_449);
x_453 = lean_ctor_get(x_452, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_454 = x_452;
} else {
 lean_dec_ref(x_452);
 x_454 = lean_box(0);
}
if (lean_is_scalar(x_454)) {
 x_455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_455 = x_454;
}
lean_ctor_set(x_455, 0, x_9);
lean_ctor_set(x_455, 1, x_453);
x_456 = l_Lean_IR_explicitBoxing(x_446, x_2, x_455);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_459 = x_456;
} else {
 lean_dec_ref(x_456);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(0, 2, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_9);
lean_ctor_set(x_460, 1, x_458);
x_461 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_462 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_457);
x_463 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_461, x_462, x_457, x_2, x_460);
x_464 = lean_ctor_get(x_463, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_465 = x_463;
} else {
 lean_dec_ref(x_463);
 x_465 = lean_box(0);
}
if (lean_is_scalar(x_465)) {
 x_466 = lean_alloc_ctor(0, 2, 0);
} else {
 x_466 = x_465;
}
lean_ctor_set(x_466, 0, x_9);
lean_ctor_set(x_466, 1, x_464);
x_467 = l_Lean_IR_explicitRC(x_457, x_2, x_466);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_470 = x_467;
} else {
 lean_dec_ref(x_467);
 x_470 = lean_box(0);
}
if (lean_is_scalar(x_470)) {
 x_471 = lean_alloc_ctor(0, 2, 0);
} else {
 x_471 = x_470;
}
lean_ctor_set(x_471, 0, x_9);
lean_ctor_set(x_471, 1, x_469);
x_472 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_473 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_468);
x_474 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_472, x_473, x_468, x_2, x_471);
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_476 = x_474;
} else {
 lean_dec_ref(x_474);
 x_476 = lean_box(0);
}
if (lean_is_scalar(x_476)) {
 x_477 = lean_alloc_ctor(0, 2, 0);
} else {
 x_477 = x_476;
}
lean_ctor_set(x_477, 0, x_9);
lean_ctor_set(x_477, 1, x_475);
x_478 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_10, x_468);
x_479 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_480 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_478);
x_481 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_479, x_480, x_478, x_2, x_477);
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_483 = x_481;
} else {
 lean_dec_ref(x_481);
 x_483 = lean_box(0);
}
if (lean_is_scalar(x_483)) {
 x_484 = lean_alloc_ctor(0, 2, 0);
} else {
 x_484 = x_483;
}
lean_ctor_set(x_484, 0, x_9);
lean_ctor_set(x_484, 1, x_482);
x_485 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_478);
lean_inc(x_485);
x_486 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_23, x_24, x_485, x_2, x_484);
x_487 = lean_ctor_get(x_486, 1);
lean_inc(x_487);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_488 = x_486;
} else {
 lean_dec_ref(x_486);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_9);
lean_ctor_set(x_489, 1, x_487);
x_490 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_491 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_485);
x_492 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_490, x_491, x_485, x_2, x_489);
x_493 = lean_ctor_get(x_492, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_494 = x_492;
} else {
 lean_dec_ref(x_492);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(0, 2, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_9);
lean_ctor_set(x_495, 1, x_493);
lean_inc(x_485);
x_496 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_485, x_485, x_10, x_2, x_495);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_498 = x_496;
} else {
 lean_dec_ref(x_496);
 x_498 = lean_box(0);
}
if (lean_is_scalar(x_498)) {
 x_499 = lean_alloc_ctor(0, 2, 0);
} else {
 x_499 = x_498;
}
lean_ctor_set(x_499, 0, x_9);
lean_ctor_set(x_499, 1, x_497);
x_500 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_485, x_10, x_2, x_499);
lean_dec(x_485);
x_501 = lean_ctor_get(x_500, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_502 = x_500;
} else {
 lean_dec_ref(x_500);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(0, 2, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_9);
lean_ctor_set(x_503, 1, x_501);
return x_503;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_485);
x_504 = lean_ctor_get(x_496, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_496, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_506 = x_496;
} else {
 lean_dec_ref(x_496);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_505);
return x_507;
}
}
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_508 = lean_ctor_get(x_37, 1);
lean_inc(x_508);
lean_dec(x_37);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_9);
lean_ctor_set(x_509, 1, x_508);
x_510 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_10, x_34);
x_511 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_512 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_510);
x_513 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_511, x_512, x_510, x_2, x_509);
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
x_517 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_510);
x_518 = l_Lean_IR_inferBorrow(x_517, x_2, x_516);
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 x_521 = x_518;
} else {
 lean_dec_ref(x_518);
 x_521 = lean_box(0);
}
if (lean_is_scalar(x_521)) {
 x_522 = lean_alloc_ctor(0, 2, 0);
} else {
 x_522 = x_521;
}
lean_ctor_set(x_522, 0, x_9);
lean_ctor_set(x_522, 1, x_520);
x_523 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_524 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_519);
x_525 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_523, x_524, x_519, x_2, x_522);
x_526 = lean_ctor_get(x_525, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 lean_ctor_release(x_525, 1);
 x_527 = x_525;
} else {
 lean_dec_ref(x_525);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_9);
lean_ctor_set(x_528, 1, x_526);
x_529 = l_Lean_IR_explicitBoxing(x_519, x_2, x_528);
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_532 = x_529;
} else {
 lean_dec_ref(x_529);
 x_532 = lean_box(0);
}
if (lean_is_scalar(x_532)) {
 x_533 = lean_alloc_ctor(0, 2, 0);
} else {
 x_533 = x_532;
}
lean_ctor_set(x_533, 0, x_9);
lean_ctor_set(x_533, 1, x_531);
x_534 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_535 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_530);
x_536 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_534, x_535, x_530, x_2, x_533);
x_537 = lean_ctor_get(x_536, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 lean_ctor_release(x_536, 1);
 x_538 = x_536;
} else {
 lean_dec_ref(x_536);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_9);
lean_ctor_set(x_539, 1, x_537);
x_540 = l_Lean_IR_explicitRC(x_530, x_2, x_539);
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_543 = x_540;
} else {
 lean_dec_ref(x_540);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_9);
lean_ctor_set(x_544, 1, x_542);
x_545 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_546 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_541);
x_547 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_545, x_546, x_541, x_2, x_544);
x_548 = lean_ctor_get(x_547, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_549 = x_547;
} else {
 lean_dec_ref(x_547);
 x_549 = lean_box(0);
}
if (lean_is_scalar(x_549)) {
 x_550 = lean_alloc_ctor(0, 2, 0);
} else {
 x_550 = x_549;
}
lean_ctor_set(x_550, 0, x_9);
lean_ctor_set(x_550, 1, x_548);
x_551 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_10, x_541);
x_552 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_553 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_551);
x_554 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_552, x_553, x_551, x_2, x_550);
x_555 = lean_ctor_get(x_554, 1);
lean_inc(x_555);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 lean_ctor_release(x_554, 1);
 x_556 = x_554;
} else {
 lean_dec_ref(x_554);
 x_556 = lean_box(0);
}
if (lean_is_scalar(x_556)) {
 x_557 = lean_alloc_ctor(0, 2, 0);
} else {
 x_557 = x_556;
}
lean_ctor_set(x_557, 0, x_9);
lean_ctor_set(x_557, 1, x_555);
x_558 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_551);
lean_inc(x_558);
x_559 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_23, x_24, x_558, x_2, x_557);
x_560 = lean_ctor_get(x_559, 1);
lean_inc(x_560);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_561 = x_559;
} else {
 lean_dec_ref(x_559);
 x_561 = lean_box(0);
}
if (lean_is_scalar(x_561)) {
 x_562 = lean_alloc_ctor(0, 2, 0);
} else {
 x_562 = x_561;
}
lean_ctor_set(x_562, 0, x_9);
lean_ctor_set(x_562, 1, x_560);
x_563 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_564 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_558);
x_565 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_563, x_564, x_558, x_2, x_562);
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
lean_inc(x_558);
x_569 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_558, x_558, x_10, x_2, x_568);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_570 = lean_ctor_get(x_569, 1);
lean_inc(x_570);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_571 = x_569;
} else {
 lean_dec_ref(x_569);
 x_571 = lean_box(0);
}
if (lean_is_scalar(x_571)) {
 x_572 = lean_alloc_ctor(0, 2, 0);
} else {
 x_572 = x_571;
}
lean_ctor_set(x_572, 0, x_9);
lean_ctor_set(x_572, 1, x_570);
x_573 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_558, x_10, x_2, x_572);
lean_dec(x_558);
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
return x_576;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_558);
x_577 = lean_ctor_get(x_569, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_569, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_579 = x_569;
} else {
 lean_dec_ref(x_569);
 x_579 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_580 = lean_alloc_ctor(1, 2, 0);
} else {
 x_580 = x_579;
}
lean_ctor_set(x_580, 0, x_577);
lean_ctor_set(x_580, 1, x_578);
return x_580;
}
}
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_581 = lean_ctor_get(x_31, 1);
lean_inc(x_581);
lean_dec(x_31);
x_582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_582, 0, x_9);
lean_ctor_set(x_582, 1, x_581);
x_583 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(x_10, x_28);
x_584 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
x_585 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_inc(x_583);
x_586 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_584, x_585, x_583, x_2, x_582);
x_587 = lean_ctor_get(x_586, 1);
lean_inc(x_587);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 x_588 = x_586;
} else {
 lean_dec_ref(x_586);
 x_588 = lean_box(0);
}
if (lean_is_scalar(x_588)) {
 x_589 = lean_alloc_ctor(0, 2, 0);
} else {
 x_589 = x_588;
}
lean_ctor_set(x_589, 0, x_9);
lean_ctor_set(x_589, 1, x_587);
x_590 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_10, x_583);
x_591 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_592 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_590);
x_593 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_591, x_592, x_590, x_2, x_589);
x_594 = lean_ctor_get(x_593, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_595 = x_593;
} else {
 lean_dec_ref(x_593);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(0, 2, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_9);
lean_ctor_set(x_596, 1, x_594);
x_597 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_590);
x_598 = l_Lean_IR_inferBorrow(x_597, x_2, x_596);
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 x_601 = x_598;
} else {
 lean_dec_ref(x_598);
 x_601 = lean_box(0);
}
if (lean_is_scalar(x_601)) {
 x_602 = lean_alloc_ctor(0, 2, 0);
} else {
 x_602 = x_601;
}
lean_ctor_set(x_602, 0, x_9);
lean_ctor_set(x_602, 1, x_600);
x_603 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_604 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_599);
x_605 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_603, x_604, x_599, x_2, x_602);
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
x_609 = l_Lean_IR_explicitBoxing(x_599, x_2, x_608);
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_612 = x_609;
} else {
 lean_dec_ref(x_609);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(0, 2, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_9);
lean_ctor_set(x_613, 1, x_611);
x_614 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_615 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_610);
x_616 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_614, x_615, x_610, x_2, x_613);
x_617 = lean_ctor_get(x_616, 1);
lean_inc(x_617);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 x_618 = x_616;
} else {
 lean_dec_ref(x_616);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(0, 2, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_9);
lean_ctor_set(x_619, 1, x_617);
x_620 = l_Lean_IR_explicitRC(x_610, x_2, x_619);
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_623 = x_620;
} else {
 lean_dec_ref(x_620);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(0, 2, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_9);
lean_ctor_set(x_624, 1, x_622);
x_625 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_626 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_621);
x_627 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_625, x_626, x_621, x_2, x_624);
x_628 = lean_ctor_get(x_627, 1);
lean_inc(x_628);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 lean_ctor_release(x_627, 1);
 x_629 = x_627;
} else {
 lean_dec_ref(x_627);
 x_629 = lean_box(0);
}
if (lean_is_scalar(x_629)) {
 x_630 = lean_alloc_ctor(0, 2, 0);
} else {
 x_630 = x_629;
}
lean_ctor_set(x_630, 0, x_9);
lean_ctor_set(x_630, 1, x_628);
x_631 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_10, x_621);
x_632 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_633 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_631);
x_634 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_632, x_633, x_631, x_2, x_630);
x_635 = lean_ctor_get(x_634, 1);
lean_inc(x_635);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_636 = x_634;
} else {
 lean_dec_ref(x_634);
 x_636 = lean_box(0);
}
if (lean_is_scalar(x_636)) {
 x_637 = lean_alloc_ctor(0, 2, 0);
} else {
 x_637 = x_636;
}
lean_ctor_set(x_637, 0, x_9);
lean_ctor_set(x_637, 1, x_635);
x_638 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_631);
lean_inc(x_638);
x_639 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_23, x_24, x_638, x_2, x_637);
x_640 = lean_ctor_get(x_639, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_641 = x_639;
} else {
 lean_dec_ref(x_639);
 x_641 = lean_box(0);
}
if (lean_is_scalar(x_641)) {
 x_642 = lean_alloc_ctor(0, 2, 0);
} else {
 x_642 = x_641;
}
lean_ctor_set(x_642, 0, x_9);
lean_ctor_set(x_642, 1, x_640);
x_643 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_644 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_638);
x_645 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_643, x_644, x_638, x_2, x_642);
x_646 = lean_ctor_get(x_645, 1);
lean_inc(x_646);
if (lean_is_exclusive(x_645)) {
 lean_ctor_release(x_645, 0);
 lean_ctor_release(x_645, 1);
 x_647 = x_645;
} else {
 lean_dec_ref(x_645);
 x_647 = lean_box(0);
}
if (lean_is_scalar(x_647)) {
 x_648 = lean_alloc_ctor(0, 2, 0);
} else {
 x_648 = x_647;
}
lean_ctor_set(x_648, 0, x_9);
lean_ctor_set(x_648, 1, x_646);
lean_inc(x_638);
x_649 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_638, x_638, x_10, x_2, x_648);
if (lean_obj_tag(x_649) == 0)
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_650 = lean_ctor_get(x_649, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 x_651 = x_649;
} else {
 lean_dec_ref(x_649);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_651)) {
 x_652 = lean_alloc_ctor(0, 2, 0);
} else {
 x_652 = x_651;
}
lean_ctor_set(x_652, 0, x_9);
lean_ctor_set(x_652, 1, x_650);
x_653 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_638, x_10, x_2, x_652);
lean_dec(x_638);
x_654 = lean_ctor_get(x_653, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_653)) {
 lean_ctor_release(x_653, 0);
 lean_ctor_release(x_653, 1);
 x_655 = x_653;
} else {
 lean_dec_ref(x_653);
 x_655 = lean_box(0);
}
if (lean_is_scalar(x_655)) {
 x_656 = lean_alloc_ctor(0, 2, 0);
} else {
 x_656 = x_655;
}
lean_ctor_set(x_656, 0, x_9);
lean_ctor_set(x_656, 1, x_654);
return x_656;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec(x_638);
x_657 = lean_ctor_get(x_649, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_649, 1);
lean_inc(x_658);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 x_659 = x_649;
} else {
 lean_dec_ref(x_649);
 x_659 = lean_box(0);
}
if (lean_is_scalar(x_659)) {
 x_660 = lean_alloc_ctor(1, 2, 0);
} else {
 x_660 = x_659;
}
lean_ctor_set(x_660, 0, x_657);
lean_ctor_set(x_660, 1, x_658);
return x_660;
}
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_661 = lean_ctor_get(x_25, 1);
lean_inc(x_661);
lean_dec(x_25);
x_662 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_662, 0, x_9);
lean_ctor_set(x_662, 1, x_661);
x_663 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__2(x_10, x_22);
x_664 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10;
x_665 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
lean_inc(x_663);
x_666 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_664, x_665, x_663, x_2, x_662);
x_667 = lean_ctor_get(x_666, 1);
lean_inc(x_667);
if (lean_is_exclusive(x_666)) {
 lean_ctor_release(x_666, 0);
 lean_ctor_release(x_666, 1);
 x_668 = x_666;
} else {
 lean_dec_ref(x_666);
 x_668 = lean_box(0);
}
if (lean_is_scalar(x_668)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_668;
}
lean_ctor_set(x_669, 0, x_9);
lean_ctor_set(x_669, 1, x_667);
x_670 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(x_10, x_663);
x_671 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
x_672 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_inc(x_670);
x_673 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_671, x_672, x_670, x_2, x_669);
x_674 = lean_ctor_get(x_673, 1);
lean_inc(x_674);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 x_675 = x_673;
} else {
 lean_dec_ref(x_673);
 x_675 = lean_box(0);
}
if (lean_is_scalar(x_675)) {
 x_676 = lean_alloc_ctor(0, 2, 0);
} else {
 x_676 = x_675;
}
lean_ctor_set(x_676, 0, x_9);
lean_ctor_set(x_676, 1, x_674);
x_677 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_10, x_670);
x_678 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_679 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_677);
x_680 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_678, x_679, x_677, x_2, x_676);
x_681 = lean_ctor_get(x_680, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_682 = x_680;
} else {
 lean_dec_ref(x_680);
 x_682 = lean_box(0);
}
if (lean_is_scalar(x_682)) {
 x_683 = lean_alloc_ctor(0, 2, 0);
} else {
 x_683 = x_682;
}
lean_ctor_set(x_683, 0, x_9);
lean_ctor_set(x_683, 1, x_681);
x_684 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_677);
x_685 = l_Lean_IR_inferBorrow(x_684, x_2, x_683);
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 x_688 = x_685;
} else {
 lean_dec_ref(x_685);
 x_688 = lean_box(0);
}
if (lean_is_scalar(x_688)) {
 x_689 = lean_alloc_ctor(0, 2, 0);
} else {
 x_689 = x_688;
}
lean_ctor_set(x_689, 0, x_9);
lean_ctor_set(x_689, 1, x_687);
x_690 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_691 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_686);
x_692 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_690, x_691, x_686, x_2, x_689);
x_693 = lean_ctor_get(x_692, 1);
lean_inc(x_693);
if (lean_is_exclusive(x_692)) {
 lean_ctor_release(x_692, 0);
 lean_ctor_release(x_692, 1);
 x_694 = x_692;
} else {
 lean_dec_ref(x_692);
 x_694 = lean_box(0);
}
if (lean_is_scalar(x_694)) {
 x_695 = lean_alloc_ctor(0, 2, 0);
} else {
 x_695 = x_694;
}
lean_ctor_set(x_695, 0, x_9);
lean_ctor_set(x_695, 1, x_693);
x_696 = l_Lean_IR_explicitBoxing(x_686, x_2, x_695);
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
if (lean_is_exclusive(x_696)) {
 lean_ctor_release(x_696, 0);
 lean_ctor_release(x_696, 1);
 x_699 = x_696;
} else {
 lean_dec_ref(x_696);
 x_699 = lean_box(0);
}
if (lean_is_scalar(x_699)) {
 x_700 = lean_alloc_ctor(0, 2, 0);
} else {
 x_700 = x_699;
}
lean_ctor_set(x_700, 0, x_9);
lean_ctor_set(x_700, 1, x_698);
x_701 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_702 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_697);
x_703 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_701, x_702, x_697, x_2, x_700);
x_704 = lean_ctor_get(x_703, 1);
lean_inc(x_704);
if (lean_is_exclusive(x_703)) {
 lean_ctor_release(x_703, 0);
 lean_ctor_release(x_703, 1);
 x_705 = x_703;
} else {
 lean_dec_ref(x_703);
 x_705 = lean_box(0);
}
if (lean_is_scalar(x_705)) {
 x_706 = lean_alloc_ctor(0, 2, 0);
} else {
 x_706 = x_705;
}
lean_ctor_set(x_706, 0, x_9);
lean_ctor_set(x_706, 1, x_704);
x_707 = l_Lean_IR_explicitRC(x_697, x_2, x_706);
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_710 = x_707;
} else {
 lean_dec_ref(x_707);
 x_710 = lean_box(0);
}
if (lean_is_scalar(x_710)) {
 x_711 = lean_alloc_ctor(0, 2, 0);
} else {
 x_711 = x_710;
}
lean_ctor_set(x_711, 0, x_9);
lean_ctor_set(x_711, 1, x_709);
x_712 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_713 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_708);
x_714 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_712, x_713, x_708, x_2, x_711);
x_715 = lean_ctor_get(x_714, 1);
lean_inc(x_715);
if (lean_is_exclusive(x_714)) {
 lean_ctor_release(x_714, 0);
 lean_ctor_release(x_714, 1);
 x_716 = x_714;
} else {
 lean_dec_ref(x_714);
 x_716 = lean_box(0);
}
if (lean_is_scalar(x_716)) {
 x_717 = lean_alloc_ctor(0, 2, 0);
} else {
 x_717 = x_716;
}
lean_ctor_set(x_717, 0, x_9);
lean_ctor_set(x_717, 1, x_715);
x_718 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_10, x_708);
x_719 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_720 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_718);
x_721 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_719, x_720, x_718, x_2, x_717);
x_722 = lean_ctor_get(x_721, 1);
lean_inc(x_722);
if (lean_is_exclusive(x_721)) {
 lean_ctor_release(x_721, 0);
 lean_ctor_release(x_721, 1);
 x_723 = x_721;
} else {
 lean_dec_ref(x_721);
 x_723 = lean_box(0);
}
if (lean_is_scalar(x_723)) {
 x_724 = lean_alloc_ctor(0, 2, 0);
} else {
 x_724 = x_723;
}
lean_ctor_set(x_724, 0, x_9);
lean_ctor_set(x_724, 1, x_722);
x_725 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_718);
lean_inc(x_725);
x_726 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_23, x_24, x_725, x_2, x_724);
x_727 = lean_ctor_get(x_726, 1);
lean_inc(x_727);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_728 = x_726;
} else {
 lean_dec_ref(x_726);
 x_728 = lean_box(0);
}
if (lean_is_scalar(x_728)) {
 x_729 = lean_alloc_ctor(0, 2, 0);
} else {
 x_729 = x_728;
}
lean_ctor_set(x_729, 0, x_9);
lean_ctor_set(x_729, 1, x_727);
x_730 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_731 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_725);
x_732 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_730, x_731, x_725, x_2, x_729);
x_733 = lean_ctor_get(x_732, 1);
lean_inc(x_733);
if (lean_is_exclusive(x_732)) {
 lean_ctor_release(x_732, 0);
 lean_ctor_release(x_732, 1);
 x_734 = x_732;
} else {
 lean_dec_ref(x_732);
 x_734 = lean_box(0);
}
if (lean_is_scalar(x_734)) {
 x_735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_735 = x_734;
}
lean_ctor_set(x_735, 0, x_9);
lean_ctor_set(x_735, 1, x_733);
lean_inc(x_725);
x_736 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_725, x_725, x_10, x_2, x_735);
if (lean_obj_tag(x_736) == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_737 = lean_ctor_get(x_736, 1);
lean_inc(x_737);
if (lean_is_exclusive(x_736)) {
 lean_ctor_release(x_736, 0);
 lean_ctor_release(x_736, 1);
 x_738 = x_736;
} else {
 lean_dec_ref(x_736);
 x_738 = lean_box(0);
}
if (lean_is_scalar(x_738)) {
 x_739 = lean_alloc_ctor(0, 2, 0);
} else {
 x_739 = x_738;
}
lean_ctor_set(x_739, 0, x_9);
lean_ctor_set(x_739, 1, x_737);
x_740 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_725, x_10, x_2, x_739);
lean_dec(x_725);
x_741 = lean_ctor_get(x_740, 1);
lean_inc(x_741);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 lean_ctor_release(x_740, 1);
 x_742 = x_740;
} else {
 lean_dec_ref(x_740);
 x_742 = lean_box(0);
}
if (lean_is_scalar(x_742)) {
 x_743 = lean_alloc_ctor(0, 2, 0);
} else {
 x_743 = x_742;
}
lean_ctor_set(x_743, 0, x_9);
lean_ctor_set(x_743, 1, x_741);
return x_743;
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
lean_dec(x_725);
x_744 = lean_ctor_get(x_736, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_736, 1);
lean_inc(x_745);
if (lean_is_exclusive(x_736)) {
 lean_ctor_release(x_736, 0);
 lean_ctor_release(x_736, 1);
 x_746 = x_736;
} else {
 lean_dec_ref(x_736);
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
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_748 = lean_ctor_get(x_19, 1);
lean_inc(x_748);
lean_dec(x_19);
x_749 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_749, 0, x_9);
lean_ctor_set(x_749, 1, x_748);
x_750 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_16);
x_751 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7;
x_752 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6;
lean_inc(x_750);
x_753 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_751, x_752, x_750, x_2, x_749);
x_754 = lean_ctor_get(x_753, 1);
lean_inc(x_754);
if (lean_is_exclusive(x_753)) {
 lean_ctor_release(x_753, 0);
 lean_ctor_release(x_753, 1);
 x_755 = x_753;
} else {
 lean_dec_ref(x_753);
 x_755 = lean_box(0);
}
if (lean_is_scalar(x_755)) {
 x_756 = lean_alloc_ctor(0, 2, 0);
} else {
 x_756 = x_755;
}
lean_ctor_set(x_756, 0, x_9);
lean_ctor_set(x_756, 1, x_754);
x_757 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__2(x_10, x_750);
x_758 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10;
x_759 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
lean_inc(x_757);
x_760 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_758, x_759, x_757, x_2, x_756);
x_761 = lean_ctor_get(x_760, 1);
lean_inc(x_761);
if (lean_is_exclusive(x_760)) {
 lean_ctor_release(x_760, 0);
 lean_ctor_release(x_760, 1);
 x_762 = x_760;
} else {
 lean_dec_ref(x_760);
 x_762 = lean_box(0);
}
if (lean_is_scalar(x_762)) {
 x_763 = lean_alloc_ctor(0, 2, 0);
} else {
 x_763 = x_762;
}
lean_ctor_set(x_763, 0, x_9);
lean_ctor_set(x_763, 1, x_761);
x_764 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(x_10, x_757);
x_765 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
x_766 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_inc(x_764);
x_767 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_765, x_766, x_764, x_2, x_763);
x_768 = lean_ctor_get(x_767, 1);
lean_inc(x_768);
if (lean_is_exclusive(x_767)) {
 lean_ctor_release(x_767, 0);
 lean_ctor_release(x_767, 1);
 x_769 = x_767;
} else {
 lean_dec_ref(x_767);
 x_769 = lean_box(0);
}
if (lean_is_scalar(x_769)) {
 x_770 = lean_alloc_ctor(0, 2, 0);
} else {
 x_770 = x_769;
}
lean_ctor_set(x_770, 0, x_9);
lean_ctor_set(x_770, 1, x_768);
x_771 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_10, x_764);
x_772 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_773 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_771);
x_774 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_772, x_773, x_771, x_2, x_770);
x_775 = lean_ctor_get(x_774, 1);
lean_inc(x_775);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 x_776 = x_774;
} else {
 lean_dec_ref(x_774);
 x_776 = lean_box(0);
}
if (lean_is_scalar(x_776)) {
 x_777 = lean_alloc_ctor(0, 2, 0);
} else {
 x_777 = x_776;
}
lean_ctor_set(x_777, 0, x_9);
lean_ctor_set(x_777, 1, x_775);
x_778 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_771);
x_779 = l_Lean_IR_inferBorrow(x_778, x_2, x_777);
x_780 = lean_ctor_get(x_779, 0);
lean_inc(x_780);
x_781 = lean_ctor_get(x_779, 1);
lean_inc(x_781);
if (lean_is_exclusive(x_779)) {
 lean_ctor_release(x_779, 0);
 lean_ctor_release(x_779, 1);
 x_782 = x_779;
} else {
 lean_dec_ref(x_779);
 x_782 = lean_box(0);
}
if (lean_is_scalar(x_782)) {
 x_783 = lean_alloc_ctor(0, 2, 0);
} else {
 x_783 = x_782;
}
lean_ctor_set(x_783, 0, x_9);
lean_ctor_set(x_783, 1, x_781);
x_784 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_785 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_780);
x_786 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_784, x_785, x_780, x_2, x_783);
x_787 = lean_ctor_get(x_786, 1);
lean_inc(x_787);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 x_788 = x_786;
} else {
 lean_dec_ref(x_786);
 x_788 = lean_box(0);
}
if (lean_is_scalar(x_788)) {
 x_789 = lean_alloc_ctor(0, 2, 0);
} else {
 x_789 = x_788;
}
lean_ctor_set(x_789, 0, x_9);
lean_ctor_set(x_789, 1, x_787);
x_790 = l_Lean_IR_explicitBoxing(x_780, x_2, x_789);
x_791 = lean_ctor_get(x_790, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_790, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_790)) {
 lean_ctor_release(x_790, 0);
 lean_ctor_release(x_790, 1);
 x_793 = x_790;
} else {
 lean_dec_ref(x_790);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(0, 2, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_9);
lean_ctor_set(x_794, 1, x_792);
x_795 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_796 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_791);
x_797 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_795, x_796, x_791, x_2, x_794);
x_798 = lean_ctor_get(x_797, 1);
lean_inc(x_798);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 x_799 = x_797;
} else {
 lean_dec_ref(x_797);
 x_799 = lean_box(0);
}
if (lean_is_scalar(x_799)) {
 x_800 = lean_alloc_ctor(0, 2, 0);
} else {
 x_800 = x_799;
}
lean_ctor_set(x_800, 0, x_9);
lean_ctor_set(x_800, 1, x_798);
x_801 = l_Lean_IR_explicitRC(x_791, x_2, x_800);
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_801, 1);
lean_inc(x_803);
if (lean_is_exclusive(x_801)) {
 lean_ctor_release(x_801, 0);
 lean_ctor_release(x_801, 1);
 x_804 = x_801;
} else {
 lean_dec_ref(x_801);
 x_804 = lean_box(0);
}
if (lean_is_scalar(x_804)) {
 x_805 = lean_alloc_ctor(0, 2, 0);
} else {
 x_805 = x_804;
}
lean_ctor_set(x_805, 0, x_9);
lean_ctor_set(x_805, 1, x_803);
x_806 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_807 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_802);
x_808 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_806, x_807, x_802, x_2, x_805);
x_809 = lean_ctor_get(x_808, 1);
lean_inc(x_809);
if (lean_is_exclusive(x_808)) {
 lean_ctor_release(x_808, 0);
 lean_ctor_release(x_808, 1);
 x_810 = x_808;
} else {
 lean_dec_ref(x_808);
 x_810 = lean_box(0);
}
if (lean_is_scalar(x_810)) {
 x_811 = lean_alloc_ctor(0, 2, 0);
} else {
 x_811 = x_810;
}
lean_ctor_set(x_811, 0, x_9);
lean_ctor_set(x_811, 1, x_809);
x_812 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_10, x_802);
x_813 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_814 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_812);
x_815 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_813, x_814, x_812, x_2, x_811);
x_816 = lean_ctor_get(x_815, 1);
lean_inc(x_816);
if (lean_is_exclusive(x_815)) {
 lean_ctor_release(x_815, 0);
 lean_ctor_release(x_815, 1);
 x_817 = x_815;
} else {
 lean_dec_ref(x_815);
 x_817 = lean_box(0);
}
if (lean_is_scalar(x_817)) {
 x_818 = lean_alloc_ctor(0, 2, 0);
} else {
 x_818 = x_817;
}
lean_ctor_set(x_818, 0, x_9);
lean_ctor_set(x_818, 1, x_816);
x_819 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_812);
lean_inc(x_819);
x_820 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_751, x_752, x_819, x_2, x_818);
x_821 = lean_ctor_get(x_820, 1);
lean_inc(x_821);
if (lean_is_exclusive(x_820)) {
 lean_ctor_release(x_820, 0);
 lean_ctor_release(x_820, 1);
 x_822 = x_820;
} else {
 lean_dec_ref(x_820);
 x_822 = lean_box(0);
}
if (lean_is_scalar(x_822)) {
 x_823 = lean_alloc_ctor(0, 2, 0);
} else {
 x_823 = x_822;
}
lean_ctor_set(x_823, 0, x_9);
lean_ctor_set(x_823, 1, x_821);
x_824 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_825 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_819);
x_826 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_824, x_825, x_819, x_2, x_823);
x_827 = lean_ctor_get(x_826, 1);
lean_inc(x_827);
if (lean_is_exclusive(x_826)) {
 lean_ctor_release(x_826, 0);
 lean_ctor_release(x_826, 1);
 x_828 = x_826;
} else {
 lean_dec_ref(x_826);
 x_828 = lean_box(0);
}
if (lean_is_scalar(x_828)) {
 x_829 = lean_alloc_ctor(0, 2, 0);
} else {
 x_829 = x_828;
}
lean_ctor_set(x_829, 0, x_9);
lean_ctor_set(x_829, 1, x_827);
lean_inc(x_819);
x_830 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_819, x_819, x_10, x_2, x_829);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_831 = lean_ctor_get(x_830, 1);
lean_inc(x_831);
if (lean_is_exclusive(x_830)) {
 lean_ctor_release(x_830, 0);
 lean_ctor_release(x_830, 1);
 x_832 = x_830;
} else {
 lean_dec_ref(x_830);
 x_832 = lean_box(0);
}
if (lean_is_scalar(x_832)) {
 x_833 = lean_alloc_ctor(0, 2, 0);
} else {
 x_833 = x_832;
}
lean_ctor_set(x_833, 0, x_9);
lean_ctor_set(x_833, 1, x_831);
x_834 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_819, x_10, x_2, x_833);
lean_dec(x_819);
x_835 = lean_ctor_get(x_834, 1);
lean_inc(x_835);
if (lean_is_exclusive(x_834)) {
 lean_ctor_release(x_834, 0);
 lean_ctor_release(x_834, 1);
 x_836 = x_834;
} else {
 lean_dec_ref(x_834);
 x_836 = lean_box(0);
}
if (lean_is_scalar(x_836)) {
 x_837 = lean_alloc_ctor(0, 2, 0);
} else {
 x_837 = x_836;
}
lean_ctor_set(x_837, 0, x_9);
lean_ctor_set(x_837, 1, x_835);
return x_837;
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; 
lean_dec(x_819);
x_838 = lean_ctor_get(x_830, 0);
lean_inc(x_838);
x_839 = lean_ctor_get(x_830, 1);
lean_inc(x_839);
if (lean_is_exclusive(x_830)) {
 lean_ctor_release(x_830, 0);
 lean_ctor_release(x_830, 1);
 x_840 = x_830;
} else {
 lean_dec_ref(x_830);
 x_840 = lean_box(0);
}
if (lean_is_scalar(x_840)) {
 x_841 = lean_alloc_ctor(1, 2, 0);
} else {
 x_841 = x_840;
}
lean_ctor_set(x_841, 0, x_838);
lean_ctor_set(x_841, 1, x_839);
return x_841;
}
}
}
else
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; 
x_842 = lean_ctor_get(x_14, 0);
x_843 = lean_ctor_get(x_14, 1);
lean_inc(x_843);
lean_inc(x_842);
lean_dec(x_14);
x_844 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_844, 0, x_9);
lean_ctor_set(x_844, 1, x_843);
x_845 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__4;
x_846 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3;
lean_inc(x_842);
x_847 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_845, x_846, x_842, x_2, x_844);
x_848 = lean_ctor_get(x_847, 1);
lean_inc(x_848);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 x_849 = x_847;
} else {
 lean_dec_ref(x_847);
 x_849 = lean_box(0);
}
if (lean_is_scalar(x_849)) {
 x_850 = lean_alloc_ctor(0, 2, 0);
} else {
 x_850 = x_849;
}
lean_ctor_set(x_850, 0, x_9);
lean_ctor_set(x_850, 1, x_848);
x_851 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_842);
x_852 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7;
x_853 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6;
lean_inc(x_851);
x_854 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_852, x_853, x_851, x_2, x_850);
x_855 = lean_ctor_get(x_854, 1);
lean_inc(x_855);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_856 = x_854;
} else {
 lean_dec_ref(x_854);
 x_856 = lean_box(0);
}
if (lean_is_scalar(x_856)) {
 x_857 = lean_alloc_ctor(0, 2, 0);
} else {
 x_857 = x_856;
}
lean_ctor_set(x_857, 0, x_9);
lean_ctor_set(x_857, 1, x_855);
x_858 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__2(x_10, x_851);
x_859 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10;
x_860 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
lean_inc(x_858);
x_861 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_859, x_860, x_858, x_2, x_857);
x_862 = lean_ctor_get(x_861, 1);
lean_inc(x_862);
if (lean_is_exclusive(x_861)) {
 lean_ctor_release(x_861, 0);
 lean_ctor_release(x_861, 1);
 x_863 = x_861;
} else {
 lean_dec_ref(x_861);
 x_863 = lean_box(0);
}
if (lean_is_scalar(x_863)) {
 x_864 = lean_alloc_ctor(0, 2, 0);
} else {
 x_864 = x_863;
}
lean_ctor_set(x_864, 0, x_9);
lean_ctor_set(x_864, 1, x_862);
x_865 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(x_10, x_858);
x_866 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
x_867 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_inc(x_865);
x_868 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_866, x_867, x_865, x_2, x_864);
x_869 = lean_ctor_get(x_868, 1);
lean_inc(x_869);
if (lean_is_exclusive(x_868)) {
 lean_ctor_release(x_868, 0);
 lean_ctor_release(x_868, 1);
 x_870 = x_868;
} else {
 lean_dec_ref(x_868);
 x_870 = lean_box(0);
}
if (lean_is_scalar(x_870)) {
 x_871 = lean_alloc_ctor(0, 2, 0);
} else {
 x_871 = x_870;
}
lean_ctor_set(x_871, 0, x_9);
lean_ctor_set(x_871, 1, x_869);
x_872 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_10, x_865);
x_873 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_874 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_872);
x_875 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_873, x_874, x_872, x_2, x_871);
x_876 = lean_ctor_get(x_875, 1);
lean_inc(x_876);
if (lean_is_exclusive(x_875)) {
 lean_ctor_release(x_875, 0);
 lean_ctor_release(x_875, 1);
 x_877 = x_875;
} else {
 lean_dec_ref(x_875);
 x_877 = lean_box(0);
}
if (lean_is_scalar(x_877)) {
 x_878 = lean_alloc_ctor(0, 2, 0);
} else {
 x_878 = x_877;
}
lean_ctor_set(x_878, 0, x_9);
lean_ctor_set(x_878, 1, x_876);
x_879 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_872);
x_880 = l_Lean_IR_inferBorrow(x_879, x_2, x_878);
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_880, 1);
lean_inc(x_882);
if (lean_is_exclusive(x_880)) {
 lean_ctor_release(x_880, 0);
 lean_ctor_release(x_880, 1);
 x_883 = x_880;
} else {
 lean_dec_ref(x_880);
 x_883 = lean_box(0);
}
if (lean_is_scalar(x_883)) {
 x_884 = lean_alloc_ctor(0, 2, 0);
} else {
 x_884 = x_883;
}
lean_ctor_set(x_884, 0, x_9);
lean_ctor_set(x_884, 1, x_882);
x_885 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_886 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_881);
x_887 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_885, x_886, x_881, x_2, x_884);
x_888 = lean_ctor_get(x_887, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_887)) {
 lean_ctor_release(x_887, 0);
 lean_ctor_release(x_887, 1);
 x_889 = x_887;
} else {
 lean_dec_ref(x_887);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_890 = lean_alloc_ctor(0, 2, 0);
} else {
 x_890 = x_889;
}
lean_ctor_set(x_890, 0, x_9);
lean_ctor_set(x_890, 1, x_888);
x_891 = l_Lean_IR_explicitBoxing(x_881, x_2, x_890);
x_892 = lean_ctor_get(x_891, 0);
lean_inc(x_892);
x_893 = lean_ctor_get(x_891, 1);
lean_inc(x_893);
if (lean_is_exclusive(x_891)) {
 lean_ctor_release(x_891, 0);
 lean_ctor_release(x_891, 1);
 x_894 = x_891;
} else {
 lean_dec_ref(x_891);
 x_894 = lean_box(0);
}
if (lean_is_scalar(x_894)) {
 x_895 = lean_alloc_ctor(0, 2, 0);
} else {
 x_895 = x_894;
}
lean_ctor_set(x_895, 0, x_9);
lean_ctor_set(x_895, 1, x_893);
x_896 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_897 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_892);
x_898 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_896, x_897, x_892, x_2, x_895);
x_899 = lean_ctor_get(x_898, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_900 = x_898;
} else {
 lean_dec_ref(x_898);
 x_900 = lean_box(0);
}
if (lean_is_scalar(x_900)) {
 x_901 = lean_alloc_ctor(0, 2, 0);
} else {
 x_901 = x_900;
}
lean_ctor_set(x_901, 0, x_9);
lean_ctor_set(x_901, 1, x_899);
x_902 = l_Lean_IR_explicitRC(x_892, x_2, x_901);
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_902, 1);
lean_inc(x_904);
if (lean_is_exclusive(x_902)) {
 lean_ctor_release(x_902, 0);
 lean_ctor_release(x_902, 1);
 x_905 = x_902;
} else {
 lean_dec_ref(x_902);
 x_905 = lean_box(0);
}
if (lean_is_scalar(x_905)) {
 x_906 = lean_alloc_ctor(0, 2, 0);
} else {
 x_906 = x_905;
}
lean_ctor_set(x_906, 0, x_9);
lean_ctor_set(x_906, 1, x_904);
x_907 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_908 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_903);
x_909 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_907, x_908, x_903, x_2, x_906);
x_910 = lean_ctor_get(x_909, 1);
lean_inc(x_910);
if (lean_is_exclusive(x_909)) {
 lean_ctor_release(x_909, 0);
 lean_ctor_release(x_909, 1);
 x_911 = x_909;
} else {
 lean_dec_ref(x_909);
 x_911 = lean_box(0);
}
if (lean_is_scalar(x_911)) {
 x_912 = lean_alloc_ctor(0, 2, 0);
} else {
 x_912 = x_911;
}
lean_ctor_set(x_912, 0, x_9);
lean_ctor_set(x_912, 1, x_910);
x_913 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_10, x_903);
x_914 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_915 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_913);
x_916 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_914, x_915, x_913, x_2, x_912);
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
x_920 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_913);
lean_inc(x_920);
x_921 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_852, x_853, x_920, x_2, x_919);
x_922 = lean_ctor_get(x_921, 1);
lean_inc(x_922);
if (lean_is_exclusive(x_921)) {
 lean_ctor_release(x_921, 0);
 lean_ctor_release(x_921, 1);
 x_923 = x_921;
} else {
 lean_dec_ref(x_921);
 x_923 = lean_box(0);
}
if (lean_is_scalar(x_923)) {
 x_924 = lean_alloc_ctor(0, 2, 0);
} else {
 x_924 = x_923;
}
lean_ctor_set(x_924, 0, x_9);
lean_ctor_set(x_924, 1, x_922);
x_925 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_926 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_920);
x_927 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_925, x_926, x_920, x_2, x_924);
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
lean_inc(x_920);
x_931 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_920, x_920, x_10, x_2, x_930);
if (lean_obj_tag(x_931) == 0)
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_932 = lean_ctor_get(x_931, 1);
lean_inc(x_932);
if (lean_is_exclusive(x_931)) {
 lean_ctor_release(x_931, 0);
 lean_ctor_release(x_931, 1);
 x_933 = x_931;
} else {
 lean_dec_ref(x_931);
 x_933 = lean_box(0);
}
if (lean_is_scalar(x_933)) {
 x_934 = lean_alloc_ctor(0, 2, 0);
} else {
 x_934 = x_933;
}
lean_ctor_set(x_934, 0, x_9);
lean_ctor_set(x_934, 1, x_932);
x_935 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_920, x_10, x_2, x_934);
lean_dec(x_920);
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
return x_938;
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
lean_dec(x_920);
x_939 = lean_ctor_get(x_931, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_931, 1);
lean_inc(x_940);
if (lean_is_exclusive(x_931)) {
 lean_ctor_release(x_931, 0);
 lean_ctor_release(x_931, 1);
 x_941 = x_931;
} else {
 lean_dec_ref(x_931);
 x_941 = lean_box(0);
}
if (lean_is_scalar(x_941)) {
 x_942 = lean_alloc_ctor(1, 2, 0);
} else {
 x_942 = x_941;
}
lean_ctor_set(x_942, 0, x_939);
lean_ctor_set(x_942, 1, x_940);
return x_942;
}
}
}
else
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
x_943 = lean_ctor_get(x_11, 1);
lean_inc(x_943);
lean_dec(x_11);
x_944 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_944, 0, x_9);
lean_ctor_set(x_944, 1, x_943);
x_945 = l_Lean_IR_elimDeadBranches(x_1, x_2, x_944);
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_948 = x_945;
} else {
 lean_dec_ref(x_945);
 x_948 = lean_box(0);
}
if (lean_is_scalar(x_948)) {
 x_949 = lean_alloc_ctor(0, 2, 0);
} else {
 x_949 = x_948;
}
lean_ctor_set(x_949, 0, x_9);
lean_ctor_set(x_949, 1, x_947);
x_950 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__4;
x_951 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3;
lean_inc(x_946);
x_952 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_950, x_951, x_946, x_2, x_949);
x_953 = lean_ctor_get(x_952, 1);
lean_inc(x_953);
if (lean_is_exclusive(x_952)) {
 lean_ctor_release(x_952, 0);
 lean_ctor_release(x_952, 1);
 x_954 = x_952;
} else {
 lean_dec_ref(x_952);
 x_954 = lean_box(0);
}
if (lean_is_scalar(x_954)) {
 x_955 = lean_alloc_ctor(0, 2, 0);
} else {
 x_955 = x_954;
}
lean_ctor_set(x_955, 0, x_9);
lean_ctor_set(x_955, 1, x_953);
x_956 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_946);
x_957 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7;
x_958 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6;
lean_inc(x_956);
x_959 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_957, x_958, x_956, x_2, x_955);
x_960 = lean_ctor_get(x_959, 1);
lean_inc(x_960);
if (lean_is_exclusive(x_959)) {
 lean_ctor_release(x_959, 0);
 lean_ctor_release(x_959, 1);
 x_961 = x_959;
} else {
 lean_dec_ref(x_959);
 x_961 = lean_box(0);
}
if (lean_is_scalar(x_961)) {
 x_962 = lean_alloc_ctor(0, 2, 0);
} else {
 x_962 = x_961;
}
lean_ctor_set(x_962, 0, x_9);
lean_ctor_set(x_962, 1, x_960);
x_963 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__2(x_10, x_956);
x_964 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10;
x_965 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
lean_inc(x_963);
x_966 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_964, x_965, x_963, x_2, x_962);
x_967 = lean_ctor_get(x_966, 1);
lean_inc(x_967);
if (lean_is_exclusive(x_966)) {
 lean_ctor_release(x_966, 0);
 lean_ctor_release(x_966, 1);
 x_968 = x_966;
} else {
 lean_dec_ref(x_966);
 x_968 = lean_box(0);
}
if (lean_is_scalar(x_968)) {
 x_969 = lean_alloc_ctor(0, 2, 0);
} else {
 x_969 = x_968;
}
lean_ctor_set(x_969, 0, x_9);
lean_ctor_set(x_969, 1, x_967);
x_970 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(x_10, x_963);
x_971 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
x_972 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_inc(x_970);
x_973 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_971, x_972, x_970, x_2, x_969);
x_974 = lean_ctor_get(x_973, 1);
lean_inc(x_974);
if (lean_is_exclusive(x_973)) {
 lean_ctor_release(x_973, 0);
 lean_ctor_release(x_973, 1);
 x_975 = x_973;
} else {
 lean_dec_ref(x_973);
 x_975 = lean_box(0);
}
if (lean_is_scalar(x_975)) {
 x_976 = lean_alloc_ctor(0, 2, 0);
} else {
 x_976 = x_975;
}
lean_ctor_set(x_976, 0, x_9);
lean_ctor_set(x_976, 1, x_974);
x_977 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_10, x_970);
x_978 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_979 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_977);
x_980 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_978, x_979, x_977, x_2, x_976);
x_981 = lean_ctor_get(x_980, 1);
lean_inc(x_981);
if (lean_is_exclusive(x_980)) {
 lean_ctor_release(x_980, 0);
 lean_ctor_release(x_980, 1);
 x_982 = x_980;
} else {
 lean_dec_ref(x_980);
 x_982 = lean_box(0);
}
if (lean_is_scalar(x_982)) {
 x_983 = lean_alloc_ctor(0, 2, 0);
} else {
 x_983 = x_982;
}
lean_ctor_set(x_983, 0, x_9);
lean_ctor_set(x_983, 1, x_981);
x_984 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_10, x_977);
x_985 = l_Lean_IR_inferBorrow(x_984, x_2, x_983);
x_986 = lean_ctor_get(x_985, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_985, 1);
lean_inc(x_987);
if (lean_is_exclusive(x_985)) {
 lean_ctor_release(x_985, 0);
 lean_ctor_release(x_985, 1);
 x_988 = x_985;
} else {
 lean_dec_ref(x_985);
 x_988 = lean_box(0);
}
if (lean_is_scalar(x_988)) {
 x_989 = lean_alloc_ctor(0, 2, 0);
} else {
 x_989 = x_988;
}
lean_ctor_set(x_989, 0, x_9);
lean_ctor_set(x_989, 1, x_987);
x_990 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_991 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_986);
x_992 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_990, x_991, x_986, x_2, x_989);
x_993 = lean_ctor_get(x_992, 1);
lean_inc(x_993);
if (lean_is_exclusive(x_992)) {
 lean_ctor_release(x_992, 0);
 lean_ctor_release(x_992, 1);
 x_994 = x_992;
} else {
 lean_dec_ref(x_992);
 x_994 = lean_box(0);
}
if (lean_is_scalar(x_994)) {
 x_995 = lean_alloc_ctor(0, 2, 0);
} else {
 x_995 = x_994;
}
lean_ctor_set(x_995, 0, x_9);
lean_ctor_set(x_995, 1, x_993);
x_996 = l_Lean_IR_explicitBoxing(x_986, x_2, x_995);
x_997 = lean_ctor_get(x_996, 0);
lean_inc(x_997);
x_998 = lean_ctor_get(x_996, 1);
lean_inc(x_998);
if (lean_is_exclusive(x_996)) {
 lean_ctor_release(x_996, 0);
 lean_ctor_release(x_996, 1);
 x_999 = x_996;
} else {
 lean_dec_ref(x_996);
 x_999 = lean_box(0);
}
if (lean_is_scalar(x_999)) {
 x_1000 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1000 = x_999;
}
lean_ctor_set(x_1000, 0, x_9);
lean_ctor_set(x_1000, 1, x_998);
x_1001 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_1002 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_997);
x_1003 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1001, x_1002, x_997, x_2, x_1000);
x_1004 = lean_ctor_get(x_1003, 1);
lean_inc(x_1004);
if (lean_is_exclusive(x_1003)) {
 lean_ctor_release(x_1003, 0);
 lean_ctor_release(x_1003, 1);
 x_1005 = x_1003;
} else {
 lean_dec_ref(x_1003);
 x_1005 = lean_box(0);
}
if (lean_is_scalar(x_1005)) {
 x_1006 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1006 = x_1005;
}
lean_ctor_set(x_1006, 0, x_9);
lean_ctor_set(x_1006, 1, x_1004);
x_1007 = l_Lean_IR_explicitRC(x_997, x_2, x_1006);
x_1008 = lean_ctor_get(x_1007, 0);
lean_inc(x_1008);
x_1009 = lean_ctor_get(x_1007, 1);
lean_inc(x_1009);
if (lean_is_exclusive(x_1007)) {
 lean_ctor_release(x_1007, 0);
 lean_ctor_release(x_1007, 1);
 x_1010 = x_1007;
} else {
 lean_dec_ref(x_1007);
 x_1010 = lean_box(0);
}
if (lean_is_scalar(x_1010)) {
 x_1011 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1011 = x_1010;
}
lean_ctor_set(x_1011, 0, x_9);
lean_ctor_set(x_1011, 1, x_1009);
x_1012 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_1013 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_1008);
x_1014 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1012, x_1013, x_1008, x_2, x_1011);
x_1015 = lean_ctor_get(x_1014, 1);
lean_inc(x_1015);
if (lean_is_exclusive(x_1014)) {
 lean_ctor_release(x_1014, 0);
 lean_ctor_release(x_1014, 1);
 x_1016 = x_1014;
} else {
 lean_dec_ref(x_1014);
 x_1016 = lean_box(0);
}
if (lean_is_scalar(x_1016)) {
 x_1017 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1017 = x_1016;
}
lean_ctor_set(x_1017, 0, x_9);
lean_ctor_set(x_1017, 1, x_1015);
x_1018 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_10, x_1008);
x_1019 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_1020 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_1018);
x_1021 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1019, x_1020, x_1018, x_2, x_1017);
x_1022 = lean_ctor_get(x_1021, 1);
lean_inc(x_1022);
if (lean_is_exclusive(x_1021)) {
 lean_ctor_release(x_1021, 0);
 lean_ctor_release(x_1021, 1);
 x_1023 = x_1021;
} else {
 lean_dec_ref(x_1021);
 x_1023 = lean_box(0);
}
if (lean_is_scalar(x_1023)) {
 x_1024 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1024 = x_1023;
}
lean_ctor_set(x_1024, 0, x_9);
lean_ctor_set(x_1024, 1, x_1022);
x_1025 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_10, x_1018);
lean_inc(x_1025);
x_1026 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_957, x_958, x_1025, x_2, x_1024);
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
x_1030 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_1031 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_1025);
x_1032 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1030, x_1031, x_1025, x_2, x_1029);
x_1033 = lean_ctor_get(x_1032, 1);
lean_inc(x_1033);
if (lean_is_exclusive(x_1032)) {
 lean_ctor_release(x_1032, 0);
 lean_ctor_release(x_1032, 1);
 x_1034 = x_1032;
} else {
 lean_dec_ref(x_1032);
 x_1034 = lean_box(0);
}
if (lean_is_scalar(x_1034)) {
 x_1035 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1035 = x_1034;
}
lean_ctor_set(x_1035, 0, x_9);
lean_ctor_set(x_1035, 1, x_1033);
lean_inc(x_1025);
x_1036 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1025, x_1025, x_10, x_2, x_1035);
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
x_1040 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_1025, x_10, x_2, x_1039);
lean_dec(x_1025);
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
return x_1043;
}
else
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
lean_dec(x_1025);
x_1044 = lean_ctor_get(x_1036, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1036, 1);
lean_inc(x_1045);
if (lean_is_exclusive(x_1036)) {
 lean_ctor_release(x_1036, 0);
 lean_ctor_release(x_1036, 1);
 x_1046 = x_1036;
} else {
 lean_dec_ref(x_1036);
 x_1046 = lean_box(0);
}
if (lean_is_scalar(x_1046)) {
 x_1047 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1047 = x_1046;
}
lean_ctor_set(x_1047, 0, x_1044);
lean_ctor_set(x_1047, 1, x_1045);
return x_1047;
}
}
}
else
{
uint8_t x_1048; 
lean_dec(x_1);
x_1048 = !lean_is_exclusive(x_11);
if (x_1048 == 0)
{
return x_11;
}
else
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
x_1049 = lean_ctor_get(x_11, 0);
x_1050 = lean_ctor_get(x_11, 1);
lean_inc(x_1050);
lean_inc(x_1049);
lean_dec(x_11);
x_1051 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1051, 0, x_1049);
lean_ctor_set(x_1051, 1, x_1050);
return x_1051;
}
}
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
x_1052 = lean_ctor_get(x_6, 1);
lean_inc(x_1052);
lean_dec(x_6);
x_1053 = lean_box(0);
x_1054 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1054, 0, x_1053);
lean_ctor_set(x_1054, 1, x_1052);
x_1055 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_1056 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1, x_1, x_1055, x_2, x_1054);
if (lean_obj_tag(x_1056) == 0)
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
x_1057 = lean_ctor_get(x_1056, 1);
lean_inc(x_1057);
if (lean_is_exclusive(x_1056)) {
 lean_ctor_release(x_1056, 0);
 lean_ctor_release(x_1056, 1);
 x_1058 = x_1056;
} else {
 lean_dec_ref(x_1056);
 x_1058 = lean_box(0);
}
if (lean_is_scalar(x_1058)) {
 x_1059 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1059 = x_1058;
}
lean_ctor_set(x_1059, 0, x_1053);
lean_ctor_set(x_1059, 1, x_1057);
x_1060 = l_Lean_IR_elimDeadBranches(x_1, x_2, x_1059);
x_1061 = lean_ctor_get(x_1060, 0);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_1060, 1);
lean_inc(x_1062);
if (lean_is_exclusive(x_1060)) {
 lean_ctor_release(x_1060, 0);
 lean_ctor_release(x_1060, 1);
 x_1063 = x_1060;
} else {
 lean_dec_ref(x_1060);
 x_1063 = lean_box(0);
}
if (lean_is_scalar(x_1063)) {
 x_1064 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1064 = x_1063;
}
lean_ctor_set(x_1064, 0, x_1053);
lean_ctor_set(x_1064, 1, x_1062);
x_1065 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__4;
x_1066 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__3;
lean_inc(x_1061);
x_1067 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1065, x_1066, x_1061, x_2, x_1064);
x_1068 = lean_ctor_get(x_1067, 1);
lean_inc(x_1068);
if (lean_is_exclusive(x_1067)) {
 lean_ctor_release(x_1067, 0);
 lean_ctor_release(x_1067, 1);
 x_1069 = x_1067;
} else {
 lean_dec_ref(x_1067);
 x_1069 = lean_box(0);
}
if (lean_is_scalar(x_1069)) {
 x_1070 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1070 = x_1069;
}
lean_ctor_set(x_1070, 0, x_1053);
lean_ctor_set(x_1070, 1, x_1068);
x_1071 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_1055, x_1061);
x_1072 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__7;
x_1073 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__6;
lean_inc(x_1071);
x_1074 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1072, x_1073, x_1071, x_2, x_1070);
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
lean_ctor_set(x_1077, 0, x_1053);
lean_ctor_set(x_1077, 1, x_1075);
x_1078 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__2(x_1055, x_1071);
x_1079 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__10;
x_1080 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__9;
lean_inc(x_1078);
x_1081 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1079, x_1080, x_1078, x_2, x_1077);
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
lean_ctor_set(x_1084, 0, x_1053);
lean_ctor_set(x_1084, 1, x_1082);
x_1085 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__3(x_1055, x_1078);
x_1086 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__13;
x_1087 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__12;
lean_inc(x_1085);
x_1088 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1086, x_1087, x_1085, x_2, x_1084);
x_1089 = lean_ctor_get(x_1088, 1);
lean_inc(x_1089);
if (lean_is_exclusive(x_1088)) {
 lean_ctor_release(x_1088, 0);
 lean_ctor_release(x_1088, 1);
 x_1090 = x_1088;
} else {
 lean_dec_ref(x_1088);
 x_1090 = lean_box(0);
}
if (lean_is_scalar(x_1090)) {
 x_1091 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1091 = x_1090;
}
lean_ctor_set(x_1091, 0, x_1053);
lean_ctor_set(x_1091, 1, x_1089);
x_1092 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__4(x_1055, x_1085);
x_1093 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__16;
x_1094 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__15;
lean_inc(x_1092);
x_1095 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1093, x_1094, x_1092, x_2, x_1091);
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
lean_ctor_set(x_1098, 0, x_1053);
lean_ctor_set(x_1098, 1, x_1096);
x_1099 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__5(x_1055, x_1092);
x_1100 = l_Lean_IR_inferBorrow(x_1099, x_2, x_1098);
x_1101 = lean_ctor_get(x_1100, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1100, 1);
lean_inc(x_1102);
if (lean_is_exclusive(x_1100)) {
 lean_ctor_release(x_1100, 0);
 lean_ctor_release(x_1100, 1);
 x_1103 = x_1100;
} else {
 lean_dec_ref(x_1100);
 x_1103 = lean_box(0);
}
if (lean_is_scalar(x_1103)) {
 x_1104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1104 = x_1103;
}
lean_ctor_set(x_1104, 0, x_1053);
lean_ctor_set(x_1104, 1, x_1102);
x_1105 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__19;
x_1106 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__18;
lean_inc(x_1101);
x_1107 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1105, x_1106, x_1101, x_2, x_1104);
x_1108 = lean_ctor_get(x_1107, 1);
lean_inc(x_1108);
if (lean_is_exclusive(x_1107)) {
 lean_ctor_release(x_1107, 0);
 lean_ctor_release(x_1107, 1);
 x_1109 = x_1107;
} else {
 lean_dec_ref(x_1107);
 x_1109 = lean_box(0);
}
if (lean_is_scalar(x_1109)) {
 x_1110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1110 = x_1109;
}
lean_ctor_set(x_1110, 0, x_1053);
lean_ctor_set(x_1110, 1, x_1108);
x_1111 = l_Lean_IR_explicitBoxing(x_1101, x_2, x_1110);
x_1112 = lean_ctor_get(x_1111, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1111, 1);
lean_inc(x_1113);
if (lean_is_exclusive(x_1111)) {
 lean_ctor_release(x_1111, 0);
 lean_ctor_release(x_1111, 1);
 x_1114 = x_1111;
} else {
 lean_dec_ref(x_1111);
 x_1114 = lean_box(0);
}
if (lean_is_scalar(x_1114)) {
 x_1115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1115 = x_1114;
}
lean_ctor_set(x_1115, 0, x_1053);
lean_ctor_set(x_1115, 1, x_1113);
x_1116 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__22;
x_1117 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__21;
lean_inc(x_1112);
x_1118 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1116, x_1117, x_1112, x_2, x_1115);
x_1119 = lean_ctor_get(x_1118, 1);
lean_inc(x_1119);
if (lean_is_exclusive(x_1118)) {
 lean_ctor_release(x_1118, 0);
 lean_ctor_release(x_1118, 1);
 x_1120 = x_1118;
} else {
 lean_dec_ref(x_1118);
 x_1120 = lean_box(0);
}
if (lean_is_scalar(x_1120)) {
 x_1121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1121 = x_1120;
}
lean_ctor_set(x_1121, 0, x_1053);
lean_ctor_set(x_1121, 1, x_1119);
x_1122 = l_Lean_IR_explicitRC(x_1112, x_2, x_1121);
x_1123 = lean_ctor_get(x_1122, 0);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_1122, 1);
lean_inc(x_1124);
if (lean_is_exclusive(x_1122)) {
 lean_ctor_release(x_1122, 0);
 lean_ctor_release(x_1122, 1);
 x_1125 = x_1122;
} else {
 lean_dec_ref(x_1122);
 x_1125 = lean_box(0);
}
if (lean_is_scalar(x_1125)) {
 x_1126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1126 = x_1125;
}
lean_ctor_set(x_1126, 0, x_1053);
lean_ctor_set(x_1126, 1, x_1124);
x_1127 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__25;
x_1128 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__24;
lean_inc(x_1123);
x_1129 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1127, x_1128, x_1123, x_2, x_1126);
x_1130 = lean_ctor_get(x_1129, 1);
lean_inc(x_1130);
if (lean_is_exclusive(x_1129)) {
 lean_ctor_release(x_1129, 0);
 lean_ctor_release(x_1129, 1);
 x_1131 = x_1129;
} else {
 lean_dec_ref(x_1129);
 x_1131 = lean_box(0);
}
if (lean_is_scalar(x_1131)) {
 x_1132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1132 = x_1131;
}
lean_ctor_set(x_1132, 0, x_1053);
lean_ctor_set(x_1132, 1, x_1130);
x_1133 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__6(x_1055, x_1123);
x_1134 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__28;
x_1135 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__27;
lean_inc(x_1133);
x_1136 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1134, x_1135, x_1133, x_2, x_1132);
x_1137 = lean_ctor_get(x_1136, 1);
lean_inc(x_1137);
if (lean_is_exclusive(x_1136)) {
 lean_ctor_release(x_1136, 0);
 lean_ctor_release(x_1136, 1);
 x_1138 = x_1136;
} else {
 lean_dec_ref(x_1136);
 x_1138 = lean_box(0);
}
if (lean_is_scalar(x_1138)) {
 x_1139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1139 = x_1138;
}
lean_ctor_set(x_1139, 0, x_1053);
lean_ctor_set(x_1139, 1, x_1137);
x_1140 = l_Array_ummapAux___main___at___private_Init_Lean_Compiler_IR_Default_1__compileAux___spec__1(x_1055, x_1133);
lean_inc(x_1140);
x_1141 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1072, x_1073, x_1140, x_2, x_1139);
x_1142 = lean_ctor_get(x_1141, 1);
lean_inc(x_1142);
if (lean_is_exclusive(x_1141)) {
 lean_ctor_release(x_1141, 0);
 lean_ctor_release(x_1141, 1);
 x_1143 = x_1141;
} else {
 lean_dec_ref(x_1141);
 x_1143 = lean_box(0);
}
if (lean_is_scalar(x_1143)) {
 x_1144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1144 = x_1143;
}
lean_ctor_set(x_1144, 0, x_1053);
lean_ctor_set(x_1144, 1, x_1142);
x_1145 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31;
x_1146 = l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30;
lean_inc(x_1140);
x_1147 = l___private_Init_Lean_Compiler_IR_CompilerM_2__logDeclsAux(x_1145, x_1146, x_1140, x_2, x_1144);
x_1148 = lean_ctor_get(x_1147, 1);
lean_inc(x_1148);
if (lean_is_exclusive(x_1147)) {
 lean_ctor_release(x_1147, 0);
 lean_ctor_release(x_1147, 1);
 x_1149 = x_1147;
} else {
 lean_dec_ref(x_1147);
 x_1149 = lean_box(0);
}
if (lean_is_scalar(x_1149)) {
 x_1150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1150 = x_1149;
}
lean_ctor_set(x_1150, 0, x_1053);
lean_ctor_set(x_1150, 1, x_1148);
lean_inc(x_1140);
x_1151 = l_Array_mforAux___main___at_Lean_IR_checkDecls___spec__1(x_1140, x_1140, x_1055, x_2, x_1150);
if (lean_obj_tag(x_1151) == 0)
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
x_1152 = lean_ctor_get(x_1151, 1);
lean_inc(x_1152);
if (lean_is_exclusive(x_1151)) {
 lean_ctor_release(x_1151, 0);
 lean_ctor_release(x_1151, 1);
 x_1153 = x_1151;
} else {
 lean_dec_ref(x_1151);
 x_1153 = lean_box(0);
}
if (lean_is_scalar(x_1153)) {
 x_1154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1154 = x_1153;
}
lean_ctor_set(x_1154, 0, x_1053);
lean_ctor_set(x_1154, 1, x_1152);
x_1155 = l_Array_mforAux___main___at_Lean_IR_addDecls___spec__1(x_1140, x_1055, x_2, x_1154);
lean_dec(x_1140);
x_1156 = lean_ctor_get(x_1155, 1);
lean_inc(x_1156);
if (lean_is_exclusive(x_1155)) {
 lean_ctor_release(x_1155, 0);
 lean_ctor_release(x_1155, 1);
 x_1157 = x_1155;
} else {
 lean_dec_ref(x_1155);
 x_1157 = lean_box(0);
}
if (lean_is_scalar(x_1157)) {
 x_1158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1158 = x_1157;
}
lean_ctor_set(x_1158, 0, x_1053);
lean_ctor_set(x_1158, 1, x_1156);
return x_1158;
}
else
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; 
lean_dec(x_1140);
x_1159 = lean_ctor_get(x_1151, 0);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_1151, 1);
lean_inc(x_1160);
if (lean_is_exclusive(x_1151)) {
 lean_ctor_release(x_1151, 0);
 lean_ctor_release(x_1151, 1);
 x_1161 = x_1151;
} else {
 lean_dec_ref(x_1151);
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
else
{
lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; 
lean_dec(x_1);
x_1163 = lean_ctor_get(x_1056, 0);
lean_inc(x_1163);
x_1164 = lean_ctor_get(x_1056, 1);
lean_inc(x_1164);
if (lean_is_exclusive(x_1056)) {
 lean_ctor_release(x_1056, 0);
 lean_ctor_release(x_1056, 1);
 x_1165 = x_1056;
} else {
 lean_dec_ref(x_1056);
 x_1165 = lean_box(0);
}
if (lean_is_scalar(x_1165)) {
 x_1166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1166 = x_1165;
}
lean_ctor_set(x_1166, 0, x_1163);
lean_ctor_set(x_1166, 1, x_1164);
return x_1166;
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
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_getEnv___rarg(x_3);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_7);
x_11 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
x_12 = l_Lean_mkOptionalNode___rarg___closed__1;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_Lean_IR_explicitRC(x_13, x_2, x_4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_14, 0, x_8);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(x_16, x_17, x_2, x_14);
lean_dec(x_16);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(x_23, x_26, x_2, x_25);
lean_dec(x_23);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_4, 0);
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_4);
x_33 = lean_box(0);
lean_inc(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_31, x_1);
lean_dec(x_31);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_32);
x_37 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
x_38 = l_Lean_mkOptionalNode___rarg___closed__1;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_Lean_IR_explicitRC(x_39, x_2, x_34);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Array_mforAux___main___at_Lean_IR_addBoxedVersionAux___spec__1(x_41, x_45, x_2, x_44);
lean_dec(x_41);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_33);
lean_ctor_set(x_49, 1, x_47);
return x_49;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
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
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__29 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__29();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__29);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__30);
l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31 = _init_l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_Default_1__compileAux___closed__31);
return w;
}
#ifdef __cplusplus
}
#endif
