// Lean compiler output
// Module: Lean.Compiler.IR.Format
// Imports: Init Lean.Data.Format Lean.Compiler.IR.Basic
#include <lean/lean.h>
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
lean_object* l_Lean_IR_litValHasFormat___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__18;
lean_object* l___private_Lean_Compiler_IR_Format_1__formatArg___closed__1;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__15;
lean_object* l_Lean_IR_typeHasToString;
lean_object* l_Lean_IR_formatFnBodyHead___closed__15;
lean_object* l_Lean_IR_formatFnBodyHead___closed__3;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__5;
lean_object* l_Lean_IR_fnBodyHasFormat;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__30;
lean_object* l_Lean_IR_formatFnBodyHead___closed__29;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__6;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__6;
lean_object* l_Lean_IR_formatFnBodyHead___closed__33;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__24;
lean_object* l_Lean_IR_formatFnBodyHead___closed__22;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__16;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__7;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__29;
lean_object* l_Lean_IR_formatAlt___closed__1;
lean_object* l___private_Lean_Compiler_IR_Format_3__formatCtorInfo(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__24;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__16;
lean_object* l_Lean_Format_joinSep___main___at___private_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBody___main___closed__3;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr(lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__14;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__28;
lean_object* l_Lean_IR_formatFnBody___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__22;
lean_object* l_Lean_IR_formatAlt___closed__4;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_formatKVMap___closed__1;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__10;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__32;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__15;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__18;
lean_object* l___private_Lean_Compiler_IR_Format_1__formatArg___closed__2;
lean_object* l_Lean_IR_formatArray___at_Lean_IR_formatParams___spec__1(lean_object*);
lean_object* l_Lean_IR_formatAlt___closed__2;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__19;
lean_object* l_Lean_IR_formatFnBodyHead___closed__11;
lean_object* l_Lean_IR_formatFnBodyHead___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___boxed(lean_object*);
lean_object* l_Lean_IR_argHasFormat___closed__1;
lean_object* l_Lean_IR_formatArray___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* l_Lean_IR_declHasFormat___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__23;
lean_object* l_Lean_IR_formatFnBody___main___closed__4;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__10;
lean_object* l_Lean_IR_formatFnBodyHead___closed__1;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__7;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__24;
lean_object* l_Lean_IR_formatFnBodyHead___closed__17;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__7;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__11;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__12;
lean_object* l_Lean_IR_formatArray___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__1___boxed(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__6;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19;
lean_object* l_Lean_IR_litValHasFormat;
lean_object* l_Lean_IR_formatArray___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__1(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_formatParams___boxed(lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType(lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_6__formatParam___closed__2;
lean_object* l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3;
lean_object* l_Lean_IR_formatFnBodyHead___closed__16;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__12;
lean_object* l___private_Lean_Compiler_IR_Format_6__formatParam___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__2;
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__8;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__20;
extern lean_object* l_Lean_Format_join___closed__1;
lean_object* l_Lean_IR_formatDecl___closed__3;
extern lean_object* l_Std_PersistentArray_Stats_toString___closed__4;
lean_object* l_Lean_IR_formatArray(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_IR_formatFnBody___main___closed__2;
lean_object* l_Lean_IR_formatFnBody___main___closed__1;
lean_object* l_Lean_IR_formatDecl___closed__1;
lean_object* l_Lean_IR_formatDecl___closed__2;
lean_object* l_Lean_formatKVMap(lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__23;
lean_object* l_Lean_IR_declHasFormat;
lean_object* l_Lean_IR_formatFnBodyHead___closed__20;
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
lean_object* l_Lean_IR_exprHasFormat___closed__1;
lean_object* l_Lean_IR_ctorInfoHasFormat___closed__1;
lean_object* l___private_Lean_Compiler_IR_Format_2__formatLitVal(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__26;
lean_object* l_Lean_IR_typeHasFormat___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__31;
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__4;
lean_object* lean_ir_decl_to_string(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__27;
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__13;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__23;
lean_object* l_Lean_Format_joinSep___main___at___private_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__26;
extern lean_object* l_Lean_HasRepr___closed__1;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__8;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main(lean_object*);
lean_object* l_Lean_IR_fnBodyHasToString(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__25;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
lean_object* lean_ir_format_fn_body_head(lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__9;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__27;
lean_object* l_Lean_IR_formatAlt___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__34;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__2;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__11;
lean_object* l_Lean_IR_ctorInfoHasFormat;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__31;
lean_object* l_Lean_IR_formatDecl(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__13;
lean_object* l_Lean_IR_argHasFormat;
extern lean_object* l_Lean_Format_sbracket___closed__4;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__9;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__18;
lean_object* l_Lean_IR_formatFnBodyHead___closed__5;
lean_object* l_Lean_IR_formatFnBodyHead___closed__30;
extern lean_object* l_Lean_IR_JoinPointId_HasToString___closed__1;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__17;
lean_object* l_Lean_IR_paramHasFormat;
lean_object* l_Lean_IR_formatFnBodyHead___closed__28;
extern lean_object* l_Lean_Format_paren___closed__4;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__3;
lean_object* l_Lean_IR_formatFnBodyHead___closed__14;
lean_object* l_Lean_IR_paramHasFormat___closed__1;
lean_object* l_Lean_IR_declHasToString;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__8;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__21;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__1;
lean_object* l_Lean_IR_formatDecl___closed__4;
lean_object* l_Lean_IR_typeHasToString___closed__1;
lean_object* l_Lean_IR_formatArray___at_Lean_IR_formatParams___spec__1___boxed(lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___boxed(lean_object*);
extern lean_object* l_Lean_IR_VarId_HasToString___closed__1;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__2;
lean_object* l_Lean_IR_formatParams(lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__5;
lean_object* l_Lean_IR_formatFnBodyHead___closed__10;
lean_object* l_Lean_IR_formatFnBodyHead___closed__32;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__14;
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_IR_typeHasFormat;
lean_object* l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__2;
lean_object* l_Lean_IR_formatFnBodyHead___closed__12;
extern lean_object* l_Lean_Format_paren___closed__3;
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__3;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__17;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__13;
lean_object* l_Lean_IR_formatFnBodyHead___closed__4;
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__25;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_exprHasFormat;
lean_object* l_Lean_IR_fnBodyHasFormat___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__9;
lean_object* l_Lean_IR_declHasToString___closed__1;
lean_object* l___private_Lean_Compiler_IR_Format_1__formatArg(lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__22;
lean_object* l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__1;
lean_object* l_Lean_IR_formatFnBodyHead___closed__19;
extern lean_object* l_Lean_ppGoal___closed__8;
lean_object* l_Lean_IR_formatFnBodyHead___closed__36;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_IR_exprHasToString(lean_object*);
lean_object* l_Lean_IR_formatFnBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__35;
extern lean_object* l_addParenHeuristic___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1(lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__21;
lean_object* l_Lean_IR_formatArray___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21;
lean_object* l_Lean_IR_formatAlt(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_IR_formatFnBodyHead___closed__2;
lean_object* l___private_Lean_Compiler_IR_Format_6__formatParam(lean_object*);
lean_object* _init_l___private_Lean_Compiler_IR_Format_1__formatArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("◾");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_1__formatArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_1__formatArg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Compiler_IR_Format_1__formatArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = l_Lean_IR_VarId_HasToString___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_IR_Format_1__formatArg___closed__2;
return x_7;
}
}
}
lean_object* _init_l_Lean_IR_argHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_1__formatArg), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_argHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_argHasFormat___closed__1;
return x_1;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_8);
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_4 = x_14;
x_5 = x_12;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_IR_formatArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_box(0);
x_5 = l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg(x_1, x_2, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_formatArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_formatArray___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_IR_formatArray___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_IR_formatArray___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_formatArray___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Compiler_IR_Format_2__formatLitVal(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Nat_repr(x_2);
x_4 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_String_quote(x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
lean_object* _init_l_Lean_IR_litValHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_2__formatLitVal), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_litValHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_litValHasFormat___closed__1;
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ctor_");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_System_FilePath_dirName___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Compiler_IR_Format_3__formatCtorInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Nat_repr(x_3);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__2;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_4);
x_12 = lean_box(0);
x_13 = lean_name_eq(x_2, x_12);
if (x_11 == 0)
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_10, x_5);
if (x_14 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
if (x_13 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = l_Lean_Format_sbracket___closed__3;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_System_FilePath_dirName___closed__1;
x_18 = l_Lean_Name_toStringWithSep___main(x_17, x_2);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Format_sbracket___closed__4;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
else
{
lean_dec(x_2);
return x_9;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Nat_repr(x_4);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_29 = l_Nat_repr(x_5);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
if (x_13 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = l_Lean_Format_sbracket___closed__3;
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_System_FilePath_dirName___closed__1;
x_35 = l_Lean_Name_toStringWithSep___main(x_34, x_2);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Format_sbracket___closed__4;
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_dec(x_2);
return x_31;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3;
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_9);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Nat_repr(x_4);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
x_46 = l_Nat_repr(x_5);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
if (x_13 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = l_Lean_Format_sbracket___closed__3;
x_50 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_System_FilePath_dirName___closed__1;
x_52 = l_Lean_Name_toStringWithSep___main(x_51, x_2);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Format_sbracket___closed__4;
x_56 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
else
{
lean_dec(x_2);
return x_48;
}
}
}
}
lean_object* _init_l_Lean_IR_ctorInfoHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_3__formatCtorInfo), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_ctorInfoHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_ctorInfoHasFormat___closed__1;
return x_1;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = l___private_Lean_Compiler_IR_Format_1__formatArg(x_7);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_11;
goto _start;
}
}
}
lean_object* l_Lean_IR_formatArray___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Array_iterateMAux___main___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_1, x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reset[");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reuse");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" in ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__6;
x_2 = l_Lean_Format_join___closed__1;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__9;
x_2 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("!");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__6;
x_2 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__12;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__13;
x_2 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("proj[");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("uproj[");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sproj[");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pap ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__21;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__23;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("box ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__25;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unbox ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__27;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isShared ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__29;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isTaggedPtr ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__31;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Compiler_IR_Format_4__formatExpr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Lean_Compiler_IR_Format_3__formatCtorInfo(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = l_Array_iterateMAux___main___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_3, x_3, x_5, x_6);
lean_dec(x_3);
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Nat_repr(x_9);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__2;
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Nat_repr(x_10);
x_18 = l_Lean_IR_VarId_HasToString___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
case 2:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Nat_repr(x_22);
x_27 = l_Lean_IR_VarId_HasToString___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l___private_Lean_Compiler_IR_Format_3__formatCtorInfo(x_23);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_box(0);
x_33 = l_Array_iterateMAux___main___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_25, x_25, x_31, x_32);
lean_dec(x_25);
if (x_24 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__10;
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
x_36 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__8;
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__14;
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_29);
x_42 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__8;
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_30);
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_33);
return x_45;
}
}
case 3:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
lean_dec(x_1);
x_48 = l_Nat_repr(x_46);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__16;
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
x_53 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Nat_repr(x_47);
x_55 = l_Lean_IR_VarId_HasToString___closed__1;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
case 4:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_dec(x_1);
x_61 = l_Nat_repr(x_59);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__18;
x_64 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
x_66 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Nat_repr(x_60);
x_68 = l_Lean_IR_VarId_HasToString___closed__1;
x_69 = lean_string_append(x_68, x_67);
lean_dec(x_67);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
case 5:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_72 = lean_ctor_get(x_1, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 2);
lean_inc(x_74);
lean_dec(x_1);
x_75 = l_Nat_repr(x_72);
x_76 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__20;
x_78 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Lean_formatKVMap___closed__1;
x_80 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Nat_repr(x_73);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__4;
x_85 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Nat_repr(x_74);
x_87 = l_Lean_IR_VarId_HasToString___closed__1;
x_88 = lean_string_append(x_87, x_86);
lean_dec(x_86);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
case 6:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_1, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_1, 1);
lean_inc(x_92);
lean_dec(x_1);
x_93 = l_System_FilePath_dirName___closed__1;
x_94 = l_Lean_Name_toStringWithSep___main(x_93, x_91);
x_95 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_box(0);
x_98 = l_Array_iterateMAux___main___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_92, x_92, x_96, x_97);
lean_dec(x_92);
x_99 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
case 7:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_1, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_1, 1);
lean_inc(x_101);
lean_dec(x_1);
x_102 = l_System_FilePath_dirName___closed__1;
x_103 = l_Lean_Name_toStringWithSep___main(x_102, x_100);
x_104 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__22;
x_106 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_box(0);
x_109 = l_Array_iterateMAux___main___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_101, x_101, x_107, x_108);
lean_dec(x_101);
x_110 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
case 8:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
lean_dec(x_1);
x_113 = l_Nat_repr(x_111);
x_114 = l_Lean_IR_VarId_HasToString___closed__1;
x_115 = lean_string_append(x_114, x_113);
lean_dec(x_113);
x_116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__24;
x_118 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_box(0);
x_121 = l_Array_iterateMAux___main___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_112, x_112, x_119, x_120);
lean_dec(x_112);
x_122 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
case 9:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_123 = lean_ctor_get(x_1, 1);
lean_inc(x_123);
lean_dec(x_1);
x_124 = l_Nat_repr(x_123);
x_125 = l_Lean_IR_VarId_HasToString___closed__1;
x_126 = lean_string_append(x_125, x_124);
lean_dec(x_124);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__26;
x_129 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
case 10:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_130 = lean_ctor_get(x_1, 0);
lean_inc(x_130);
lean_dec(x_1);
x_131 = l_Nat_repr(x_130);
x_132 = l_Lean_IR_VarId_HasToString___closed__1;
x_133 = lean_string_append(x_132, x_131);
lean_dec(x_131);
x_134 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_134, 0, x_133);
x_135 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__28;
x_136 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
case 11:
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_1, 0);
lean_inc(x_137);
lean_dec(x_1);
x_138 = l___private_Lean_Compiler_IR_Format_2__formatLitVal(x_137);
return x_138;
}
case 12:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_1, 0);
lean_inc(x_139);
lean_dec(x_1);
x_140 = l_Nat_repr(x_139);
x_141 = l_Lean_IR_VarId_HasToString___closed__1;
x_142 = lean_string_append(x_141, x_140);
lean_dec(x_140);
x_143 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__30;
x_145 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
default: 
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_146 = lean_ctor_get(x_1, 0);
lean_inc(x_146);
lean_dec(x_1);
x_147 = l_Nat_repr(x_146);
x_148 = l_Lean_IR_VarId_HasToString___closed__1;
x_149 = lean_string_append(x_148, x_147);
lean_dec(x_147);
x_150 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__32;
x_152 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_formatArray___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_formatArray___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_exprHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_4__formatExpr), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_exprHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_exprHasFormat___closed__1;
return x_1;
}
}
lean_object* l_Lean_IR_exprHasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Compiler_IR_Format_4__formatExpr(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Format_pretty(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Format_joinSep___main___at___private_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main(x_7);
lean_inc(x_2);
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Lean_Format_joinSep___main___at___private_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(x_4, x_2);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("float");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("u8");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("u16");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("u32");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("u64");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("usize");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("obj");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tobj");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("struct ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_addParenHeuristic___closed__1;
x_2 = lean_string_length(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_addParenHeuristic___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PersistentArray_Stats_toString___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("union ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__23;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__4;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__6;
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__8;
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__10;
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__12;
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_IR_Format_1__formatArg___closed__2;
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__14;
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__16;
return x_10;
}
case 9:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Array_toList___rarg(x_11);
x_13 = l_Lean_formatKVMap___closed__1;
x_14 = l_Lean_Format_joinSep___main___at___private_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(x_12, x_13);
lean_dec(x_12);
x_15 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__22;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20;
x_20 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = 0;
x_22 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__18;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
default: 
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = lean_ctor_get(x_1, 1);
x_26 = l_Array_toList___rarg(x_25);
x_27 = l_Lean_formatKVMap___closed__1;
x_28 = l_Lean_Format_joinSep___main___at___private_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(x_26, x_27);
lean_dec(x_26);
x_29 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21;
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__22;
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20;
x_34 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = 0;
x_36 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__24;
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
lean_object* l_Lean_Format_joinSep___main___at___private_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Format_joinSep___main___at___private_Lean_Compiler_IR_Format_5__formatIRType___main___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Compiler_IR_Format_5__formatIRType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_Format_5__formatIRType(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_typeHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_5__formatIRType___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_typeHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_typeHasFormat___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_IR_typeHasToString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_IR_typeHasFormat___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_typeHasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_typeHasToString___closed__1;
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_6__formatParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("@& ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Compiler_IR_Format_6__formatParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Format_6__formatParam___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Compiler_IR_Format_6__formatParam(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Nat_repr(x_2);
x_6 = l_Lean_IR_VarId_HasToString___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Format_paren___closed__3;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main(x_4);
lean_dec(x_4);
if (x_3 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Format_join___closed__1;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = l_Lean_Format_paren___closed__4;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = l___private_Lean_Compiler_IR_Format_6__formatParam___closed__2;
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
x_22 = l_Lean_Format_paren___closed__4;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
lean_object* _init_l_Lean_IR_paramHasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Format_6__formatParam), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_paramHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_paramHasFormat___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatAlt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" →");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatAlt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatAlt___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatAlt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("default →");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatAlt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatAlt___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_formatAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_System_FilePath_dirName___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_6);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_IR_formatAlt___closed__2;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_nat_to_int(x_2);
x_13 = lean_apply_1(x_1, x_5);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_nat_to_int(x_2);
x_20 = lean_apply_1(x_1, x_18);
x_21 = lean_box(1);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_IR_formatAlt___closed__4;
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = l___private_Lean_Compiler_IR_Format_6__formatParam(x_7);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_11;
goto _start;
}
}
}
lean_object* l_Lean_IR_formatArray___at_Lean_IR_formatParams___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_1, x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_formatParams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_1, x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_formatArray___at_Lean_IR_formatParams___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_formatArray___at_Lean_IR_formatParams___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_formatParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_formatParams(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("let ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" := ...");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("set ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] := ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("setTag ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("uset ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sset ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] : ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inc");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__18;
x_2 = l_Lean_Format_join___closed__1;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__19;
x_2 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dec");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__21;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__22;
x_2 = l_Lean_Format_join___closed__1;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__23;
x_2 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("del ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__25;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mdata ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__27;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" of ...");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__29;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ret ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__31;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("jmp ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__33;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("⊥");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBodyHead___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBodyHead___closed__35;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* lean_ir_format_fn_body_head(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Nat_repr(x_2);
x_6 = l_Lean_IR_VarId_HasToString___closed__1;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_IR_formatFnBodyHead___closed__2;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main(x_3);
lean_dec(x_3);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_formatEntry___closed__2;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Lean_Compiler_IR_Format_4__formatExpr(x_4);
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Nat_repr(x_19);
x_22 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_box(0);
x_27 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_20, x_20, x_25, x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_IR_formatFnBodyHead___closed__4;
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
case 2:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
lean_dec(x_1);
x_34 = l_Nat_repr(x_31);
x_35 = l_Lean_IR_VarId_HasToString___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_IR_formatFnBodyHead___closed__6;
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Format_sbracket___closed__3;
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Nat_repr(x_32);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_IR_formatFnBodyHead___closed__8;
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l___private_Lean_Compiler_IR_Format_1__formatArg(x_33);
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
case 3:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
lean_dec(x_1);
x_51 = l_Nat_repr(x_49);
x_52 = l_Lean_IR_VarId_HasToString___closed__1;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_IR_formatFnBodyHead___closed__10;
x_56 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_formatEntry___closed__2;
x_58 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Nat_repr(x_50);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
case 4:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 2);
lean_inc(x_64);
lean_dec(x_1);
x_65 = l_Nat_repr(x_62);
x_66 = l_Lean_IR_VarId_HasToString___closed__1;
x_67 = lean_string_append(x_66, x_65);
lean_dec(x_65);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = l_Lean_IR_formatFnBodyHead___closed__12;
x_70 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_Format_sbracket___closed__3;
x_72 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Nat_repr(x_63);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_IR_formatFnBodyHead___closed__8;
x_77 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Nat_repr(x_64);
x_79 = lean_string_append(x_66, x_78);
lean_dec(x_78);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
case 5:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_1, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_1, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_1, 4);
lean_inc(x_86);
lean_dec(x_1);
x_87 = l_Nat_repr(x_82);
x_88 = l_Lean_IR_VarId_HasToString___closed__1;
x_89 = lean_string_append(x_88, x_87);
lean_dec(x_87);
x_90 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Lean_IR_formatFnBodyHead___closed__14;
x_92 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Lean_Format_sbracket___closed__3;
x_94 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Nat_repr(x_83);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_formatKVMap___closed__1;
x_99 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Nat_repr(x_84);
x_101 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_IR_formatFnBodyHead___closed__16;
x_104 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main(x_86);
lean_dec(x_86);
x_106 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_formatEntry___closed__2;
x_108 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Nat_repr(x_85);
x_110 = lean_string_append(x_88, x_109);
lean_dec(x_109);
x_111 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
case 6:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_113 = lean_ctor_get(x_1, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_1, 1);
lean_inc(x_114);
lean_dec(x_1);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_dec_eq(x_114, x_115);
x_117 = l_Nat_repr(x_113);
x_118 = l_Lean_IR_VarId_HasToString___closed__1;
x_119 = lean_string_append(x_118, x_117);
lean_dec(x_117);
x_120 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_120, 0, x_119);
if (x_116 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_121 = l_Nat_repr(x_114);
x_122 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = l_Lean_Format_sbracket___closed__3;
x_124 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = l_Lean_Format_sbracket___closed__4;
x_126 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_Format_sbracket___closed__2;
x_128 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = 0;
x_130 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_129);
x_131 = l_Lean_IR_formatFnBodyHead___closed__18;
x_132 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_134 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_120);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_114);
x_136 = l_Lean_IR_formatFnBodyHead___closed__20;
x_137 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_120);
return x_137;
}
}
case 7:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_138 = lean_ctor_get(x_1, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_1, 1);
lean_inc(x_139);
lean_dec(x_1);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_dec_eq(x_139, x_140);
x_142 = l_Nat_repr(x_138);
x_143 = l_Lean_IR_VarId_HasToString___closed__1;
x_144 = lean_string_append(x_143, x_142);
lean_dec(x_142);
x_145 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_145, 0, x_144);
if (x_141 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_146 = l_Nat_repr(x_139);
x_147 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_147, 0, x_146);
x_148 = l_Lean_Format_sbracket___closed__3;
x_149 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_150 = l_Lean_Format_sbracket___closed__4;
x_151 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_Format_sbracket___closed__2;
x_153 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = 0;
x_155 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set_uint8(x_155, sizeof(void*)*1, x_154);
x_156 = l_Lean_IR_formatFnBodyHead___closed__22;
x_157 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_159 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_145);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_139);
x_161 = l_Lean_IR_formatFnBodyHead___closed__24;
x_162 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_145);
return x_162;
}
}
case 8:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_163 = lean_ctor_get(x_1, 0);
lean_inc(x_163);
lean_dec(x_1);
x_164 = l_Nat_repr(x_163);
x_165 = l_Lean_IR_VarId_HasToString___closed__1;
x_166 = lean_string_append(x_165, x_164);
lean_dec(x_164);
x_167 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_168 = l_Lean_IR_formatFnBodyHead___closed__26;
x_169 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
case 9:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_1, 0);
lean_inc(x_170);
lean_dec(x_1);
x_171 = l_Lean_formatKVMap(x_170);
x_172 = l_Lean_IR_formatFnBodyHead___closed__28;
x_173 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
case 10:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_174 = lean_ctor_get(x_1, 1);
lean_inc(x_174);
lean_dec(x_1);
x_175 = l_Nat_repr(x_174);
x_176 = l_Lean_IR_VarId_HasToString___closed__1;
x_177 = lean_string_append(x_176, x_175);
lean_dec(x_175);
x_178 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = l_Lean_ppGoal___closed__8;
x_180 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
x_181 = l_Lean_IR_formatFnBodyHead___closed__30;
x_182 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
case 11:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_1, 0);
lean_inc(x_183);
lean_dec(x_1);
x_184 = l___private_Lean_Compiler_IR_Format_1__formatArg(x_183);
x_185 = l_Lean_IR_formatFnBodyHead___closed__32;
x_186 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
case 12:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_187 = lean_ctor_get(x_1, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_1, 1);
lean_inc(x_188);
lean_dec(x_1);
x_189 = l_Nat_repr(x_187);
x_190 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_191 = lean_string_append(x_190, x_189);
lean_dec(x_189);
x_192 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = l_Lean_IR_formatFnBodyHead___closed__34;
x_194 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = lean_unsigned_to_nat(0u);
x_196 = lean_box(0);
x_197 = l_Array_iterateMAux___main___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_188, x_188, x_195, x_196);
lean_dec(x_188);
x_198 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_198, 0, x_194);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
default: 
{
lean_object* x_199; 
x_199 = l_Lean_IR_formatFnBodyHead___closed__36;
return x_199;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_IR_formatFnBody___main), 2, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_1);
x_12 = l_Lean_IR_formatAlt(x_11, x_1, x_8);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_13;
goto _start;
}
}
}
lean_object* _init_l_Lean_IR_formatFnBody___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(";");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBody___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBody___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatFnBody___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" of");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatFnBody___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatFnBody___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_formatFnBody___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Nat_repr(x_3);
x_8 = l_Lean_IR_VarId_HasToString___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_IR_formatFnBodyHead___closed__2;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main(x_4);
lean_dec(x_4);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_formatEntry___closed__2;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Lean_Compiler_IR_Format_4__formatExpr(x_5);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_IR_formatFnBody___main___closed__2;
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_IR_formatFnBody___main(x_1, x_6);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 3);
lean_inc(x_30);
lean_dec(x_2);
x_31 = l_Nat_repr(x_27);
x_32 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_box(0);
x_37 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_28, x_28, x_35, x_36);
lean_dec(x_28);
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__8;
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_1);
x_41 = lean_nat_to_int(x_1);
lean_inc(x_1);
x_42 = l_Lean_IR_formatFnBody___main(x_1, x_29);
x_43 = lean_box(1);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_IR_formatFnBody___main___closed__2;
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_43);
x_50 = l_Lean_IR_formatFnBody___main(x_1, x_30);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
case 2:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 3);
lean_inc(x_55);
lean_dec(x_2);
x_56 = l_Nat_repr(x_52);
x_57 = l_Lean_IR_VarId_HasToString___closed__1;
x_58 = lean_string_append(x_57, x_56);
lean_dec(x_56);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lean_IR_formatFnBodyHead___closed__6;
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_Format_sbracket___closed__3;
x_63 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Nat_repr(x_53);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_IR_formatFnBodyHead___closed__8;
x_68 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l___private_Lean_Compiler_IR_Format_1__formatArg(x_54);
x_70 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_IR_formatFnBody___main___closed__2;
x_72 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_box(1);
x_74 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_IR_formatFnBody___main(x_1, x_55);
x_76 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
case 3:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_77 = lean_ctor_get(x_2, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_2, 2);
lean_inc(x_79);
lean_dec(x_2);
x_80 = l_Nat_repr(x_77);
x_81 = l_Lean_IR_VarId_HasToString___closed__1;
x_82 = lean_string_append(x_81, x_80);
lean_dec(x_80);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_Lean_IR_formatFnBodyHead___closed__10;
x_85 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_Lean_formatEntry___closed__2;
x_87 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Nat_repr(x_78);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_IR_formatFnBody___main___closed__2;
x_92 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_box(1);
x_94 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_IR_formatFnBody___main(x_1, x_79);
x_96 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
case 4:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_97 = lean_ctor_get(x_2, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_2, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 3);
lean_inc(x_100);
lean_dec(x_2);
x_101 = l_Nat_repr(x_97);
x_102 = l_Lean_IR_VarId_HasToString___closed__1;
x_103 = lean_string_append(x_102, x_101);
lean_dec(x_101);
x_104 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = l_Lean_IR_formatFnBodyHead___closed__12;
x_106 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_Lean_Format_sbracket___closed__3;
x_108 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Nat_repr(x_98);
x_110 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_IR_formatFnBodyHead___closed__8;
x_113 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Nat_repr(x_99);
x_115 = lean_string_append(x_102, x_114);
lean_dec(x_114);
x_116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_IR_formatFnBody___main___closed__2;
x_119 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_box(1);
x_121 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_IR_formatFnBody___main(x_1, x_100);
x_123 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
case 5:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_124 = lean_ctor_get(x_2, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_2, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_2, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_2, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_2, 4);
lean_inc(x_128);
x_129 = lean_ctor_get(x_2, 5);
lean_inc(x_129);
lean_dec(x_2);
x_130 = l_Nat_repr(x_124);
x_131 = l_Lean_IR_VarId_HasToString___closed__1;
x_132 = lean_string_append(x_131, x_130);
lean_dec(x_130);
x_133 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Lean_IR_formatFnBodyHead___closed__14;
x_135 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l_Lean_Format_sbracket___closed__3;
x_137 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Nat_repr(x_125);
x_139 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Lean_formatKVMap___closed__1;
x_142 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Nat_repr(x_126);
x_144 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_IR_formatFnBodyHead___closed__16;
x_147 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main(x_128);
lean_dec(x_128);
x_149 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = l_Lean_formatEntry___closed__2;
x_151 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Nat_repr(x_127);
x_153 = lean_string_append(x_131, x_152);
lean_dec(x_152);
x_154 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_155, 0, x_151);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_IR_formatFnBody___main___closed__2;
x_157 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_box(1);
x_159 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_IR_formatFnBody___main(x_1, x_129);
x_161 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
case 6:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_162 = lean_ctor_get(x_2, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_2, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_2, 2);
lean_inc(x_164);
lean_dec(x_2);
x_165 = lean_unsigned_to_nat(1u);
x_166 = lean_nat_dec_eq(x_163, x_165);
x_167 = l_Nat_repr(x_162);
x_168 = l_Lean_IR_VarId_HasToString___closed__1;
x_169 = lean_string_append(x_168, x_167);
lean_dec(x_167);
x_170 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_170, 0, x_169);
x_171 = l_Lean_IR_formatFnBody___main(x_1, x_164);
if (x_166 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_172 = l_Nat_repr(x_163);
x_173 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = l_Lean_Format_sbracket___closed__3;
x_175 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
x_176 = l_Lean_Format_sbracket___closed__4;
x_177 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Lean_Format_sbracket___closed__2;
x_179 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
x_180 = 0;
x_181 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*1, x_180);
x_182 = l_Lean_IR_formatFnBodyHead___closed__18;
x_183 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
x_184 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_185 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_170);
x_187 = l_Lean_IR_formatFnBody___main___closed__2;
x_188 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_box(1);
x_190 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_171);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_163);
x_192 = l_Lean_IR_formatFnBodyHead___closed__20;
x_193 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_170);
x_194 = l_Lean_IR_formatFnBody___main___closed__2;
x_195 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_box(1);
x_197 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_171);
return x_198;
}
}
case 7:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_199 = lean_ctor_get(x_2, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_2, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_2, 2);
lean_inc(x_201);
lean_dec(x_2);
x_202 = lean_unsigned_to_nat(1u);
x_203 = lean_nat_dec_eq(x_200, x_202);
x_204 = l_Nat_repr(x_199);
x_205 = l_Lean_IR_VarId_HasToString___closed__1;
x_206 = lean_string_append(x_205, x_204);
lean_dec(x_204);
x_207 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = l_Lean_IR_formatFnBody___main(x_1, x_201);
if (x_203 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_209 = l_Nat_repr(x_200);
x_210 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_210, 0, x_209);
x_211 = l_Lean_Format_sbracket___closed__3;
x_212 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_210);
x_213 = l_Lean_Format_sbracket___closed__4;
x_214 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = l_Lean_Format_sbracket___closed__2;
x_216 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
x_217 = 0;
x_218 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set_uint8(x_218, sizeof(void*)*1, x_217);
x_219 = l_Lean_IR_formatFnBodyHead___closed__22;
x_220 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_218);
x_221 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_222 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_207);
x_224 = l_Lean_IR_formatFnBody___main___closed__2;
x_225 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_box(1);
x_227 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_208);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_200);
x_229 = l_Lean_IR_formatFnBodyHead___closed__24;
x_230 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_207);
x_231 = l_Lean_IR_formatFnBody___main___closed__2;
x_232 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_box(1);
x_234 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_208);
return x_235;
}
}
case 8:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_236 = lean_ctor_get(x_2, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_2, 1);
lean_inc(x_237);
lean_dec(x_2);
x_238 = l_Nat_repr(x_236);
x_239 = l_Lean_IR_VarId_HasToString___closed__1;
x_240 = lean_string_append(x_239, x_238);
lean_dec(x_238);
x_241 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_241, 0, x_240);
x_242 = l_Lean_IR_formatFnBodyHead___closed__26;
x_243 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_241);
x_244 = l_Lean_IR_formatFnBody___main___closed__2;
x_245 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_box(1);
x_247 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = l_Lean_IR_formatFnBody___main(x_1, x_237);
x_249 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
case 9:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_250 = lean_ctor_get(x_2, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_2, 1);
lean_inc(x_251);
lean_dec(x_2);
x_252 = l_Lean_formatKVMap(x_250);
x_253 = l_Lean_IR_formatFnBodyHead___closed__28;
x_254 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_252);
x_255 = l_Lean_IR_formatFnBody___main___closed__2;
x_256 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_box(1);
x_258 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
x_259 = l_Lean_IR_formatFnBody___main(x_1, x_251);
x_260 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
case 10:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_261 = lean_ctor_get(x_2, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_2, 2);
lean_inc(x_262);
x_263 = lean_ctor_get(x_2, 3);
lean_inc(x_263);
lean_dec(x_2);
x_264 = l_Nat_repr(x_261);
x_265 = l_Lean_IR_VarId_HasToString___closed__1;
x_266 = lean_string_append(x_265, x_264);
lean_dec(x_264);
x_267 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_267, 0, x_266);
x_268 = l_Lean_ppGoal___closed__8;
x_269 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_271 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
x_272 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main(x_262);
lean_dec(x_262);
x_273 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_274 = l_Lean_IR_formatFnBody___main___closed__4;
x_275 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
x_276 = lean_unsigned_to_nat(0u);
x_277 = lean_box(0);
x_278 = l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1(x_1, x_263, x_263, x_276, x_277);
lean_dec(x_263);
x_279 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_279, 0, x_275);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
case 11:
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_1);
x_280 = lean_ctor_get(x_2, 0);
lean_inc(x_280);
lean_dec(x_2);
x_281 = l___private_Lean_Compiler_IR_Format_1__formatArg(x_280);
x_282 = l_Lean_IR_formatFnBodyHead___closed__32;
x_283 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
case 12:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_1);
x_284 = lean_ctor_get(x_2, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_2, 1);
lean_inc(x_285);
lean_dec(x_2);
x_286 = l_Nat_repr(x_284);
x_287 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_288 = lean_string_append(x_287, x_286);
lean_dec(x_286);
x_289 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_289, 0, x_288);
x_290 = l_Lean_IR_formatFnBodyHead___closed__34;
x_291 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_289);
x_292 = lean_unsigned_to_nat(0u);
x_293 = lean_box(0);
x_294 = l_Array_iterateMAux___main___at___private_Lean_Compiler_IR_Format_4__formatExpr___spec__2(x_285, x_285, x_292, x_293);
lean_dec(x_285);
x_295 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_295, 0, x_291);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
default: 
{
lean_object* x_296; 
lean_dec(x_1);
x_296 = l_Lean_IR_formatFnBodyHead___closed__36;
return x_296;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_IR_formatFnBody___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_IR_formatFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_formatFnBody___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_fnBodyHasFormat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_alloc_closure((void*)(l_Lean_IR_formatFnBody), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_fnBodyHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_fnBodyHasFormat___closed__1;
return x_1;
}
}
lean_object* l_Lean_IR_fnBodyHasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_IR_formatFnBody___main(x_2, x_1);
x_4 = lean_box(0);
x_5 = l_Lean_Format_pretty(x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_IR_formatDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("def ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatDecl___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_formatDecl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("extern ");
return x_1;
}
}
lean_object* _init_l_Lean_IR_formatDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_formatDecl___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_formatDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_System_FilePath_dirName___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_3);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_IR_formatDecl___closed__2;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_box(0);
x_14 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_4, x_4, x_12, x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main(x_5);
lean_dec(x_5);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__8;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_1);
x_22 = lean_nat_to_int(x_1);
x_23 = l_Lean_IR_formatFnBody___main(x_1, x_6);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_inc(x_30);
lean_dec(x_2);
x_31 = l_System_FilePath_dirName___closed__1;
x_32 = l_Lean_Name_toStringWithSep___main(x_31, x_28);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_IR_formatDecl___closed__4;
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_box(0);
x_38 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_29, x_29, x_36, x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l___private_Lean_Compiler_IR_Format_5__formatIRType___main(x_30);
lean_dec(x_30);
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
lean_object* _init_l_Lean_IR_declHasFormat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_alloc_closure((void*)(l_Lean_IR_formatDecl), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_declHasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_declHasFormat___closed__1;
return x_1;
}
}
lean_object* lean_ir_decl_to_string(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = l_Lean_IR_formatDecl(x_2, x_1);
x_4 = lean_box(0);
x_5 = l_Lean_Format_pretty(x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_IR_declHasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(lean_ir_decl_to_string), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_declHasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_declHasToString___closed__1;
return x_1;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Format(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Compiler_IR_Format(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_IR_Format_1__formatArg___closed__1 = _init_l___private_Lean_Compiler_IR_Format_1__formatArg___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_1__formatArg___closed__1);
l___private_Lean_Compiler_IR_Format_1__formatArg___closed__2 = _init_l___private_Lean_Compiler_IR_Format_1__formatArg___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_1__formatArg___closed__2);
l_Lean_IR_argHasFormat___closed__1 = _init_l_Lean_IR_argHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_argHasFormat___closed__1);
l_Lean_IR_argHasFormat = _init_l_Lean_IR_argHasFormat();
lean_mark_persistent(l_Lean_IR_argHasFormat);
l_Lean_IR_litValHasFormat___closed__1 = _init_l_Lean_IR_litValHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_litValHasFormat___closed__1);
l_Lean_IR_litValHasFormat = _init_l_Lean_IR_litValHasFormat();
lean_mark_persistent(l_Lean_IR_litValHasFormat);
l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__1 = _init_l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__1);
l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__2 = _init_l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__2);
l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3 = _init_l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_3__formatCtorInfo___closed__3);
l_Lean_IR_ctorInfoHasFormat___closed__1 = _init_l_Lean_IR_ctorInfoHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_ctorInfoHasFormat___closed__1);
l_Lean_IR_ctorInfoHasFormat = _init_l_Lean_IR_ctorInfoHasFormat();
lean_mark_persistent(l_Lean_IR_ctorInfoHasFormat);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__1 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__1);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__2 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__2);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__3 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__3);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__4 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__4);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__5 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__5();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__5);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__6 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__6();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__6);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__7 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__7();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__7);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__8 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__8();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__8);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__9 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__9();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__9);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__10 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__10();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__10);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__11 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__11();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__11);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__12 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__12();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__12);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__13 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__13();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__13);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__14 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__14();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__14);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__15 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__15();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__15);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__16 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__16();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__16);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__17 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__17();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__17);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__18 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__18();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__18);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__19 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__19();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__19);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__20 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__20();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__20);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__21 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__21();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__21);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__22 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__22();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__22);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__23 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__23();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__23);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__24 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__24();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__24);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__25 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__25();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__25);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__26 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__26();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__26);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__27 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__27();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__27);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__28 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__28();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__28);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__29 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__29();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__29);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__30 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__30();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__30);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__31 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__31();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__31);
l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__32 = _init_l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__32();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_4__formatExpr___closed__32);
l_Lean_IR_exprHasFormat___closed__1 = _init_l_Lean_IR_exprHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_exprHasFormat___closed__1);
l_Lean_IR_exprHasFormat = _init_l_Lean_IR_exprHasFormat();
lean_mark_persistent(l_Lean_IR_exprHasFormat);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__1 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__1);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__2 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__2);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__3 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__3);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__4 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__4);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__5 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__5();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__5);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__6 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__6();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__6);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__7 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__7();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__7);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__8 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__8();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__8);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__9 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__9();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__9);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__10 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__10();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__10);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__11 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__11();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__11);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__12 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__12();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__12);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__13 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__13();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__13);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__14 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__14();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__14);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__15 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__15();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__15);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__16 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__16();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__16);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__17 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__17();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__17);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__18 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__18();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__18);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__19);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__22 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__22();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__22);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__23 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__23();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__23);
l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__24 = _init_l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__24();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_5__formatIRType___main___closed__24);
l_Lean_IR_typeHasFormat___closed__1 = _init_l_Lean_IR_typeHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_typeHasFormat___closed__1);
l_Lean_IR_typeHasFormat = _init_l_Lean_IR_typeHasFormat();
lean_mark_persistent(l_Lean_IR_typeHasFormat);
l_Lean_IR_typeHasToString___closed__1 = _init_l_Lean_IR_typeHasToString___closed__1();
lean_mark_persistent(l_Lean_IR_typeHasToString___closed__1);
l_Lean_IR_typeHasToString = _init_l_Lean_IR_typeHasToString();
lean_mark_persistent(l_Lean_IR_typeHasToString);
l___private_Lean_Compiler_IR_Format_6__formatParam___closed__1 = _init_l___private_Lean_Compiler_IR_Format_6__formatParam___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_6__formatParam___closed__1);
l___private_Lean_Compiler_IR_Format_6__formatParam___closed__2 = _init_l___private_Lean_Compiler_IR_Format_6__formatParam___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_Format_6__formatParam___closed__2);
l_Lean_IR_paramHasFormat___closed__1 = _init_l_Lean_IR_paramHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_paramHasFormat___closed__1);
l_Lean_IR_paramHasFormat = _init_l_Lean_IR_paramHasFormat();
lean_mark_persistent(l_Lean_IR_paramHasFormat);
l_Lean_IR_formatAlt___closed__1 = _init_l_Lean_IR_formatAlt___closed__1();
lean_mark_persistent(l_Lean_IR_formatAlt___closed__1);
l_Lean_IR_formatAlt___closed__2 = _init_l_Lean_IR_formatAlt___closed__2();
lean_mark_persistent(l_Lean_IR_formatAlt___closed__2);
l_Lean_IR_formatAlt___closed__3 = _init_l_Lean_IR_formatAlt___closed__3();
lean_mark_persistent(l_Lean_IR_formatAlt___closed__3);
l_Lean_IR_formatAlt___closed__4 = _init_l_Lean_IR_formatAlt___closed__4();
lean_mark_persistent(l_Lean_IR_formatAlt___closed__4);
l_Lean_IR_formatFnBodyHead___closed__1 = _init_l_Lean_IR_formatFnBodyHead___closed__1();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__1);
l_Lean_IR_formatFnBodyHead___closed__2 = _init_l_Lean_IR_formatFnBodyHead___closed__2();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__2);
l_Lean_IR_formatFnBodyHead___closed__3 = _init_l_Lean_IR_formatFnBodyHead___closed__3();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__3);
l_Lean_IR_formatFnBodyHead___closed__4 = _init_l_Lean_IR_formatFnBodyHead___closed__4();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__4);
l_Lean_IR_formatFnBodyHead___closed__5 = _init_l_Lean_IR_formatFnBodyHead___closed__5();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__5);
l_Lean_IR_formatFnBodyHead___closed__6 = _init_l_Lean_IR_formatFnBodyHead___closed__6();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__6);
l_Lean_IR_formatFnBodyHead___closed__7 = _init_l_Lean_IR_formatFnBodyHead___closed__7();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__7);
l_Lean_IR_formatFnBodyHead___closed__8 = _init_l_Lean_IR_formatFnBodyHead___closed__8();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__8);
l_Lean_IR_formatFnBodyHead___closed__9 = _init_l_Lean_IR_formatFnBodyHead___closed__9();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__9);
l_Lean_IR_formatFnBodyHead___closed__10 = _init_l_Lean_IR_formatFnBodyHead___closed__10();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__10);
l_Lean_IR_formatFnBodyHead___closed__11 = _init_l_Lean_IR_formatFnBodyHead___closed__11();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__11);
l_Lean_IR_formatFnBodyHead___closed__12 = _init_l_Lean_IR_formatFnBodyHead___closed__12();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__12);
l_Lean_IR_formatFnBodyHead___closed__13 = _init_l_Lean_IR_formatFnBodyHead___closed__13();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__13);
l_Lean_IR_formatFnBodyHead___closed__14 = _init_l_Lean_IR_formatFnBodyHead___closed__14();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__14);
l_Lean_IR_formatFnBodyHead___closed__15 = _init_l_Lean_IR_formatFnBodyHead___closed__15();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__15);
l_Lean_IR_formatFnBodyHead___closed__16 = _init_l_Lean_IR_formatFnBodyHead___closed__16();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__16);
l_Lean_IR_formatFnBodyHead___closed__17 = _init_l_Lean_IR_formatFnBodyHead___closed__17();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__17);
l_Lean_IR_formatFnBodyHead___closed__18 = _init_l_Lean_IR_formatFnBodyHead___closed__18();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__18);
l_Lean_IR_formatFnBodyHead___closed__19 = _init_l_Lean_IR_formatFnBodyHead___closed__19();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__19);
l_Lean_IR_formatFnBodyHead___closed__20 = _init_l_Lean_IR_formatFnBodyHead___closed__20();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__20);
l_Lean_IR_formatFnBodyHead___closed__21 = _init_l_Lean_IR_formatFnBodyHead___closed__21();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__21);
l_Lean_IR_formatFnBodyHead___closed__22 = _init_l_Lean_IR_formatFnBodyHead___closed__22();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__22);
l_Lean_IR_formatFnBodyHead___closed__23 = _init_l_Lean_IR_formatFnBodyHead___closed__23();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__23);
l_Lean_IR_formatFnBodyHead___closed__24 = _init_l_Lean_IR_formatFnBodyHead___closed__24();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__24);
l_Lean_IR_formatFnBodyHead___closed__25 = _init_l_Lean_IR_formatFnBodyHead___closed__25();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__25);
l_Lean_IR_formatFnBodyHead___closed__26 = _init_l_Lean_IR_formatFnBodyHead___closed__26();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__26);
l_Lean_IR_formatFnBodyHead___closed__27 = _init_l_Lean_IR_formatFnBodyHead___closed__27();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__27);
l_Lean_IR_formatFnBodyHead___closed__28 = _init_l_Lean_IR_formatFnBodyHead___closed__28();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__28);
l_Lean_IR_formatFnBodyHead___closed__29 = _init_l_Lean_IR_formatFnBodyHead___closed__29();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__29);
l_Lean_IR_formatFnBodyHead___closed__30 = _init_l_Lean_IR_formatFnBodyHead___closed__30();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__30);
l_Lean_IR_formatFnBodyHead___closed__31 = _init_l_Lean_IR_formatFnBodyHead___closed__31();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__31);
l_Lean_IR_formatFnBodyHead___closed__32 = _init_l_Lean_IR_formatFnBodyHead___closed__32();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__32);
l_Lean_IR_formatFnBodyHead___closed__33 = _init_l_Lean_IR_formatFnBodyHead___closed__33();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__33);
l_Lean_IR_formatFnBodyHead___closed__34 = _init_l_Lean_IR_formatFnBodyHead___closed__34();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__34);
l_Lean_IR_formatFnBodyHead___closed__35 = _init_l_Lean_IR_formatFnBodyHead___closed__35();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__35);
l_Lean_IR_formatFnBodyHead___closed__36 = _init_l_Lean_IR_formatFnBodyHead___closed__36();
lean_mark_persistent(l_Lean_IR_formatFnBodyHead___closed__36);
l_Lean_IR_formatFnBody___main___closed__1 = _init_l_Lean_IR_formatFnBody___main___closed__1();
lean_mark_persistent(l_Lean_IR_formatFnBody___main___closed__1);
l_Lean_IR_formatFnBody___main___closed__2 = _init_l_Lean_IR_formatFnBody___main___closed__2();
lean_mark_persistent(l_Lean_IR_formatFnBody___main___closed__2);
l_Lean_IR_formatFnBody___main___closed__3 = _init_l_Lean_IR_formatFnBody___main___closed__3();
lean_mark_persistent(l_Lean_IR_formatFnBody___main___closed__3);
l_Lean_IR_formatFnBody___main___closed__4 = _init_l_Lean_IR_formatFnBody___main___closed__4();
lean_mark_persistent(l_Lean_IR_formatFnBody___main___closed__4);
l_Lean_IR_fnBodyHasFormat___closed__1 = _init_l_Lean_IR_fnBodyHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_fnBodyHasFormat___closed__1);
l_Lean_IR_fnBodyHasFormat = _init_l_Lean_IR_fnBodyHasFormat();
lean_mark_persistent(l_Lean_IR_fnBodyHasFormat);
l_Lean_IR_formatDecl___closed__1 = _init_l_Lean_IR_formatDecl___closed__1();
lean_mark_persistent(l_Lean_IR_formatDecl___closed__1);
l_Lean_IR_formatDecl___closed__2 = _init_l_Lean_IR_formatDecl___closed__2();
lean_mark_persistent(l_Lean_IR_formatDecl___closed__2);
l_Lean_IR_formatDecl___closed__3 = _init_l_Lean_IR_formatDecl___closed__3();
lean_mark_persistent(l_Lean_IR_formatDecl___closed__3);
l_Lean_IR_formatDecl___closed__4 = _init_l_Lean_IR_formatDecl___closed__4();
lean_mark_persistent(l_Lean_IR_formatDecl___closed__4);
l_Lean_IR_declHasFormat___closed__1 = _init_l_Lean_IR_declHasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_declHasFormat___closed__1);
l_Lean_IR_declHasFormat = _init_l_Lean_IR_declHasFormat();
lean_mark_persistent(l_Lean_IR_declHasFormat);
l_Lean_IR_declHasToString___closed__1 = _init_l_Lean_IR_declHasToString___closed__1();
lean_mark_persistent(l_Lean_IR_declHasToString___closed__1);
l_Lean_IR_declHasToString = _init_l_Lean_IR_declHasToString();
lean_mark_persistent(l_Lean_IR_declHasToString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
