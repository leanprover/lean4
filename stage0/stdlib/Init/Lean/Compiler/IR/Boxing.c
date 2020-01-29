// Lean compiler output
// Module: Init.Lean.Compiler.IR.Boxing
// Imports: Init.Control.EState Init.Control.Reader Init.Data.AssocList Init.Data.Nat Init.Lean.Runtime Init.Lean.Compiler.ClosedTermCache Init.Lean.Compiler.ExternAttr Init.Lean.Compiler.IR.Basic Init.Lean.Compiler.IR.CompilerM Init.Lean.Compiler.IR.FreeVars Init.Lean.Compiler.IR.ElimDeadVars
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
lean_object* l___private_Init_Lean_Compiler_IR_Boxing_2__isExpensiveConstantValueBoxing(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_ExplicitBoxing_eqvTypes(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getVarType___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_IR_ExplicitBoxing_withJDecl(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_closureMaxArgs;
lean_object* l_Lean_IR_ExplicitBoxing_withParams(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Boxing_1__mkFresh(lean_object*);
lean_object* l_ReaderT_Monad___rarg(lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_explicitBoxing___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkFresh(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_resultType(lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_Boxing_2__isExpensiveConstantValueBoxing___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_run(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getResultType___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withParams___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__2;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__1;
lean_object* l_Lean_IR_ExplicitBoxing_mkCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_beq(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getValue(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_paramInh;
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_beq___main(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_explicitBoxing(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getJPParams___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withParams___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getScrutineeType___boxed(lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
extern uint8_t l_String_posOfAux___main___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_posOfAux___main___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withJDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Id_Monad;
lean_object* l_Lean_IR_ExplicitBoxing_withVDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_isBoxedName___boxed(lean_object*);
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getVarType(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion___boxed(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_Monad___rarg(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_ExplicitBoxing_isBoxedName(lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_LocalContext_addParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getEnv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_eqvTypes___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getResultType(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkFresh___boxed(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getScrutineeType(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withVDecl(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_IR_ExplicitBoxing_mkCast___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Decl_Inhabited___closed__1;
lean_object* l_Lean_IR_ExplicitBoxing_castVarIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
lean_object* l_Lean_IR_Decl_params(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getJPParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getEnv(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1;
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkFresh___rarg(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__2;
lean_object* _init_l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_boxed");
return x_1;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_IR_ExplicitBoxing_isBoxedName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_4 = lean_string_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_isBoxedName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Boxing_1__mkFresh(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = l_Lean_IR_IRType_isScalar(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
lean_dec(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
}
}
else
{
lean_dec(x_8);
if (x_2 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_5 = x_16;
goto _start;
}
else
{
lean_dec(x_5);
return x_2;
}
}
}
}
}
uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lean_IR_Decl_params(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_3);
x_7 = l_Lean_closureMaxArgs;
x_8 = lean_nat_dec_lt(x_7, x_4);
lean_dec(x_4);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_IR_Decl_resultType(x_2);
x_10 = l_Lean_IR_IRType_isScalar(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Array_anyRangeMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(x_2, x_6, x_3, x_4, x_5);
lean_dec(x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_IR_Decl_name(x_2);
x_13 = l_Lean_isExtern(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_closureMaxArgs;
x_15 = lean_nat_dec_lt(x_14, x_4);
lean_dec(x_4);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_4);
x_16 = 1;
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_4);
x_17 = 1;
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_3);
x_18 = 1;
return x_18;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Array_anyRangeMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_box(0);
x_11 = x_10;
x_12 = lean_array_fset(x_2, x_1, x_11);
x_13 = l___private_Init_Lean_Compiler_IR_Boxing_1__mkFresh(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = lean_box(7);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_1, x_19);
x_21 = x_18;
lean_dec(x_9);
x_22 = lean_array_fset(x_12, x_1, x_21);
lean_dec(x_1);
x_1 = x_20;
x_2 = x_22;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_16 = l_Lean_IR_paramInh;
x_17 = lean_array_get(x_16, x_1, x_12);
x_18 = lean_array_get(x_16, x_2, x_12);
lean_dec(x_12);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_IR_IRType_isScalar(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_String_posOfAux___main___closed__2;
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_free_object(x_5);
x_22 = l___private_Init_Lean_Compiler_IR_Boxing_1__mkFresh(x_6);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_box(13);
lean_inc(x_24);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_19);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_array_push(x_14, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_24);
x_32 = lean_array_push(x_15, x_31);
lean_ctor_set(x_22, 1, x_32);
lean_ctor_set(x_22, 0, x_30);
x_4 = x_10;
x_5 = x_22;
x_6 = x_25;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_36 = lean_ctor_get(x_18, 0);
lean_inc(x_36);
lean_dec(x_18);
x_37 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_box(13);
lean_inc(x_34);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_19);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_array_push(x_14, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_34);
x_42 = lean_array_push(x_15, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_4 = x_10;
x_5 = x_43;
x_6 = x_35;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_19);
x_45 = lean_ctor_get(x_18, 0);
lean_inc(x_45);
lean_dec(x_18);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_array_push(x_15, x_46);
lean_ctor_set(x_5, 1, x_47);
x_4 = x_10;
goto _start;
}
}
else
{
uint8_t x_49; 
x_49 = l_String_posOfAux___main___closed__1;
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
lean_free_object(x_5);
x_50 = l___private_Init_Lean_Compiler_IR_Boxing_1__mkFresh(x_6);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = lean_ctor_get(x_18, 0);
lean_inc(x_54);
lean_dec(x_18);
x_55 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_box(13);
lean_inc(x_52);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_19);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_array_push(x_14, x_57);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_52);
x_60 = lean_array_push(x_15, x_59);
lean_ctor_set(x_50, 1, x_60);
lean_ctor_set(x_50, 0, x_58);
x_4 = x_10;
x_5 = x_50;
x_6 = x_53;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_62 = lean_ctor_get(x_50, 0);
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_50);
x_64 = lean_ctor_get(x_18, 0);
lean_inc(x_64);
lean_dec(x_18);
x_65 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_box(13);
lean_inc(x_62);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_19);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set(x_67, 3, x_66);
x_68 = lean_array_push(x_14, x_67);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_62);
x_70 = lean_array_push(x_15, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_4 = x_10;
x_5 = x_71;
x_6 = x_63;
goto _start;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_19);
x_73 = lean_ctor_get(x_18, 0);
lean_inc(x_73);
lean_dec(x_18);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_array_push(x_15, x_74);
lean_ctor_set(x_5, 1, x_75);
x_4 = x_10;
goto _start;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_77 = lean_ctor_get(x_5, 0);
x_78 = lean_ctor_get(x_5, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_5);
x_79 = l_Lean_IR_paramInh;
x_80 = lean_array_get(x_79, x_1, x_12);
x_81 = lean_array_get(x_79, x_2, x_12);
lean_dec(x_12);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_IR_IRType_isScalar(x_82);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = l_String_posOfAux___main___closed__2;
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_85 = l___private_Init_Lean_Compiler_IR_Boxing_1__mkFresh(x_6);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_81, 0);
lean_inc(x_89);
lean_dec(x_81);
x_90 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_box(13);
lean_inc(x_86);
x_92 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_92, 0, x_86);
lean_ctor_set(x_92, 1, x_82);
lean_ctor_set(x_92, 2, x_90);
lean_ctor_set(x_92, 3, x_91);
x_93 = lean_array_push(x_77, x_92);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_86);
x_95 = lean_array_push(x_78, x_94);
if (lean_is_scalar(x_88)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_88;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_4 = x_10;
x_5 = x_96;
x_6 = x_87;
goto _start;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_82);
x_98 = lean_ctor_get(x_81, 0);
lean_inc(x_98);
lean_dec(x_81);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_array_push(x_78, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_77);
lean_ctor_set(x_101, 1, x_100);
x_4 = x_10;
x_5 = x_101;
goto _start;
}
}
else
{
uint8_t x_103; 
x_103 = l_String_posOfAux___main___closed__1;
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_104 = l___private_Init_Lean_Compiler_IR_Boxing_1__mkFresh(x_6);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_81, 0);
lean_inc(x_108);
lean_dec(x_81);
x_109 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_box(13);
lean_inc(x_105);
x_111 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_82);
lean_ctor_set(x_111, 2, x_109);
lean_ctor_set(x_111, 3, x_110);
x_112 = lean_array_push(x_77, x_111);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_105);
x_114 = lean_array_push(x_78, x_113);
if (lean_is_scalar(x_107)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_107;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_4 = x_10;
x_5 = x_115;
x_6 = x_106;
goto _start;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_82);
x_117 = lean_ctor_get(x_81, 0);
lean_inc(x_117);
lean_dec(x_81);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_array_push(x_78, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_77);
lean_ctor_set(x_120, 1, x_119);
x_4 = x_10;
x_5 = x_120;
goto _start;
}
}
}
}
else
{
lean_object* x_122; 
lean_dec(x_4);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_5);
lean_ctor_set(x_122, 1, x_6);
return x_122;
}
}
}
lean_object* _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_3 = l_Lean_IR_Decl_params(x_1);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_5 = l_Array_umapMAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1(x_4, x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_array_get_size(x_6);
x_9 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
lean_inc(x_8);
x_10 = l_Nat_foldMAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(x_3, x_6, x_8, x_8, x_9, x_7);
lean_dec(x_8);
lean_dec(x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Init_Lean_Compiler_IR_Boxing_1__mkFresh(x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_IR_Decl_resultType(x_1);
x_20 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_20);
x_21 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
x_22 = lean_box(13);
lean_inc(x_19);
lean_inc(x_17);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_22);
x_24 = lean_array_push(x_13, x_23);
x_25 = l_Lean_IR_IRType_isScalar(x_19);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_String_posOfAux___main___closed__2;
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_free_object(x_15);
x_27 = l___private_Init_Lean_Compiler_IR_Boxing_1__mkFresh(x_18);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_17);
x_31 = lean_box(7);
lean_inc(x_29);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_22);
x_33 = lean_array_push(x_24, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_35 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_IR_reshape(x_33, x_35);
x_37 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_38 = lean_name_mk_string(x_20, x_37);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_6);
lean_ctor_set(x_39, 2, x_31);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_27, 0, x_39);
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_19);
lean_ctor_set(x_42, 1, x_17);
x_43 = lean_box(7);
lean_inc(x_40);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_42);
lean_ctor_set(x_44, 3, x_22);
x_45 = lean_array_push(x_24, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_40);
x_47 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_IR_reshape(x_45, x_47);
x_49 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_50 = lean_name_mk_string(x_20, x_49);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_6);
lean_ctor_set(x_51, 2, x_43);
lean_ctor_set(x_51, 3, x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_41);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_19);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_17);
x_54 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_IR_reshape(x_24, x_54);
x_56 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_57 = lean_name_mk_string(x_20, x_56);
x_58 = lean_box(7);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_6);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set(x_59, 3, x_55);
lean_ctor_set(x_15, 0, x_59);
return x_15;
}
}
else
{
uint8_t x_60; 
x_60 = l_String_posOfAux___main___closed__1;
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
lean_free_object(x_15);
x_61 = l___private_Init_Lean_Compiler_IR_Boxing_1__mkFresh(x_18);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_64, 0, x_19);
lean_ctor_set(x_64, 1, x_17);
x_65 = lean_box(7);
lean_inc(x_63);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_22);
x_67 = lean_array_push(x_24, x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_69 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_IR_reshape(x_67, x_69);
x_71 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_72 = lean_name_mk_string(x_20, x_71);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_6);
lean_ctor_set(x_73, 2, x_65);
lean_ctor_set(x_73, 3, x_70);
lean_ctor_set(x_61, 0, x_73);
return x_61;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_74 = lean_ctor_get(x_61, 0);
x_75 = lean_ctor_get(x_61, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_61);
x_76 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_76, 0, x_19);
lean_ctor_set(x_76, 1, x_17);
x_77 = lean_box(7);
lean_inc(x_74);
x_78 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_76);
lean_ctor_set(x_78, 3, x_22);
x_79 = lean_array_push(x_24, x_78);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_74);
x_81 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = l_Lean_IR_reshape(x_79, x_81);
x_83 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_84 = lean_name_mk_string(x_20, x_83);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_6);
lean_ctor_set(x_85, 2, x_77);
lean_ctor_set(x_85, 3, x_82);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_75);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_19);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_17);
x_88 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_Lean_IR_reshape(x_24, x_88);
x_90 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_91 = lean_name_mk_string(x_20, x_90);
x_92 = lean_box(7);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_6);
lean_ctor_set(x_93, 2, x_92);
lean_ctor_set(x_93, 3, x_89);
lean_ctor_set(x_15, 0, x_93);
return x_15;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_94 = lean_ctor_get(x_15, 0);
x_95 = lean_ctor_get(x_15, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_15);
x_96 = l_Lean_IR_Decl_resultType(x_1);
x_97 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_97);
x_98 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_14);
x_99 = lean_box(13);
lean_inc(x_96);
lean_inc(x_94);
x_100 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_96);
lean_ctor_set(x_100, 2, x_98);
lean_ctor_set(x_100, 3, x_99);
x_101 = lean_array_push(x_13, x_100);
x_102 = l_Lean_IR_IRType_isScalar(x_96);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = l_String_posOfAux___main___closed__2;
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_104 = l___private_Init_Lean_Compiler_IR_Boxing_1__mkFresh(x_95);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_108, 0, x_96);
lean_ctor_set(x_108, 1, x_94);
x_109 = lean_box(7);
lean_inc(x_105);
x_110 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_108);
lean_ctor_set(x_110, 3, x_99);
x_111 = lean_array_push(x_101, x_110);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_105);
x_113 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = l_Lean_IR_reshape(x_111, x_113);
x_115 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_116 = lean_name_mk_string(x_97, x_115);
x_117 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_6);
lean_ctor_set(x_117, 2, x_109);
lean_ctor_set(x_117, 3, x_114);
if (lean_is_scalar(x_107)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_107;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_106);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_96);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_94);
x_120 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = l_Lean_IR_reshape(x_101, x_120);
x_122 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_123 = lean_name_mk_string(x_97, x_122);
x_124 = lean_box(7);
x_125 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_6);
lean_ctor_set(x_125, 2, x_124);
lean_ctor_set(x_125, 3, x_121);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_95);
return x_126;
}
}
else
{
uint8_t x_127; 
x_127 = l_String_posOfAux___main___closed__1;
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_128 = l___private_Init_Lean_Compiler_IR_Boxing_1__mkFresh(x_95);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
x_132 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_132, 0, x_96);
lean_ctor_set(x_132, 1, x_94);
x_133 = lean_box(7);
lean_inc(x_129);
x_134 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_132);
lean_ctor_set(x_134, 3, x_99);
x_135 = lean_array_push(x_101, x_134);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_129);
x_137 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = l_Lean_IR_reshape(x_135, x_137);
x_139 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_140 = lean_name_mk_string(x_97, x_139);
x_141 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_6);
lean_ctor_set(x_141, 2, x_133);
lean_ctor_set(x_141, 3, x_138);
if (lean_is_scalar(x_131)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_131;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_130);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_96);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_94);
x_144 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = l_Lean_IR_reshape(x_101, x_144);
x_146 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_147 = lean_name_mk_string(x_97, x_146);
x_148 = lean_box(7);
x_149 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_6);
lean_ctor_set(x_149, 2, x_148);
lean_ctor_set(x_149, 3, x_145);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_95);
return x_150;
}
}
}
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldMAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_1, x_8);
x_10 = l_coeDecidableEq(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
if (x_10 == 0)
{
lean_dec(x_8);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_8);
lean_dec(x_8);
x_15 = lean_array_push(x_5, x_14);
x_4 = x_12;
x_5 = x_15;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_empty___closed__1;
x_5 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(x_1, x_2, x_2, x_3, x_4);
x_6 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_5, x_5, x_3, x_2);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_array_fget(x_2, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_IR_CtorInfo_isScalar(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = 1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
goto _start;
}
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getScrutineeType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
uint8_t x_18; 
x_18 = 0;
x_5 = x_18;
goto block_17;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_anyRangeMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(x_1, x_1, x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 1;
x_5 = x_21;
goto block_17;
}
else
{
uint8_t x_22; 
x_22 = 0;
x_5 = x_22;
goto block_17;
}
}
block_17:
{
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_box(7);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(256u);
x_8 = lean_nat_dec_lt(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(65536u);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_cstr_to_nat("4294967296");
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_box(7);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_box(3);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_box(2);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = lean_box(1);
return x_16;
}
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getScrutineeType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_IR_ExplicitBoxing_eqvTypes(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = l_Lean_IR_IRType_isScalar(x_1);
x_4 = l_Lean_IR_IRType_isScalar(x_2);
if (x_3 == 0)
{
if (x_4 == 0)
{
uint8_t x_9; 
x_9 = 1;
x_5 = x_9;
goto block_8;
}
else
{
uint8_t x_10; 
x_10 = 0;
x_5 = x_10;
goto block_8;
}
}
else
{
if (x_4 == 0)
{
uint8_t x_11; 
x_11 = 0;
x_5 = x_11;
goto block_8;
}
else
{
uint8_t x_12; 
x_12 = 1;
x_5 = x_12;
goto block_8;
}
}
block_8:
{
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
if (x_3 == 0)
{
return x_5;
}
else
{
uint8_t x_7; 
x_7 = l_Lean_IR_IRType_beq___main(x_1, x_2);
return x_7;
}
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_eqvTypes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_mkFresh___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_ctor_set(x_1, 0, x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_mkFresh(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_mkFresh___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_mkFresh___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ExplicitBoxing_mkFresh(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_getEnv(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_getLocalContext(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getResultType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getResultType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_getResultType(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_ExplicitBoxing_getLocalContext(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_IR_LocalContext_getType(x_6, x_1);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_box(7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = l_Lean_IR_LocalContext_getType(x_10, x_1);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_getVarType(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getJPParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_ExplicitBoxing_getLocalContext(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_IR_LocalContext_getJPParams(x_6, x_1);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_Array_empty___closed__1;
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = l_Lean_IR_LocalContext_getJPParams(x_10, x_1);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Array_empty___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getJPParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_getJPParams(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 4);
x_5 = lean_ctor_get(x_2, 3);
x_6 = l_Lean_IR_findEnvDecl_x27(x_4, x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_IR_Decl_Inhabited___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_getDecl(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_withParams___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_iterateMAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_1, x_1, x_7, x_6);
lean_ctor_set(x_3, 1, x_8);
x_9 = lean_apply_2(x_2, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_iterateMAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_1, x_1, x_15, x_11);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_14);
x_18 = lean_apply_2(x_2, x_17, x_4);
return x_18;
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_withParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_withParams___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_withParams___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_withParams___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_withVDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_IR_LocalContext_addLocal(x_8, x_1, x_2, x_3);
lean_ctor_set(x_5, 1, x_9);
x_10 = lean_apply_2(x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_16 = l_Lean_IR_LocalContext_addLocal(x_12, x_1, x_2, x_3);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_15);
x_18 = lean_apply_2(x_4, x_17, x_6);
return x_18;
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_withVDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_withVDecl___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_withJDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_IR_LocalContext_addJP(x_8, x_1, x_2, x_3);
lean_ctor_set(x_5, 1, x_9);
x_10 = lean_apply_2(x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_16 = l_Lean_IR_LocalContext_addJP(x_12, x_1, x_2, x_3);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_15);
x_18 = lean_apply_2(x_4, x_17, x_6);
return x_18;
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_withJDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_withJDecl___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Boxing_2__isExpensiveConstantValueBoxing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_42; 
x_42 = l_Lean_IR_IRType_isScalar(x_2);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = 1;
x_5 = x_43;
goto block_41;
}
else
{
uint8_t x_44; 
x_44 = 0;
x_5 = x_44;
goto block_41;
}
block_41:
{
uint8_t x_6; 
x_6 = l_coeDecidableEq(x_5);
if (x_6 == 0)
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
default: 
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_IR_ExplicitBoxing_getLocalContext(x_3, x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_IR_LocalContext_getValue(x_13, x_1);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
switch (lean_obj_tag(x_15)) {
case 6:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_17);
x_20 = l_coeDecidableEq(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_14);
x_21 = lean_box(0);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
}
case 11:
{
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
default: 
{
lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_14);
x_22 = lean_box(0);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = l_Lean_IR_LocalContext_getValue(x_23, x_1);
lean_dec(x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
switch (lean_obj_tag(x_27)) {
case 6:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_29, x_30);
lean_dec(x_29);
x_32 = l_coeDecidableEq(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_25);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_24);
return x_35;
}
}
case 11:
{
lean_object* x_36; 
lean_dec(x_27);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_24);
return x_36;
}
default: 
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_27);
lean_dec(x_25);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_24);
return x_38;
}
}
}
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_4);
return x_40;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_Boxing_2__isExpensiveConstantValueBoxing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Compiler_IR_Boxing_2__isExpensiveConstantValueBoxing(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_AssocList_find___main___at_Lean_IR_ExplicitBoxing_mkCast___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_1);
x_7 = l_Lean_IR_FnBody_beq(x_4, x_1);
if (x_7 == 0)
{
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ExplicitBoxing_mkCast___closed__1;
x_2 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_boxed_const");
return x_1;
}
}
lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_mkCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Init_Lean_Compiler_IR_Boxing_2__isExpensiveConstantValueBoxing(x_1, x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = l_Lean_IR_IRType_isScalar(x_2);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = l_Lean_IR_IRType_isScalar(x_2);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_7, 0);
lean_inc(x_24);
lean_dec(x_7);
x_25 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_unsigned_to_nat(2u);
x_28 = l_Lean_IR_ExplicitBoxing_mkCast___closed__2;
lean_inc(x_3);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_29);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_22, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_22, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_30);
x_35 = l_AssocList_find___main___at_Lean_IR_ExplicitBoxing_mkCast___spec__1(x_30, x_33);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_37 = lean_ctor_get(x_22, 3);
lean_dec(x_37);
x_38 = lean_ctor_get(x_22, 2);
lean_dec(x_38);
x_39 = lean_ctor_get(x_22, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_22, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_4, 0);
x_42 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_34);
x_43 = l_Lean_Name_appendIndexAfter(x_42, x_34);
x_44 = l_Lean_Name_append___main(x_41, x_43);
x_45 = l_Array_empty___closed__1;
lean_inc(x_44);
x_46 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_30);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_3);
lean_ctor_set(x_47, 3, x_30);
x_48 = lean_array_push(x_32, x_47);
lean_inc(x_46);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_30);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_49, 2, x_33);
x_50 = lean_nat_add(x_34, x_25);
lean_dec(x_34);
lean_ctor_set(x_22, 3, x_50);
lean_ctor_set(x_22, 2, x_49);
lean_ctor_set(x_22, 1, x_48);
lean_ctor_set(x_6, 0, x_46);
return x_6;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_22);
x_51 = lean_ctor_get(x_4, 0);
x_52 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_34);
x_53 = l_Lean_Name_appendIndexAfter(x_52, x_34);
x_54 = l_Lean_Name_append___main(x_51, x_53);
x_55 = l_Array_empty___closed__1;
lean_inc(x_54);
x_56 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_30);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_3);
lean_ctor_set(x_57, 3, x_30);
x_58 = lean_array_push(x_32, x_57);
lean_inc(x_56);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_30);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_33);
x_60 = lean_nat_add(x_34, x_25);
lean_dec(x_34);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_31);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_6, 1, x_61);
lean_ctor_set(x_6, 0, x_56);
return x_6;
}
}
else
{
lean_object* x_62; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_3);
x_62 = lean_ctor_get(x_35, 0);
lean_inc(x_62);
lean_dec(x_35);
lean_ctor_set(x_6, 0, x_62);
return x_6;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_63 = lean_ctor_get(x_6, 1);
lean_inc(x_63);
lean_dec(x_6);
x_64 = lean_ctor_get(x_7, 0);
lean_inc(x_64);
lean_dec(x_7);
x_65 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_2);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_unsigned_to_nat(2u);
x_68 = l_Lean_IR_ExplicitBoxing_mkCast___closed__2;
lean_inc(x_3);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_3);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_2);
lean_ctor_set(x_70, 2, x_64);
lean_ctor_set(x_70, 3, x_69);
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_63, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_63, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_70);
x_75 = l_AssocList_find___main___at_Lean_IR_ExplicitBoxing_mkCast___spec__1(x_70, x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 lean_ctor_release(x_63, 3);
 x_76 = x_63;
} else {
 lean_dec_ref(x_63);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_4, 0);
x_78 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_74);
x_79 = l_Lean_Name_appendIndexAfter(x_78, x_74);
x_80 = l_Lean_Name_append___main(x_77, x_79);
x_81 = l_Array_empty___closed__1;
lean_inc(x_80);
x_82 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_70);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 2, x_3);
lean_ctor_set(x_83, 3, x_70);
x_84 = lean_array_push(x_72, x_83);
lean_inc(x_82);
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_70);
lean_ctor_set(x_85, 1, x_82);
lean_ctor_set(x_85, 2, x_73);
x_86 = lean_nat_add(x_74, x_65);
lean_dec(x_74);
if (lean_is_scalar(x_76)) {
 x_87 = lean_alloc_ctor(0, 4, 0);
} else {
 x_87 = x_76;
}
lean_ctor_set(x_87, 0, x_71);
lean_ctor_set(x_87, 1, x_84);
lean_ctor_set(x_87, 2, x_85);
lean_ctor_set(x_87, 3, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_3);
x_89 = lean_ctor_get(x_75, 0);
lean_inc(x_89);
lean_dec(x_75);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_63);
return x_90;
}
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_mkCast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ExplicitBoxing_mkCast(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castVarIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_6 = l_Lean_IR_ExplicitBoxing_getVarType(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_7, x_2);
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_2);
x_14 = l_Lean_IR_ExplicitBoxing_mkCast(x_1, x_7, x_2, x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
x_17 = lean_apply_3(x_3, x_12, x_4, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_15);
lean_ctor_set(x_23, 3, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_7);
lean_dec(x_2);
x_25 = lean_apply_3(x_3, x_1, x_4, x_8);
return x_25;
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_IR_ExplicitBoxing_getVarType(x_7, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_9, x_2);
x_12 = l_coeDecidableEq(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_2);
x_16 = l_Lean_IR_ExplicitBoxing_mkCast(x_7, x_9, x_2, x_4, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_14);
lean_ctor_set(x_1, 0, x_14);
x_19 = lean_apply_3(x_3, x_1, x_4, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_2);
lean_ctor_set(x_25, 2, x_17);
lean_ctor_set(x_25, 3, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_9);
lean_dec(x_2);
x_27 = lean_apply_3(x_3, x_1, x_4, x_10);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lean_IR_ExplicitBoxing_getVarType(x_28, x_4, x_5);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_30, x_2);
x_33 = l_coeDecidableEq(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_31);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_2);
x_37 = l_Lean_IR_ExplicitBoxing_mkCast(x_28, x_30, x_2, x_4, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_35);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_41 = lean_apply_3(x_3, x_40, x_4, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set(x_45, 1, x_2);
lean_ctor_set(x_45, 2, x_38);
lean_ctor_set(x_45, 3, x_42);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_30);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_28);
x_48 = lean_apply_3(x_3, x_47, x_4, x_31);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_2);
x_49 = lean_apply_3(x_3, x_1, x_4, x_5);
return x_49;
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = l_Lean_IR_ExplicitBoxing_getVarType(x_11, x_5, x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_14, x_7);
x_17 = l_coeDecidableEq(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_free_object(x_12);
lean_free_object(x_4);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_3, 0);
lean_dec(x_19);
x_20 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_15);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_7);
x_24 = l_Lean_IR_ExplicitBoxing_mkCast(x_11, x_14, x_7, x_5, x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_box(13);
lean_inc(x_22);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_7);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_3, 0, x_22);
x_30 = lean_array_push(x_9, x_3);
x_31 = lean_array_push(x_10, x_29);
lean_ctor_set(x_24, 1, x_31);
lean_ctor_set(x_24, 0, x_30);
lean_ctor_set(x_20, 1, x_27);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_box(13);
lean_inc(x_22);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_7);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_3, 0, x_22);
x_36 = lean_array_push(x_9, x_3);
x_37 = lean_array_push(x_10, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_20, 1, x_33);
lean_ctor_set(x_20, 0, x_38);
return x_20;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_20);
lean_inc(x_7);
x_41 = l_Lean_IR_ExplicitBoxing_mkCast(x_11, x_14, x_7, x_5, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_box(13);
lean_inc(x_39);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_7);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_45);
lean_ctor_set(x_3, 0, x_39);
x_47 = lean_array_push(x_9, x_3);
x_48 = lean_array_push(x_10, x_46);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_43);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_3);
x_51 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_15);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
lean_inc(x_7);
x_55 = l_Lean_IR_ExplicitBoxing_mkCast(x_11, x_14, x_7, x_5, x_53);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_59 = lean_box(13);
lean_inc(x_52);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_7);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_59);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_52);
x_62 = lean_array_push(x_9, x_61);
x_63 = lean_array_push(x_10, x_60);
if (lean_is_scalar(x_58)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_58;
}
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
if (lean_is_scalar(x_54)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_54;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
return x_65;
}
}
else
{
lean_object* x_66; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_7);
x_66 = lean_array_push(x_9, x_3);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 0, x_66);
lean_ctor_set(x_4, 1, x_15);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_12, 0);
x_68 = lean_ctor_get(x_12, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_12);
x_69 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_67, x_7);
x_70 = l_coeDecidableEq(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_free_object(x_4);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_71 = x_3;
} else {
 lean_dec_ref(x_3);
 x_71 = lean_box(0);
}
x_72 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_68);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
lean_inc(x_7);
x_76 = l_Lean_IR_ExplicitBoxing_mkCast(x_11, x_67, x_7, x_5, x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_box(13);
lean_inc(x_73);
x_81 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_81, 0, x_73);
lean_ctor_set(x_81, 1, x_7);
lean_ctor_set(x_81, 2, x_77);
lean_ctor_set(x_81, 3, x_80);
if (lean_is_scalar(x_71)) {
 x_82 = lean_alloc_ctor(0, 1, 0);
} else {
 x_82 = x_71;
}
lean_ctor_set(x_82, 0, x_73);
x_83 = lean_array_push(x_9, x_82);
x_84 = lean_array_push(x_10, x_81);
if (lean_is_scalar(x_79)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_79;
}
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
if (lean_is_scalar(x_75)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_75;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_78);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_67);
lean_dec(x_11);
lean_dec(x_7);
x_87 = lean_array_push(x_9, x_3);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_10);
lean_ctor_set(x_4, 1, x_68);
lean_ctor_set(x_4, 0, x_88);
return x_4;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; 
x_89 = lean_ctor_get(x_4, 0);
x_90 = lean_ctor_get(x_4, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_4);
x_91 = lean_ctor_get(x_3, 0);
lean_inc(x_91);
x_92 = l_Lean_IR_ExplicitBoxing_getVarType(x_91, x_5, x_6);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_93, x_7);
x_97 = l_coeDecidableEq(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_95);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_98 = x_3;
} else {
 lean_dec_ref(x_3);
 x_98 = lean_box(0);
}
x_99 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_94);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
lean_inc(x_7);
x_103 = l_Lean_IR_ExplicitBoxing_mkCast(x_91, x_93, x_7, x_5, x_101);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
x_107 = lean_box(13);
lean_inc(x_100);
x_108 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_108, 0, x_100);
lean_ctor_set(x_108, 1, x_7);
lean_ctor_set(x_108, 2, x_104);
lean_ctor_set(x_108, 3, x_107);
if (lean_is_scalar(x_98)) {
 x_109 = lean_alloc_ctor(0, 1, 0);
} else {
 x_109 = x_98;
}
lean_ctor_set(x_109, 0, x_100);
x_110 = lean_array_push(x_89, x_109);
x_111 = lean_array_push(x_90, x_108);
if (lean_is_scalar(x_106)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_106;
}
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
if (lean_is_scalar(x_102)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_102;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_105);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_7);
x_114 = lean_array_push(x_89, x_3);
if (lean_is_scalar(x_95)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_95;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_90);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_94);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_7);
x_117 = !lean_is_exclusive(x_4);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_4, 0);
x_119 = lean_array_push(x_118, x_3);
lean_ctor_set(x_4, 0, x_119);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_4);
lean_ctor_set(x_120, 1, x_6);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_4, 0);
x_122 = lean_ctor_get(x_4, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_4);
x_123 = lean_array_push(x_121, x_3);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_6);
return x_125;
}
}
}
}
lean_object* _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_Monad;
x_2 = l_StateT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1;
x_2 = l_ReaderT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___lambda__1___boxed), 6, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__2;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_9 = l_Array_iterateMAux___main___rarg(x_6, lean_box(0), x_1, x_5, x_7, x_8);
x_10 = lean_apply_2(x_9, x_3, x_4);
return x_10;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
x_14 = l_Lean_IR_paramInh;
x_15 = lean_array_get(x_14, x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
x_20 = l_Lean_IR_ExplicitBoxing_getVarType(x_19, x_6, x_7);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_22, x_16);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_free_object(x_20);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_11, 0);
lean_dec(x_27);
x_28 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_16);
x_31 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_22, x_16, x_6, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_box(13);
lean_inc(x_29);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_16);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_11, 0, x_29);
x_37 = lean_array_push(x_17, x_11);
x_38 = lean_array_push(x_18, x_36);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_37);
x_4 = x_13;
x_5 = x_31;
x_7 = x_34;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
x_42 = lean_box(13);
lean_inc(x_29);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_16);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_11, 0, x_29);
x_44 = lean_array_push(x_17, x_11);
x_45 = lean_array_push(x_18, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_4 = x_13;
x_5 = x_46;
x_7 = x_41;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_11);
x_48 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_16);
x_51 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_22, x_16, x_6, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_box(13);
lean_inc(x_49);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_16);
lean_ctor_set(x_56, 2, x_52);
lean_ctor_set(x_56, 3, x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_49);
x_58 = lean_array_push(x_17, x_57);
x_59 = lean_array_push(x_18, x_56);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_4 = x_13;
x_5 = x_60;
x_7 = x_53;
goto _start;
}
}
else
{
lean_object* x_62; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_16);
x_62 = lean_array_push(x_17, x_11);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 0, x_62);
x_4 = x_13;
x_5 = x_20;
x_7 = x_23;
goto _start;
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_20, 0);
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_20);
x_66 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_64, x_16);
x_67 = l_coeDecidableEq(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_68 = x_11;
} else {
 lean_dec_ref(x_11);
 x_68 = lean_box(0);
}
x_69 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_65);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_16);
x_72 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_64, x_16, x_6, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_box(13);
lean_inc(x_70);
x_77 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_16);
lean_ctor_set(x_77, 2, x_73);
lean_ctor_set(x_77, 3, x_76);
if (lean_is_scalar(x_68)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_68;
}
lean_ctor_set(x_78, 0, x_70);
x_79 = lean_array_push(x_17, x_78);
x_80 = lean_array_push(x_18, x_77);
if (lean_is_scalar(x_75)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_75;
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_4 = x_13;
x_5 = x_81;
x_7 = x_74;
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_64);
lean_dec(x_19);
lean_dec(x_16);
x_83 = lean_array_push(x_17, x_11);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_18);
x_4 = x_13;
x_5 = x_84;
x_7 = x_65;
goto _start;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_15);
x_86 = !lean_is_exclusive(x_5);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_5, 0);
x_88 = lean_array_push(x_87, x_11);
lean_ctor_set(x_5, 0, x_88);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_5, 0);
x_91 = lean_ctor_get(x_5, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_5);
x_92 = lean_array_push(x_90, x_11);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_4 = x_13;
x_5 = x_93;
goto _start;
}
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_7 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(x_1, x_2, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1(x_2, x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_3, x_9, x_4, x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_IR_reshape(x_10, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l_Lean_IR_reshape(x_10, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = l_Lean_IR_ExplicitBoxing_getVarType(x_15, x_5, x_6);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_box(7);
x_21 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_18, x_20);
x_22 = l_coeDecidableEq(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_free_object(x_16);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_10, 0);
lean_dec(x_24);
x_25 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_18, x_20, x_5, x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_box(13);
lean_inc(x_26);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_20);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_32);
lean_ctor_set(x_10, 0, x_26);
x_34 = lean_array_push(x_13, x_10);
x_35 = lean_array_push(x_14, x_33);
lean_ctor_set(x_28, 1, x_35);
lean_ctor_set(x_28, 0, x_34);
x_3 = x_12;
x_4 = x_28;
x_6 = x_31;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
x_39 = lean_box(13);
lean_inc(x_26);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_20);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_39);
lean_ctor_set(x_10, 0, x_26);
x_41 = lean_array_push(x_13, x_10);
x_42 = lean_array_push(x_14, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_3 = x_12;
x_4 = x_43;
x_6 = x_38;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_10);
x_45 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_19);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_18, x_20, x_5, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = lean_box(13);
lean_inc(x_46);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_20);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_46);
x_55 = lean_array_push(x_13, x_54);
x_56 = lean_array_push(x_14, x_53);
if (lean_is_scalar(x_51)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_51;
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_3 = x_12;
x_4 = x_57;
x_6 = x_50;
goto _start;
}
}
else
{
lean_object* x_59; 
lean_dec(x_18);
lean_dec(x_15);
x_59 = lean_array_push(x_13, x_10);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 0, x_59);
x_3 = x_12;
x_4 = x_16;
x_6 = x_19;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_16, 0);
x_62 = lean_ctor_get(x_16, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_16);
x_63 = lean_box(7);
x_64 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_61, x_63);
x_65 = l_coeDecidableEq(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_66 = x_10;
} else {
 lean_dec_ref(x_10);
 x_66 = lean_box(0);
}
x_67 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_62);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_61, x_63, x_5, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_box(13);
lean_inc(x_68);
x_75 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_63);
lean_ctor_set(x_75, 2, x_71);
lean_ctor_set(x_75, 3, x_74);
if (lean_is_scalar(x_66)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_66;
}
lean_ctor_set(x_76, 0, x_68);
x_77 = lean_array_push(x_13, x_76);
x_78 = lean_array_push(x_14, x_75);
if (lean_is_scalar(x_73)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_73;
}
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_3 = x_12;
x_4 = x_79;
x_6 = x_72;
goto _start;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_61);
lean_dec(x_15);
x_81 = lean_array_push(x_13, x_10);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_14);
x_3 = x_12;
x_4 = x_82;
x_6 = x_62;
goto _start;
}
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_4);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_4, 0);
x_86 = lean_array_push(x_85, x_10);
lean_ctor_set(x_4, 0, x_86);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_4, 0);
x_89 = lean_ctor_get(x_4, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_4);
x_90 = lean_array_push(x_88, x_10);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_3 = x_12;
x_4 = x_91;
goto _start;
}
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_6 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(x_1, x_1, x_4, x_5, x_2, x_3);
return x_6;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_3(x_2, x_8, x_3, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_IR_reshape(x_9, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l_Lean_IR_reshape(x_9, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; 
x_7 = l_Lean_IR_IRType_isScalar(x_2);
x_8 = l_coeDecidableEq(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_4);
x_16 = lean_box(7);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_15);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
lean_inc(x_18);
x_20 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_4);
x_22 = lean_box(7);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; 
x_8 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_2, x_4);
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_11);
x_13 = l_Lean_IR_ExplicitBoxing_mkCast(x_11, x_4, x_2, x_6, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_5);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_5);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 2, x_3);
lean_ctor_set(x_21, 3, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
x_14 = l_Lean_IR_paramInh;
x_15 = lean_array_get(x_14, x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
x_20 = l_Lean_IR_ExplicitBoxing_getVarType(x_19, x_6, x_7);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_22, x_16);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_free_object(x_20);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_11, 0);
lean_dec(x_27);
x_28 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_16);
x_31 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_22, x_16, x_6, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_box(13);
lean_inc(x_29);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_16);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_11, 0, x_29);
x_37 = lean_array_push(x_17, x_11);
x_38 = lean_array_push(x_18, x_36);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_37);
x_4 = x_13;
x_5 = x_31;
x_7 = x_34;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
x_42 = lean_box(13);
lean_inc(x_29);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_16);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_11, 0, x_29);
x_44 = lean_array_push(x_17, x_11);
x_45 = lean_array_push(x_18, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_4 = x_13;
x_5 = x_46;
x_7 = x_41;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_11);
x_48 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_16);
x_51 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_22, x_16, x_6, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_box(13);
lean_inc(x_49);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_16);
lean_ctor_set(x_56, 2, x_52);
lean_ctor_set(x_56, 3, x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_49);
x_58 = lean_array_push(x_17, x_57);
x_59 = lean_array_push(x_18, x_56);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_4 = x_13;
x_5 = x_60;
x_7 = x_53;
goto _start;
}
}
else
{
lean_object* x_62; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_16);
x_62 = lean_array_push(x_17, x_11);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 0, x_62);
x_4 = x_13;
x_5 = x_20;
x_7 = x_23;
goto _start;
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_20, 0);
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_20);
x_66 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_64, x_16);
x_67 = l_coeDecidableEq(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_68 = x_11;
} else {
 lean_dec_ref(x_11);
 x_68 = lean_box(0);
}
x_69 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_65);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_16);
x_72 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_64, x_16, x_6, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_box(13);
lean_inc(x_70);
x_77 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_16);
lean_ctor_set(x_77, 2, x_73);
lean_ctor_set(x_77, 3, x_76);
if (lean_is_scalar(x_68)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_68;
}
lean_ctor_set(x_78, 0, x_70);
x_79 = lean_array_push(x_17, x_78);
x_80 = lean_array_push(x_18, x_77);
if (lean_is_scalar(x_75)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_75;
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_4 = x_13;
x_5 = x_81;
x_7 = x_74;
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_64);
lean_dec(x_19);
lean_dec(x_16);
x_83 = lean_array_push(x_17, x_11);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_18);
x_4 = x_13;
x_5 = x_84;
x_7 = x_65;
goto _start;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_15);
x_86 = !lean_is_exclusive(x_5);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_5, 0);
x_88 = lean_array_push(x_87, x_11);
lean_ctor_set(x_5, 0, x_88);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_5, 0);
x_91 = lean_ctor_get(x_5, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_5);
x_92 = lean_array_push(x_90, x_11);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_4 = x_13;
x_5 = x_93;
goto _start;
}
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_7 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(x_1, x_2, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = l_Lean_IR_CtorInfo_isScalar(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_String_posOfAux___main___closed__1;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_9, x_5, x_6);
lean_dec(x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_ctor_set(x_3, 1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_3);
lean_ctor_set(x_18, 3, x_4);
x_19 = l_Lean_IR_reshape(x_17, x_18);
lean_ctor_set(x_13, 1, x_14);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
lean_ctor_set(x_3, 1, x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_4);
x_23 = l_Lean_IR_reshape(x_21, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_3);
lean_dec(x_9);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_4);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
}
else
{
uint8_t x_30; uint8_t x_31; 
x_30 = l_Lean_IR_IRType_isScalar(x_2);
x_31 = l_coeDecidableEq(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_9, x_5, x_6);
lean_dec(x_9);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 1);
lean_ctor_set(x_3, 1, x_36);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_2);
lean_ctor_set(x_38, 2, x_3);
lean_ctor_set(x_38, 3, x_4);
x_39 = l_Lean_IR_reshape(x_37, x_38);
lean_ctor_set(x_33, 1, x_34);
lean_ctor_set(x_33, 0, x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
lean_ctor_set(x_3, 1, x_40);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_2);
lean_ctor_set(x_42, 2, x_3);
lean_ctor_set(x_42, 3, x_4);
x_43 = l_Lean_IR_reshape(x_41, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_34);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_3);
lean_dec(x_9);
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
lean_dec(x_8);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_2);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_4);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_6);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_3, 0);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_3);
x_52 = l_Lean_IR_CtorInfo_isScalar(x_50);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_String_posOfAux___main___closed__1;
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_51, x_5, x_6);
lean_dec(x_51);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_59 = x_55;
} else {
 lean_dec_ref(x_55);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_57);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_2);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_4);
x_62 = l_Lean_IR_reshape(x_58, x_61);
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_51);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_dec(x_50);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_2);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_4);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_6);
return x_68;
}
}
else
{
uint8_t x_69; uint8_t x_70; 
x_69 = l_Lean_IR_IRType_isScalar(x_2);
x_70 = l_coeDecidableEq(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_71 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_51, x_5, x_6);
lean_dec(x_51);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_50);
lean_ctor_set(x_77, 1, x_74);
x_78 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_2);
lean_ctor_set(x_78, 2, x_77);
lean_ctor_set(x_78, 3, x_4);
x_79 = l_Lean_IR_reshape(x_75, x_78);
if (lean_is_scalar(x_76)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_76;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_73);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_51);
x_81 = lean_ctor_get(x_50, 1);
lean_inc(x_81);
lean_dec(x_50);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_84, 0, x_1);
lean_ctor_set(x_84, 1, x_2);
lean_ctor_set(x_84, 2, x_83);
lean_ctor_set(x_84, 3, x_4);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_6);
return x_85;
}
}
}
}
case 2:
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_3, 2);
x_88 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_87, x_5, x_6);
lean_dec(x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = !lean_is_exclusive(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_89, 0);
x_93 = lean_ctor_get(x_89, 1);
lean_ctor_set(x_3, 2, x_92);
x_94 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_94, 0, x_1);
lean_ctor_set(x_94, 1, x_2);
lean_ctor_set(x_94, 2, x_3);
lean_ctor_set(x_94, 3, x_4);
x_95 = l_Lean_IR_reshape(x_93, x_94);
lean_ctor_set(x_89, 1, x_90);
lean_ctor_set(x_89, 0, x_95);
return x_89;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_89, 0);
x_97 = lean_ctor_get(x_89, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_89);
lean_ctor_set(x_3, 2, x_96);
x_98 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_2);
lean_ctor_set(x_98, 2, x_3);
lean_ctor_set(x_98, 3, x_4);
x_99 = l_Lean_IR_reshape(x_97, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_90);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_101 = lean_ctor_get(x_3, 0);
x_102 = lean_ctor_get(x_3, 1);
x_103 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_104 = lean_ctor_get(x_3, 2);
lean_inc(x_104);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_3);
x_105 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_104, x_5, x_6);
lean_dec(x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_110 = x_106;
} else {
 lean_dec_ref(x_106);
 x_110 = lean_box(0);
}
x_111 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_111, 0, x_101);
lean_ctor_set(x_111, 1, x_102);
lean_ctor_set(x_111, 2, x_108);
lean_ctor_set_uint8(x_111, sizeof(void*)*3, x_103);
x_112 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_112, 0, x_1);
lean_ctor_set(x_112, 1, x_2);
lean_ctor_set(x_112, 2, x_111);
lean_ctor_set(x_112, 3, x_4);
x_113 = l_Lean_IR_reshape(x_109, x_112);
if (lean_is_scalar(x_110)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_110;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_107);
return x_114;
}
}
case 6:
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_3);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_116 = lean_ctor_get(x_3, 0);
x_117 = lean_ctor_get(x_3, 1);
x_118 = l_Lean_IR_ExplicitBoxing_getDecl(x_116, x_5, x_6);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = l_Lean_IR_Decl_params(x_119);
x_122 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(x_121, x_117, x_5, x_120);
lean_dec(x_117);
lean_dec(x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
lean_ctor_set(x_3, 1, x_125);
x_127 = l_Lean_IR_Decl_resultType(x_119);
lean_dec(x_119);
x_128 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_2, x_3, x_127, x_4, x_5, x_124);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = l_Lean_IR_reshape(x_126, x_130);
lean_ctor_set(x_128, 0, x_131);
return x_128;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_128, 0);
x_133 = lean_ctor_get(x_128, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_128);
x_134 = l_Lean_IR_reshape(x_126, x_132);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_136 = lean_ctor_get(x_3, 0);
x_137 = lean_ctor_get(x_3, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_3);
x_138 = l_Lean_IR_ExplicitBoxing_getDecl(x_136, x_5, x_6);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = l_Lean_IR_Decl_params(x_139);
x_142 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(x_141, x_137, x_5, x_140);
lean_dec(x_137);
lean_dec(x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_147 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_147, 0, x_136);
lean_ctor_set(x_147, 1, x_145);
x_148 = l_Lean_IR_Decl_resultType(x_139);
lean_dec(x_139);
x_149 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_2, x_147, x_148, x_4, x_5, x_144);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = l_Lean_IR_reshape(x_146, x_150);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
return x_154;
}
}
case 7:
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_3);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; uint8_t x_165; lean_object* x_166; 
x_156 = lean_ctor_get(x_3, 0);
x_157 = lean_ctor_get(x_3, 1);
x_158 = l_Lean_IR_ExplicitBoxing_getEnv(x_5, x_6);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lean_IR_ExplicitBoxing_getDecl(x_156, x_5, x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_159, x_162);
lean_dec(x_162);
lean_dec(x_159);
x_165 = l_coeDecidableEq(x_164);
x_166 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_157, x_5, x_163);
lean_dec(x_157);
if (x_165 == 0)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = !lean_is_exclusive(x_167);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_167, 0);
x_171 = lean_ctor_get(x_167, 1);
lean_ctor_set(x_3, 1, x_170);
x_172 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_172, 0, x_1);
lean_ctor_set(x_172, 1, x_2);
lean_ctor_set(x_172, 2, x_3);
lean_ctor_set(x_172, 3, x_4);
x_173 = l_Lean_IR_reshape(x_171, x_172);
lean_ctor_set(x_167, 1, x_168);
lean_ctor_set(x_167, 0, x_173);
return x_167;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_167, 0);
x_175 = lean_ctor_get(x_167, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_167);
lean_ctor_set(x_3, 1, x_174);
x_176 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_176, 0, x_1);
lean_ctor_set(x_176, 1, x_2);
lean_ctor_set(x_176, 2, x_3);
lean_ctor_set(x_176, 3, x_4);
x_177 = l_Lean_IR_reshape(x_175, x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_168);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_179 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_180 = lean_name_mk_string(x_156, x_179);
x_181 = lean_ctor_get(x_166, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_166, 1);
lean_inc(x_182);
lean_dec(x_166);
x_183 = !lean_is_exclusive(x_181);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_181, 0);
x_185 = lean_ctor_get(x_181, 1);
lean_ctor_set(x_3, 1, x_184);
lean_ctor_set(x_3, 0, x_180);
x_186 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_186, 0, x_1);
lean_ctor_set(x_186, 1, x_2);
lean_ctor_set(x_186, 2, x_3);
lean_ctor_set(x_186, 3, x_4);
x_187 = l_Lean_IR_reshape(x_185, x_186);
lean_ctor_set(x_181, 1, x_182);
lean_ctor_set(x_181, 0, x_187);
return x_181;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_188 = lean_ctor_get(x_181, 0);
x_189 = lean_ctor_get(x_181, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_181);
lean_ctor_set(x_3, 1, x_188);
lean_ctor_set(x_3, 0, x_180);
x_190 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_190, 0, x_1);
lean_ctor_set(x_190, 1, x_2);
lean_ctor_set(x_190, 2, x_3);
lean_ctor_set(x_190, 3, x_4);
x_191 = l_Lean_IR_reshape(x_189, x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_182);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; uint8_t x_202; lean_object* x_203; 
x_193 = lean_ctor_get(x_3, 0);
x_194 = lean_ctor_get(x_3, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_3);
x_195 = l_Lean_IR_ExplicitBoxing_getEnv(x_5, x_6);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = l_Lean_IR_ExplicitBoxing_getDecl(x_193, x_5, x_197);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_196, x_199);
lean_dec(x_199);
lean_dec(x_196);
x_202 = l_coeDecidableEq(x_201);
x_203 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_194, x_5, x_200);
lean_dec(x_194);
if (x_202 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_208 = x_204;
} else {
 lean_dec_ref(x_204);
 x_208 = lean_box(0);
}
x_209 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_209, 0, x_193);
lean_ctor_set(x_209, 1, x_206);
x_210 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_210, 0, x_1);
lean_ctor_set(x_210, 1, x_2);
lean_ctor_set(x_210, 2, x_209);
lean_ctor_set(x_210, 3, x_4);
x_211 = l_Lean_IR_reshape(x_207, x_210);
if (lean_is_scalar(x_208)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_208;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_205);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_213 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_214 = lean_name_mk_string(x_193, x_213);
x_215 = lean_ctor_get(x_203, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_203, 1);
lean_inc(x_216);
lean_dec(x_203);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_219 = x_215;
} else {
 lean_dec_ref(x_215);
 x_219 = lean_box(0);
}
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_214);
lean_ctor_set(x_220, 1, x_217);
x_221 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_221, 0, x_1);
lean_ctor_set(x_221, 1, x_2);
lean_ctor_set(x_221, 2, x_220);
lean_ctor_set(x_221, 3, x_4);
x_222 = l_Lean_IR_reshape(x_218, x_221);
if (lean_is_scalar(x_219)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_219;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_216);
return x_223;
}
}
}
case 8:
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_3);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_225 = lean_ctor_get(x_3, 1);
x_226 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_225, x_5, x_6);
lean_dec(x_225);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_ctor_get(x_227, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_dec(x_227);
lean_ctor_set(x_3, 1, x_229);
x_231 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_1, x_2, x_3, x_4, x_5, x_228);
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_231, 0);
x_234 = l_Lean_IR_reshape(x_230, x_233);
lean_ctor_set(x_231, 0, x_234);
return x_231;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_231, 0);
x_236 = lean_ctor_get(x_231, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_231);
x_237 = l_Lean_IR_reshape(x_230, x_235);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_239 = lean_ctor_get(x_3, 0);
x_240 = lean_ctor_get(x_3, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_3);
x_241 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_240, x_5, x_6);
lean_dec(x_240);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_ctor_get(x_242, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
lean_dec(x_242);
x_246 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_246, 0, x_239);
lean_ctor_set(x_246, 1, x_244);
x_247 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_1, x_2, x_246, x_4, x_5, x_243);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_250 = x_247;
} else {
 lean_dec_ref(x_247);
 x_250 = lean_box(0);
}
x_251 = l_Lean_IR_reshape(x_245, x_248);
if (lean_is_scalar(x_250)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_250;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_249);
return x_252;
}
}
default: 
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_253, 0, x_1);
lean_ctor_set(x_253, 1, x_2);
lean_ctor_set(x_253, 2, x_3);
lean_ctor_set(x_253, 3, x_4);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_6);
return x_254;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = l_Array_empty___closed__1;
x_8 = x_2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_2, x_1);
x_11 = lean_box(0);
x_12 = x_11;
x_13 = lean_array_fset(x_2, x_1, x_12);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_3);
x_16 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_15, x_3, x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_1, x_20);
x_22 = x_19;
lean_dec(x_10);
x_23 = lean_array_fset(x_13, x_1, x_22);
lean_dec(x_1);
x_1 = x_21;
x_2 = x_23;
x_4 = x_18;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
lean_inc(x_3);
x_26 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_25, x_3, x_4);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_1, x_30);
x_32 = x_29;
lean_dec(x_10);
x_33 = lean_array_fset(x_13, x_1, x_32);
lean_dec(x_1);
x_1 = x_31;
x_2 = x_33;
x_4 = x_28;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
x_14 = l_Lean_IR_paramInh;
x_15 = lean_array_get(x_14, x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
x_20 = l_Lean_IR_ExplicitBoxing_getVarType(x_19, x_6, x_7);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_22, x_16);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_free_object(x_20);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_11, 0);
lean_dec(x_27);
x_28 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_16);
x_31 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_22, x_16, x_6, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_box(13);
lean_inc(x_29);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_16);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_11, 0, x_29);
x_37 = lean_array_push(x_17, x_11);
x_38 = lean_array_push(x_18, x_36);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_37);
x_4 = x_13;
x_5 = x_31;
x_7 = x_34;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
x_42 = lean_box(13);
lean_inc(x_29);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_16);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_11, 0, x_29);
x_44 = lean_array_push(x_17, x_11);
x_45 = lean_array_push(x_18, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_4 = x_13;
x_5 = x_46;
x_7 = x_41;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_11);
x_48 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_16);
x_51 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_22, x_16, x_6, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_box(13);
lean_inc(x_49);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_16);
lean_ctor_set(x_56, 2, x_52);
lean_ctor_set(x_56, 3, x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_49);
x_58 = lean_array_push(x_17, x_57);
x_59 = lean_array_push(x_18, x_56);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_4 = x_13;
x_5 = x_60;
x_7 = x_53;
goto _start;
}
}
else
{
lean_object* x_62; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_16);
x_62 = lean_array_push(x_17, x_11);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 0, x_62);
x_4 = x_13;
x_5 = x_20;
x_7 = x_23;
goto _start;
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_20, 0);
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_20);
x_66 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_64, x_16);
x_67 = l_coeDecidableEq(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_68 = x_11;
} else {
 lean_dec_ref(x_11);
 x_68 = lean_box(0);
}
x_69 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_65);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_16);
x_72 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_64, x_16, x_6, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_box(13);
lean_inc(x_70);
x_77 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_16);
lean_ctor_set(x_77, 2, x_73);
lean_ctor_set(x_77, 3, x_76);
if (lean_is_scalar(x_68)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_68;
}
lean_ctor_set(x_78, 0, x_70);
x_79 = lean_array_push(x_17, x_78);
x_80 = lean_array_push(x_18, x_77);
if (lean_is_scalar(x_75)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_75;
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_4 = x_13;
x_5 = x_81;
x_7 = x_74;
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_64);
lean_dec(x_19);
lean_dec(x_16);
x_83 = lean_array_push(x_17, x_11);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_18);
x_4 = x_13;
x_5 = x_84;
x_7 = x_65;
goto _start;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_15);
x_86 = !lean_is_exclusive(x_5);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_5, 0);
x_88 = lean_array_push(x_87, x_11);
lean_ctor_set(x_5, 0, x_88);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_5, 0);
x_91 = lean_ctor_get(x_5, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_5);
x_92 = lean_array_push(x_90, x_11);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_4 = x_13;
x_5 = x_93;
goto _start;
}
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_7 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(x_1, x_2, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 4);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_IR_LocalContext_addLocal(x_9, x_4, x_5, x_6);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_14, 4, x_12);
x_15 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_7, x_14, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr(x_4, x_5, x_6, x_16, x_2, x_17);
lean_dec(x_2);
return x_18;
}
case 1:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_ctor_get(x_1, 3);
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get(x_2, 3);
x_29 = lean_ctor_get(x_2, 4);
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_26);
x_31 = l_Array_iterateMAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_22, x_22, x_30, x_26);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_ctor_set(x_2, 1, x_31);
x_32 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_23, x_2, x_3);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_33);
lean_inc(x_22);
lean_inc(x_21);
x_35 = l_Lean_IR_LocalContext_addJP(x_26, x_21, x_22, x_33);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_27);
lean_ctor_set(x_36, 3, x_28);
lean_ctor_set(x_36, 4, x_29);
x_37 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_24, x_36, x_34);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_ctor_set(x_1, 3, x_39);
lean_ctor_set(x_1, 2, x_33);
lean_ctor_set(x_37, 0, x_1);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_37);
lean_ctor_set(x_1, 3, x_40);
lean_ctor_set(x_1, 2, x_33);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
x_45 = lean_ctor_get(x_1, 2);
x_46 = lean_ctor_get(x_1, 3);
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_ctor_get(x_2, 1);
x_49 = lean_ctor_get(x_2, 2);
x_50 = lean_ctor_get(x_2, 3);
x_51 = lean_ctor_get(x_2, 4);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_2);
x_52 = lean_unsigned_to_nat(0u);
lean_inc(x_48);
x_53 = l_Array_iterateMAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_44, x_44, x_52, x_48);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_47);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_49);
lean_ctor_set(x_54, 3, x_50);
lean_ctor_set(x_54, 4, x_51);
x_55 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_45, x_54, x_3);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_56);
lean_inc(x_44);
lean_inc(x_43);
x_58 = l_Lean_IR_LocalContext_addJP(x_48, x_43, x_44, x_56);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_49);
lean_ctor_set(x_59, 3, x_50);
lean_ctor_set(x_59, 4, x_51);
x_60 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_46, x_59, x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
lean_ctor_set(x_1, 3, x_61);
lean_ctor_set(x_1, 2, x_56);
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_65 = lean_ctor_get(x_1, 0);
x_66 = lean_ctor_get(x_1, 1);
x_67 = lean_ctor_get(x_1, 2);
x_68 = lean_ctor_get(x_1, 3);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_1);
x_69 = lean_ctor_get(x_2, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_2, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_2, 4);
lean_inc(x_73);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_74 = x_2;
} else {
 lean_dec_ref(x_2);
 x_74 = lean_box(0);
}
x_75 = lean_unsigned_to_nat(0u);
lean_inc(x_70);
x_76 = l_Array_iterateMAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_66, x_66, x_75, x_70);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_69);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 5, 0);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_71);
lean_ctor_set(x_77, 3, x_72);
lean_ctor_set(x_77, 4, x_73);
x_78 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_67, x_77, x_3);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_79);
lean_inc(x_66);
lean_inc(x_65);
x_81 = l_Lean_IR_LocalContext_addJP(x_70, x_65, x_66, x_79);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_69);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_71);
lean_ctor_set(x_82, 3, x_72);
lean_ctor_set(x_82, 4, x_73);
x_83 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_68, x_82, x_80);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_87, 0, x_65);
lean_ctor_set(x_87, 1, x_66);
lean_ctor_set(x_87, 2, x_79);
lean_ctor_set(x_87, 3, x_84);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
case 4:
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_1);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_90 = lean_ctor_get(x_1, 2);
x_91 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_92 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_91, x_2, x_3);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_IR_ExplicitBoxing_getVarType(x_90, x_2, x_94);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
x_99 = lean_box(5);
x_100 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_97, x_99);
x_101 = l_coeDecidableEq(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_free_object(x_95);
x_102 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_98);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_IR_ExplicitBoxing_mkCast(x_90, x_97, x_99, x_2, x_104);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_103);
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set(x_1, 2, x_103);
x_108 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_99);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_1);
lean_ctor_set(x_105, 0, x_108);
return x_105;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_105, 0);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_105);
lean_inc(x_103);
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set(x_1, 2, x_103);
x_111 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_99);
lean_ctor_set(x_111, 2, x_109);
lean_ctor_set(x_111, 3, x_1);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_dec(x_97);
lean_dec(x_2);
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set(x_95, 0, x_1);
return x_95;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; 
x_113 = lean_ctor_get(x_95, 0);
x_114 = lean_ctor_get(x_95, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_95);
x_115 = lean_box(5);
x_116 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_113, x_115);
x_117 = l_coeDecidableEq(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_118 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_114);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = l_Lean_IR_ExplicitBoxing_mkCast(x_90, x_113, x_115, x_2, x_120);
lean_dec(x_2);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
lean_inc(x_119);
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set(x_1, 2, x_119);
x_125 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_125, 0, x_119);
lean_ctor_set(x_125, 1, x_115);
lean_ctor_set(x_125, 2, x_122);
lean_ctor_set(x_125, 3, x_1);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
return x_126;
}
else
{
lean_object* x_127; 
lean_dec(x_113);
lean_dec(x_2);
lean_ctor_set(x_1, 3, x_93);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_114);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; 
x_128 = lean_ctor_get(x_1, 0);
x_129 = lean_ctor_get(x_1, 1);
x_130 = lean_ctor_get(x_1, 2);
x_131 = lean_ctor_get(x_1, 3);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_1);
lean_inc(x_2);
x_132 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_131, x_2, x_3);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Lean_IR_ExplicitBoxing_getVarType(x_130, x_2, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_138 = x_135;
} else {
 lean_dec_ref(x_135);
 x_138 = lean_box(0);
}
x_139 = lean_box(5);
x_140 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_136, x_139);
x_141 = l_coeDecidableEq(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_138);
x_142 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_137);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = l_Lean_IR_ExplicitBoxing_mkCast(x_130, x_136, x_139, x_2, x_144);
lean_dec(x_2);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
lean_inc(x_143);
x_149 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_149, 0, x_128);
lean_ctor_set(x_149, 1, x_129);
lean_ctor_set(x_149, 2, x_143);
lean_ctor_set(x_149, 3, x_133);
x_150 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_150, 0, x_143);
lean_ctor_set(x_150, 1, x_139);
lean_ctor_set(x_150, 2, x_146);
lean_ctor_set(x_150, 3, x_149);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_147);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_136);
lean_dec(x_2);
x_152 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_152, 0, x_128);
lean_ctor_set(x_152, 1, x_129);
lean_ctor_set(x_152, 2, x_130);
lean_ctor_set(x_152, 3, x_133);
if (lean_is_scalar(x_138)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_138;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_137);
return x_153;
}
}
}
case 5:
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_1);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_155 = lean_ctor_get(x_1, 3);
x_156 = lean_ctor_get(x_1, 4);
x_157 = lean_ctor_get(x_1, 5);
lean_inc(x_2);
x_158 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_157, x_2, x_3);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lean_IR_ExplicitBoxing_getVarType(x_155, x_2, x_160);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_166; 
x_163 = lean_ctor_get(x_161, 0);
x_164 = lean_ctor_get(x_161, 1);
x_165 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_163, x_156);
x_166 = l_coeDecidableEq(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
lean_free_object(x_161);
x_167 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_164);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
lean_inc(x_156);
x_170 = l_Lean_IR_ExplicitBoxing_mkCast(x_155, x_163, x_156, x_2, x_169);
lean_dec(x_2);
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_156);
lean_inc(x_168);
lean_ctor_set(x_1, 5, x_159);
lean_ctor_set(x_1, 3, x_168);
x_173 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_156);
lean_ctor_set(x_173, 2, x_172);
lean_ctor_set(x_173, 3, x_1);
lean_ctor_set(x_170, 0, x_173);
return x_170;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_170, 0);
x_175 = lean_ctor_get(x_170, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_170);
lean_inc(x_156);
lean_inc(x_168);
lean_ctor_set(x_1, 5, x_159);
lean_ctor_set(x_1, 3, x_168);
x_176 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_156);
lean_ctor_set(x_176, 2, x_174);
lean_ctor_set(x_176, 3, x_1);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
lean_dec(x_163);
lean_dec(x_2);
lean_ctor_set(x_1, 5, x_159);
lean_ctor_set(x_161, 0, x_1);
return x_161;
}
}
else
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; uint8_t x_181; 
x_178 = lean_ctor_get(x_161, 0);
x_179 = lean_ctor_get(x_161, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_161);
x_180 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_178, x_156);
x_181 = l_coeDecidableEq(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_182 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_179);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
lean_inc(x_156);
x_185 = l_Lean_IR_ExplicitBoxing_mkCast(x_155, x_178, x_156, x_2, x_184);
lean_dec(x_2);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
lean_inc(x_156);
lean_inc(x_183);
lean_ctor_set(x_1, 5, x_159);
lean_ctor_set(x_1, 3, x_183);
x_189 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_189, 0, x_183);
lean_ctor_set(x_189, 1, x_156);
lean_ctor_set(x_189, 2, x_186);
lean_ctor_set(x_189, 3, x_1);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_187);
return x_190;
}
else
{
lean_object* x_191; 
lean_dec(x_178);
lean_dec(x_2);
lean_ctor_set(x_1, 5, x_159);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_1);
lean_ctor_set(x_191, 1, x_179);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_206; 
x_192 = lean_ctor_get(x_1, 0);
x_193 = lean_ctor_get(x_1, 1);
x_194 = lean_ctor_get(x_1, 2);
x_195 = lean_ctor_get(x_1, 3);
x_196 = lean_ctor_get(x_1, 4);
x_197 = lean_ctor_get(x_1, 5);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_1);
lean_inc(x_2);
x_198 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_197, x_2, x_3);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = l_Lean_IR_ExplicitBoxing_getVarType(x_195, x_2, x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_204 = x_201;
} else {
 lean_dec_ref(x_201);
 x_204 = lean_box(0);
}
x_205 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_202, x_196);
x_206 = l_coeDecidableEq(x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_204);
x_207 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_203);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
lean_inc(x_196);
x_210 = l_Lean_IR_ExplicitBoxing_mkCast(x_195, x_202, x_196, x_2, x_209);
lean_dec(x_2);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_213 = x_210;
} else {
 lean_dec_ref(x_210);
 x_213 = lean_box(0);
}
lean_inc(x_196);
lean_inc(x_208);
x_214 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_214, 0, x_192);
lean_ctor_set(x_214, 1, x_193);
lean_ctor_set(x_214, 2, x_194);
lean_ctor_set(x_214, 3, x_208);
lean_ctor_set(x_214, 4, x_196);
lean_ctor_set(x_214, 5, x_199);
x_215 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_215, 0, x_208);
lean_ctor_set(x_215, 1, x_196);
lean_ctor_set(x_215, 2, x_211);
lean_ctor_set(x_215, 3, x_214);
if (lean_is_scalar(x_213)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_213;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_212);
return x_216;
}
else
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_202);
lean_dec(x_2);
x_217 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_217, 0, x_192);
lean_ctor_set(x_217, 1, x_193);
lean_ctor_set(x_217, 2, x_194);
lean_ctor_set(x_217, 3, x_195);
lean_ctor_set(x_217, 4, x_196);
lean_ctor_set(x_217, 5, x_199);
if (lean_is_scalar(x_204)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_204;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_203);
return x_218;
}
}
}
case 9:
{
uint8_t x_219; 
x_219 = !lean_is_exclusive(x_1);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_220 = lean_ctor_get(x_1, 1);
x_221 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_220, x_2, x_3);
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_221, 0);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_221, 0, x_1);
return x_221;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_221, 0);
x_225 = lean_ctor_get(x_221, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_221);
lean_ctor_set(x_1, 1, x_224);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_1);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_227 = lean_ctor_get(x_1, 0);
x_228 = lean_ctor_get(x_1, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_1);
x_229 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_228, x_2, x_3);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_232 = x_229;
} else {
 lean_dec_ref(x_229);
 x_232 = lean_box(0);
}
x_233 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_233, 0, x_227);
lean_ctor_set(x_233, 1, x_230);
if (lean_is_scalar(x_232)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_232;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_231);
return x_234;
}
}
case 10:
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_1);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_236 = lean_ctor_get(x_1, 1);
x_237 = lean_ctor_get(x_1, 3);
x_238 = lean_ctor_get(x_1, 2);
lean_dec(x_238);
x_239 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_237);
x_240 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_241 = l_Array_umapMAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(x_240, x_237, x_2, x_3);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_IR_ExplicitBoxing_getVarType(x_236, x_2, x_243);
x_245 = !lean_is_exclusive(x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; uint8_t x_249; 
x_246 = lean_ctor_get(x_244, 0);
x_247 = lean_ctor_get(x_244, 1);
x_248 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_246, x_239);
x_249 = l_coeDecidableEq(x_248);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
lean_free_object(x_244);
x_250 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_247);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
lean_inc(x_239);
x_253 = l_Lean_IR_ExplicitBoxing_mkCast(x_236, x_246, x_239, x_2, x_252);
lean_dec(x_2);
x_254 = !lean_is_exclusive(x_253);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_253, 0);
lean_inc(x_239);
lean_inc(x_251);
lean_ctor_set(x_1, 3, x_242);
lean_ctor_set(x_1, 2, x_239);
lean_ctor_set(x_1, 1, x_251);
x_256 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_256, 0, x_251);
lean_ctor_set(x_256, 1, x_239);
lean_ctor_set(x_256, 2, x_255);
lean_ctor_set(x_256, 3, x_1);
lean_ctor_set(x_253, 0, x_256);
return x_253;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_257 = lean_ctor_get(x_253, 0);
x_258 = lean_ctor_get(x_253, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_253);
lean_inc(x_239);
lean_inc(x_251);
lean_ctor_set(x_1, 3, x_242);
lean_ctor_set(x_1, 2, x_239);
lean_ctor_set(x_1, 1, x_251);
x_259 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_259, 0, x_251);
lean_ctor_set(x_259, 1, x_239);
lean_ctor_set(x_259, 2, x_257);
lean_ctor_set(x_259, 3, x_1);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
else
{
lean_dec(x_246);
lean_dec(x_2);
lean_ctor_set(x_1, 3, x_242);
lean_ctor_set(x_1, 2, x_239);
lean_ctor_set(x_244, 0, x_1);
return x_244;
}
}
else
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; uint8_t x_264; 
x_261 = lean_ctor_get(x_244, 0);
x_262 = lean_ctor_get(x_244, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_244);
x_263 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_261, x_239);
x_264 = l_coeDecidableEq(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_265 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_262);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
lean_inc(x_239);
x_268 = l_Lean_IR_ExplicitBoxing_mkCast(x_236, x_261, x_239, x_2, x_267);
lean_dec(x_2);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_271 = x_268;
} else {
 lean_dec_ref(x_268);
 x_271 = lean_box(0);
}
lean_inc(x_239);
lean_inc(x_266);
lean_ctor_set(x_1, 3, x_242);
lean_ctor_set(x_1, 2, x_239);
lean_ctor_set(x_1, 1, x_266);
x_272 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_272, 0, x_266);
lean_ctor_set(x_272, 1, x_239);
lean_ctor_set(x_272, 2, x_269);
lean_ctor_set(x_272, 3, x_1);
if (lean_is_scalar(x_271)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_271;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_270);
return x_273;
}
else
{
lean_object* x_274; 
lean_dec(x_261);
lean_dec(x_2);
lean_ctor_set(x_1, 3, x_242);
lean_ctor_set(x_1, 2, x_239);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_1);
lean_ctor_set(x_274, 1, x_262);
return x_274;
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; uint8_t x_288; 
x_275 = lean_ctor_get(x_1, 0);
x_276 = lean_ctor_get(x_1, 1);
x_277 = lean_ctor_get(x_1, 3);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_1);
x_278 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_277);
x_279 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_280 = l_Array_umapMAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(x_279, x_277, x_2, x_3);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = l_Lean_IR_ExplicitBoxing_getVarType(x_276, x_2, x_282);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_286 = x_283;
} else {
 lean_dec_ref(x_283);
 x_286 = lean_box(0);
}
x_287 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_284, x_278);
x_288 = l_coeDecidableEq(x_287);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_286);
x_289 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_285);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
lean_inc(x_278);
x_292 = l_Lean_IR_ExplicitBoxing_mkCast(x_276, x_284, x_278, x_2, x_291);
lean_dec(x_2);
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_295 = x_292;
} else {
 lean_dec_ref(x_292);
 x_295 = lean_box(0);
}
lean_inc(x_278);
lean_inc(x_290);
x_296 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_296, 0, x_275);
lean_ctor_set(x_296, 1, x_290);
lean_ctor_set(x_296, 2, x_278);
lean_ctor_set(x_296, 3, x_281);
x_297 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_297, 0, x_290);
lean_ctor_set(x_297, 1, x_278);
lean_ctor_set(x_297, 2, x_293);
lean_ctor_set(x_297, 3, x_296);
if (lean_is_scalar(x_295)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_295;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_294);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; 
lean_dec(x_284);
lean_dec(x_2);
x_299 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_299, 0, x_275);
lean_ctor_set(x_299, 1, x_276);
lean_ctor_set(x_299, 2, x_278);
lean_ctor_set(x_299, 3, x_281);
if (lean_is_scalar(x_286)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_286;
}
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_285);
return x_300;
}
}
}
case 11:
{
uint8_t x_301; 
x_301 = !lean_is_exclusive(x_1);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_1, 0);
x_303 = l_Lean_IR_ExplicitBoxing_getResultType(x_2, x_3);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = !lean_is_exclusive(x_302);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_307 = lean_ctor_get(x_302, 0);
x_308 = l_Lean_IR_ExplicitBoxing_getVarType(x_307, x_2, x_305);
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; uint8_t x_312; uint8_t x_313; 
x_310 = lean_ctor_get(x_308, 0);
x_311 = lean_ctor_get(x_308, 1);
x_312 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_310, x_304);
x_313 = l_coeDecidableEq(x_312);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; 
lean_free_object(x_308);
x_314 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_311);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
lean_inc(x_304);
x_317 = l_Lean_IR_ExplicitBoxing_mkCast(x_307, x_310, x_304, x_2, x_316);
lean_dec(x_2);
x_318 = !lean_is_exclusive(x_317);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_317, 0);
lean_inc(x_315);
lean_ctor_set(x_302, 0, x_315);
x_320 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_320, 0, x_315);
lean_ctor_set(x_320, 1, x_304);
lean_ctor_set(x_320, 2, x_319);
lean_ctor_set(x_320, 3, x_1);
lean_ctor_set(x_317, 0, x_320);
return x_317;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_321 = lean_ctor_get(x_317, 0);
x_322 = lean_ctor_get(x_317, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_317);
lean_inc(x_315);
lean_ctor_set(x_302, 0, x_315);
x_323 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_323, 0, x_315);
lean_ctor_set(x_323, 1, x_304);
lean_ctor_set(x_323, 2, x_321);
lean_ctor_set(x_323, 3, x_1);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
else
{
lean_dec(x_310);
lean_dec(x_304);
lean_dec(x_2);
lean_ctor_set(x_308, 0, x_1);
return x_308;
}
}
else
{
lean_object* x_325; lean_object* x_326; uint8_t x_327; uint8_t x_328; 
x_325 = lean_ctor_get(x_308, 0);
x_326 = lean_ctor_get(x_308, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_308);
x_327 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_325, x_304);
x_328 = l_coeDecidableEq(x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_329 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_326);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
lean_inc(x_304);
x_332 = l_Lean_IR_ExplicitBoxing_mkCast(x_307, x_325, x_304, x_2, x_331);
lean_dec(x_2);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_335 = x_332;
} else {
 lean_dec_ref(x_332);
 x_335 = lean_box(0);
}
lean_inc(x_330);
lean_ctor_set(x_302, 0, x_330);
x_336 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_336, 0, x_330);
lean_ctor_set(x_336, 1, x_304);
lean_ctor_set(x_336, 2, x_333);
lean_ctor_set(x_336, 3, x_1);
if (lean_is_scalar(x_335)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_335;
}
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_334);
return x_337;
}
else
{
lean_object* x_338; 
lean_dec(x_325);
lean_dec(x_304);
lean_dec(x_2);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_1);
lean_ctor_set(x_338, 1, x_326);
return x_338;
}
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; uint8_t x_345; 
x_339 = lean_ctor_get(x_302, 0);
lean_inc(x_339);
lean_dec(x_302);
x_340 = l_Lean_IR_ExplicitBoxing_getVarType(x_339, x_2, x_305);
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
x_344 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_341, x_304);
x_345 = l_coeDecidableEq(x_344);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_343);
x_346 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_342);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
lean_inc(x_304);
x_349 = l_Lean_IR_ExplicitBoxing_mkCast(x_339, x_341, x_304, x_2, x_348);
lean_dec(x_2);
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_352 = x_349;
} else {
 lean_dec_ref(x_349);
 x_352 = lean_box(0);
}
lean_inc(x_347);
x_353 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_353, 0, x_347);
lean_ctor_set(x_1, 0, x_353);
x_354 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_354, 0, x_347);
lean_ctor_set(x_354, 1, x_304);
lean_ctor_set(x_354, 2, x_350);
lean_ctor_set(x_354, 3, x_1);
if (lean_is_scalar(x_352)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_352;
}
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_351);
return x_355;
}
else
{
lean_object* x_356; lean_object* x_357; 
lean_dec(x_341);
lean_dec(x_304);
lean_dec(x_2);
x_356 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_356, 0, x_339);
lean_ctor_set(x_1, 0, x_356);
if (lean_is_scalar(x_343)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_343;
}
lean_ctor_set(x_357, 0, x_1);
lean_ctor_set(x_357, 1, x_342);
return x_357;
}
}
}
else
{
uint8_t x_358; 
lean_dec(x_2);
x_358 = !lean_is_exclusive(x_303);
if (x_358 == 0)
{
lean_object* x_359; 
x_359 = lean_ctor_get(x_303, 0);
lean_dec(x_359);
lean_ctor_set(x_303, 0, x_1);
return x_303;
}
else
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_303, 1);
lean_inc(x_360);
lean_dec(x_303);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_1);
lean_ctor_set(x_361, 1, x_360);
return x_361;
}
}
}
else
{
lean_object* x_362; lean_object* x_363; 
x_362 = lean_ctor_get(x_1, 0);
lean_inc(x_362);
lean_dec(x_1);
x_363 = l_Lean_IR_ExplicitBoxing_getResultType(x_2, x_3);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; uint8_t x_373; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_ctor_get(x_362, 0);
lean_inc(x_366);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 x_367 = x_362;
} else {
 lean_dec_ref(x_362);
 x_367 = lean_box(0);
}
x_368 = l_Lean_IR_ExplicitBoxing_getVarType(x_366, x_2, x_365);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_371 = x_368;
} else {
 lean_dec_ref(x_368);
 x_371 = lean_box(0);
}
x_372 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_369, x_364);
x_373 = l_coeDecidableEq(x_372);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_371);
x_374 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_370);
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
lean_inc(x_364);
x_377 = l_Lean_IR_ExplicitBoxing_mkCast(x_366, x_369, x_364, x_2, x_376);
lean_dec(x_2);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_380 = x_377;
} else {
 lean_dec_ref(x_377);
 x_380 = lean_box(0);
}
lean_inc(x_375);
if (lean_is_scalar(x_367)) {
 x_381 = lean_alloc_ctor(0, 1, 0);
} else {
 x_381 = x_367;
}
lean_ctor_set(x_381, 0, x_375);
x_382 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_382, 0, x_381);
x_383 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_383, 0, x_375);
lean_ctor_set(x_383, 1, x_364);
lean_ctor_set(x_383, 2, x_378);
lean_ctor_set(x_383, 3, x_382);
if (lean_is_scalar(x_380)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_380;
}
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_379);
return x_384;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_369);
lean_dec(x_364);
lean_dec(x_2);
if (lean_is_scalar(x_367)) {
 x_385 = lean_alloc_ctor(0, 1, 0);
} else {
 x_385 = x_367;
}
lean_ctor_set(x_385, 0, x_366);
x_386 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_386, 0, x_385);
if (lean_is_scalar(x_371)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_371;
}
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_370);
return x_387;
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_2);
x_388 = lean_ctor_get(x_363, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_389 = x_363;
} else {
 lean_dec_ref(x_363);
 x_389 = lean_box(0);
}
x_390 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_390, 0, x_362);
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_388);
return x_391;
}
}
}
case 12:
{
uint8_t x_392; 
x_392 = !lean_is_exclusive(x_1);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; 
x_393 = lean_ctor_get(x_1, 0);
x_394 = lean_ctor_get(x_1, 1);
x_395 = l_Lean_IR_ExplicitBoxing_getJPParams(x_393, x_2, x_3);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(x_396, x_394, x_2, x_397);
lean_dec(x_2);
lean_dec(x_394);
lean_dec(x_396);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = !lean_is_exclusive(x_399);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_399, 0);
x_403 = lean_ctor_get(x_399, 1);
lean_ctor_set(x_1, 1, x_402);
x_404 = l_Lean_IR_reshape(x_403, x_1);
lean_ctor_set(x_399, 1, x_400);
lean_ctor_set(x_399, 0, x_404);
return x_399;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_405 = lean_ctor_get(x_399, 0);
x_406 = lean_ctor_get(x_399, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_399);
lean_ctor_set(x_1, 1, x_405);
x_407 = l_Lean_IR_reshape(x_406, x_1);
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_400);
return x_408;
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_409 = lean_ctor_get(x_1, 0);
x_410 = lean_ctor_get(x_1, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_1);
x_411 = l_Lean_IR_ExplicitBoxing_getJPParams(x_409, x_2, x_3);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(x_412, x_410, x_2, x_413);
lean_dec(x_2);
lean_dec(x_410);
lean_dec(x_412);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = lean_ctor_get(x_415, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_415, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_419 = x_415;
} else {
 lean_dec_ref(x_415);
 x_419 = lean_box(0);
}
x_420 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_420, 0, x_409);
lean_ctor_set(x_420, 1, x_417);
x_421 = l_Lean_IR_reshape(x_418, x_420);
if (lean_is_scalar(x_419)) {
 x_422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_422 = x_419;
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_416);
return x_422;
}
}
default: 
{
lean_object* x_423; 
lean_dec(x_2);
x_423 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_423, 0, x_1);
lean_ctor_set(x_423, 1, x_3);
return x_423;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_5, x_6);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 3);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_18 = l_Lean_IR_MaxIndex_collectDecl(x_10, x_17);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_10, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_10, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_10, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_10, 0);
lean_dec(x_23);
x_24 = lean_nat_add(x_18, x_11);
lean_dec(x_18);
x_25 = lean_box(0);
lean_inc(x_4);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_25);
lean_ctor_set(x_26, 3, x_11);
lean_inc(x_3);
x_27 = l_Array_iterateMAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_14, x_14, x_17, x_3);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_15);
lean_inc(x_13);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_15);
lean_ctor_set(x_28, 3, x_2);
lean_ctor_set(x_28, 4, x_1);
x_29 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_16, x_28, x_26);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_32, x_32, x_17, x_7);
lean_dec(x_32);
lean_ctor_set(x_10, 3, x_30);
x_34 = l_Lean_IR_Decl_elimDead(x_10);
x_35 = lean_array_push(x_33, x_34);
x_6 = x_12;
x_7 = x_35;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
x_37 = lean_nat_add(x_18, x_11);
lean_dec(x_18);
x_38 = lean_box(0);
lean_inc(x_4);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_4);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set(x_39, 3, x_11);
lean_inc(x_3);
x_40 = l_Array_iterateMAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_14, x_14, x_17, x_3);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_15);
lean_inc(x_13);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_13);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_15);
lean_ctor_set(x_41, 3, x_2);
lean_ctor_set(x_41, 4, x_1);
x_42 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_16, x_41, x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_45, x_45, x_17, x_7);
lean_dec(x_45);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_13);
lean_ctor_set(x_47, 1, x_14);
lean_ctor_set(x_47, 2, x_15);
lean_ctor_set(x_47, 3, x_43);
x_48 = l_Lean_IR_Decl_elimDead(x_47);
x_49 = lean_array_push(x_46, x_48);
x_6 = x_12;
x_7 = x_49;
goto _start;
}
}
else
{
lean_object* x_51; 
x_51 = lean_array_push(x_7, x_10);
x_6 = x_12;
x_7 = x_51;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_box(0);
x_4 = l_Array_empty___closed__1;
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1(x_1, x_2, x_3, x_4, x_2, x_5, x_4);
lean_dec(x_2);
x_7 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Lean_IR_explicitBoxing(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_getEnv___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_IR_ExplicitBoxing_run(x_6, x_1);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_Lean_IR_ExplicitBoxing_run(x_8, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
lean_object* l_Lean_IR_explicitBoxing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_explicitBoxing(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Control_EState(lean_object*);
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Data_AssocList(lean_object*);
lean_object* initialize_Init_Data_Nat(lean_object*);
lean_object* initialize_Init_Lean_Runtime(lean_object*);
lean_object* initialize_Init_Lean_Compiler_ClosedTermCache(lean_object*);
lean_object* initialize_Init_Lean_Compiler_ExternAttr(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_Basic(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_CompilerM(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_FreeVars(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_ElimDeadVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_Boxing(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_EState(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_AssocList(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Runtime(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_ClosedTermCache(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_ExternAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_CompilerM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_FreeVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_ElimDeadVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1);
l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1);
l_Lean_IR_ExplicitBoxing_mkCast___closed__1 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__1);
l_Lean_IR_ExplicitBoxing_mkCast___closed__2 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__2();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__2);
l_Lean_IR_ExplicitBoxing_mkCast___closed__3 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__3();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__3);
l_Lean_IR_ExplicitBoxing_mkCast___closed__4 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__4();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__4);
l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1 = _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1);
l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__2 = _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__2();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
