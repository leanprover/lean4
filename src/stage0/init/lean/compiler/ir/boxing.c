// Lean compiler output
// Module: init.lean.compiler.ir.boxing
// Imports: init.data.assoclist init.control.estate init.control.reader init.lean.runtime init.lean.compiler.closedtermcache init.lean.compiler.externattr init.lean.compiler.ir.basic init.lean.compiler.ir.compilerm init.lean.compiler.ir.freevars init.lean.compiler.ir.elimdead
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
lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_eqvTypes___boxed(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_beq(uint8_t, uint8_t);
lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getResultType(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withJDecl(lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_explicitBoxing___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_IR_ExplicitBoxing_mkCast___spec__1(lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_boxing_2__isExpensiveConstantValueBoxing___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mfoldAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mfoldAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getScrutineeType___boxed(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__2;
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
uint8_t l_Lean_IR_ExplicitBoxing_isBoxedName(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_run(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion___boxed(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withParams___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions___boxed(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_Decl_resultType(lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withVDecl(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castVarIfNeeded(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkFresh___boxed(lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getResultType___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkFresh___rarg(lean_object*);
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
uint8_t l_Lean_IR_ExplicitBoxing_eqvTypes(uint8_t, uint8_t);
lean_object* l_Array_fget(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getVarType(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__1;
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withVDecl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_paramInh;
lean_object* l_Array_push(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withJDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getJPParams___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext(lean_object*, lean_object*);
extern lean_object* l_Lean_closureMaxArgs;
lean_object* l_Lean_IR_ExplicitBoxing_isBoxedName___boxed(lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkFresh(lean_object*);
uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_beq(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_size(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castVarIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_fset(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getEnv(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(uint8_t);
lean_object* l_Lean_IR_ExplicitBoxing_getVarType___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Decl_Inhabited___closed__1;
lean_object* l_Lean_IR_ExplicitBoxing_getDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getJPParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions(lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_boxing_2__isExpensiveConstantValueBoxing(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_boxing_1__mkFresh(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getEnv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_object* l_Array_miterateAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_ExplicitBoxing_getScrutineeType(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getValue(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withParams(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_explicitBoxing(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withVDecl___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkCast(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withParams___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_init_lean_compiler_ir_boxing_1__mkFresh(lean_object* x_1) {
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
uint8_t l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*1 + 1);
x_9 = l_Lean_IR_IRType_isScalar(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_3);
return x_10;
}
}
else
{
lean_dec(x_7);
if (x_1 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
x_3 = x_15;
goto _start;
}
else
{
lean_dec(x_3);
return x_1;
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
uint8_t x_9; uint8_t x_10; 
x_9 = l_Lean_IR_Decl_resultType(x_2);
x_10 = l_Lean_IR_IRType_isScalar(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(x_6, x_3, x_5);
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
lean_object* l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(x_4, x_2, x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
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
lean_object* l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_box(0);
lean_inc(x_9);
x_11 = x_10;
x_12 = lean_array_fset(x_2, x_1, x_11);
x_13 = l___private_init_lean_compiler_ir_boxing_1__mkFresh(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = 7;
x_18 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 1, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_1, x_19);
x_21 = x_18;
x_22 = lean_array_fset(x_12, x_1, x_21);
lean_dec(x_1);
x_1 = x_20;
x_2 = x_22;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Nat_mfoldAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_16 = l_Lean_IR_paramInh;
x_17 = lean_array_get(x_16, x_1, x_12);
x_18 = lean_array_get(x_16, x_2, x_12);
lean_dec(x_12);
x_19 = lean_ctor_get_uint8(x_17, sizeof(void*)*1 + 1);
lean_dec(x_17);
x_20 = l_Lean_IR_IRType_isScalar(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_array_push(x_15, x_22);
lean_ctor_set(x_5, 1, x_23);
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_free_object(x_5);
x_25 = l___private_init_lean_compiler_ir_boxing_1__mkFresh(x_6);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_box(13);
lean_inc(x_27);
x_32 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_19);
x_33 = lean_array_push(x_14, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_27);
x_35 = lean_array_push(x_15, x_34);
lean_ctor_set(x_25, 1, x_35);
lean_ctor_set(x_25, 0, x_33);
x_4 = x_10;
x_5 = x_25;
x_6 = x_28;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
x_39 = lean_ctor_get(x_18, 0);
lean_inc(x_39);
lean_dec(x_18);
x_40 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_box(13);
lean_inc(x_37);
x_42 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*3, x_19);
x_43 = lean_array_push(x_14, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_37);
x_45 = lean_array_push(x_15, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_4 = x_10;
x_5 = x_46;
x_6 = x_38;
goto _start;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; 
x_48 = lean_ctor_get(x_5, 0);
x_49 = lean_ctor_get(x_5, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_5);
x_50 = l_Lean_IR_paramInh;
x_51 = lean_array_get(x_50, x_1, x_12);
x_52 = lean_array_get(x_50, x_2, x_12);
lean_dec(x_12);
x_53 = lean_ctor_get_uint8(x_51, sizeof(void*)*1 + 1);
lean_dec(x_51);
x_54 = l_Lean_IR_IRType_isScalar(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_array_push(x_49, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_57);
x_4 = x_10;
x_5 = x_58;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_60 = l___private_init_lean_compiler_ir_boxing_1__mkFresh(x_6);
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
x_64 = lean_ctor_get(x_52, 0);
lean_inc(x_64);
lean_dec(x_52);
x_65 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_box(13);
lean_inc(x_61);
x_67 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*3, x_53);
x_68 = lean_array_push(x_48, x_67);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_61);
x_70 = lean_array_push(x_49, x_69);
if (lean_is_scalar(x_63)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_63;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_4 = x_10;
x_5 = x_71;
x_6 = x_62;
goto _start;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_4);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_5);
lean_ctor_set(x_73, 1, x_6);
return x_73;
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
x_5 = l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1(x_4, x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_array_get_size(x_6);
x_9 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
lean_inc(x_8);
x_10 = l_Nat_mfoldAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(x_3, x_6, x_8, x_8, x_9, x_7);
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
x_15 = l___private_init_lean_compiler_ir_boxing_1__mkFresh(x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_IR_Decl_resultType(x_1);
x_20 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_20);
x_21 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
x_22 = lean_box(13);
lean_inc(x_17);
x_23 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_19);
x_24 = lean_array_push(x_13, x_23);
x_25 = l_Lean_IR_IRType_isScalar(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_17);
x_27 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_IR_reshape(x_24, x_27);
x_29 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_30 = lean_name_mk_string(x_20, x_29);
x_31 = 7;
x_32 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_6);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_31);
lean_ctor_set(x_15, 0, x_32);
return x_15;
}
else
{
lean_object* x_33; uint8_t x_34; 
lean_free_object(x_15);
x_33 = l___private_init_lean_compiler_ir_boxing_1__mkFresh(x_18);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_alloc_ctor(9, 1, 1);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_19);
x_37 = 7;
lean_inc(x_35);
x_38 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_22);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_37);
x_39 = lean_array_push(x_24, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_41 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lean_IR_reshape(x_39, x_41);
x_43 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_44 = lean_name_mk_string(x_20, x_43);
x_45 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_6);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_37);
lean_ctor_set(x_33, 0, x_45);
return x_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_46 = lean_ctor_get(x_33, 0);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_33);
x_48 = lean_alloc_ctor(9, 1, 1);
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_19);
x_49 = 7;
lean_inc(x_46);
x_50 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_50, 2, x_22);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_49);
x_51 = lean_array_push(x_24, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_46);
x_53 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_IR_reshape(x_51, x_53);
x_55 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_56 = lean_name_mk_string(x_20, x_55);
x_57 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_6);
lean_ctor_set(x_57, 2, x_54);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_49);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_47);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_59 = lean_ctor_get(x_15, 0);
x_60 = lean_ctor_get(x_15, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_15);
x_61 = l_Lean_IR_Decl_resultType(x_1);
x_62 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_62);
x_63 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_14);
x_64 = lean_box(13);
lean_inc(x_59);
x_65 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*3, x_61);
x_66 = lean_array_push(x_13, x_65);
x_67 = l_Lean_IR_IRType_isScalar(x_61);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_59);
x_69 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Lean_IR_reshape(x_66, x_69);
x_71 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_72 = lean_name_mk_string(x_62, x_71);
x_73 = 7;
x_74 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_6);
lean_ctor_set(x_74, 2, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*3, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_60);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_76 = l___private_init_lean_compiler_ir_boxing_1__mkFresh(x_60);
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
x_80 = lean_alloc_ctor(9, 1, 1);
lean_ctor_set(x_80, 0, x_59);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_61);
x_81 = 7;
lean_inc(x_77);
x_82 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_64);
lean_ctor_set_uint8(x_82, sizeof(void*)*3, x_81);
x_83 = lean_array_push(x_66, x_82);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_77);
x_85 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = l_Lean_IR_reshape(x_83, x_85);
x_87 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_88 = lean_name_mk_string(x_62, x_87);
x_89 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_6);
lean_ctor_set(x_89, 2, x_86);
lean_ctor_set_uint8(x_89, sizeof(void*)*3, x_81);
if (lean_is_scalar(x_79)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_79;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_78);
return x_90;
}
}
}
}
lean_object* l_Nat_mfoldAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_mfoldAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
if (x_9 == 0)
{
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_8);
lean_dec(x_8);
x_14 = lean_array_push(x_5, x_13);
x_4 = x_11;
x_5 = x_14;
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
x_5 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(x_1, x_2, x_2, x_3, x_4);
x_6 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_5, x_5, x_3, x_2);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(x_1, x_2, x_3, x_4, x_5);
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
uint8_t l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_array_fget(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_IR_CtorInfo_isScalar(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_2 = x_11;
goto _start;
}
}
else
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_2);
x_13 = 1;
return x_13;
}
}
}
}
uint8_t l_Lean_IR_ExplicitBoxing_getScrutineeType(lean_object* x_1) {
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
x_20 = l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(x_1, x_19);
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
uint8_t x_6; 
lean_dec(x_2);
x_6 = 7;
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
uint8_t x_13; 
x_13 = 7;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 3;
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = 2;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = 1;
return x_16;
}
}
}
}
}
lean_object* l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_getScrutineeType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_IR_ExplicitBoxing_eqvTypes(uint8_t x_1, uint8_t x_2) {
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
x_7 = l_Lean_IR_IRType_beq(x_1, x_2);
return x_7;
}
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_eqvTypes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
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
x_3 = lean_ctor_get(x_1, 3);
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
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
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
uint8_t x_8; lean_object* x_9; 
x_8 = 7;
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = l_Lean_IR_LocalContext_getType(x_11, x_1);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 7;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
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
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 2);
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
x_8 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_1, x_1, x_7, x_6);
lean_ctor_set(x_3, 1, x_8);
x_9 = lean_apply_2(x_2, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*4);
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_ctor_get(x_3, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_1, x_1, x_15, x_11);
x_17 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*4, x_12);
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
lean_object* l_Lean_IR_ExplicitBoxing_withVDecl___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*4);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_16 = l_Lean_IR_LocalContext_addLocal(x_12, x_1, x_2, x_3);
x_17 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*4, x_13);
x_18 = lean_apply_2(x_4, x_17, x_6);
return x_18;
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_withVDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_withVDecl___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_withVDecl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_IR_ExplicitBoxing_withVDecl___rarg(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
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
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*4);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_16 = l_Lean_IR_LocalContext_addJP(x_12, x_1, x_2, x_3);
x_17 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*4, x_13);
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
lean_object* l___private_init_lean_compiler_ir_boxing_2__isExpensiveConstantValueBoxing(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_IR_IRType_isScalar(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_box(x_2);
switch (lean_obj_tag(x_8)) {
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
default: 
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_8);
x_13 = l_Lean_IR_ExplicitBoxing_getLocalContext(x_3, x_4);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_IR_LocalContext_getValue(x_15, x_1);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
switch (lean_obj_tag(x_17)) {
case 6:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_array_get_size(x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_16);
x_22 = lean_box(0);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
}
case 11:
{
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
default: 
{
lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_16);
x_23 = lean_box(0);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = l_Lean_IR_LocalContext_getValue(x_24, x_1);
lean_dec(x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
switch (lean_obj_tag(x_28)) {
case 6:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_array_get_size(x_29);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_26);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_25);
return x_35;
}
}
case 11:
{
lean_object* x_36; 
lean_dec(x_28);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_25);
return x_36;
}
default: 
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_28);
lean_dec(x_26);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_25);
return x_38;
}
}
}
}
}
}
}
}
}
lean_object* l___private_init_lean_compiler_ir_boxing_2__isExpensiveConstantValueBoxing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_init_lean_compiler_ir_boxing_2__isExpensiveConstantValueBoxing(x_1, x_5, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
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
lean_object* l_Lean_IR_ExplicitBoxing_mkCast(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_init_lean_compiler_ir_boxing_2__isExpensiveConstantValueBoxing(x_1, x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = l_Lean_IR_IRType_isScalar(x_2);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(9, 1, 1);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_2);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_Lean_IR_IRType_isScalar(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(9, 1, 1);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_6, 1);
x_21 = lean_ctor_get(x_6, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_alloc_ctor(9, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_2);
x_25 = lean_unsigned_to_nat(2u);
x_26 = l_Lean_IR_ExplicitBoxing_mkCast___closed__2;
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_3);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_2);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_20, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_20, 3);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_28);
x_33 = l_AssocList_find___main___at_Lean_IR_ExplicitBoxing_mkCast___spec__1(x_28, x_31);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = lean_ctor_get(x_20, 3);
lean_dec(x_35);
x_36 = lean_ctor_get(x_20, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_20, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_20, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_4, 0);
x_40 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_32);
x_41 = l_Lean_Name_appendIndexAfter(x_40, x_32);
x_42 = l_Lean_Name_append___main(x_39, x_41);
x_43 = l_Array_empty___closed__1;
lean_inc(x_42);
x_44 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_28);
x_45 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_28);
lean_ctor_set_uint8(x_45, sizeof(void*)*3, x_3);
x_46 = lean_array_push(x_30, x_45);
lean_inc(x_44);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_28);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_31);
x_48 = lean_nat_add(x_32, x_23);
lean_dec(x_32);
lean_ctor_set(x_20, 3, x_48);
lean_ctor_set(x_20, 2, x_47);
lean_ctor_set(x_20, 1, x_46);
lean_ctor_set(x_6, 0, x_44);
return x_6;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_20);
x_49 = lean_ctor_get(x_4, 0);
x_50 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_32);
x_51 = l_Lean_Name_appendIndexAfter(x_50, x_32);
x_52 = l_Lean_Name_append___main(x_49, x_51);
x_53 = l_Array_empty___closed__1;
lean_inc(x_52);
x_54 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_inc(x_28);
x_55 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_28);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_3);
x_56 = lean_array_push(x_30, x_55);
lean_inc(x_54);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_28);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_31);
x_58 = lean_nat_add(x_32, x_23);
lean_dec(x_32);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_29);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_57);
lean_ctor_set(x_59, 3, x_58);
lean_ctor_set(x_6, 1, x_59);
lean_ctor_set(x_6, 0, x_54);
return x_6;
}
}
else
{
lean_object* x_60; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
x_60 = lean_ctor_get(x_33, 0);
lean_inc(x_60);
lean_dec(x_33);
lean_ctor_set(x_6, 0, x_60);
return x_6;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
lean_dec(x_6);
x_62 = lean_ctor_get(x_7, 0);
lean_inc(x_62);
lean_dec(x_7);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_alloc_ctor(9, 1, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_2);
x_65 = lean_unsigned_to_nat(2u);
x_66 = l_Lean_IR_ExplicitBoxing_mkCast___closed__2;
x_67 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*3, x_3);
x_68 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_62);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*3, x_2);
x_69 = lean_ctor_get(x_61, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_61, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_61, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_68);
x_73 = l_AssocList_find___main___at_Lean_IR_ExplicitBoxing_mkCast___spec__1(x_68, x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 lean_ctor_release(x_61, 3);
 x_74 = x_61;
} else {
 lean_dec_ref(x_61);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_4, 0);
x_76 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_72);
x_77 = l_Lean_Name_appendIndexAfter(x_76, x_72);
x_78 = l_Lean_Name_append___main(x_75, x_77);
x_79 = l_Array_empty___closed__1;
lean_inc(x_78);
x_80 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
lean_inc(x_68);
x_81 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set(x_81, 2, x_68);
lean_ctor_set_uint8(x_81, sizeof(void*)*3, x_3);
x_82 = lean_array_push(x_70, x_81);
lean_inc(x_80);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_68);
lean_ctor_set(x_83, 1, x_80);
lean_ctor_set(x_83, 2, x_71);
x_84 = lean_nat_add(x_72, x_63);
lean_dec(x_72);
if (lean_is_scalar(x_74)) {
 x_85 = lean_alloc_ctor(0, 4, 0);
} else {
 x_85 = x_74;
}
lean_ctor_set(x_85, 0, x_69);
lean_ctor_set(x_85, 1, x_82);
lean_ctor_set(x_85, 2, x_83);
lean_ctor_set(x_85, 3, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
x_87 = lean_ctor_get(x_73, 0);
lean_inc(x_87);
lean_dec(x_73);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_61);
return x_88;
}
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_mkCast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_IR_ExplicitBoxing_mkCast(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castVarIfNeeded(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_6 = l_Lean_IR_ExplicitBoxing_getVarType(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = l_Lean_IR_ExplicitBoxing_mkCast(x_1, x_14, x_2, x_4, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_12);
x_18 = lean_apply_3(x_3, x_12, x_4, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_2);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec(x_7);
x_26 = lean_apply_3(x_3, x_1, x_4, x_8);
return x_26;
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castVarIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_IR_ExplicitBoxing_castVarIfNeeded(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = lean_unbox(x_9);
x_12 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_11, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unbox(x_9);
lean_dec(x_9);
x_17 = l_Lean_IR_ExplicitBoxing_mkCast(x_7, x_16, x_2, x_4, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_14);
lean_ctor_set(x_1, 0, x_14);
x_20 = lean_apply_3(x_3, x_1, x_4, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_2);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_9);
x_28 = lean_apply_3(x_3, x_1, x_4, x_10);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Lean_IR_ExplicitBoxing_getVarType(x_29, x_4, x_5);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unbox(x_31);
x_34 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_33, x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_32);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_unbox(x_31);
lean_dec(x_31);
x_39 = l_Lean_IR_ExplicitBoxing_mkCast(x_29, x_38, x_2, x_4, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_36);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_36);
x_43 = lean_apply_3(x_3, x_42, x_4, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_40);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_2);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_31);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_29);
x_50 = lean_apply_3(x_3, x_49, x_4, x_32);
return x_50;
}
}
}
else
{
lean_object* x_51; 
x_51 = lean_apply_3(x_3, x_1, x_4, x_5);
return x_51;
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_IR_ExplicitBoxing_castArgIfNeeded(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_4);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
x_19 = l_Lean_IR_ExplicitBoxing_getVarType(x_18, x_6, x_7);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_unbox(x_21);
x_24 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_23, x_15);
if (x_24 == 0)
{
uint8_t x_25; 
lean_free_object(x_19);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_11, 0);
lean_dec(x_26);
x_27 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unbox(x_21);
lean_dec(x_21);
x_31 = l_Lean_IR_ExplicitBoxing_mkCast(x_18, x_30, x_15, x_6, x_29);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_box(13);
lean_inc(x_28);
x_36 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_15);
lean_ctor_set(x_11, 0, x_28);
x_37 = lean_array_push(x_16, x_11);
x_38 = lean_array_push(x_17, x_36);
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
lean_inc(x_28);
x_43 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_15);
lean_ctor_set(x_11, 0, x_28);
x_44 = lean_array_push(x_16, x_11);
x_45 = lean_array_push(x_17, x_43);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_11);
x_48 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_22);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unbox(x_21);
lean_dec(x_21);
x_52 = l_Lean_IR_ExplicitBoxing_mkCast(x_18, x_51, x_15, x_6, x_50);
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
x_56 = lean_box(13);
lean_inc(x_49);
x_57 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_15);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_49);
x_59 = lean_array_push(x_16, x_58);
x_60 = lean_array_push(x_17, x_57);
if (lean_is_scalar(x_55)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_55;
}
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_4 = x_13;
x_5 = x_61;
x_7 = x_54;
goto _start;
}
}
else
{
lean_object* x_63; 
lean_dec(x_21);
lean_dec(x_18);
x_63 = lean_array_push(x_16, x_11);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 0, x_63);
x_4 = x_13;
x_5 = x_19;
x_7 = x_22;
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_19, 0);
x_66 = lean_ctor_get(x_19, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_19);
x_67 = lean_unbox(x_65);
x_68 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_67, x_15);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_69 = x_11;
} else {
 lean_dec_ref(x_11);
 x_69 = lean_box(0);
}
x_70 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_66);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_unbox(x_65);
lean_dec(x_65);
x_74 = l_Lean_IR_ExplicitBoxing_mkCast(x_18, x_73, x_15, x_6, x_72);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = lean_box(13);
lean_inc(x_71);
x_79 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_79, 0, x_71);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*3, x_15);
if (lean_is_scalar(x_69)) {
 x_80 = lean_alloc_ctor(0, 1, 0);
} else {
 x_80 = x_69;
}
lean_ctor_set(x_80, 0, x_71);
x_81 = lean_array_push(x_16, x_80);
x_82 = lean_array_push(x_17, x_79);
if (lean_is_scalar(x_77)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_77;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_4 = x_13;
x_5 = x_83;
x_7 = x_76;
goto _start;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_65);
lean_dec(x_18);
x_85 = lean_array_push(x_16, x_11);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_17);
x_4 = x_13;
x_5 = x_86;
x_7 = x_66;
goto _start;
}
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_5);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_5, 0);
x_90 = lean_array_push(x_89, x_11);
lean_ctor_set(x_5, 0, x_90);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_94 = lean_array_push(x_92, x_11);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_4 = x_13;
x_5 = x_95;
goto _start;
}
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_7 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(x_1, x_2, x_1, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
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
x_24 = lean_unbox(x_22);
x_25 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_24, x_16);
if (x_25 == 0)
{
uint8_t x_26; 
lean_free_object(x_20);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_11, 0);
lean_dec(x_27);
x_28 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unbox(x_22);
lean_dec(x_22);
x_32 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_31, x_16, x_6, x_30);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_box(13);
lean_inc(x_29);
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_16);
lean_ctor_set(x_11, 0, x_29);
x_38 = lean_array_push(x_17, x_11);
x_39 = lean_array_push(x_18, x_37);
lean_ctor_set(x_32, 1, x_39);
lean_ctor_set(x_32, 0, x_38);
x_4 = x_13;
x_5 = x_32;
x_7 = x_35;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_box(13);
lean_inc(x_29);
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_16);
lean_ctor_set(x_11, 0, x_29);
x_45 = lean_array_push(x_17, x_11);
x_46 = lean_array_push(x_18, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_4 = x_13;
x_5 = x_47;
x_7 = x_42;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_11);
x_49 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unbox(x_22);
lean_dec(x_22);
x_53 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_52, x_16, x_6, x_51);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_box(13);
lean_inc(x_50);
x_58 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_16);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_50);
x_60 = lean_array_push(x_17, x_59);
x_61 = lean_array_push(x_18, x_58);
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_56;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_4 = x_13;
x_5 = x_62;
x_7 = x_55;
goto _start;
}
}
else
{
lean_object* x_64; 
lean_dec(x_22);
lean_dec(x_19);
x_64 = lean_array_push(x_17, x_11);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 0, x_64);
x_4 = x_13;
x_5 = x_20;
x_7 = x_23;
goto _start;
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_20, 0);
x_67 = lean_ctor_get(x_20, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_20);
x_68 = lean_unbox(x_66);
x_69 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_68, x_16);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_70 = x_11;
} else {
 lean_dec_ref(x_11);
 x_70 = lean_box(0);
}
x_71 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_67);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unbox(x_66);
lean_dec(x_66);
x_75 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_74, x_16, x_6, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_box(13);
lean_inc(x_72);
x_80 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*3, x_16);
if (lean_is_scalar(x_70)) {
 x_81 = lean_alloc_ctor(0, 1, 0);
} else {
 x_81 = x_70;
}
lean_ctor_set(x_81, 0, x_72);
x_82 = lean_array_push(x_17, x_81);
x_83 = lean_array_push(x_18, x_80);
if (lean_is_scalar(x_78)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_78;
}
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_4 = x_13;
x_5 = x_84;
x_7 = x_77;
goto _start;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_66);
lean_dec(x_19);
x_86 = lean_array_push(x_17, x_11);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_18);
x_4 = x_13;
x_5 = x_87;
x_7 = x_67;
goto _start;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_15);
x_89 = !lean_is_exclusive(x_5);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_5, 0);
x_91 = lean_array_push(x_90, x_11);
lean_ctor_set(x_5, 0, x_91);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_95 = lean_array_push(x_93, x_11);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_4 = x_13;
x_5 = x_96;
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
x_7 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(x_1, x_2, x_2, x_5, x_6, x_3, x_4);
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
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = 7;
x_21 = lean_unbox(x_18);
x_22 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_21, x_20);
if (x_22 == 0)
{
uint8_t x_23; 
lean_free_object(x_16);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_10, 0);
lean_dec(x_24);
x_25 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unbox(x_18);
lean_dec(x_18);
x_29 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_28, x_20, x_5, x_27);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_box(13);
lean_inc(x_26);
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_20);
lean_ctor_set(x_10, 0, x_26);
x_35 = lean_array_push(x_13, x_10);
x_36 = lean_array_push(x_14, x_34);
lean_ctor_set(x_29, 1, x_36);
lean_ctor_set(x_29, 0, x_35);
x_3 = x_12;
x_4 = x_29;
x_6 = x_32;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_40 = lean_box(13);
lean_inc(x_26);
x_41 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_20);
lean_ctor_set(x_10, 0, x_26);
x_42 = lean_array_push(x_13, x_10);
x_43 = lean_array_push(x_14, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_3 = x_12;
x_4 = x_44;
x_6 = x_39;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_10);
x_46 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_19);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unbox(x_18);
lean_dec(x_18);
x_50 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_49, x_20, x_5, x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_box(13);
lean_inc(x_47);
x_55 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_20);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_47);
x_57 = lean_array_push(x_13, x_56);
x_58 = lean_array_push(x_14, x_55);
if (lean_is_scalar(x_53)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_53;
}
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_3 = x_12;
x_4 = x_59;
x_6 = x_52;
goto _start;
}
}
else
{
lean_object* x_61; 
lean_dec(x_18);
lean_dec(x_15);
x_61 = lean_array_push(x_13, x_10);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 0, x_61);
x_3 = x_12;
x_4 = x_16;
x_6 = x_19;
goto _start;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_16, 0);
x_64 = lean_ctor_get(x_16, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_16);
x_65 = 7;
x_66 = lean_unbox(x_63);
x_67 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_66, x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_68 = x_10;
} else {
 lean_dec_ref(x_10);
 x_68 = lean_box(0);
}
x_69 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_64);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_unbox(x_63);
lean_dec(x_63);
x_73 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_72, x_65, x_5, x_71);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
x_77 = lean_box(13);
lean_inc(x_70);
x_78 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set(x_78, 2, x_77);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_65);
if (lean_is_scalar(x_68)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_68;
}
lean_ctor_set(x_79, 0, x_70);
x_80 = lean_array_push(x_13, x_79);
x_81 = lean_array_push(x_14, x_78);
if (lean_is_scalar(x_76)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_76;
}
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_3 = x_12;
x_4 = x_82;
x_6 = x_75;
goto _start;
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_63);
lean_dec(x_15);
x_84 = lean_array_push(x_13, x_10);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_14);
x_3 = x_12;
x_4 = x_85;
x_6 = x_64;
goto _start;
}
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_4);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_4, 0);
x_89 = lean_array_push(x_88, x_10);
lean_ctor_set(x_4, 0, x_89);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_4, 0);
x_92 = lean_ctor_get(x_4, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_4);
x_93 = lean_array_push(x_91, x_10);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_3 = x_12;
x_4 = x_94;
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
x_6 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(x_1, x_1, x_4, x_5, x_2, x_3);
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
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_IR_IRType_isScalar(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_2);
x_15 = 7;
x_16 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
lean_inc(x_17);
x_19 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_4);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_2);
x_21 = 7;
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_2, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_IR_ExplicitBoxing_mkCast(x_10, x_4, x_2, x_6, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_5);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_2);
x_16 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_4);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_5);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_2);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_5);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_8, x_3, x_9, x_5, x_6, x_7);
lean_dec(x_6);
return x_10;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
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
x_24 = lean_unbox(x_22);
x_25 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_24, x_16);
if (x_25 == 0)
{
uint8_t x_26; 
lean_free_object(x_20);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_11, 0);
lean_dec(x_27);
x_28 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unbox(x_22);
lean_dec(x_22);
x_32 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_31, x_16, x_6, x_30);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_box(13);
lean_inc(x_29);
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_16);
lean_ctor_set(x_11, 0, x_29);
x_38 = lean_array_push(x_17, x_11);
x_39 = lean_array_push(x_18, x_37);
lean_ctor_set(x_32, 1, x_39);
lean_ctor_set(x_32, 0, x_38);
x_4 = x_13;
x_5 = x_32;
x_7 = x_35;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_box(13);
lean_inc(x_29);
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_16);
lean_ctor_set(x_11, 0, x_29);
x_45 = lean_array_push(x_17, x_11);
x_46 = lean_array_push(x_18, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_4 = x_13;
x_5 = x_47;
x_7 = x_42;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_11);
x_49 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unbox(x_22);
lean_dec(x_22);
x_53 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_52, x_16, x_6, x_51);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_box(13);
lean_inc(x_50);
x_58 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_16);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_50);
x_60 = lean_array_push(x_17, x_59);
x_61 = lean_array_push(x_18, x_58);
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_56;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_4 = x_13;
x_5 = x_62;
x_7 = x_55;
goto _start;
}
}
else
{
lean_object* x_64; 
lean_dec(x_22);
lean_dec(x_19);
x_64 = lean_array_push(x_17, x_11);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 0, x_64);
x_4 = x_13;
x_5 = x_20;
x_7 = x_23;
goto _start;
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_20, 0);
x_67 = lean_ctor_get(x_20, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_20);
x_68 = lean_unbox(x_66);
x_69 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_68, x_16);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_70 = x_11;
} else {
 lean_dec_ref(x_11);
 x_70 = lean_box(0);
}
x_71 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_67);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unbox(x_66);
lean_dec(x_66);
x_75 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_74, x_16, x_6, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_box(13);
lean_inc(x_72);
x_80 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*3, x_16);
if (lean_is_scalar(x_70)) {
 x_81 = lean_alloc_ctor(0, 1, 0);
} else {
 x_81 = x_70;
}
lean_ctor_set(x_81, 0, x_72);
x_82 = lean_array_push(x_17, x_81);
x_83 = lean_array_push(x_18, x_80);
if (lean_is_scalar(x_78)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_78;
}
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_4 = x_13;
x_5 = x_84;
x_7 = x_77;
goto _start;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_66);
lean_dec(x_19);
x_86 = lean_array_push(x_17, x_11);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_18);
x_4 = x_13;
x_5 = x_87;
x_7 = x_67;
goto _start;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_15);
x_89 = !lean_is_exclusive(x_5);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_5, 0);
x_91 = lean_array_push(x_90, x_11);
lean_ctor_set(x_5, 0, x_91);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_95 = lean_array_push(x_93, x_11);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_4 = x_13;
x_5 = x_96;
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
x_7 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(x_1, x_2, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_9, x_5, x_6);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_ctor_set(x_3, 1, x_15);
x_17 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_4);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_2);
x_18 = l_Lean_IR_reshape(x_16, x_17);
lean_ctor_set(x_12, 1, x_13);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
lean_ctor_set(x_3, 1, x_19);
x_21 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 2, x_4);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_2);
x_22 = l_Lean_IR_reshape(x_20, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = l_Lean_IR_IRType_isScalar(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_9, x_5, x_6);
lean_dec(x_9);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_ctor_set(x_3, 1, x_29);
x_31 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_4);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_2);
x_32 = l_Lean_IR_reshape(x_30, x_31);
lean_ctor_set(x_26, 1, x_27);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
lean_ctor_set(x_3, 1, x_33);
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_3);
lean_ctor_set(x_35, 2, x_4);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_2);
x_36 = l_Lean_IR_reshape(x_34, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_3);
lean_dec(x_9);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_dec(x_8);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_4);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_6);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_3, 0);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_3);
x_45 = l_Lean_IR_CtorInfo_isScalar(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_44, x_5, x_6);
lean_dec(x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_51 = x_47;
} else {
 lean_dec_ref(x_47);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_49);
x_53 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_4);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_2);
x_54 = l_Lean_IR_reshape(x_50, x_53);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = l_Lean_IR_IRType_isScalar(x_2);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_57 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_44, x_5, x_6);
lean_dec(x_44);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_62 = x_58;
} else {
 lean_dec_ref(x_58);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_43);
lean_ctor_set(x_63, 1, x_60);
x_64 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_4);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_2);
x_65 = l_Lean_IR_reshape(x_61, x_64);
if (lean_is_scalar(x_62)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_62;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_59);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_44);
x_67 = lean_ctor_get(x_43, 1);
lean_inc(x_67);
lean_dec(x_43);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_70, 0, x_1);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_4);
lean_ctor_set_uint8(x_70, sizeof(void*)*3, x_2);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_6);
return x_71;
}
}
}
}
case 2:
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_3);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_3, 2);
x_74 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_73, x_5, x_6);
lean_dec(x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_ctor_get(x_75, 1);
lean_ctor_set(x_3, 2, x_78);
x_80 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_3);
lean_ctor_set(x_80, 2, x_4);
lean_ctor_set_uint8(x_80, sizeof(void*)*3, x_2);
x_81 = l_Lean_IR_reshape(x_79, x_80);
lean_ctor_set(x_75, 1, x_76);
lean_ctor_set(x_75, 0, x_81);
return x_75;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_75, 0);
x_83 = lean_ctor_get(x_75, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_75);
lean_ctor_set(x_3, 2, x_82);
x_84 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_84, 0, x_1);
lean_ctor_set(x_84, 1, x_3);
lean_ctor_set(x_84, 2, x_4);
lean_ctor_set_uint8(x_84, sizeof(void*)*3, x_2);
x_85 = l_Lean_IR_reshape(x_83, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_76);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_87 = lean_ctor_get(x_3, 0);
x_88 = lean_ctor_get(x_3, 1);
x_89 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_90 = lean_ctor_get(x_3, 2);
lean_inc(x_90);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_3);
x_91 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_90, x_5, x_6);
lean_dec(x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_96 = x_92;
} else {
 lean_dec_ref(x_92);
 x_96 = lean_box(0);
}
x_97 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_88);
lean_ctor_set(x_97, 2, x_94);
lean_ctor_set_uint8(x_97, sizeof(void*)*3, x_89);
x_98 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_4);
lean_ctor_set_uint8(x_98, sizeof(void*)*3, x_2);
x_99 = l_Lean_IR_reshape(x_95, x_98);
if (lean_is_scalar(x_96)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_96;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_93);
return x_100;
}
}
case 6:
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_3);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; uint8_t x_115; 
x_102 = lean_ctor_get(x_3, 0);
x_103 = lean_ctor_get(x_3, 1);
x_104 = l_Lean_IR_ExplicitBoxing_getDecl(x_102, x_5, x_6);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_IR_Decl_params(x_105);
x_108 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(x_107, x_103, x_5, x_106);
lean_dec(x_103);
lean_dec(x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
lean_ctor_set(x_3, 1, x_111);
x_113 = l_Lean_IR_Decl_resultType(x_105);
lean_dec(x_105);
x_114 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_2, x_3, x_113, x_4, x_5, x_110);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = l_Lean_IR_reshape(x_112, x_116);
lean_ctor_set(x_114, 0, x_117);
return x_114;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_114, 0);
x_119 = lean_ctor_get(x_114, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_114);
x_120 = l_Lean_IR_reshape(x_112, x_118);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_122 = lean_ctor_get(x_3, 0);
x_123 = lean_ctor_get(x_3, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_3);
x_124 = l_Lean_IR_ExplicitBoxing_getDecl(x_122, x_5, x_6);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_Lean_IR_Decl_params(x_125);
x_128 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(x_127, x_123, x_5, x_126);
lean_dec(x_123);
lean_dec(x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_133, 0, x_122);
lean_ctor_set(x_133, 1, x_131);
x_134 = l_Lean_IR_Decl_resultType(x_125);
lean_dec(x_125);
x_135 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_2, x_133, x_134, x_4, x_5, x_130);
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
x_139 = l_Lean_IR_reshape(x_132, x_136);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
}
case 7:
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_3);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; 
x_142 = lean_ctor_get(x_3, 0);
x_143 = lean_ctor_get(x_3, 1);
x_144 = l_Lean_IR_ExplicitBoxing_getEnv(x_5, x_6);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_IR_ExplicitBoxing_getDecl(x_142, x_5, x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_145, x_148);
lean_dec(x_148);
lean_dec(x_145);
x_151 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_143, x_5, x_149);
lean_dec(x_143);
if (x_150 == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = !lean_is_exclusive(x_152);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_152, 0);
x_156 = lean_ctor_get(x_152, 1);
lean_ctor_set(x_3, 1, x_155);
x_157 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_157, 0, x_1);
lean_ctor_set(x_157, 1, x_3);
lean_ctor_set(x_157, 2, x_4);
lean_ctor_set_uint8(x_157, sizeof(void*)*3, x_2);
x_158 = l_Lean_IR_reshape(x_156, x_157);
lean_ctor_set(x_152, 1, x_153);
lean_ctor_set(x_152, 0, x_158);
return x_152;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = lean_ctor_get(x_152, 0);
x_160 = lean_ctor_get(x_152, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_152);
lean_ctor_set(x_3, 1, x_159);
x_161 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_161, 0, x_1);
lean_ctor_set(x_161, 1, x_3);
lean_ctor_set(x_161, 2, x_4);
lean_ctor_set_uint8(x_161, sizeof(void*)*3, x_2);
x_162 = l_Lean_IR_reshape(x_160, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_153);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_164 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_165 = lean_name_mk_string(x_142, x_164);
x_166 = lean_ctor_get(x_151, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_151, 1);
lean_inc(x_167);
lean_dec(x_151);
x_168 = !lean_is_exclusive(x_166);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_166, 0);
x_170 = lean_ctor_get(x_166, 1);
lean_ctor_set(x_3, 1, x_169);
lean_ctor_set(x_3, 0, x_165);
x_171 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_171, 0, x_1);
lean_ctor_set(x_171, 1, x_3);
lean_ctor_set(x_171, 2, x_4);
lean_ctor_set_uint8(x_171, sizeof(void*)*3, x_2);
x_172 = l_Lean_IR_reshape(x_170, x_171);
lean_ctor_set(x_166, 1, x_167);
lean_ctor_set(x_166, 0, x_172);
return x_166;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_173 = lean_ctor_get(x_166, 0);
x_174 = lean_ctor_get(x_166, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_166);
lean_ctor_set(x_3, 1, x_173);
lean_ctor_set(x_3, 0, x_165);
x_175 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_175, 0, x_1);
lean_ctor_set(x_175, 1, x_3);
lean_ctor_set(x_175, 2, x_4);
lean_ctor_set_uint8(x_175, sizeof(void*)*3, x_2);
x_176 = l_Lean_IR_reshape(x_174, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_167);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; 
x_178 = lean_ctor_get(x_3, 0);
x_179 = lean_ctor_get(x_3, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_3);
x_180 = l_Lean_IR_ExplicitBoxing_getEnv(x_5, x_6);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l_Lean_IR_ExplicitBoxing_getDecl(x_178, x_5, x_182);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_181, x_184);
lean_dec(x_184);
lean_dec(x_181);
x_187 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_179, x_5, x_185);
lean_dec(x_179);
if (x_186 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_192 = x_188;
} else {
 lean_dec_ref(x_188);
 x_192 = lean_box(0);
}
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_178);
lean_ctor_set(x_193, 1, x_190);
x_194 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_194, 0, x_1);
lean_ctor_set(x_194, 1, x_193);
lean_ctor_set(x_194, 2, x_4);
lean_ctor_set_uint8(x_194, sizeof(void*)*3, x_2);
x_195 = l_Lean_IR_reshape(x_191, x_194);
if (lean_is_scalar(x_192)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_192;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_189);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_197 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_198 = lean_name_mk_string(x_178, x_197);
x_199 = lean_ctor_get(x_187, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_187, 1);
lean_inc(x_200);
lean_dec(x_187);
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_203 = x_199;
} else {
 lean_dec_ref(x_199);
 x_203 = lean_box(0);
}
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_198);
lean_ctor_set(x_204, 1, x_201);
x_205 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_205, 0, x_1);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_205, 2, x_4);
lean_ctor_set_uint8(x_205, sizeof(void*)*3, x_2);
x_206 = l_Lean_IR_reshape(x_202, x_205);
if (lean_is_scalar(x_203)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_203;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_200);
return x_207;
}
}
}
case 8:
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_3);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_209 = lean_ctor_get(x_3, 1);
x_210 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_209, x_5, x_6);
lean_dec(x_209);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
lean_ctor_set(x_3, 1, x_213);
x_215 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_1, x_2, x_3, x_4, x_5, x_212);
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_215, 0);
x_218 = l_Lean_IR_reshape(x_214, x_217);
lean_ctor_set(x_215, 0, x_218);
return x_215;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_219 = lean_ctor_get(x_215, 0);
x_220 = lean_ctor_get(x_215, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_215);
x_221 = l_Lean_IR_reshape(x_214, x_219);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_223 = lean_ctor_get(x_3, 0);
x_224 = lean_ctor_get(x_3, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_3);
x_225 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(x_224, x_5, x_6);
lean_dec(x_224);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_ctor_get(x_226, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_226, 1);
lean_inc(x_229);
lean_dec(x_226);
x_230 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_230, 0, x_223);
lean_ctor_set(x_230, 1, x_228);
x_231 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_1, x_2, x_230, x_4, x_5, x_227);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_234 = x_231;
} else {
 lean_dec_ref(x_231);
 x_234 = lean_box(0);
}
x_235 = l_Lean_IR_reshape(x_229, x_232);
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_234;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_233);
return x_236;
}
}
default: 
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_237, 0, x_1);
lean_ctor_set(x_237, 1, x_3);
lean_ctor_set(x_237, 2, x_4);
lean_ctor_set_uint8(x_237, sizeof(void*)*3, x_2);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_6);
return x_238;
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_10);
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
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
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
x_24 = lean_unbox(x_22);
x_25 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_24, x_16);
if (x_25 == 0)
{
uint8_t x_26; 
lean_free_object(x_20);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_11, 0);
lean_dec(x_27);
x_28 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unbox(x_22);
lean_dec(x_22);
x_32 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_31, x_16, x_6, x_30);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_box(13);
lean_inc(x_29);
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_16);
lean_ctor_set(x_11, 0, x_29);
x_38 = lean_array_push(x_17, x_11);
x_39 = lean_array_push(x_18, x_37);
lean_ctor_set(x_32, 1, x_39);
lean_ctor_set(x_32, 0, x_38);
x_4 = x_13;
x_5 = x_32;
x_7 = x_35;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_box(13);
lean_inc(x_29);
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_16);
lean_ctor_set(x_11, 0, x_29);
x_45 = lean_array_push(x_17, x_11);
x_46 = lean_array_push(x_18, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_4 = x_13;
x_5 = x_47;
x_7 = x_42;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_11);
x_49 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unbox(x_22);
lean_dec(x_22);
x_53 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_52, x_16, x_6, x_51);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = lean_box(13);
lean_inc(x_50);
x_58 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_16);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_50);
x_60 = lean_array_push(x_17, x_59);
x_61 = lean_array_push(x_18, x_58);
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_56;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_4 = x_13;
x_5 = x_62;
x_7 = x_55;
goto _start;
}
}
else
{
lean_object* x_64; 
lean_dec(x_22);
lean_dec(x_19);
x_64 = lean_array_push(x_17, x_11);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 0, x_64);
x_4 = x_13;
x_5 = x_20;
x_7 = x_23;
goto _start;
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_20, 0);
x_67 = lean_ctor_get(x_20, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_20);
x_68 = lean_unbox(x_66);
x_69 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_68, x_16);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_70 = x_11;
} else {
 lean_dec_ref(x_11);
 x_70 = lean_box(0);
}
x_71 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_67);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unbox(x_66);
lean_dec(x_66);
x_75 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_74, x_16, x_6, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_box(13);
lean_inc(x_72);
x_80 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*3, x_16);
if (lean_is_scalar(x_70)) {
 x_81 = lean_alloc_ctor(0, 1, 0);
} else {
 x_81 = x_70;
}
lean_ctor_set(x_81, 0, x_72);
x_82 = lean_array_push(x_17, x_81);
x_83 = lean_array_push(x_18, x_80);
if (lean_is_scalar(x_78)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_78;
}
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_4 = x_13;
x_5 = x_84;
x_7 = x_77;
goto _start;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_66);
lean_dec(x_19);
x_86 = lean_array_push(x_17, x_11);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_18);
x_4 = x_13;
x_5 = x_87;
x_7 = x_67;
goto _start;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_15);
x_89 = !lean_is_exclusive(x_5);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_5, 0);
x_91 = lean_array_push(x_90, x_11);
lean_ctor_set(x_5, 0, x_91);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_95 = lean_array_push(x_93, x_11);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_4 = x_13;
x_5 = x_96;
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
x_7 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(x_1, x_2, x_2, x_5, x_6, x_3, x_4);
return x_7;
}
}
lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_4);
x_13 = l_Lean_IR_LocalContext_addLocal(x_9, x_4, x_5, x_6);
x_14 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*4, x_10);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_ctor_get(x_1, 3);
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_28 = lean_ctor_get(x_2, 2);
x_29 = lean_ctor_get(x_2, 3);
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_26);
x_31 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_22, x_22, x_30, x_26);
lean_inc(x_29);
lean_inc(x_28);
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
x_36 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_28);
lean_ctor_set(x_36, 3, x_29);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_27);
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
x_45 = lean_ctor_get(x_1, 2);
x_46 = lean_ctor_get(x_1, 3);
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_ctor_get(x_2, 1);
x_49 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_50 = lean_ctor_get(x_2, 2);
x_51 = lean_ctor_get(x_2, 3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_2);
x_52 = lean_unsigned_to_nat(0u);
lean_inc(x_48);
x_53 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_44, x_44, x_52, x_48);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_47);
x_54 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_50);
lean_ctor_set(x_54, 3, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_49);
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
x_59 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_50);
lean_ctor_set(x_59, 3, x_51);
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_49);
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
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
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
x_71 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
x_72 = lean_ctor_get(x_2, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_2, 3);
lean_inc(x_73);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 x_74 = x_2;
} else {
 lean_dec_ref(x_2);
 x_74 = lean_box(0);
}
x_75 = lean_unsigned_to_nat(0u);
lean_inc(x_70);
x_76 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_66, x_66, x_75, x_70);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_69);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 4, 1);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_72);
lean_ctor_set(x_77, 3, x_73);
lean_ctor_set_uint8(x_77, sizeof(void*)*4, x_71);
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
x_82 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_82, 0, x_69);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_72);
lean_ctor_set(x_82, 3, x_73);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_71);
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
lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
x_99 = 5;
x_100 = lean_unbox(x_97);
x_101 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_100, x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; uint8_t x_107; 
lean_free_object(x_95);
x_102 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_98);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_unbox(x_97);
lean_dec(x_97);
x_106 = l_Lean_IR_ExplicitBoxing_mkCast(x_90, x_105, x_99, x_2, x_104);
lean_dec(x_2);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_103);
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set(x_1, 2, x_103);
x_109 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_109, 0, x_103);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_109, 2, x_1);
lean_ctor_set_uint8(x_109, sizeof(void*)*3, x_99);
lean_ctor_set(x_106, 0, x_109);
return x_106;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_106);
lean_inc(x_103);
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set(x_1, 2, x_103);
x_112 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_112, 0, x_103);
lean_ctor_set(x_112, 1, x_110);
lean_ctor_set(x_112, 2, x_1);
lean_ctor_set_uint8(x_112, sizeof(void*)*3, x_99);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
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
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; 
x_114 = lean_ctor_get(x_95, 0);
x_115 = lean_ctor_get(x_95, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_95);
x_116 = 5;
x_117 = lean_unbox(x_114);
x_118 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_117, x_116);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_119 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_115);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_unbox(x_114);
lean_dec(x_114);
x_123 = l_Lean_IR_ExplicitBoxing_mkCast(x_90, x_122, x_116, x_2, x_121);
lean_dec(x_2);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
lean_inc(x_120);
lean_ctor_set(x_1, 3, x_93);
lean_ctor_set(x_1, 2, x_120);
x_127 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_127, 0, x_120);
lean_ctor_set(x_127, 1, x_124);
lean_ctor_set(x_127, 2, x_1);
lean_ctor_set_uint8(x_127, sizeof(void*)*3, x_116);
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_126;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
else
{
lean_object* x_129; 
lean_dec(x_114);
lean_dec(x_2);
lean_ctor_set(x_1, 3, x_93);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_1);
lean_ctor_set(x_129, 1, x_115);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; 
x_130 = lean_ctor_get(x_1, 0);
x_131 = lean_ctor_get(x_1, 1);
x_132 = lean_ctor_get(x_1, 2);
x_133 = lean_ctor_get(x_1, 3);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_1);
lean_inc(x_2);
x_134 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_133, x_2, x_3);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_IR_ExplicitBoxing_getVarType(x_132, x_2, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = 5;
x_142 = lean_unbox(x_138);
x_143 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_142, x_141);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_140);
x_144 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_139);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_unbox(x_138);
lean_dec(x_138);
x_148 = l_Lean_IR_ExplicitBoxing_mkCast(x_132, x_147, x_141, x_2, x_146);
lean_dec(x_2);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
lean_inc(x_145);
x_152 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_152, 0, x_130);
lean_ctor_set(x_152, 1, x_131);
lean_ctor_set(x_152, 2, x_145);
lean_ctor_set(x_152, 3, x_135);
x_153 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_153, 0, x_145);
lean_ctor_set(x_153, 1, x_149);
lean_ctor_set(x_153, 2, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*3, x_141);
if (lean_is_scalar(x_151)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_151;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_150);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_138);
lean_dec(x_2);
x_155 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_155, 0, x_130);
lean_ctor_set(x_155, 1, x_131);
lean_ctor_set(x_155, 2, x_132);
lean_ctor_set(x_155, 3, x_135);
if (lean_is_scalar(x_140)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_140;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_139);
return x_156;
}
}
}
case 5:
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_1);
if (x_157 == 0)
{
lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_158 = lean_ctor_get(x_1, 3);
x_159 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_160 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
x_161 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_160, x_2, x_3);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = l_Lean_IR_ExplicitBoxing_getVarType(x_158, x_2, x_163);
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_164, 0);
x_167 = lean_ctor_get(x_164, 1);
x_168 = lean_unbox(x_166);
x_169 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_168, x_159);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; uint8_t x_175; 
lean_free_object(x_164);
x_170 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_167);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_unbox(x_166);
lean_dec(x_166);
x_174 = l_Lean_IR_ExplicitBoxing_mkCast(x_158, x_173, x_159, x_2, x_172);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_174, 0);
lean_inc(x_171);
lean_ctor_set(x_1, 4, x_162);
lean_ctor_set(x_1, 3, x_171);
x_177 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_177, 0, x_171);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_177, 2, x_1);
lean_ctor_set_uint8(x_177, sizeof(void*)*3, x_159);
lean_ctor_set(x_174, 0, x_177);
return x_174;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_174, 0);
x_179 = lean_ctor_get(x_174, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_174);
lean_inc(x_171);
lean_ctor_set(x_1, 4, x_162);
lean_ctor_set(x_1, 3, x_171);
x_180 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_180, 0, x_171);
lean_ctor_set(x_180, 1, x_178);
lean_ctor_set(x_180, 2, x_1);
lean_ctor_set_uint8(x_180, sizeof(void*)*3, x_159);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
lean_dec(x_166);
lean_dec(x_2);
lean_ctor_set(x_1, 4, x_162);
lean_ctor_set(x_164, 0, x_1);
return x_164;
}
}
else
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_185; 
x_182 = lean_ctor_get(x_164, 0);
x_183 = lean_ctor_get(x_164, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_164);
x_184 = lean_unbox(x_182);
x_185 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_184, x_159);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_186 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_183);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_unbox(x_182);
lean_dec(x_182);
x_190 = l_Lean_IR_ExplicitBoxing_mkCast(x_158, x_189, x_159, x_2, x_188);
lean_dec(x_2);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_193 = x_190;
} else {
 lean_dec_ref(x_190);
 x_193 = lean_box(0);
}
lean_inc(x_187);
lean_ctor_set(x_1, 4, x_162);
lean_ctor_set(x_1, 3, x_187);
x_194 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_194, 0, x_187);
lean_ctor_set(x_194, 1, x_191);
lean_ctor_set(x_194, 2, x_1);
lean_ctor_set_uint8(x_194, sizeof(void*)*3, x_159);
if (lean_is_scalar(x_193)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_193;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_192);
return x_195;
}
else
{
lean_object* x_196; 
lean_dec(x_182);
lean_dec(x_2);
lean_ctor_set(x_1, 4, x_162);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_1);
lean_ctor_set(x_196, 1, x_183);
return x_196;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_211; 
x_197 = lean_ctor_get(x_1, 0);
x_198 = lean_ctor_get(x_1, 1);
x_199 = lean_ctor_get(x_1, 2);
x_200 = lean_ctor_get(x_1, 3);
x_201 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_202 = lean_ctor_get(x_1, 4);
lean_inc(x_202);
lean_inc(x_200);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_1);
lean_inc(x_2);
x_203 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_202, x_2, x_3);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = l_Lean_IR_ExplicitBoxing_getVarType(x_200, x_2, x_205);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_209 = x_206;
} else {
 lean_dec_ref(x_206);
 x_209 = lean_box(0);
}
x_210 = lean_unbox(x_207);
x_211 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_210, x_201);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_209);
x_212 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_208);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_unbox(x_207);
lean_dec(x_207);
x_216 = l_Lean_IR_ExplicitBoxing_mkCast(x_200, x_215, x_201, x_2, x_214);
lean_dec(x_2);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_219 = x_216;
} else {
 lean_dec_ref(x_216);
 x_219 = lean_box(0);
}
lean_inc(x_213);
x_220 = lean_alloc_ctor(5, 5, 1);
lean_ctor_set(x_220, 0, x_197);
lean_ctor_set(x_220, 1, x_198);
lean_ctor_set(x_220, 2, x_199);
lean_ctor_set(x_220, 3, x_213);
lean_ctor_set(x_220, 4, x_204);
lean_ctor_set_uint8(x_220, sizeof(void*)*5, x_201);
x_221 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_221, 0, x_213);
lean_ctor_set(x_221, 1, x_217);
lean_ctor_set(x_221, 2, x_220);
lean_ctor_set_uint8(x_221, sizeof(void*)*3, x_201);
if (lean_is_scalar(x_219)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_219;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_218);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_207);
lean_dec(x_2);
x_223 = lean_alloc_ctor(5, 5, 1);
lean_ctor_set(x_223, 0, x_197);
lean_ctor_set(x_223, 1, x_198);
lean_ctor_set(x_223, 2, x_199);
lean_ctor_set(x_223, 3, x_200);
lean_ctor_set(x_223, 4, x_204);
lean_ctor_set_uint8(x_223, sizeof(void*)*5, x_201);
if (lean_is_scalar(x_209)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_209;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_208);
return x_224;
}
}
}
case 9:
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_1);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_226 = lean_ctor_get(x_1, 1);
x_227 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_226, x_2, x_3);
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_227, 0);
lean_ctor_set(x_1, 1, x_229);
lean_ctor_set(x_227, 0, x_1);
return x_227;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_227, 0);
x_231 = lean_ctor_get(x_227, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_227);
lean_ctor_set(x_1, 1, x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_1);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_233 = lean_ctor_get(x_1, 0);
x_234 = lean_ctor_get(x_1, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_1);
x_235 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_234, x_2, x_3);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_238 = x_235;
} else {
 lean_dec_ref(x_235);
 x_238 = lean_box(0);
}
x_239 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_239, 0, x_233);
lean_ctor_set(x_239, 1, x_236);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
return x_240;
}
}
case 10:
{
uint8_t x_241; 
x_241 = !lean_is_exclusive(x_1);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_242 = lean_ctor_get(x_1, 1);
x_243 = lean_ctor_get(x_1, 2);
x_244 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_243);
x_245 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_246 = l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(x_245, x_243, x_2, x_3);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = l_Lean_IR_ExplicitBoxing_getVarType(x_242, x_2, x_248);
x_250 = !lean_is_exclusive(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; 
x_251 = lean_ctor_get(x_249, 0);
x_252 = lean_ctor_get(x_249, 1);
x_253 = lean_unbox(x_251);
x_254 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_253, x_244);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; uint8_t x_260; 
lean_free_object(x_249);
x_255 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_252);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_unbox(x_251);
lean_dec(x_251);
x_259 = l_Lean_IR_ExplicitBoxing_mkCast(x_242, x_258, x_244, x_2, x_257);
lean_dec(x_2);
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_259, 0);
lean_inc(x_256);
lean_ctor_set(x_1, 2, x_247);
lean_ctor_set(x_1, 1, x_256);
x_262 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_262, 0, x_256);
lean_ctor_set(x_262, 1, x_261);
lean_ctor_set(x_262, 2, x_1);
lean_ctor_set_uint8(x_262, sizeof(void*)*3, x_244);
lean_ctor_set(x_259, 0, x_262);
return x_259;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_263 = lean_ctor_get(x_259, 0);
x_264 = lean_ctor_get(x_259, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_259);
lean_inc(x_256);
lean_ctor_set(x_1, 2, x_247);
lean_ctor_set(x_1, 1, x_256);
x_265 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_265, 0, x_256);
lean_ctor_set(x_265, 1, x_263);
lean_ctor_set(x_265, 2, x_1);
lean_ctor_set_uint8(x_265, sizeof(void*)*3, x_244);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
else
{
lean_dec(x_251);
lean_dec(x_2);
lean_ctor_set(x_1, 2, x_247);
lean_ctor_set(x_249, 0, x_1);
return x_249;
}
}
else
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; uint8_t x_270; 
x_267 = lean_ctor_get(x_249, 0);
x_268 = lean_ctor_get(x_249, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_249);
x_269 = lean_unbox(x_267);
x_270 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_269, x_244);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_271 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_268);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_unbox(x_267);
lean_dec(x_267);
x_275 = l_Lean_IR_ExplicitBoxing_mkCast(x_242, x_274, x_244, x_2, x_273);
lean_dec(x_2);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_278 = x_275;
} else {
 lean_dec_ref(x_275);
 x_278 = lean_box(0);
}
lean_inc(x_272);
lean_ctor_set(x_1, 2, x_247);
lean_ctor_set(x_1, 1, x_272);
x_279 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_279, 0, x_272);
lean_ctor_set(x_279, 1, x_276);
lean_ctor_set(x_279, 2, x_1);
lean_ctor_set_uint8(x_279, sizeof(void*)*3, x_244);
if (lean_is_scalar(x_278)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_278;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_277);
return x_280;
}
else
{
lean_object* x_281; 
lean_dec(x_267);
lean_dec(x_2);
lean_ctor_set(x_1, 2, x_247);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_1);
lean_ctor_set(x_281, 1, x_268);
return x_281;
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; uint8_t x_295; 
x_282 = lean_ctor_get(x_1, 0);
x_283 = lean_ctor_get(x_1, 1);
x_284 = lean_ctor_get(x_1, 2);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_1);
x_285 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_284);
x_286 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_287 = l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(x_286, x_284, x_2, x_3);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = l_Lean_IR_ExplicitBoxing_getVarType(x_283, x_2, x_289);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_293 = x_290;
} else {
 lean_dec_ref(x_290);
 x_293 = lean_box(0);
}
x_294 = lean_unbox(x_291);
x_295 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_294, x_285);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_293);
x_296 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_292);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_unbox(x_291);
lean_dec(x_291);
x_300 = l_Lean_IR_ExplicitBoxing_mkCast(x_283, x_299, x_285, x_2, x_298);
lean_dec(x_2);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_303 = x_300;
} else {
 lean_dec_ref(x_300);
 x_303 = lean_box(0);
}
lean_inc(x_297);
x_304 = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(x_304, 0, x_282);
lean_ctor_set(x_304, 1, x_297);
lean_ctor_set(x_304, 2, x_288);
x_305 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_305, 0, x_297);
lean_ctor_set(x_305, 1, x_301);
lean_ctor_set(x_305, 2, x_304);
lean_ctor_set_uint8(x_305, sizeof(void*)*3, x_285);
if (lean_is_scalar(x_303)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_303;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_302);
return x_306;
}
else
{
lean_object* x_307; lean_object* x_308; 
lean_dec(x_291);
lean_dec(x_2);
x_307 = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(x_307, 0, x_282);
lean_ctor_set(x_307, 1, x_283);
lean_ctor_set(x_307, 2, x_288);
if (lean_is_scalar(x_293)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_293;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_292);
return x_308;
}
}
}
case 11:
{
uint8_t x_309; 
x_309 = !lean_is_exclusive(x_1);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_1, 0);
x_311 = l_Lean_IR_ExplicitBoxing_getResultType(x_2, x_3);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = !lean_is_exclusive(x_310);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_315 = lean_ctor_get(x_310, 0);
x_316 = l_Lean_IR_ExplicitBoxing_getVarType(x_315, x_2, x_313);
x_317 = !lean_is_exclusive(x_316);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; uint8_t x_320; uint8_t x_321; uint8_t x_322; 
x_318 = lean_ctor_get(x_316, 0);
x_319 = lean_ctor_get(x_316, 1);
x_320 = lean_unbox(x_318);
x_321 = lean_unbox(x_312);
x_322 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_320, x_321);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; uint8_t x_327; lean_object* x_328; uint8_t x_329; 
lean_free_object(x_316);
x_323 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_319);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_unbox(x_318);
lean_dec(x_318);
x_327 = lean_unbox(x_312);
x_328 = l_Lean_IR_ExplicitBoxing_mkCast(x_315, x_326, x_327, x_2, x_325);
lean_dec(x_2);
x_329 = !lean_is_exclusive(x_328);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; uint8_t x_332; 
x_330 = lean_ctor_get(x_328, 0);
lean_inc(x_324);
lean_ctor_set(x_310, 0, x_324);
x_331 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_331, 0, x_324);
lean_ctor_set(x_331, 1, x_330);
lean_ctor_set(x_331, 2, x_1);
x_332 = lean_unbox(x_312);
lean_dec(x_312);
lean_ctor_set_uint8(x_331, sizeof(void*)*3, x_332);
lean_ctor_set(x_328, 0, x_331);
return x_328;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; 
x_333 = lean_ctor_get(x_328, 0);
x_334 = lean_ctor_get(x_328, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_328);
lean_inc(x_324);
lean_ctor_set(x_310, 0, x_324);
x_335 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_335, 0, x_324);
lean_ctor_set(x_335, 1, x_333);
lean_ctor_set(x_335, 2, x_1);
x_336 = lean_unbox(x_312);
lean_dec(x_312);
lean_ctor_set_uint8(x_335, sizeof(void*)*3, x_336);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_334);
return x_337;
}
}
else
{
lean_dec(x_318);
lean_dec(x_312);
lean_dec(x_2);
lean_ctor_set(x_316, 0, x_1);
return x_316;
}
}
else
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; uint8_t x_341; uint8_t x_342; 
x_338 = lean_ctor_get(x_316, 0);
x_339 = lean_ctor_get(x_316, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_316);
x_340 = lean_unbox(x_338);
x_341 = lean_unbox(x_312);
x_342 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_340, x_341);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; uint8_t x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; 
x_343 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_339);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = lean_unbox(x_338);
lean_dec(x_338);
x_347 = lean_unbox(x_312);
x_348 = l_Lean_IR_ExplicitBoxing_mkCast(x_315, x_346, x_347, x_2, x_345);
lean_dec(x_2);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 x_351 = x_348;
} else {
 lean_dec_ref(x_348);
 x_351 = lean_box(0);
}
lean_inc(x_344);
lean_ctor_set(x_310, 0, x_344);
x_352 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_352, 0, x_344);
lean_ctor_set(x_352, 1, x_349);
lean_ctor_set(x_352, 2, x_1);
x_353 = lean_unbox(x_312);
lean_dec(x_312);
lean_ctor_set_uint8(x_352, sizeof(void*)*3, x_353);
if (lean_is_scalar(x_351)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_351;
}
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_350);
return x_354;
}
else
{
lean_object* x_355; 
lean_dec(x_338);
lean_dec(x_312);
lean_dec(x_2);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_1);
lean_ctor_set(x_355, 1, x_339);
return x_355;
}
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; uint8_t x_362; uint8_t x_363; 
x_356 = lean_ctor_get(x_310, 0);
lean_inc(x_356);
lean_dec(x_310);
x_357 = l_Lean_IR_ExplicitBoxing_getVarType(x_356, x_2, x_313);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_360 = x_357;
} else {
 lean_dec_ref(x_357);
 x_360 = lean_box(0);
}
x_361 = lean_unbox(x_358);
x_362 = lean_unbox(x_312);
x_363 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_361, x_362);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; 
lean_dec(x_360);
x_364 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_359);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_367 = lean_unbox(x_358);
lean_dec(x_358);
x_368 = lean_unbox(x_312);
x_369 = l_Lean_IR_ExplicitBoxing_mkCast(x_356, x_367, x_368, x_2, x_366);
lean_dec(x_2);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_372 = x_369;
} else {
 lean_dec_ref(x_369);
 x_372 = lean_box(0);
}
lean_inc(x_365);
x_373 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_373, 0, x_365);
lean_ctor_set(x_1, 0, x_373);
x_374 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_374, 0, x_365);
lean_ctor_set(x_374, 1, x_370);
lean_ctor_set(x_374, 2, x_1);
x_375 = lean_unbox(x_312);
lean_dec(x_312);
lean_ctor_set_uint8(x_374, sizeof(void*)*3, x_375);
if (lean_is_scalar(x_372)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_372;
}
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_371);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; 
lean_dec(x_358);
lean_dec(x_312);
lean_dec(x_2);
x_377 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_377, 0, x_356);
lean_ctor_set(x_1, 0, x_377);
if (lean_is_scalar(x_360)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_360;
}
lean_ctor_set(x_378, 0, x_1);
lean_ctor_set(x_378, 1, x_359);
return x_378;
}
}
}
else
{
uint8_t x_379; 
lean_dec(x_2);
x_379 = !lean_is_exclusive(x_311);
if (x_379 == 0)
{
lean_object* x_380; 
x_380 = lean_ctor_get(x_311, 0);
lean_dec(x_380);
lean_ctor_set(x_311, 0, x_1);
return x_311;
}
else
{
lean_object* x_381; lean_object* x_382; 
x_381 = lean_ctor_get(x_311, 1);
lean_inc(x_381);
lean_dec(x_311);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_1);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
else
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_1, 0);
lean_inc(x_383);
lean_dec(x_1);
x_384 = l_Lean_IR_ExplicitBoxing_getResultType(x_2, x_3);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; uint8_t x_394; uint8_t x_395; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_387 = lean_ctor_get(x_383, 0);
lean_inc(x_387);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 x_388 = x_383;
} else {
 lean_dec_ref(x_383);
 x_388 = lean_box(0);
}
x_389 = l_Lean_IR_ExplicitBoxing_getVarType(x_387, x_2, x_386);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_392 = x_389;
} else {
 lean_dec_ref(x_389);
 x_392 = lean_box(0);
}
x_393 = lean_unbox(x_390);
x_394 = lean_unbox(x_385);
x_395 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_393, x_394);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; lean_object* x_409; 
lean_dec(x_392);
x_396 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_391);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_unbox(x_390);
lean_dec(x_390);
x_400 = lean_unbox(x_385);
x_401 = l_Lean_IR_ExplicitBoxing_mkCast(x_387, x_399, x_400, x_2, x_398);
lean_dec(x_2);
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
lean_inc(x_397);
if (lean_is_scalar(x_388)) {
 x_405 = lean_alloc_ctor(0, 1, 0);
} else {
 x_405 = x_388;
}
lean_ctor_set(x_405, 0, x_397);
x_406 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_406, 0, x_405);
x_407 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_407, 0, x_397);
lean_ctor_set(x_407, 1, x_402);
lean_ctor_set(x_407, 2, x_406);
x_408 = lean_unbox(x_385);
lean_dec(x_385);
lean_ctor_set_uint8(x_407, sizeof(void*)*3, x_408);
if (lean_is_scalar(x_404)) {
 x_409 = lean_alloc_ctor(0, 2, 0);
} else {
 x_409 = x_404;
}
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_403);
return x_409;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_390);
lean_dec(x_385);
lean_dec(x_2);
if (lean_is_scalar(x_388)) {
 x_410 = lean_alloc_ctor(0, 1, 0);
} else {
 x_410 = x_388;
}
lean_ctor_set(x_410, 0, x_387);
x_411 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_411, 0, x_410);
if (lean_is_scalar(x_392)) {
 x_412 = lean_alloc_ctor(0, 2, 0);
} else {
 x_412 = x_392;
}
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_391);
return x_412;
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_2);
x_413 = lean_ctor_get(x_384, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_414 = x_384;
} else {
 lean_dec_ref(x_384);
 x_414 = lean_box(0);
}
x_415 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_415, 0, x_383);
if (lean_is_scalar(x_414)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_414;
}
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_413);
return x_416;
}
}
}
case 12:
{
uint8_t x_417; 
x_417 = !lean_is_exclusive(x_1);
if (x_417 == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; 
x_418 = lean_ctor_get(x_1, 0);
x_419 = lean_ctor_get(x_1, 1);
x_420 = l_Lean_IR_ExplicitBoxing_getJPParams(x_418, x_2, x_3);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(x_421, x_419, x_2, x_422);
lean_dec(x_2);
lean_dec(x_419);
lean_dec(x_421);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
x_426 = !lean_is_exclusive(x_424);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_424, 0);
x_428 = lean_ctor_get(x_424, 1);
lean_ctor_set(x_1, 1, x_427);
x_429 = l_Lean_IR_reshape(x_428, x_1);
lean_ctor_set(x_424, 1, x_425);
lean_ctor_set(x_424, 0, x_429);
return x_424;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_430 = lean_ctor_get(x_424, 0);
x_431 = lean_ctor_get(x_424, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_424);
lean_ctor_set(x_1, 1, x_430);
x_432 = l_Lean_IR_reshape(x_431, x_1);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_425);
return x_433;
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_434 = lean_ctor_get(x_1, 0);
x_435 = lean_ctor_get(x_1, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_1);
x_436 = l_Lean_IR_ExplicitBoxing_getJPParams(x_434, x_2, x_3);
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
x_439 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(x_437, x_435, x_2, x_438);
lean_dec(x_2);
lean_dec(x_435);
lean_dec(x_437);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_442 = lean_ctor_get(x_440, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_440, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_444 = x_440;
} else {
 lean_dec_ref(x_440);
 x_444 = lean_box(0);
}
x_445 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_445, 0, x_434);
lean_ctor_set(x_445, 1, x_442);
x_446 = l_Lean_IR_reshape(x_443, x_445);
if (lean_is_scalar(x_444)) {
 x_447 = lean_alloc_ctor(0, 2, 0);
} else {
 x_447 = x_444;
}
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_441);
return x_447;
}
}
default: 
{
lean_object* x_448; 
lean_dec(x_2);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_1);
lean_ctor_set(x_448, 1, x_3);
return x_448;
}
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_16 = lean_ctor_get(x_10, 2);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_18 = l_Lean_IR_MaxIndex_collectDecl(x_10, x_17);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_10, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_10, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = lean_nat_add(x_18, x_11);
lean_dec(x_18);
x_24 = lean_box(0);
lean_inc(x_4);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_11);
lean_inc(x_3);
x_26 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_14, x_14, x_17, x_3);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_13);
x_27 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_2);
lean_ctor_set(x_27, 3, x_1);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_15);
x_28 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_16, x_27, x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_31, x_31, x_17, x_7);
lean_dec(x_31);
lean_ctor_set(x_10, 2, x_29);
x_33 = l_Lean_IR_Decl_elimDead(x_10);
x_34 = lean_array_push(x_32, x_33);
x_6 = x_12;
x_7 = x_34;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_10);
x_36 = lean_nat_add(x_18, x_11);
lean_dec(x_18);
x_37 = lean_box(0);
lean_inc(x_4);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_4);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_11);
lean_inc(x_3);
x_39 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_14, x_14, x_17, x_3);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_13);
x_40 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_40, 0, x_13);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_2);
lean_ctor_set(x_40, 3, x_1);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_15);
x_41 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_16, x_40, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Array_miterateAux___main___at_Array_append___spec__1___rarg(x_44, x_44, x_17, x_7);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_46, 0, x_13);
lean_ctor_set(x_46, 1, x_14);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_15);
x_47 = l_Lean_IR_Decl_elimDead(x_46);
x_48 = lean_array_push(x_45, x_47);
x_6 = x_12;
x_7 = x_48;
goto _start;
}
}
else
{
lean_object* x_50; 
x_50 = lean_array_push(x_7, x_10);
x_6 = x_12;
x_7 = x_50;
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
x_6 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1(x_1, x_2, x_3, x_4, x_2, x_5, x_4);
lean_dec(x_2);
x_7 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Lean_IR_explicitBoxing(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
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
lean_object* initialize_init_data_assoclist(lean_object*);
lean_object* initialize_init_control_estate(lean_object*);
lean_object* initialize_init_control_reader(lean_object*);
lean_object* initialize_init_lean_runtime(lean_object*);
lean_object* initialize_init_lean_compiler_closedtermcache(lean_object*);
lean_object* initialize_init_lean_compiler_externattr(lean_object*);
lean_object* initialize_init_lean_compiler_ir_basic(lean_object*);
lean_object* initialize_init_lean_compiler_ir_compilerm(lean_object*);
lean_object* initialize_init_lean_compiler_ir_freevars(lean_object*);
lean_object* initialize_init_lean_compiler_ir_elimdead(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_compiler_ir_boxing(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_assoclist(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_estate(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_runtime(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_closedtermcache(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_externattr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_freevars(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_elimdead(w);
if (lean_io_result_is_error(w)) return w;
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
return w;
}
#ifdef __cplusplus
}
#endif
