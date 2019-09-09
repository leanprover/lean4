// Lean compiler output
// Module: init.lean.compiler.ir.boxing
// Imports: init.control.estate init.control.reader init.lean.runtime init.lean.compiler.externattr init.lean.compiler.ir.basic init.lean.compiler.ir.compilerm init.lean.compiler.ir.freevars
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
lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getResultType(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withJDecl(lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_explicitBoxing___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName(lean_object*);
lean_object* l_Nat_mfoldAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mfoldAux___main___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getScrutineeType___boxed(lean_object*);
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
lean_object* l_Lean_IR_ExplicitBoxing_mkCast___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getResultType___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkFresh___rarg(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_ExplicitBoxing_eqvTypes(uint8_t, uint8_t);
lean_object* l_Array_fget(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getVarType(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
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
lean_object* l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitVDeclExpr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_init_lean_compiler_ir_boxing_1__mkFresh(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_getEnv___boxed(lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_ExplicitBoxing_getScrutineeType(lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_castArgsIfNeeded___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withParams(lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_explicitBoxing(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_withVDecl___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitBoxing_mkCast(lean_object*, uint8_t);
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
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
x_3 = lean_ctor_get(x_1, 2);
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
x_3 = lean_ctor_get(x_1, 0);
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
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
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
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 1);
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
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_1, x_1, x_7, x_6);
lean_ctor_set(x_3, 0, x_8);
x_9 = lean_apply_2(x_2, x_3, x_4);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_1, x_1, x_14, x_10);
x_16 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_11);
x_17 = lean_apply_2(x_2, x_16, x_4);
return x_17;
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
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lean_IR_LocalContext_addLocal(x_8, x_1, x_2, x_3);
lean_ctor_set(x_5, 0, x_9);
x_10 = lean_apply_2(x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
lean_dec(x_5);
x_15 = l_Lean_IR_LocalContext_addLocal(x_11, x_1, x_2, x_3);
x_16 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_12);
x_17 = lean_apply_2(x_4, x_16, x_6);
return x_17;
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
x_8 = lean_ctor_get(x_5, 0);
x_9 = l_Lean_IR_LocalContext_addJP(x_8, x_1, x_2, x_3);
lean_ctor_set(x_5, 0, x_9);
x_10 = lean_apply_2(x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
lean_dec(x_5);
x_15 = l_Lean_IR_LocalContext_addJP(x_11, x_1, x_2, x_3);
x_16 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_12);
x_17 = lean_apply_2(x_4, x_16, x_6);
return x_17;
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
lean_object* l_Lean_IR_ExplicitBoxing_mkCast(lean_object* x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_IRType_isScalar(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(9, 1, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_2);
return x_5;
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_mkCast___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_IR_ExplicitBoxing_mkCast(x_1, x_3);
return x_4;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = l_Lean_IR_ExplicitBoxing_mkCast(x_1, x_14);
lean_inc(x_12);
x_16 = lean_apply_3(x_3, x_12, x_4, x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_2);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_7);
x_24 = lean_apply_3(x_3, x_1, x_4, x_8);
return x_24;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unbox(x_9);
lean_dec(x_9);
x_17 = l_Lean_IR_ExplicitBoxing_mkCast(x_7, x_16);
lean_inc(x_14);
lean_ctor_set(x_1, 0, x_14);
x_18 = lean_apply_3(x_3, x_1, x_4, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_17);
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
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_17);
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
lean_dec(x_9);
x_26 = lean_apply_3(x_3, x_1, x_4, x_10);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lean_IR_ExplicitBoxing_getVarType(x_27, x_4, x_5);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unbox(x_29);
x_32 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_31, x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_30);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unbox(x_29);
lean_dec(x_29);
x_37 = l_Lean_IR_ExplicitBoxing_mkCast(x_27, x_36);
lean_inc(x_34);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_34);
x_39 = lean_apply_3(x_3, x_38, x_4, x_35);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_37);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_2);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_29);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_27);
x_46 = lean_apply_3(x_3, x_45, x_4, x_30);
return x_46;
}
}
}
else
{
lean_object* x_47; 
x_47 = lean_apply_3(x_3, x_1, x_4, x_5);
return x_47;
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
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_11, 0);
lean_dec(x_26);
x_27 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_22);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_unbox(x_21);
lean_dec(x_21);
x_32 = l_Lean_IR_ExplicitBoxing_mkCast(x_18, x_31);
x_33 = lean_box(13);
lean_inc(x_29);
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_15);
lean_ctor_set(x_11, 0, x_29);
x_35 = lean_array_push(x_16, x_11);
x_36 = lean_array_push(x_17, x_34);
lean_ctor_set(x_27, 1, x_36);
lean_ctor_set(x_27, 0, x_35);
x_4 = x_13;
x_5 = x_27;
x_7 = x_30;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_27);
x_40 = lean_unbox(x_21);
lean_dec(x_21);
x_41 = l_Lean_IR_ExplicitBoxing_mkCast(x_18, x_40);
x_42 = lean_box(13);
lean_inc(x_38);
x_43 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_15);
lean_ctor_set(x_11, 0, x_38);
x_44 = lean_array_push(x_16, x_11);
x_45 = lean_array_push(x_17, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_4 = x_13;
x_5 = x_46;
x_7 = x_39;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_11);
x_48 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_22);
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
x_52 = lean_unbox(x_21);
lean_dec(x_21);
x_53 = l_Lean_IR_ExplicitBoxing_mkCast(x_18, x_52);
x_54 = lean_box(13);
lean_inc(x_49);
x_55 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_15);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_49);
x_57 = lean_array_push(x_16, x_56);
x_58 = lean_array_push(x_17, x_55);
if (lean_is_scalar(x_51)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_51;
}
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_4 = x_13;
x_5 = x_59;
x_7 = x_50;
goto _start;
}
}
else
{
lean_object* x_61; 
lean_dec(x_21);
lean_dec(x_18);
x_61 = lean_array_push(x_16, x_11);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 0, x_61);
x_4 = x_13;
x_5 = x_19;
x_7 = x_22;
goto _start;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_19, 0);
x_64 = lean_ctor_get(x_19, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_19);
x_65 = lean_unbox(x_63);
x_66 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_65, x_15);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_67 = x_11;
} else {
 lean_dec_ref(x_11);
 x_67 = lean_box(0);
}
x_68 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_64);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_unbox(x_63);
lean_dec(x_63);
x_73 = l_Lean_IR_ExplicitBoxing_mkCast(x_18, x_72);
x_74 = lean_box(13);
lean_inc(x_69);
x_75 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set(x_75, 2, x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*3, x_15);
if (lean_is_scalar(x_67)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_67;
}
lean_ctor_set(x_76, 0, x_69);
x_77 = lean_array_push(x_16, x_76);
x_78 = lean_array_push(x_17, x_75);
if (lean_is_scalar(x_71)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_71;
}
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_4 = x_13;
x_5 = x_79;
x_7 = x_70;
goto _start;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_63);
lean_dec(x_18);
x_81 = lean_array_push(x_16, x_11);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_17);
x_4 = x_13;
x_5 = x_82;
x_7 = x_64;
goto _start;
}
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_5);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_5, 0);
x_86 = lean_array_push(x_85, x_11);
lean_ctor_set(x_5, 0, x_86);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_5, 0);
x_89 = lean_ctor_get(x_5, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_5);
x_90 = lean_array_push(x_88, x_11);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_4 = x_13;
x_5 = x_91;
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
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_11, 0);
lean_dec(x_27);
x_28 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_unbox(x_22);
lean_dec(x_22);
x_33 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_32);
x_34 = lean_box(13);
lean_inc(x_30);
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_16);
lean_ctor_set(x_11, 0, x_30);
x_36 = lean_array_push(x_17, x_11);
x_37 = lean_array_push(x_18, x_35);
lean_ctor_set(x_28, 1, x_37);
lean_ctor_set(x_28, 0, x_36);
x_4 = x_13;
x_5 = x_28;
x_7 = x_31;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
x_41 = lean_unbox(x_22);
lean_dec(x_22);
x_42 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_41);
x_43 = lean_box(13);
lean_inc(x_39);
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_16);
lean_ctor_set(x_11, 0, x_39);
x_45 = lean_array_push(x_17, x_11);
x_46 = lean_array_push(x_18, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_4 = x_13;
x_5 = x_47;
x_7 = x_40;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_11);
x_49 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_unbox(x_22);
lean_dec(x_22);
x_54 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_53);
x_55 = lean_box(13);
lean_inc(x_50);
x_56 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_16);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_50);
x_58 = lean_array_push(x_17, x_57);
x_59 = lean_array_push(x_18, x_56);
if (lean_is_scalar(x_52)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_52;
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_4 = x_13;
x_5 = x_60;
x_7 = x_51;
goto _start;
}
}
else
{
lean_object* x_62; 
lean_dec(x_22);
lean_dec(x_19);
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
x_66 = lean_unbox(x_64);
x_67 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_66, x_16);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
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
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_unbox(x_64);
lean_dec(x_64);
x_74 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_73);
x_75 = lean_box(13);
lean_inc(x_70);
x_76 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_16);
if (lean_is_scalar(x_68)) {
 x_77 = lean_alloc_ctor(0, 1, 0);
} else {
 x_77 = x_68;
}
lean_ctor_set(x_77, 0, x_70);
x_78 = lean_array_push(x_17, x_77);
x_79 = lean_array_push(x_18, x_76);
if (lean_is_scalar(x_72)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_72;
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_4 = x_13;
x_5 = x_80;
x_7 = x_71;
goto _start;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_64);
lean_dec(x_19);
x_82 = lean_array_push(x_17, x_11);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_18);
x_4 = x_13;
x_5 = x_83;
x_7 = x_65;
goto _start;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_15);
x_85 = !lean_is_exclusive(x_5);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_5, 0);
x_87 = lean_array_push(x_86, x_11);
lean_ctor_set(x_5, 0, x_87);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_5, 0);
x_90 = lean_ctor_get(x_5, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_5);
x_91 = lean_array_push(x_89, x_11);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_4 = x_13;
x_5 = x_92;
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
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_10, 0);
lean_dec(x_24);
x_25 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_19);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_unbox(x_18);
lean_dec(x_18);
x_30 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_29);
x_31 = lean_box(13);
lean_inc(x_27);
x_32 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_20);
lean_ctor_set(x_10, 0, x_27);
x_33 = lean_array_push(x_13, x_10);
x_34 = lean_array_push(x_14, x_32);
lean_ctor_set(x_25, 1, x_34);
lean_ctor_set(x_25, 0, x_33);
x_3 = x_12;
x_4 = x_25;
x_6 = x_28;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_unbox(x_18);
lean_dec(x_18);
x_39 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_38);
x_40 = lean_box(13);
lean_inc(x_36);
x_41 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_20);
lean_ctor_set(x_10, 0, x_36);
x_42 = lean_array_push(x_13, x_10);
x_43 = lean_array_push(x_14, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_3 = x_12;
x_4 = x_44;
x_6 = x_37;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_10);
x_46 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_19);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_unbox(x_18);
lean_dec(x_18);
x_51 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_50);
x_52 = lean_box(13);
lean_inc(x_47);
x_53 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_20);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_47);
x_55 = lean_array_push(x_13, x_54);
x_56 = lean_array_push(x_14, x_53);
if (lean_is_scalar(x_49)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_49;
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_3 = x_12;
x_4 = x_57;
x_6 = x_48;
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
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_16, 0);
x_62 = lean_ctor_get(x_16, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_16);
x_63 = 7;
x_64 = lean_unbox(x_61);
x_65 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_64, x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
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
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = lean_unbox(x_61);
lean_dec(x_61);
x_72 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_71);
x_73 = lean_box(13);
lean_inc(x_68);
x_74 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_72);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*3, x_63);
if (lean_is_scalar(x_66)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_66;
}
lean_ctor_set(x_75, 0, x_68);
x_76 = lean_array_push(x_13, x_75);
x_77 = lean_array_push(x_14, x_74);
if (lean_is_scalar(x_70)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_70;
}
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_3 = x_12;
x_4 = x_78;
x_6 = x_69;
goto _start;
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_61);
lean_dec(x_15);
x_80 = lean_array_push(x_13, x_10);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_14);
x_3 = x_12;
x_4 = x_81;
x_6 = x_62;
goto _start;
}
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_4);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_4, 0);
x_85 = lean_array_push(x_84, x_10);
lean_ctor_set(x_4, 0, x_85);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_4, 0);
x_88 = lean_ctor_get(x_4, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_4);
x_89 = lean_array_push(x_87, x_10);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_3 = x_12;
x_4 = x_90;
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
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = l_Lean_IR_ExplicitBoxing_mkCast(x_11, x_4);
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_5);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_2);
x_14 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_4);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
lean_inc(x_15);
x_17 = l_Lean_IR_ExplicitBoxing_mkCast(x_15, x_4);
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_5);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_2);
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_4);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 2, x_5);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
return x_22;
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
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_11, 0);
lean_dec(x_27);
x_28 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_unbox(x_22);
lean_dec(x_22);
x_33 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_32);
x_34 = lean_box(13);
lean_inc(x_30);
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_16);
lean_ctor_set(x_11, 0, x_30);
x_36 = lean_array_push(x_17, x_11);
x_37 = lean_array_push(x_18, x_35);
lean_ctor_set(x_28, 1, x_37);
lean_ctor_set(x_28, 0, x_36);
x_4 = x_13;
x_5 = x_28;
x_7 = x_31;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
x_41 = lean_unbox(x_22);
lean_dec(x_22);
x_42 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_41);
x_43 = lean_box(13);
lean_inc(x_39);
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_16);
lean_ctor_set(x_11, 0, x_39);
x_45 = lean_array_push(x_17, x_11);
x_46 = lean_array_push(x_18, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_4 = x_13;
x_5 = x_47;
x_7 = x_40;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_11);
x_49 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_unbox(x_22);
lean_dec(x_22);
x_54 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_53);
x_55 = lean_box(13);
lean_inc(x_50);
x_56 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_16);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_50);
x_58 = lean_array_push(x_17, x_57);
x_59 = lean_array_push(x_18, x_56);
if (lean_is_scalar(x_52)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_52;
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_4 = x_13;
x_5 = x_60;
x_7 = x_51;
goto _start;
}
}
else
{
lean_object* x_62; 
lean_dec(x_22);
lean_dec(x_19);
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
x_66 = lean_unbox(x_64);
x_67 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_66, x_16);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
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
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_unbox(x_64);
lean_dec(x_64);
x_74 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_73);
x_75 = lean_box(13);
lean_inc(x_70);
x_76 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_16);
if (lean_is_scalar(x_68)) {
 x_77 = lean_alloc_ctor(0, 1, 0);
} else {
 x_77 = x_68;
}
lean_ctor_set(x_77, 0, x_70);
x_78 = lean_array_push(x_17, x_77);
x_79 = lean_array_push(x_18, x_76);
if (lean_is_scalar(x_72)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_72;
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_4 = x_13;
x_5 = x_80;
x_7 = x_71;
goto _start;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_64);
lean_dec(x_19);
x_82 = lean_array_push(x_17, x_11);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_18);
x_4 = x_13;
x_5 = x_83;
x_7 = x_65;
goto _start;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_15);
x_85 = !lean_is_exclusive(x_5);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_5, 0);
x_87 = lean_array_push(x_86, x_11);
lean_ctor_set(x_5, 0, x_87);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_5, 0);
x_90 = lean_ctor_get(x_5, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_5);
x_91 = lean_array_push(x_89, x_11);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_4 = x_13;
x_5 = x_92;
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
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_11, 0);
lean_dec(x_27);
x_28 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_unbox(x_22);
lean_dec(x_22);
x_33 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_32);
x_34 = lean_box(13);
lean_inc(x_30);
x_35 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_16);
lean_ctor_set(x_11, 0, x_30);
x_36 = lean_array_push(x_17, x_11);
x_37 = lean_array_push(x_18, x_35);
lean_ctor_set(x_28, 1, x_37);
lean_ctor_set(x_28, 0, x_36);
x_4 = x_13;
x_5 = x_28;
x_7 = x_31;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
x_41 = lean_unbox(x_22);
lean_dec(x_22);
x_42 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_41);
x_43 = lean_box(13);
lean_inc(x_39);
x_44 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_16);
lean_ctor_set(x_11, 0, x_39);
x_45 = lean_array_push(x_17, x_11);
x_46 = lean_array_push(x_18, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_4 = x_13;
x_5 = x_47;
x_7 = x_40;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_11);
x_49 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_23);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_unbox(x_22);
lean_dec(x_22);
x_54 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_53);
x_55 = lean_box(13);
lean_inc(x_50);
x_56 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_16);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_50);
x_58 = lean_array_push(x_17, x_57);
x_59 = lean_array_push(x_18, x_56);
if (lean_is_scalar(x_52)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_52;
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_4 = x_13;
x_5 = x_60;
x_7 = x_51;
goto _start;
}
}
else
{
lean_object* x_62; 
lean_dec(x_22);
lean_dec(x_19);
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
x_66 = lean_unbox(x_64);
x_67 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_66, x_16);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
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
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_unbox(x_64);
lean_dec(x_64);
x_74 = l_Lean_IR_ExplicitBoxing_mkCast(x_19, x_73);
x_75 = lean_box(13);
lean_inc(x_70);
x_76 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*3, x_16);
if (lean_is_scalar(x_68)) {
 x_77 = lean_alloc_ctor(0, 1, 0);
} else {
 x_77 = x_68;
}
lean_ctor_set(x_77, 0, x_70);
x_78 = lean_array_push(x_17, x_77);
x_79 = lean_array_push(x_18, x_76);
if (lean_is_scalar(x_72)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_72;
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_4 = x_13;
x_5 = x_80;
x_7 = x_71;
goto _start;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_64);
lean_dec(x_19);
x_82 = lean_array_push(x_17, x_11);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_18);
x_4 = x_13;
x_5 = x_83;
x_7 = x_65;
goto _start;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_15);
x_85 = !lean_is_exclusive(x_5);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_5, 0);
x_87 = lean_array_push(x_86, x_11);
lean_ctor_set(x_5, 0, x_87);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_5, 0);
x_90 = lean_ctor_get(x_5, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_5);
x_91 = lean_array_push(x_89, x_11);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_4 = x_13;
x_5 = x_92;
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
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
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
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_inc(x_6);
lean_inc(x_4);
x_12 = l_Lean_IR_LocalContext_addLocal(x_8, x_4, x_5, x_6);
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_9);
x_14 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_7, x_13, x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr(x_4, x_5, x_6, x_15, x_2, x_16);
lean_dec(x_2);
return x_17;
}
case 1:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_unsigned_to_nat(0u);
lean_inc(x_24);
x_29 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_21, x_21, x_28, x_24);
lean_inc(x_27);
lean_inc(x_26);
lean_ctor_set(x_2, 0, x_29);
x_30 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_22, x_2, x_3);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_31);
lean_inc(x_21);
lean_inc(x_20);
x_33 = l_Lean_IR_LocalContext_addJP(x_24, x_20, x_21, x_31);
x_34 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_27);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_25);
x_35 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_23, x_34, x_32);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_ctor_set(x_1, 3, x_37);
lean_ctor_set(x_1, 2, x_31);
lean_ctor_set(x_35, 0, x_1);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_35);
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 2);
x_44 = lean_ctor_get(x_1, 3);
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_47 = lean_ctor_get(x_2, 1);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_45);
lean_dec(x_2);
x_49 = lean_unsigned_to_nat(0u);
lean_inc(x_45);
x_50 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_42, x_42, x_49, x_45);
lean_inc(x_48);
lean_inc(x_47);
x_51 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set_uint8(x_51, sizeof(void*)*3, x_46);
x_52 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_43, x_51, x_3);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_53);
lean_inc(x_42);
lean_inc(x_41);
x_55 = l_Lean_IR_LocalContext_addJP(x_45, x_41, x_42, x_53);
x_56 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_47);
lean_ctor_set(x_56, 2, x_48);
lean_ctor_set_uint8(x_56, sizeof(void*)*3, x_46);
x_57 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_44, x_56, x_54);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
lean_ctor_set(x_1, 3, x_58);
lean_ctor_set(x_1, 2, x_53);
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_62 = lean_ctor_get(x_1, 0);
x_63 = lean_ctor_get(x_1, 1);
x_64 = lean_ctor_get(x_1, 2);
x_65 = lean_ctor_get(x_1, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_1);
x_66 = lean_ctor_get(x_2, 0);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_68 = lean_ctor_get(x_2, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_2, 2);
lean_inc(x_69);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_70 = x_2;
} else {
 lean_dec_ref(x_2);
 x_70 = lean_box(0);
}
x_71 = lean_unsigned_to_nat(0u);
lean_inc(x_66);
x_72 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_63, x_63, x_71, x_66);
lean_inc(x_69);
lean_inc(x_68);
if (lean_is_scalar(x_70)) {
 x_73 = lean_alloc_ctor(0, 3, 1);
} else {
 x_73 = x_70;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
lean_ctor_set(x_73, 2, x_69);
lean_ctor_set_uint8(x_73, sizeof(void*)*3, x_67);
x_74 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_64, x_73, x_3);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_75);
lean_inc(x_63);
lean_inc(x_62);
x_77 = l_Lean_IR_LocalContext_addJP(x_66, x_62, x_63, x_75);
x_78 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_68);
lean_ctor_set(x_78, 2, x_69);
lean_ctor_set_uint8(x_78, sizeof(void*)*3, x_67);
x_79 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_65, x_78, x_76);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_83, 0, x_62);
lean_ctor_set(x_83, 1, x_63);
lean_ctor_set(x_83, 2, x_75);
lean_ctor_set(x_83, 3, x_80);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
case 4:
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_1);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_86 = lean_ctor_get(x_1, 2);
x_87 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_88 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_87, x_2, x_3);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_IR_ExplicitBoxing_getVarType(x_86, x_2, x_90);
lean_dec(x_2);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_ctor_get(x_91, 1);
x_95 = 5;
x_96 = lean_unbox(x_93);
x_97 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_96, x_95);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
lean_free_object(x_91);
x_98 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_94);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_unbox(x_93);
lean_dec(x_93);
x_102 = l_Lean_IR_ExplicitBoxing_mkCast(x_86, x_101);
lean_inc(x_100);
lean_ctor_set(x_1, 3, x_89);
lean_ctor_set(x_1, 2, x_100);
x_103 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_1);
lean_ctor_set_uint8(x_103, sizeof(void*)*3, x_95);
lean_ctor_set(x_98, 0, x_103);
return x_98;
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_98, 0);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_98);
x_106 = lean_unbox(x_93);
lean_dec(x_93);
x_107 = l_Lean_IR_ExplicitBoxing_mkCast(x_86, x_106);
lean_inc(x_104);
lean_ctor_set(x_1, 3, x_89);
lean_ctor_set(x_1, 2, x_104);
x_108 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_108, 2, x_1);
lean_ctor_set_uint8(x_108, sizeof(void*)*3, x_95);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_105);
return x_109;
}
}
else
{
lean_dec(x_93);
lean_ctor_set(x_1, 3, x_89);
lean_ctor_set(x_91, 0, x_1);
return x_91;
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; 
x_110 = lean_ctor_get(x_91, 0);
x_111 = lean_ctor_get(x_91, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_91);
x_112 = 5;
x_113 = lean_unbox(x_110);
x_114 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_113, x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_115 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_111);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
x_119 = lean_unbox(x_110);
lean_dec(x_110);
x_120 = l_Lean_IR_ExplicitBoxing_mkCast(x_86, x_119);
lean_inc(x_116);
lean_ctor_set(x_1, 3, x_89);
lean_ctor_set(x_1, 2, x_116);
x_121 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_121, 2, x_1);
lean_ctor_set_uint8(x_121, sizeof(void*)*3, x_112);
if (lean_is_scalar(x_118)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_118;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_117);
return x_122;
}
else
{
lean_object* x_123; 
lean_dec(x_110);
lean_ctor_set(x_1, 3, x_89);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_1);
lean_ctor_set(x_123, 1, x_111);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; 
x_124 = lean_ctor_get(x_1, 0);
x_125 = lean_ctor_get(x_1, 1);
x_126 = lean_ctor_get(x_1, 2);
x_127 = lean_ctor_get(x_1, 3);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_1);
lean_inc(x_2);
x_128 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_127, x_2, x_3);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_IR_ExplicitBoxing_getVarType(x_126, x_2, x_130);
lean_dec(x_2);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
x_135 = 5;
x_136 = lean_unbox(x_132);
x_137 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_136, x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_134);
x_138 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_133);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = lean_unbox(x_132);
lean_dec(x_132);
x_143 = l_Lean_IR_ExplicitBoxing_mkCast(x_126, x_142);
lean_inc(x_139);
x_144 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_144, 0, x_124);
lean_ctor_set(x_144, 1, x_125);
lean_ctor_set(x_144, 2, x_139);
lean_ctor_set(x_144, 3, x_129);
x_145 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_145, 0, x_139);
lean_ctor_set(x_145, 1, x_143);
lean_ctor_set(x_145, 2, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*3, x_135);
if (lean_is_scalar(x_141)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_141;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_140);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_132);
x_147 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_147, 0, x_124);
lean_ctor_set(x_147, 1, x_125);
lean_ctor_set(x_147, 2, x_126);
lean_ctor_set(x_147, 3, x_129);
if (lean_is_scalar(x_134)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_134;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_133);
return x_148;
}
}
}
case 5:
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_1);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_150 = lean_ctor_get(x_1, 3);
x_151 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_152 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
x_153 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_152, x_2, x_3);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_Lean_IR_ExplicitBoxing_getVarType(x_150, x_2, x_155);
lean_dec(x_2);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; uint8_t x_161; 
x_158 = lean_ctor_get(x_156, 0);
x_159 = lean_ctor_get(x_156, 1);
x_160 = lean_unbox(x_158);
x_161 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_160, x_151);
if (x_161 == 0)
{
lean_object* x_162; uint8_t x_163; 
lean_free_object(x_156);
x_162 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_159);
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; 
x_164 = lean_ctor_get(x_162, 0);
x_165 = lean_unbox(x_158);
lean_dec(x_158);
x_166 = l_Lean_IR_ExplicitBoxing_mkCast(x_150, x_165);
lean_inc(x_164);
lean_ctor_set(x_1, 4, x_154);
lean_ctor_set(x_1, 3, x_164);
x_167 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_166);
lean_ctor_set(x_167, 2, x_1);
lean_ctor_set_uint8(x_167, sizeof(void*)*3, x_151);
lean_ctor_set(x_162, 0, x_167);
return x_162;
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_168 = lean_ctor_get(x_162, 0);
x_169 = lean_ctor_get(x_162, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_162);
x_170 = lean_unbox(x_158);
lean_dec(x_158);
x_171 = l_Lean_IR_ExplicitBoxing_mkCast(x_150, x_170);
lean_inc(x_168);
lean_ctor_set(x_1, 4, x_154);
lean_ctor_set(x_1, 3, x_168);
x_172 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_172, 2, x_1);
lean_ctor_set_uint8(x_172, sizeof(void*)*3, x_151);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_169);
return x_173;
}
}
else
{
lean_dec(x_158);
lean_ctor_set(x_1, 4, x_154);
lean_ctor_set(x_156, 0, x_1);
return x_156;
}
}
else
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_177; 
x_174 = lean_ctor_get(x_156, 0);
x_175 = lean_ctor_get(x_156, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_156);
x_176 = lean_unbox(x_174);
x_177 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_176, x_151);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_178 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_175);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
x_182 = lean_unbox(x_174);
lean_dec(x_174);
x_183 = l_Lean_IR_ExplicitBoxing_mkCast(x_150, x_182);
lean_inc(x_179);
lean_ctor_set(x_1, 4, x_154);
lean_ctor_set(x_1, 3, x_179);
x_184 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_184, 0, x_179);
lean_ctor_set(x_184, 1, x_183);
lean_ctor_set(x_184, 2, x_1);
lean_ctor_set_uint8(x_184, sizeof(void*)*3, x_151);
if (lean_is_scalar(x_181)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_181;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_180);
return x_185;
}
else
{
lean_object* x_186; 
lean_dec(x_174);
lean_ctor_set(x_1, 4, x_154);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_1);
lean_ctor_set(x_186, 1, x_175);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; 
x_187 = lean_ctor_get(x_1, 0);
x_188 = lean_ctor_get(x_1, 1);
x_189 = lean_ctor_get(x_1, 2);
x_190 = lean_ctor_get(x_1, 3);
x_191 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
x_192 = lean_ctor_get(x_1, 4);
lean_inc(x_192);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_1);
lean_inc(x_2);
x_193 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_192, x_2, x_3);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l_Lean_IR_ExplicitBoxing_getVarType(x_190, x_2, x_195);
lean_dec(x_2);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
x_200 = lean_unbox(x_197);
x_201 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_200, x_191);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_199);
x_202 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_198);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
x_206 = lean_unbox(x_197);
lean_dec(x_197);
x_207 = l_Lean_IR_ExplicitBoxing_mkCast(x_190, x_206);
lean_inc(x_203);
x_208 = lean_alloc_ctor(5, 5, 1);
lean_ctor_set(x_208, 0, x_187);
lean_ctor_set(x_208, 1, x_188);
lean_ctor_set(x_208, 2, x_189);
lean_ctor_set(x_208, 3, x_203);
lean_ctor_set(x_208, 4, x_194);
lean_ctor_set_uint8(x_208, sizeof(void*)*5, x_191);
x_209 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_209, 0, x_203);
lean_ctor_set(x_209, 1, x_207);
lean_ctor_set(x_209, 2, x_208);
lean_ctor_set_uint8(x_209, sizeof(void*)*3, x_191);
if (lean_is_scalar(x_205)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_205;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_204);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_197);
x_211 = lean_alloc_ctor(5, 5, 1);
lean_ctor_set(x_211, 0, x_187);
lean_ctor_set(x_211, 1, x_188);
lean_ctor_set(x_211, 2, x_189);
lean_ctor_set(x_211, 3, x_190);
lean_ctor_set(x_211, 4, x_194);
lean_ctor_set_uint8(x_211, sizeof(void*)*5, x_191);
if (lean_is_scalar(x_199)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_199;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_198);
return x_212;
}
}
}
case 9:
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_1);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_214 = lean_ctor_get(x_1, 1);
x_215 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_214, x_2, x_3);
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_215, 0);
lean_ctor_set(x_1, 1, x_217);
lean_ctor_set(x_215, 0, x_1);
return x_215;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_215, 0);
x_219 = lean_ctor_get(x_215, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_215);
lean_ctor_set(x_1, 1, x_218);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_1);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_221 = lean_ctor_get(x_1, 0);
x_222 = lean_ctor_get(x_1, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_1);
x_223 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_222, x_2, x_3);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_226 = x_223;
} else {
 lean_dec_ref(x_223);
 x_226 = lean_box(0);
}
x_227 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_227, 0, x_221);
lean_ctor_set(x_227, 1, x_224);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_225);
return x_228;
}
}
case 10:
{
uint8_t x_229; 
x_229 = !lean_is_exclusive(x_1);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_230 = lean_ctor_get(x_1, 1);
x_231 = lean_ctor_get(x_1, 2);
x_232 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_231);
x_233 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_234 = l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(x_233, x_231, x_2, x_3);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = l_Lean_IR_ExplicitBoxing_getVarType(x_230, x_2, x_236);
lean_dec(x_2);
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; uint8_t x_242; 
x_239 = lean_ctor_get(x_237, 0);
x_240 = lean_ctor_get(x_237, 1);
x_241 = lean_unbox(x_239);
x_242 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_241, x_232);
if (x_242 == 0)
{
lean_object* x_243; uint8_t x_244; 
lean_free_object(x_237);
x_243 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_240);
x_244 = !lean_is_exclusive(x_243);
if (x_244 == 0)
{
lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_243, 0);
x_246 = lean_unbox(x_239);
lean_dec(x_239);
x_247 = l_Lean_IR_ExplicitBoxing_mkCast(x_230, x_246);
lean_inc(x_245);
lean_ctor_set(x_1, 2, x_235);
lean_ctor_set(x_1, 1, x_245);
x_248 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_247);
lean_ctor_set(x_248, 2, x_1);
lean_ctor_set_uint8(x_248, sizeof(void*)*3, x_232);
lean_ctor_set(x_243, 0, x_248);
return x_243;
}
else
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_249 = lean_ctor_get(x_243, 0);
x_250 = lean_ctor_get(x_243, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_243);
x_251 = lean_unbox(x_239);
lean_dec(x_239);
x_252 = l_Lean_IR_ExplicitBoxing_mkCast(x_230, x_251);
lean_inc(x_249);
lean_ctor_set(x_1, 2, x_235);
lean_ctor_set(x_1, 1, x_249);
x_253 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_253, 0, x_249);
lean_ctor_set(x_253, 1, x_252);
lean_ctor_set(x_253, 2, x_1);
lean_ctor_set_uint8(x_253, sizeof(void*)*3, x_232);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_250);
return x_254;
}
}
else
{
lean_dec(x_239);
lean_ctor_set(x_1, 2, x_235);
lean_ctor_set(x_237, 0, x_1);
return x_237;
}
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; uint8_t x_258; 
x_255 = lean_ctor_get(x_237, 0);
x_256 = lean_ctor_get(x_237, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_237);
x_257 = lean_unbox(x_255);
x_258 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_257, x_232);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_259 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_256);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_262 = x_259;
} else {
 lean_dec_ref(x_259);
 x_262 = lean_box(0);
}
x_263 = lean_unbox(x_255);
lean_dec(x_255);
x_264 = l_Lean_IR_ExplicitBoxing_mkCast(x_230, x_263);
lean_inc(x_260);
lean_ctor_set(x_1, 2, x_235);
lean_ctor_set(x_1, 1, x_260);
x_265 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_265, 0, x_260);
lean_ctor_set(x_265, 1, x_264);
lean_ctor_set(x_265, 2, x_1);
lean_ctor_set_uint8(x_265, sizeof(void*)*3, x_232);
if (lean_is_scalar(x_262)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_262;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_261);
return x_266;
}
else
{
lean_object* x_267; 
lean_dec(x_255);
lean_ctor_set(x_1, 2, x_235);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_1);
lean_ctor_set(x_267, 1, x_256);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; uint8_t x_281; 
x_268 = lean_ctor_get(x_1, 0);
x_269 = lean_ctor_get(x_1, 1);
x_270 = lean_ctor_get(x_1, 2);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_1);
x_271 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_270);
x_272 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_273 = l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__1(x_272, x_270, x_2, x_3);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = l_Lean_IR_ExplicitBoxing_getVarType(x_269, x_2, x_275);
lean_dec(x_2);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_279 = x_276;
} else {
 lean_dec_ref(x_276);
 x_279 = lean_box(0);
}
x_280 = lean_unbox(x_277);
x_281 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_280, x_271);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_279);
x_282 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_278);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_285 = x_282;
} else {
 lean_dec_ref(x_282);
 x_285 = lean_box(0);
}
x_286 = lean_unbox(x_277);
lean_dec(x_277);
x_287 = l_Lean_IR_ExplicitBoxing_mkCast(x_269, x_286);
lean_inc(x_283);
x_288 = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(x_288, 0, x_268);
lean_ctor_set(x_288, 1, x_283);
lean_ctor_set(x_288, 2, x_274);
x_289 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_289, 0, x_283);
lean_ctor_set(x_289, 1, x_287);
lean_ctor_set(x_289, 2, x_288);
lean_ctor_set_uint8(x_289, sizeof(void*)*3, x_271);
if (lean_is_scalar(x_285)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_285;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_284);
return x_290;
}
else
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_277);
x_291 = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(x_291, 0, x_268);
lean_ctor_set(x_291, 1, x_269);
lean_ctor_set(x_291, 2, x_274);
if (lean_is_scalar(x_279)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_279;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_278);
return x_292;
}
}
}
case 11:
{
uint8_t x_293; 
x_293 = !lean_is_exclusive(x_1);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_1, 0);
x_295 = l_Lean_IR_ExplicitBoxing_getResultType(x_2, x_3);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = !lean_is_exclusive(x_294);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_299 = lean_ctor_get(x_294, 0);
x_300 = l_Lean_IR_ExplicitBoxing_getVarType(x_299, x_2, x_297);
lean_dec(x_2);
x_301 = !lean_is_exclusive(x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; uint8_t x_305; uint8_t x_306; 
x_302 = lean_ctor_get(x_300, 0);
x_303 = lean_ctor_get(x_300, 1);
x_304 = lean_unbox(x_302);
x_305 = lean_unbox(x_296);
x_306 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_304, x_305);
if (x_306 == 0)
{
lean_object* x_307; uint8_t x_308; 
lean_free_object(x_300);
x_307 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_303);
x_308 = !lean_is_exclusive(x_307);
if (x_308 == 0)
{
lean_object* x_309; uint8_t x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; 
x_309 = lean_ctor_get(x_307, 0);
x_310 = lean_unbox(x_302);
lean_dec(x_302);
x_311 = l_Lean_IR_ExplicitBoxing_mkCast(x_299, x_310);
lean_inc(x_309);
lean_ctor_set(x_294, 0, x_309);
x_312 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_311);
lean_ctor_set(x_312, 2, x_1);
x_313 = lean_unbox(x_296);
lean_dec(x_296);
lean_ctor_set_uint8(x_312, sizeof(void*)*3, x_313);
lean_ctor_set(x_307, 0, x_312);
return x_307;
}
else
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; lean_object* x_320; 
x_314 = lean_ctor_get(x_307, 0);
x_315 = lean_ctor_get(x_307, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_307);
x_316 = lean_unbox(x_302);
lean_dec(x_302);
x_317 = l_Lean_IR_ExplicitBoxing_mkCast(x_299, x_316);
lean_inc(x_314);
lean_ctor_set(x_294, 0, x_314);
x_318 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_318, 0, x_314);
lean_ctor_set(x_318, 1, x_317);
lean_ctor_set(x_318, 2, x_1);
x_319 = lean_unbox(x_296);
lean_dec(x_296);
lean_ctor_set_uint8(x_318, sizeof(void*)*3, x_319);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_315);
return x_320;
}
}
else
{
lean_dec(x_302);
lean_dec(x_296);
lean_ctor_set(x_300, 0, x_1);
return x_300;
}
}
else
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; uint8_t x_324; uint8_t x_325; 
x_321 = lean_ctor_get(x_300, 0);
x_322 = lean_ctor_get(x_300, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_300);
x_323 = lean_unbox(x_321);
x_324 = lean_unbox(x_296);
x_325 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_323, x_324);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; 
x_326 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_322);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_329 = x_326;
} else {
 lean_dec_ref(x_326);
 x_329 = lean_box(0);
}
x_330 = lean_unbox(x_321);
lean_dec(x_321);
x_331 = l_Lean_IR_ExplicitBoxing_mkCast(x_299, x_330);
lean_inc(x_327);
lean_ctor_set(x_294, 0, x_327);
x_332 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_332, 0, x_327);
lean_ctor_set(x_332, 1, x_331);
lean_ctor_set(x_332, 2, x_1);
x_333 = lean_unbox(x_296);
lean_dec(x_296);
lean_ctor_set_uint8(x_332, sizeof(void*)*3, x_333);
if (lean_is_scalar(x_329)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_329;
}
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_328);
return x_334;
}
else
{
lean_object* x_335; 
lean_dec(x_321);
lean_dec(x_296);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_1);
lean_ctor_set(x_335, 1, x_322);
return x_335;
}
}
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; uint8_t x_342; uint8_t x_343; 
x_336 = lean_ctor_get(x_294, 0);
lean_inc(x_336);
lean_dec(x_294);
x_337 = l_Lean_IR_ExplicitBoxing_getVarType(x_336, x_2, x_297);
lean_dec(x_2);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_340 = x_337;
} else {
 lean_dec_ref(x_337);
 x_340 = lean_box(0);
}
x_341 = lean_unbox(x_338);
x_342 = lean_unbox(x_296);
x_343 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_341, x_342);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; 
lean_dec(x_340);
x_344 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_339);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_347 = x_344;
} else {
 lean_dec_ref(x_344);
 x_347 = lean_box(0);
}
x_348 = lean_unbox(x_338);
lean_dec(x_338);
x_349 = l_Lean_IR_ExplicitBoxing_mkCast(x_336, x_348);
lean_inc(x_345);
x_350 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_350, 0, x_345);
lean_ctor_set(x_1, 0, x_350);
x_351 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_351, 0, x_345);
lean_ctor_set(x_351, 1, x_349);
lean_ctor_set(x_351, 2, x_1);
x_352 = lean_unbox(x_296);
lean_dec(x_296);
lean_ctor_set_uint8(x_351, sizeof(void*)*3, x_352);
if (lean_is_scalar(x_347)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_347;
}
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_346);
return x_353;
}
else
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_338);
lean_dec(x_296);
x_354 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_354, 0, x_336);
lean_ctor_set(x_1, 0, x_354);
if (lean_is_scalar(x_340)) {
 x_355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_355 = x_340;
}
lean_ctor_set(x_355, 0, x_1);
lean_ctor_set(x_355, 1, x_339);
return x_355;
}
}
}
else
{
uint8_t x_356; 
lean_dec(x_2);
x_356 = !lean_is_exclusive(x_295);
if (x_356 == 0)
{
lean_object* x_357; 
x_357 = lean_ctor_get(x_295, 0);
lean_dec(x_357);
lean_ctor_set(x_295, 0, x_1);
return x_295;
}
else
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_295, 1);
lean_inc(x_358);
lean_dec(x_295);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_1);
lean_ctor_set(x_359, 1, x_358);
return x_359;
}
}
}
else
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_1, 0);
lean_inc(x_360);
lean_dec(x_1);
x_361 = l_Lean_IR_ExplicitBoxing_getResultType(x_2, x_3);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; uint8_t x_371; uint8_t x_372; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = lean_ctor_get(x_360, 0);
lean_inc(x_364);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 x_365 = x_360;
} else {
 lean_dec_ref(x_360);
 x_365 = lean_box(0);
}
x_366 = l_Lean_IR_ExplicitBoxing_getVarType(x_364, x_2, x_363);
lean_dec(x_2);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_369 = x_366;
} else {
 lean_dec_ref(x_366);
 x_369 = lean_box(0);
}
x_370 = lean_unbox(x_367);
x_371 = lean_unbox(x_362);
x_372 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_370, x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; 
lean_dec(x_369);
x_373 = l_Lean_IR_ExplicitBoxing_mkFresh___rarg(x_368);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_376 = x_373;
} else {
 lean_dec_ref(x_373);
 x_376 = lean_box(0);
}
x_377 = lean_unbox(x_367);
lean_dec(x_367);
x_378 = l_Lean_IR_ExplicitBoxing_mkCast(x_364, x_377);
lean_inc(x_374);
if (lean_is_scalar(x_365)) {
 x_379 = lean_alloc_ctor(0, 1, 0);
} else {
 x_379 = x_365;
}
lean_ctor_set(x_379, 0, x_374);
x_380 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_380, 0, x_379);
x_381 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_381, 0, x_374);
lean_ctor_set(x_381, 1, x_378);
lean_ctor_set(x_381, 2, x_380);
x_382 = lean_unbox(x_362);
lean_dec(x_362);
lean_ctor_set_uint8(x_381, sizeof(void*)*3, x_382);
if (lean_is_scalar(x_376)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_376;
}
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_375);
return x_383;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_367);
lean_dec(x_362);
if (lean_is_scalar(x_365)) {
 x_384 = lean_alloc_ctor(0, 1, 0);
} else {
 x_384 = x_365;
}
lean_ctor_set(x_384, 0, x_364);
x_385 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_385, 0, x_384);
if (lean_is_scalar(x_369)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_369;
}
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_368);
return x_386;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_2);
x_387 = lean_ctor_get(x_361, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_388 = x_361;
} else {
 lean_dec_ref(x_361);
 x_388 = lean_box(0);
}
x_389 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_389, 0, x_360);
if (lean_is_scalar(x_388)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_388;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_387);
return x_390;
}
}
}
case 12:
{
uint8_t x_391; 
x_391 = !lean_is_exclusive(x_1);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; 
x_392 = lean_ctor_get(x_1, 0);
x_393 = lean_ctor_get(x_1, 1);
x_394 = l_Lean_IR_ExplicitBoxing_getJPParams(x_392, x_2, x_3);
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec(x_394);
x_397 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(x_395, x_393, x_2, x_396);
lean_dec(x_2);
lean_dec(x_393);
lean_dec(x_395);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec(x_397);
x_400 = !lean_is_exclusive(x_398);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_398, 0);
x_402 = lean_ctor_get(x_398, 1);
lean_ctor_set(x_1, 1, x_401);
x_403 = l_Lean_IR_reshape(x_402, x_1);
lean_ctor_set(x_398, 1, x_399);
lean_ctor_set(x_398, 0, x_403);
return x_398;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_404 = lean_ctor_get(x_398, 0);
x_405 = lean_ctor_get(x_398, 1);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_398);
lean_ctor_set(x_1, 1, x_404);
x_406 = l_Lean_IR_reshape(x_405, x_1);
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_399);
return x_407;
}
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_408 = lean_ctor_get(x_1, 0);
x_409 = lean_ctor_get(x_1, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_1);
x_410 = l_Lean_IR_ExplicitBoxing_getJPParams(x_408, x_2, x_3);
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___at_Lean_IR_ExplicitBoxing_visitFnBody___main___spec__2(x_411, x_409, x_2, x_412);
lean_dec(x_2);
lean_dec(x_409);
lean_dec(x_411);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = lean_ctor_get(x_414, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_414, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_418 = x_414;
} else {
 lean_dec_ref(x_414);
 x_418 = lean_box(0);
}
x_419 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_419, 0, x_408);
lean_ctor_set(x_419, 1, x_416);
x_420 = l_Lean_IR_reshape(x_417, x_419);
if (lean_is_scalar(x_418)) {
 x_421 = lean_alloc_ctor(0, 2, 0);
} else {
 x_421 = x_418;
}
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_415);
return x_421;
}
}
default: 
{
lean_object* x_422; 
lean_dec(x_2);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_1);
lean_ctor_set(x_422, 1, x_3);
return x_422;
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
lean_object* l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_5);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = x_5;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_fget(x_5, x_4);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = x_11;
x_13 = lean_array_fset(x_5, x_4, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_19 = lean_ctor_get(x_10, 2);
lean_inc(x_19);
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_21 = l_Lean_IR_MaxIndex_collectDecl(x_10, x_20);
x_22 = lean_nat_add(x_21, x_14);
lean_dec(x_21);
lean_inc(x_3);
x_23 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_17, x_17, x_20, x_3);
lean_inc(x_1);
lean_inc(x_2);
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_1);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_18);
x_25 = l_Lean_IR_ExplicitBoxing_visitFnBody___main(x_19, x_24, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_18);
x_28 = x_27;
x_29 = lean_array_fset(x_13, x_4, x_28);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_inc(x_10);
x_31 = x_10;
x_32 = lean_array_fset(x_13, x_4, x_31);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_32;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_ExplicitBoxing_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Array_ummapAux___main___at_Lean_IR_ExplicitBoxing_run___spec__1(x_1, x_2, x_3, x_4, x_2);
x_6 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_5);
lean_dec(x_1);
return x_6;
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
lean_object* initialize_init_control_estate(lean_object*);
lean_object* initialize_init_control_reader(lean_object*);
lean_object* initialize_init_lean_runtime(lean_object*);
lean_object* initialize_init_lean_compiler_externattr(lean_object*);
lean_object* initialize_init_lean_compiler_ir_basic(lean_object*);
lean_object* initialize_init_lean_compiler_ir_compilerm(lean_object*);
lean_object* initialize_init_lean_compiler_ir_freevars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_compiler_ir_boxing(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_estate(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_control_reader(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_runtime(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_externattr(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_basic(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_freevars(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1);
l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1);
return w;
}
#ifdef __cplusplus
}
#endif
