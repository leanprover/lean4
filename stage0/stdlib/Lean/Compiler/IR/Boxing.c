// Lean compiler output
// Module: Lean.Compiler.IR.Boxing
// Imports: Init Lean.Runtime Lean.Compiler.ClosedTermCache Lean.Compiler.ExternAttr Lean.Compiler.IR.Basic Lean.Compiler.IR.CompilerM Lean.Compiler.IR.FreeVars Lean.Compiler.IR.ElimDeadVars
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
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
lean_object* l_Lean_IR_LocalContext_addParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getEnv(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getJPParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getResultType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getVarType(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___boxed(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_run___spec__1___at_Lean_IR_ExplicitBoxing_run___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withVDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_eqvTypes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withJDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getVarType___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_run___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__1;
static lean_object* l_Lean_IR_ExplicitBoxing_getDecl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedParam;
lean_object* l_Lean_IR_Decl_resultType(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_closureMaxArgs;
lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_getDecl___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_BoxingContext_f___default;
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_BoxingState_auxDecls___default;
static lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__2;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getScrutineeType(lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getScrutineeType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castVarIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_isBoxedName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_BoxingState_nextAuxId___default;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_mmodifyBody___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getJPParams(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_BoxingContext_localCtx___default;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_isBoxedName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withVDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getResultType___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_IR_LocalContext_getValue(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getEnv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_getInfo(lean_object*);
lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withJDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(lean_object*, size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_eqvTypes(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_BoxingContext_resultType___default;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_run___spec__1___at_Lean_IR_ExplicitBoxing_run___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lambda__1___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_run(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_BoxingState_auxDeclCache___default;
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_IR_ExplicitBoxing_mkCast___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_run___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_boxed", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_isBoxedName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_4 = lean_string_dec_eq(x_2, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_isBoxedName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ExplicitBoxing_isBoxedName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(lean_object* x_1) {
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = l_Lean_IR_IRType_isScalar(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
lean_dec(x_5);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_5);
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_1);
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
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_4);
x_13 = l_Array_anyMUnsafe_any___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(x_3, x_11, x_12);
lean_dec(x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_IR_Decl_name(x_2);
x_15 = l_Lean_isExtern(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_closureMaxArgs;
x_17 = lean_nat_dec_lt(x_16, x_4);
lean_dec(x_4);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_4);
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_1);
x_19 = 1;
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = 1;
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_IR_ExplicitBoxing_requiresBoxedVersion___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_2, x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
x_13 = lean_box(7);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_8, x_2, x_14);
x_2 = x_16;
x_3 = x_17;
x_4 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
lean_dec(x_5);
x_12 = lean_nat_sub(x_4, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_16 = x_6;
} else {
 lean_dec_ref(x_6);
 x_16 = lean_box(0);
}
x_17 = lean_nat_dec_lt(x_13, x_2);
x_18 = lean_array_get_size(x_3);
x_19 = lean_nat_dec_lt(x_13, x_18);
lean_dec(x_18);
if (x_17 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = l_Lean_IR_instInhabitedParam;
x_84 = l___private_Init_Util_0__outOfBounds___rarg(x_83);
x_20 = x_84;
goto block_82;
}
else
{
lean_object* x_85; 
x_85 = lean_array_fget(x_1, x_13);
x_20 = x_85;
goto block_82;
}
block_82:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_IR_IRType_isScalar(x_21);
if (x_19 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
x_23 = l_Lean_IR_instInhabitedParam;
x_24 = l___private_Init_Util_0__outOfBounds___rarg(x_23);
if (x_22 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_array_push(x_15, x_26);
if (lean_is_scalar(x_16)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_16;
}
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
x_5 = x_11;
x_6 = x_28;
goto _start;
}
else
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_16);
x_30 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_7);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = lean_ctor_get(x_24, 0);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_box(13);
lean_inc(x_32);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_21);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_array_push(x_14, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_32);
x_40 = lean_array_push(x_15, x_39);
lean_ctor_set(x_30, 1, x_40);
lean_ctor_set(x_30, 0, x_38);
x_5 = x_11;
x_6 = x_30;
x_7 = x_33;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_30, 0);
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_30);
x_44 = lean_ctor_get(x_24, 0);
lean_inc(x_44);
lean_dec(x_24);
x_45 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_box(13);
lean_inc(x_42);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_21);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_46);
x_48 = lean_array_push(x_14, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_42);
x_50 = lean_array_push(x_15, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_5 = x_11;
x_6 = x_51;
x_7 = x_43;
goto _start;
}
}
}
else
{
lean_object* x_53; 
x_53 = lean_array_fget(x_3, x_13);
lean_dec(x_13);
if (x_22 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_21);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_array_push(x_15, x_55);
if (lean_is_scalar(x_16)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_16;
}
lean_ctor_set(x_57, 0, x_14);
lean_ctor_set(x_57, 1, x_56);
x_5 = x_11;
x_6 = x_57;
goto _start;
}
else
{
lean_object* x_59; uint8_t x_60; 
lean_dec(x_16);
x_59 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_7);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
x_63 = lean_ctor_get(x_53, 0);
lean_inc(x_63);
lean_dec(x_53);
x_64 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_box(13);
lean_inc(x_61);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_21);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_66, 3, x_65);
x_67 = lean_array_push(x_14, x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_61);
x_69 = lean_array_push(x_15, x_68);
lean_ctor_set(x_59, 1, x_69);
lean_ctor_set(x_59, 0, x_67);
x_5 = x_11;
x_6 = x_59;
x_7 = x_62;
goto _start;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_71 = lean_ctor_get(x_59, 0);
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_59);
x_73 = lean_ctor_get(x_53, 0);
lean_inc(x_73);
lean_dec(x_53);
x_74 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_box(13);
lean_inc(x_71);
x_76 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_21);
lean_ctor_set(x_76, 2, x_74);
lean_ctor_set(x_76, 3, x_75);
x_77 = lean_array_push(x_14, x_76);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_71);
x_79 = lean_array_push(x_15, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
x_5 = x_11;
x_6 = x_80;
x_7 = x_72;
goto _start;
}
}
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_5);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_6);
lean_ctor_set(x_86, 1, x_7);
return x_86;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_7 = l_Lean_Name_str___override(x_1, x_6);
x_8 = l_Lean_IR_Decl_getInfo(x_2);
x_9 = lean_box(7);
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_4);
lean_ctor_set(x_10, 4, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_3 = l_Lean_IR_Decl_params(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_4);
x_6 = 0;
lean_inc(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1(x_5, x_6, x_3, x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_get_size(x_8);
x_11 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__2;
lean_inc(x_10);
x_12 = l_Nat_foldM_loop___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(x_3, x_4, x_8, x_10, x_10, x_11, x_9);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_IR_Decl_resultType(x_1);
x_21 = l_Lean_IR_Decl_name(x_1);
lean_inc(x_21);
x_22 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_box(13);
lean_inc(x_20);
lean_inc(x_18);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
x_25 = lean_array_push(x_15, x_24);
x_26 = l_Lean_IR_IRType_isScalar(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_18);
x_28 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_IR_reshape(x_25, x_28);
x_30 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___lambda__1(x_21, x_1, x_8, x_29, x_19);
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_19);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_18);
x_35 = lean_box(7);
lean_inc(x_32);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_23);
x_37 = lean_array_push(x_25, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_32);
x_39 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_IR_reshape(x_37, x_39);
x_41 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___lambda__1(x_21, x_1, x_8, x_40, x_33);
lean_dec(x_1);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__1(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldM_loop___at_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_1, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (x_8 == 0)
{
lean_dec(x_7);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_7);
x_13 = lean_array_push(x_5, x_12);
x_3 = x_10;
x_5 = x_13;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_7 = l_Array_append___rarg(x_2, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_3, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_9 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_10 = l_Array_append___rarg(x_2, x_9);
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_13 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(x_1, x_2, x_11, x_12, x_13);
x_15 = l_Array_append___rarg(x_2, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_addBoxedVersions___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_IR_CtorInfo_isScalar(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
goto _start;
}
}
else
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getScrutineeType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_15; uint8_t x_16; 
x_2 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_dec_lt(x_15, x_2);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_2);
x_17 = lean_box(7);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_2);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_box(0);
x_3 = x_20;
goto block_14;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_2);
x_23 = l_Array_anyMUnsafe_any___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(x_1, x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_box(0);
x_3 = x_24;
goto block_14;
}
else
{
lean_object* x_25; 
lean_dec(x_2);
x_25 = lean_box(7);
return x_25;
}
}
}
block_14:
{
lean_object* x_4; uint8_t x_5; 
lean_dec(x_3);
x_4 = lean_unsigned_to_nat(256u);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(65536u);
x_7 = lean_nat_dec_lt(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_cstr_to_nat("4294967296");
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(7);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_box(3);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_box(2);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_box(1);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_IR_ExplicitBoxing_getScrutineeType___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getScrutineeType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_eqvTypes(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = l_Lean_IR_IRType_isScalar(x_1);
x_4 = l_Lean_IR_IRType_isScalar(x_2);
if (x_3 == 0)
{
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
if (x_4 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l_Lean_IR_IRType_beq(x_1, x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_eqvTypes___boxed(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_IR_ExplicitBoxing_BoxingContext_f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_BoxingContext_localCtx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_BoxingContext_resultType___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_BoxingState_auxDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_BoxingState_auxDeclCache___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_BoxingState_nextAuxId___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getEnv(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_getEnv(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_getLocalContext(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getResultType(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getResultType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_getResultType(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_getVarType(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getJPParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
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
x_13 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getJPParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_getJPParams(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_3 = lean_box(0);
x_4 = l_Lean_IR_ExplicitBoxing_getDecl___closed__1;
x_5 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 4);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_IR_findEnvDecl_x27(x_4, x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_IR_ExplicitBoxing_getDecl___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Lean_IR_LocalContext_addParams(x_6, x_1);
lean_ctor_set(x_3, 1, x_7);
x_8 = lean_apply_2(x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_14 = l_Lean_IR_LocalContext_addParams(x_10, x_1);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
x_16 = lean_apply_2(x_2, x_15, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_withParams___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withVDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withVDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_withVDecl___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withJDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withJDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_withJDecl___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
default: 
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_IR_ExplicitBoxing_getLocalContext(x_3, x_4);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_IR_LocalContext_getValue(x_14, x_1);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 0);
switch (lean_obj_tag(x_18)) {
case 6:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_array_get_size(x_19);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_free_object(x_15);
lean_dec(x_18);
x_23 = lean_box(0);
lean_ctor_set(x_12, 0, x_23);
return x_12;
}
else
{
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
}
case 11:
{
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
default: 
{
lean_object* x_24; 
lean_free_object(x_15);
lean_dec(x_18);
x_24 = lean_box(0);
lean_ctor_set(x_12, 0, x_24);
return x_12;
}
}
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
switch (lean_obj_tag(x_25)) {
case 6:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_array_get_size(x_26);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_25);
x_30 = lean_box(0);
lean_ctor_set(x_12, 0, x_30);
return x_12;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_12, 0, x_31);
return x_12;
}
}
case 11:
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_12, 0, x_32);
return x_12;
}
default: 
{
lean_object* x_33; 
lean_dec(x_25);
x_33 = lean_box(0);
lean_ctor_set(x_12, 0, x_33);
return x_12;
}
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
x_36 = l_Lean_IR_LocalContext_getValue(x_34, x_1);
lean_dec(x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_40 = x_36;
} else {
 lean_dec_ref(x_36);
 x_40 = lean_box(0);
}
switch (lean_obj_tag(x_39)) {
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
x_42 = lean_array_get_size(x_41);
lean_dec(x_41);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_eq(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_40);
lean_dec(x_39);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_35);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
if (lean_is_scalar(x_40)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_40;
}
lean_ctor_set(x_47, 0, x_39);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_35);
return x_48;
}
}
case 11:
{
lean_object* x_49; lean_object* x_50; 
if (lean_is_scalar(x_40)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_40;
}
lean_ctor_set(x_49, 0, x_39);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_35);
return x_50;
}
default: 
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_40);
lean_dec(x_39);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_35);
return x_52;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_IR_ExplicitBoxing_mkCast___spec__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ExplicitBoxing_mkCast___closed__1;
x_2 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_boxed_const", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkCast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing(x_1, x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_2);
x_11 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_1);
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
lean_dec(x_2);
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
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_1);
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
lean_inc(x_2);
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_unsigned_to_nat(2u);
x_26 = l_Lean_IR_ExplicitBoxing_mkCast___closed__2;
lean_inc(x_3);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_27);
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
x_33 = l_Lean_AssocList_find_x3f___at_Lean_IR_ExplicitBoxing_mkCast___spec__1(x_28, x_31);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_20, 3);
lean_dec(x_35);
x_36 = lean_ctor_get(x_20, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_20, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_20, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_4, 0);
lean_inc(x_39);
lean_dec(x_4);
x_40 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_32);
x_41 = lean_name_append_index_after(x_40, x_32);
x_42 = l_Lean_Name_append(x_39, x_41);
x_43 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
lean_inc(x_42);
x_44 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_box(0);
lean_inc(x_28);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_3);
lean_ctor_set(x_46, 3, x_28);
lean_ctor_set(x_46, 4, x_45);
x_47 = lean_array_push(x_30, x_46);
lean_inc(x_44);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_28);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_31);
x_49 = lean_nat_add(x_32, x_23);
lean_dec(x_32);
lean_ctor_set(x_20, 3, x_49);
lean_ctor_set(x_20, 2, x_48);
lean_ctor_set(x_20, 1, x_47);
lean_ctor_set(x_6, 0, x_44);
return x_6;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_20);
x_50 = lean_ctor_get(x_4, 0);
lean_inc(x_50);
lean_dec(x_4);
x_51 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_32);
x_52 = lean_name_append_index_after(x_51, x_32);
x_53 = l_Lean_Name_append(x_50, x_52);
x_54 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
lean_inc(x_53);
x_55 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_box(0);
lean_inc(x_28);
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_3);
lean_ctor_set(x_57, 3, x_28);
lean_ctor_set(x_57, 4, x_56);
x_58 = lean_array_push(x_30, x_57);
lean_inc(x_55);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_28);
lean_ctor_set(x_59, 1, x_55);
lean_ctor_set(x_59, 2, x_31);
x_60 = lean_nat_add(x_32, x_23);
lean_dec(x_32);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_29);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_6, 1, x_61);
lean_ctor_set(x_6, 0, x_55);
return x_6;
}
}
else
{
lean_object* x_62; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
x_62 = lean_ctor_get(x_33, 0);
lean_inc(x_62);
lean_dec(x_33);
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
x_75 = l_Lean_AssocList_find_x3f___at_Lean_IR_ExplicitBoxing_mkCast___spec__1(x_70, x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
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
lean_inc(x_77);
lean_dec(x_4);
x_78 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_74);
x_79 = lean_name_append_index_after(x_78, x_74);
x_80 = l_Lean_Name_append(x_77, x_79);
x_81 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
lean_inc(x_80);
x_82 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_box(0);
lean_inc(x_70);
x_84 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_81);
lean_ctor_set(x_84, 2, x_3);
lean_ctor_set(x_84, 3, x_70);
lean_ctor_set(x_84, 4, x_83);
x_85 = lean_array_push(x_72, x_84);
lean_inc(x_82);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_70);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set(x_86, 2, x_73);
x_87 = lean_nat_add(x_74, x_65);
lean_dec(x_74);
if (lean_is_scalar(x_76)) {
 x_88 = lean_alloc_ctor(0, 4, 0);
} else {
 x_88 = x_76;
}
lean_ctor_set(x_88, 0, x_71);
lean_ctor_set(x_88, 1, x_85);
lean_ctor_set(x_88, 2, x_86);
lean_ctor_set(x_88, 3, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_82);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_4);
lean_dec(x_3);
x_90 = lean_ctor_get(x_75, 0);
lean_inc(x_90);
lean_dec(x_75);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_63);
return x_91;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castVarIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_IR_ExplicitBoxing_getVarType(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_7, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_2);
x_13 = l_Lean_IR_ExplicitBoxing_mkCast(x_1, x_7, x_2, x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
x_16 = lean_apply_3(x_3, x_11, x_4, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_18);
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
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_20);
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
lean_dec(x_2);
x_24 = lean_apply_3(x_3, x_1, x_4, x_8);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_IR_ExplicitBoxing_getVarType(x_7, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_9, x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_4);
lean_inc(x_2);
x_15 = l_Lean_IR_ExplicitBoxing_mkCast(x_7, x_9, x_2, x_4, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_ctor_set(x_1, 0, x_13);
x_18 = lean_apply_3(x_3, x_1, x_4, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_20);
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
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_22);
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
lean_dec(x_2);
x_26 = lean_apply_3(x_3, x_1, x_4, x_10);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lean_IR_ExplicitBoxing_getVarType(x_27, x_4, x_5);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_29, x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_32 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_4);
lean_inc(x_2);
x_35 = l_Lean_IR_ExplicitBoxing_mkCast(x_27, x_29, x_2, x_4, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_33);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_39 = lean_apply_3(x_3, x_38, x_4, x_37);
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
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_2);
lean_ctor_set(x_43, 2, x_36);
lean_ctor_set(x_43, 3, x_40);
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
lean_dec(x_2);
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
lean_dec(x_2);
x_47 = lean_apply_3(x_3, x_1, x_4, x_5);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_array_uget(x_2, x_4);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
lean_inc(x_13);
x_15 = lean_apply_1(x_1, x_13);
x_16 = l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___closed__1;
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = l_Lean_IR_ExplicitBoxing_getVarType(x_18, x_6, x_7);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_20, x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_6);
lean_inc(x_15);
x_26 = l_Lean_IR_ExplicitBoxing_mkCast(x_18, x_20, x_15, x_6, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(13);
lean_inc(x_24);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_15);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_10, 0, x_24);
x_31 = lean_array_push(x_14, x_10);
x_32 = lean_array_push(x_11, x_30);
x_33 = lean_box(0);
lean_inc(x_6);
x_34 = lean_apply_6(x_16, x_32, x_13, x_31, x_33, x_6, x_28);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = 1;
x_45 = lean_usize_add(x_4, x_44);
x_4 = x_45;
x_5 = x_43;
x_7 = x_42;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_20);
lean_dec(x_15);
x_47 = lean_array_push(x_14, x_10);
x_48 = lean_box(0);
lean_inc(x_6);
x_49 = lean_apply_6(x_16, x_11, x_13, x_47, x_48, x_6, x_21);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec(x_50);
lean_ctor_set(x_49, 0, x_53);
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_dec(x_49);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
lean_dec(x_50);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; size_t x_59; size_t x_60; 
x_57 = lean_ctor_get(x_49, 1);
lean_inc(x_57);
lean_dec(x_49);
x_58 = lean_ctor_get(x_50, 0);
lean_inc(x_58);
lean_dec(x_50);
x_59 = 1;
x_60 = lean_usize_add(x_4, x_59);
x_4 = x_60;
x_5 = x_58;
x_7 = x_57;
goto _start;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_10, 0);
lean_inc(x_62);
lean_dec(x_10);
x_63 = l_Lean_IR_ExplicitBoxing_getVarType(x_62, x_6, x_7);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_64, x_15);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_67 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_65);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
lean_inc(x_6);
lean_inc(x_15);
x_70 = l_Lean_IR_ExplicitBoxing_mkCast(x_62, x_64, x_15, x_6, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_box(13);
lean_inc(x_68);
x_74 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_15);
lean_ctor_set(x_74, 2, x_71);
lean_ctor_set(x_74, 3, x_73);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_68);
x_76 = lean_array_push(x_14, x_75);
x_77 = lean_array_push(x_11, x_74);
x_78 = lean_box(0);
lean_inc(x_6);
x_79 = lean_apply_6(x_16, x_77, x_13, x_76, x_78, x_6, x_72);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_6);
lean_dec(x_1);
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
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
lean_dec(x_80);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; size_t x_87; size_t x_88; 
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_dec(x_79);
x_86 = lean_ctor_get(x_80, 0);
lean_inc(x_86);
lean_dec(x_80);
x_87 = 1;
x_88 = lean_usize_add(x_4, x_87);
x_4 = x_88;
x_5 = x_86;
x_7 = x_85;
goto _start;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_64);
lean_dec(x_15);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_62);
x_91 = lean_array_push(x_14, x_90);
x_92 = lean_box(0);
lean_inc(x_6);
x_93 = lean_apply_6(x_16, x_11, x_13, x_91, x_92, x_6, x_65);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_6);
lean_dec(x_1);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
lean_dec(x_94);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; size_t x_101; size_t x_102; 
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_dec(x_93);
x_100 = lean_ctor_get(x_94, 0);
lean_inc(x_100);
lean_dec(x_94);
x_101 = 1;
x_102 = lean_usize_add(x_4, x_101);
x_4 = x_102;
x_5 = x_100;
x_7 = x_99;
goto _start;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_15);
x_104 = lean_array_push(x_14, x_10);
x_105 = lean_box(0);
lean_inc(x_6);
x_106 = lean_apply_6(x_16, x_11, x_13, x_104, x_105, x_6, x_7);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
lean_dec(x_6);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_106, 0);
lean_dec(x_109);
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
lean_dec(x_107);
lean_ctor_set(x_106, 0, x_110);
return x_106;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_dec(x_106);
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
lean_dec(x_107);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; size_t x_116; size_t x_117; 
x_114 = lean_ctor_get(x_106, 1);
lean_inc(x_114);
lean_dec(x_106);
x_115 = lean_ctor_get(x_107, 0);
lean_inc(x_115);
lean_dec(x_107);
x_116 = 1;
x_117 = lean_usize_add(x_4, x_116);
x_4 = x_117;
x_5 = x_115;
x_7 = x_114;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_2 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__2;
x_9 = l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(x_2, x_1, x_6, x_7, x_8, x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
lean_ctor_set(x_9, 1, x_15);
lean_ctor_set(x_9, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_IR_instInhabitedParam;
x_6 = l___private_Init_Util_0__outOfBounds___rarg(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_fget(x_1, x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lambda__1___boxed), 2, 1);
lean_closure_set(x_6, 0, x_2);
lean_inc(x_4);
x_7 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_1, x_6, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_apply_3(x_3, x_10, x_4, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_IR_reshape(x_11, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = l_Lean_IR_reshape(x_11, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(7);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1;
lean_inc(x_3);
x_6 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_1, x_5, x_3, x_4);
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
x_11 = lean_apply_3(x_2, x_9, x_3, x_8);
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_IR_IRType_isScalar(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_4);
x_15 = lean_box(7);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_3);
lean_ctor_set(x_16, 3, x_14);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
lean_inc(x_17);
x_19 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_4);
x_21 = lean_box(7);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_2, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_10);
x_12 = l_Lean_IR_ExplicitBoxing_mkCast(x_10, x_4, x_2, x_6, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_5);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_3);
lean_ctor_set(x_16, 3, x_15);
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
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_5);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 2, x_3);
lean_ctor_set(x_20, 3, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_4);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1;
x_12 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_9, x_11, x_5, x_6);
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
uint8_t x_25; 
x_25 = l_Lean_IR_IRType_isScalar(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1;
x_27 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_9, x_26, x_5, x_6);
lean_dec(x_9);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 1);
lean_ctor_set(x_3, 1, x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_2);
lean_ctor_set(x_33, 2, x_3);
lean_ctor_set(x_33, 3, x_4);
x_34 = l_Lean_IR_reshape(x_32, x_33);
lean_ctor_set(x_28, 1, x_29);
lean_ctor_set(x_28, 0, x_34);
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
lean_ctor_set(x_3, 1, x_35);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_2);
lean_ctor_set(x_37, 2, x_3);
lean_ctor_set(x_37, 3, x_4);
x_38 = l_Lean_IR_reshape(x_36, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_29);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_3);
lean_dec(x_9);
lean_dec(x_5);
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_dec(x_8);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_2);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_43, 3, x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_6);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_3, 0);
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_3);
x_47 = l_Lean_IR_CtorInfo_isScalar(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1;
x_49 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_46, x_48, x_5, x_6);
lean_dec(x_46);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_52);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_2);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_4);
x_57 = l_Lean_IR_reshape(x_53, x_56);
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_51);
return x_58;
}
else
{
uint8_t x_59; 
x_59 = l_Lean_IR_IRType_isScalar(x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1;
x_61 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_46, x_60, x_5, x_6);
lean_dec(x_46);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_66 = x_62;
} else {
 lean_dec_ref(x_62);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_45);
lean_ctor_set(x_67, 1, x_64);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_2);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_68, 3, x_4);
x_69 = l_Lean_IR_reshape(x_65, x_68);
if (lean_is_scalar(x_66)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_66;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_46);
lean_dec(x_5);
x_71 = lean_ctor_get(x_45, 1);
lean_inc(x_71);
lean_dec(x_45);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_2);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_4);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_6);
return x_75;
}
}
}
}
case 2:
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_3);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_77 = lean_ctor_get(x_3, 2);
x_78 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1;
x_79 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_77, x_78, x_5, x_6);
lean_dec(x_77);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_80, 0);
x_84 = lean_ctor_get(x_80, 1);
lean_ctor_set(x_3, 2, x_83);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_2);
lean_ctor_set(x_85, 2, x_3);
lean_ctor_set(x_85, 3, x_4);
x_86 = l_Lean_IR_reshape(x_84, x_85);
lean_ctor_set(x_80, 1, x_81);
lean_ctor_set(x_80, 0, x_86);
return x_80;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_80, 0);
x_88 = lean_ctor_get(x_80, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_80);
lean_ctor_set(x_3, 2, x_87);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_2);
lean_ctor_set(x_89, 2, x_3);
lean_ctor_set(x_89, 3, x_4);
x_90 = l_Lean_IR_reshape(x_88, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_81);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_92 = lean_ctor_get(x_3, 0);
x_93 = lean_ctor_get(x_3, 1);
x_94 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_95 = lean_ctor_get(x_3, 2);
lean_inc(x_95);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_3);
x_96 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1;
x_97 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_95, x_96, x_5, x_6);
lean_dec(x_95);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_102 = x_98;
} else {
 lean_dec_ref(x_98);
 x_102 = lean_box(0);
}
x_103 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_103, 0, x_92);
lean_ctor_set(x_103, 1, x_93);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set_uint8(x_103, sizeof(void*)*3, x_94);
x_104 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_104, 0, x_1);
lean_ctor_set(x_104, 1, x_2);
lean_ctor_set(x_104, 2, x_103);
lean_ctor_set(x_104, 3, x_4);
x_105 = l_Lean_IR_reshape(x_101, x_104);
if (lean_is_scalar(x_102)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_102;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_99);
return x_106;
}
}
case 6:
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_3);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_108 = lean_ctor_get(x_3, 0);
x_109 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_inc(x_108);
x_110 = l_Lean_IR_ExplicitBoxing_getDecl(x_108, x_5, x_6);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = l_Lean_IR_Decl_params(x_111);
x_114 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lambda__1___boxed), 2, 1);
lean_closure_set(x_114, 0, x_113);
lean_inc(x_5);
x_115 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_109, x_114, x_5, x_112);
lean_dec(x_109);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
lean_ctor_set(x_3, 1, x_118);
x_120 = l_Lean_IR_Decl_resultType(x_111);
lean_dec(x_111);
x_121 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_2, x_3, x_120, x_4, x_5, x_117);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = l_Lean_IR_reshape(x_119, x_123);
lean_ctor_set(x_121, 0, x_124);
return x_121;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_121, 0);
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_121);
x_127 = l_Lean_IR_reshape(x_119, x_125);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_129 = lean_ctor_get(x_3, 0);
x_130 = lean_ctor_get(x_3, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_3);
lean_inc(x_5);
lean_inc(x_129);
x_131 = l_Lean_IR_ExplicitBoxing_getDecl(x_129, x_5, x_6);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_IR_Decl_params(x_132);
x_135 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lambda__1___boxed), 2, 1);
lean_closure_set(x_135, 0, x_134);
lean_inc(x_5);
x_136 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_130, x_135, x_5, x_133);
lean_dec(x_130);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_141 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_141, 0, x_129);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_IR_Decl_resultType(x_132);
lean_dec(x_132);
x_143 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_2, x_141, x_142, x_4, x_5, x_138);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
x_147 = l_Lean_IR_reshape(x_140, x_144);
if (lean_is_scalar(x_146)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_146;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_145);
return x_148;
}
}
case 7:
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_3);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; 
x_150 = lean_ctor_get(x_3, 0);
x_151 = lean_ctor_get(x_3, 1);
x_152 = l_Lean_IR_ExplicitBoxing_getEnv(x_5, x_6);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
lean_inc(x_5);
lean_inc(x_150);
x_155 = l_Lean_IR_ExplicitBoxing_getDecl(x_150, x_5, x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_153, x_156);
lean_dec(x_156);
x_159 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1;
x_160 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_151, x_159, x_5, x_157);
lean_dec(x_151);
if (x_158 == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = !lean_is_exclusive(x_161);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = lean_ctor_get(x_161, 0);
x_165 = lean_ctor_get(x_161, 1);
lean_ctor_set(x_3, 1, x_164);
x_166 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_166, 0, x_1);
lean_ctor_set(x_166, 1, x_2);
lean_ctor_set(x_166, 2, x_3);
lean_ctor_set(x_166, 3, x_4);
x_167 = l_Lean_IR_reshape(x_165, x_166);
lean_ctor_set(x_161, 1, x_162);
lean_ctor_set(x_161, 0, x_167);
return x_161;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_161, 0);
x_169 = lean_ctor_get(x_161, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_161);
lean_ctor_set(x_3, 1, x_168);
x_170 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_170, 0, x_1);
lean_ctor_set(x_170, 1, x_2);
lean_ctor_set(x_170, 2, x_3);
lean_ctor_set(x_170, 3, x_4);
x_171 = l_Lean_IR_reshape(x_169, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_162);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_173 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_174 = l_Lean_Name_str___override(x_150, x_173);
x_175 = lean_ctor_get(x_160, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_160, 1);
lean_inc(x_176);
lean_dec(x_160);
x_177 = !lean_is_exclusive(x_175);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_175, 0);
x_179 = lean_ctor_get(x_175, 1);
lean_ctor_set(x_3, 1, x_178);
lean_ctor_set(x_3, 0, x_174);
x_180 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_180, 0, x_1);
lean_ctor_set(x_180, 1, x_2);
lean_ctor_set(x_180, 2, x_3);
lean_ctor_set(x_180, 3, x_4);
x_181 = l_Lean_IR_reshape(x_179, x_180);
lean_ctor_set(x_175, 1, x_176);
lean_ctor_set(x_175, 0, x_181);
return x_175;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_175, 0);
x_183 = lean_ctor_get(x_175, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_175);
lean_ctor_set(x_3, 1, x_182);
lean_ctor_set(x_3, 0, x_174);
x_184 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_184, 0, x_1);
lean_ctor_set(x_184, 1, x_2);
lean_ctor_set(x_184, 2, x_3);
lean_ctor_set(x_184, 3, x_4);
x_185 = l_Lean_IR_reshape(x_183, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_176);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; 
x_187 = lean_ctor_get(x_3, 0);
x_188 = lean_ctor_get(x_3, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_3);
x_189 = l_Lean_IR_ExplicitBoxing_getEnv(x_5, x_6);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
lean_inc(x_5);
lean_inc(x_187);
x_192 = l_Lean_IR_ExplicitBoxing_getDecl(x_187, x_5, x_191);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_190, x_193);
lean_dec(x_193);
x_196 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1;
x_197 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_188, x_196, x_5, x_194);
lean_dec(x_188);
if (x_195 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_202 = x_198;
} else {
 lean_dec_ref(x_198);
 x_202 = lean_box(0);
}
x_203 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_203, 0, x_187);
lean_ctor_set(x_203, 1, x_200);
x_204 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_204, 0, x_1);
lean_ctor_set(x_204, 1, x_2);
lean_ctor_set(x_204, 2, x_203);
lean_ctor_set(x_204, 3, x_4);
x_205 = l_Lean_IR_reshape(x_201, x_204);
if (lean_is_scalar(x_202)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_202;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_199);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_207 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1;
x_208 = l_Lean_Name_str___override(x_187, x_207);
x_209 = lean_ctor_get(x_197, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_197, 1);
lean_inc(x_210);
lean_dec(x_197);
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_213 = x_209;
} else {
 lean_dec_ref(x_209);
 x_213 = lean_box(0);
}
x_214 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_214, 0, x_208);
lean_ctor_set(x_214, 1, x_211);
x_215 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_215, 0, x_1);
lean_ctor_set(x_215, 1, x_2);
lean_ctor_set(x_215, 2, x_214);
lean_ctor_set(x_215, 3, x_4);
x_216 = l_Lean_IR_reshape(x_212, x_215);
if (lean_is_scalar(x_213)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_213;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_210);
return x_217;
}
}
}
case 8:
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_3);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_219 = lean_ctor_get(x_3, 1);
x_220 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1;
lean_inc(x_5);
x_221 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_219, x_220, x_5, x_6);
lean_dec(x_219);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
lean_ctor_set(x_3, 1, x_224);
x_226 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_1, x_2, x_3, x_4, x_5, x_223);
lean_dec(x_5);
x_227 = !lean_is_exclusive(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_226, 0);
x_229 = l_Lean_IR_reshape(x_225, x_228);
lean_ctor_set(x_226, 0, x_229);
return x_226;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_226, 0);
x_231 = lean_ctor_get(x_226, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_226);
x_232 = l_Lean_IR_reshape(x_225, x_230);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_234 = lean_ctor_get(x_3, 0);
x_235 = lean_ctor_get(x_3, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_3);
x_236 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1;
lean_inc(x_5);
x_237 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_235, x_236, x_5, x_6);
lean_dec(x_235);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_ctor_get(x_238, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
lean_dec(x_238);
x_242 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_242, 0, x_234);
lean_ctor_set(x_242, 1, x_240);
x_243 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(x_1, x_2, x_242, x_4, x_5, x_239);
lean_dec(x_5);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_246 = x_243;
} else {
 lean_dec_ref(x_243);
 x_246 = lean_box(0);
}
x_247 = l_Lean_IR_reshape(x_241, x_244);
if (lean_is_scalar(x_246)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_246;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_245);
return x_248;
}
}
default: 
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_5);
x_249 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_249, 0, x_1);
lean_ctor_set(x_249, 1, x_2);
lean_ctor_set(x_249, 2, x_3);
lean_ctor_set(x_249, 3, x_4);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_6);
return x_250;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_mmodifyBody___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_apply_3(x_1, x_6, x_3, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set(x_2, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = lean_apply_3(x_1, x_14, x_3, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_16);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_apply_3(x_1, x_22, x_3, x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_2, 0, x_25);
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_2, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
lean_dec(x_2);
x_30 = lean_apply_3(x_1, x_29, x_3, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_31);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_visitFnBody), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_3, x_2, x_9);
x_11 = l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__2___closed__1;
lean_inc(x_4);
x_12 = l_Lean_IR_AltCore_mmodifyBody___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__1(x_11, x_8, x_4, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_10, x_2, x_13);
x_2 = x_16;
x_3 = x_17;
x_5 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_15 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_7, x_14, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr(x_4, x_5, x_6, x_16, x_2, x_17);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_ctor_get(x_1, 3);
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get(x_2, 3);
x_29 = lean_ctor_get(x_2, 4);
lean_inc(x_22);
lean_inc(x_26);
x_30 = l_Lean_IR_LocalContext_addParams(x_26, x_22);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_ctor_set(x_2, 1, x_30);
x_31 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_23, x_2, x_3);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_32);
lean_inc(x_22);
lean_inc(x_21);
x_34 = l_Lean_IR_LocalContext_addJP(x_26, x_21, x_22, x_32);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_27);
lean_ctor_set(x_35, 3, x_28);
lean_ctor_set(x_35, 4, x_29);
x_36 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_24, x_35, x_33);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_32);
lean_ctor_set(x_36, 0, x_1);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_36);
lean_ctor_set(x_1, 3, x_39);
lean_ctor_set(x_1, 2, x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ctor_get(x_1, 2);
x_45 = lean_ctor_get(x_1, 3);
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
x_48 = lean_ctor_get(x_2, 2);
x_49 = lean_ctor_get(x_2, 3);
x_50 = lean_ctor_get(x_2, 4);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_2);
lean_inc(x_43);
lean_inc(x_47);
x_51 = l_Lean_IR_LocalContext_addParams(x_47, x_43);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_46);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_48);
lean_ctor_set(x_52, 3, x_49);
lean_ctor_set(x_52, 4, x_50);
x_53 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_44, x_52, x_3);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_54);
lean_inc(x_43);
lean_inc(x_42);
x_56 = l_Lean_IR_LocalContext_addJP(x_47, x_42, x_43, x_54);
x_57 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_57, 0, x_46);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_48);
lean_ctor_set(x_57, 3, x_49);
lean_ctor_set(x_57, 4, x_50);
x_58 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_45, x_57, x_55);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
lean_ctor_set(x_1, 3, x_59);
lean_ctor_set(x_1, 2, x_54);
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_63 = lean_ctor_get(x_1, 0);
x_64 = lean_ctor_get(x_1, 1);
x_65 = lean_ctor_get(x_1, 2);
x_66 = lean_ctor_get(x_1, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_1);
x_67 = lean_ctor_get(x_2, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_2, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_2, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 4);
lean_inc(x_71);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_72 = x_2;
} else {
 lean_dec_ref(x_2);
 x_72 = lean_box(0);
}
lean_inc(x_64);
lean_inc(x_68);
x_73 = l_Lean_IR_LocalContext_addParams(x_68, x_64);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_67);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 5, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_69);
lean_ctor_set(x_74, 3, x_70);
lean_ctor_set(x_74, 4, x_71);
x_75 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_65, x_74, x_3);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_76);
lean_inc(x_64);
lean_inc(x_63);
x_78 = l_Lean_IR_LocalContext_addJP(x_68, x_63, x_64, x_76);
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_67);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_69);
lean_ctor_set(x_79, 3, x_70);
lean_ctor_set(x_79, 4, x_71);
x_80 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_66, x_79, x_77);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
x_84 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_84, 0, x_63);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_76);
lean_ctor_set(x_84, 3, x_81);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
}
case 4:
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_1);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_87 = lean_ctor_get(x_1, 2);
x_88 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_89 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_88, x_2, x_3);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_IR_ExplicitBoxing_getVarType(x_87, x_2, x_91);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_ctor_get(x_92, 1);
x_96 = lean_box(5);
x_97 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_94, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_free_object(x_92);
x_98 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_95);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_IR_ExplicitBoxing_mkCast(x_87, x_94, x_96, x_2, x_100);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_99);
lean_ctor_set(x_1, 3, x_90);
lean_ctor_set(x_1, 2, x_99);
x_104 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_96);
lean_ctor_set(x_104, 2, x_103);
lean_ctor_set(x_104, 3, x_1);
lean_ctor_set(x_101, 0, x_104);
return x_101;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_101, 0);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_101);
lean_inc(x_99);
lean_ctor_set(x_1, 3, x_90);
lean_ctor_set(x_1, 2, x_99);
x_107 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_107, 0, x_99);
lean_ctor_set(x_107, 1, x_96);
lean_ctor_set(x_107, 2, x_105);
lean_ctor_set(x_107, 3, x_1);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_dec(x_94);
lean_dec(x_2);
lean_ctor_set(x_1, 3, x_90);
lean_ctor_set(x_92, 0, x_1);
return x_92;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_92, 0);
x_110 = lean_ctor_get(x_92, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_92);
x_111 = lean_box(5);
x_112 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_109, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_113 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_110);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_IR_ExplicitBoxing_mkCast(x_87, x_109, x_111, x_2, x_115);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
lean_inc(x_114);
lean_ctor_set(x_1, 3, x_90);
lean_ctor_set(x_1, 2, x_114);
x_120 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_111);
lean_ctor_set(x_120, 2, x_117);
lean_ctor_set(x_120, 3, x_1);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
else
{
lean_object* x_122; 
lean_dec(x_109);
lean_dec(x_2);
lean_ctor_set(x_1, 3, x_90);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_1);
lean_ctor_set(x_122, 1, x_110);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_123 = lean_ctor_get(x_1, 0);
x_124 = lean_ctor_get(x_1, 1);
x_125 = lean_ctor_get(x_1, 2);
x_126 = lean_ctor_get(x_1, 3);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_1);
lean_inc(x_2);
x_127 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_126, x_2, x_3);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = l_Lean_IR_ExplicitBoxing_getVarType(x_125, x_2, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = lean_box(5);
x_135 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_131, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_133);
x_136 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_132);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_Lean_IR_ExplicitBoxing_mkCast(x_125, x_131, x_134, x_2, x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
lean_inc(x_137);
x_143 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_143, 0, x_123);
lean_ctor_set(x_143, 1, x_124);
lean_ctor_set(x_143, 2, x_137);
lean_ctor_set(x_143, 3, x_128);
x_144 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_144, 0, x_137);
lean_ctor_set(x_144, 1, x_134);
lean_ctor_set(x_144, 2, x_140);
lean_ctor_set(x_144, 3, x_143);
if (lean_is_scalar(x_142)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_142;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_141);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_131);
lean_dec(x_2);
x_146 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_146, 0, x_123);
lean_ctor_set(x_146, 1, x_124);
lean_ctor_set(x_146, 2, x_125);
lean_ctor_set(x_146, 3, x_128);
if (lean_is_scalar(x_133)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_133;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_132);
return x_147;
}
}
}
case 5:
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_1);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_149 = lean_ctor_get(x_1, 3);
x_150 = lean_ctor_get(x_1, 4);
x_151 = lean_ctor_get(x_1, 5);
lean_inc(x_2);
x_152 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_151, x_2, x_3);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_IR_ExplicitBoxing_getVarType(x_149, x_2, x_154);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_155, 1);
x_159 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_157, x_150);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
lean_free_object(x_155);
x_160 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_158);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
lean_inc(x_150);
x_163 = l_Lean_IR_ExplicitBoxing_mkCast(x_149, x_157, x_150, x_2, x_162);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_150);
lean_inc(x_161);
lean_ctor_set(x_1, 5, x_153);
lean_ctor_set(x_1, 3, x_161);
x_166 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_150);
lean_ctor_set(x_166, 2, x_165);
lean_ctor_set(x_166, 3, x_1);
lean_ctor_set(x_163, 0, x_166);
return x_163;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_163, 0);
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_163);
lean_inc(x_150);
lean_inc(x_161);
lean_ctor_set(x_1, 5, x_153);
lean_ctor_set(x_1, 3, x_161);
x_169 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_169, 0, x_161);
lean_ctor_set(x_169, 1, x_150);
lean_ctor_set(x_169, 2, x_167);
lean_ctor_set(x_169, 3, x_1);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
lean_dec(x_157);
lean_dec(x_2);
lean_ctor_set(x_1, 5, x_153);
lean_ctor_set(x_155, 0, x_1);
return x_155;
}
}
else
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_155, 0);
x_172 = lean_ctor_get(x_155, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_155);
x_173 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_171, x_150);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_174 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_172);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
lean_inc(x_150);
x_177 = l_Lean_IR_ExplicitBoxing_mkCast(x_149, x_171, x_150, x_2, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_180 = x_177;
} else {
 lean_dec_ref(x_177);
 x_180 = lean_box(0);
}
lean_inc(x_150);
lean_inc(x_175);
lean_ctor_set(x_1, 5, x_153);
lean_ctor_set(x_1, 3, x_175);
x_181 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_181, 0, x_175);
lean_ctor_set(x_181, 1, x_150);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set(x_181, 3, x_1);
if (lean_is_scalar(x_180)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_180;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_179);
return x_182;
}
else
{
lean_object* x_183; 
lean_dec(x_171);
lean_dec(x_2);
lean_ctor_set(x_1, 5, x_153);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_1);
lean_ctor_set(x_183, 1, x_172);
return x_183;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_184 = lean_ctor_get(x_1, 0);
x_185 = lean_ctor_get(x_1, 1);
x_186 = lean_ctor_get(x_1, 2);
x_187 = lean_ctor_get(x_1, 3);
x_188 = lean_ctor_get(x_1, 4);
x_189 = lean_ctor_get(x_1, 5);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_1);
lean_inc(x_2);
x_190 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_189, x_2, x_3);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l_Lean_IR_ExplicitBoxing_getVarType(x_187, x_2, x_192);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
x_197 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_194, x_188);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_196);
x_198 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_195);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
lean_inc(x_188);
x_201 = l_Lean_IR_ExplicitBoxing_mkCast(x_187, x_194, x_188, x_2, x_200);
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
lean_inc(x_188);
lean_inc(x_199);
x_205 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_205, 0, x_184);
lean_ctor_set(x_205, 1, x_185);
lean_ctor_set(x_205, 2, x_186);
lean_ctor_set(x_205, 3, x_199);
lean_ctor_set(x_205, 4, x_188);
lean_ctor_set(x_205, 5, x_191);
x_206 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_206, 0, x_199);
lean_ctor_set(x_206, 1, x_188);
lean_ctor_set(x_206, 2, x_202);
lean_ctor_set(x_206, 3, x_205);
if (lean_is_scalar(x_204)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_204;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_203);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec(x_194);
lean_dec(x_2);
x_208 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_208, 0, x_184);
lean_ctor_set(x_208, 1, x_185);
lean_ctor_set(x_208, 2, x_186);
lean_ctor_set(x_208, 3, x_187);
lean_ctor_set(x_208, 4, x_188);
lean_ctor_set(x_208, 5, x_191);
if (lean_is_scalar(x_196)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_196;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_195);
return x_209;
}
}
}
case 9:
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_1);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_211 = lean_ctor_get(x_1, 1);
x_212 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_211, x_2, x_3);
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_212, 0);
lean_ctor_set(x_1, 1, x_214);
lean_ctor_set(x_212, 0, x_1);
return x_212;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_212, 0);
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_212);
lean_ctor_set(x_1, 1, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_1);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_218 = lean_ctor_get(x_1, 0);
x_219 = lean_ctor_get(x_1, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_1);
x_220 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_219, x_2, x_3);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
x_224 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_224, 0, x_218);
lean_ctor_set(x_224, 1, x_221);
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_222);
return x_225;
}
}
case 10:
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_1);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; size_t x_232; size_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_227 = lean_ctor_get(x_1, 1);
x_228 = lean_ctor_get(x_1, 3);
x_229 = lean_ctor_get(x_1, 2);
lean_dec(x_229);
x_230 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_228);
x_231 = lean_array_get_size(x_228);
x_232 = lean_usize_of_nat(x_231);
lean_dec(x_231);
x_233 = 0;
lean_inc(x_2);
x_234 = l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__2(x_232, x_233, x_228, x_2, x_3);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = l_Lean_IR_ExplicitBoxing_getVarType(x_227, x_2, x_236);
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_239 = lean_ctor_get(x_237, 0);
x_240 = lean_ctor_get(x_237, 1);
x_241 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_239, x_230);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
lean_free_object(x_237);
x_242 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_240);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
lean_inc(x_230);
x_245 = l_Lean_IR_ExplicitBoxing_mkCast(x_227, x_239, x_230, x_2, x_244);
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_230);
lean_inc(x_243);
lean_ctor_set(x_1, 3, x_235);
lean_ctor_set(x_1, 2, x_230);
lean_ctor_set(x_1, 1, x_243);
x_248 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_248, 0, x_243);
lean_ctor_set(x_248, 1, x_230);
lean_ctor_set(x_248, 2, x_247);
lean_ctor_set(x_248, 3, x_1);
lean_ctor_set(x_245, 0, x_248);
return x_245;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_245, 0);
x_250 = lean_ctor_get(x_245, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_245);
lean_inc(x_230);
lean_inc(x_243);
lean_ctor_set(x_1, 3, x_235);
lean_ctor_set(x_1, 2, x_230);
lean_ctor_set(x_1, 1, x_243);
x_251 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_251, 0, x_243);
lean_ctor_set(x_251, 1, x_230);
lean_ctor_set(x_251, 2, x_249);
lean_ctor_set(x_251, 3, x_1);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
else
{
lean_dec(x_239);
lean_dec(x_2);
lean_ctor_set(x_1, 3, x_235);
lean_ctor_set(x_1, 2, x_230);
lean_ctor_set(x_237, 0, x_1);
return x_237;
}
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_253 = lean_ctor_get(x_237, 0);
x_254 = lean_ctor_get(x_237, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_237);
x_255 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_253, x_230);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_256 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_254);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
lean_inc(x_230);
x_259 = l_Lean_IR_ExplicitBoxing_mkCast(x_227, x_253, x_230, x_2, x_258);
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
lean_inc(x_230);
lean_inc(x_257);
lean_ctor_set(x_1, 3, x_235);
lean_ctor_set(x_1, 2, x_230);
lean_ctor_set(x_1, 1, x_257);
x_263 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_263, 0, x_257);
lean_ctor_set(x_263, 1, x_230);
lean_ctor_set(x_263, 2, x_260);
lean_ctor_set(x_263, 3, x_1);
if (lean_is_scalar(x_262)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_262;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_261);
return x_264;
}
else
{
lean_object* x_265; 
lean_dec(x_253);
lean_dec(x_2);
lean_ctor_set(x_1, 3, x_235);
lean_ctor_set(x_1, 2, x_230);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_1);
lean_ctor_set(x_265, 1, x_254);
return x_265;
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; size_t x_271; size_t x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_266 = lean_ctor_get(x_1, 0);
x_267 = lean_ctor_get(x_1, 1);
x_268 = lean_ctor_get(x_1, 3);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_1);
x_269 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_268);
x_270 = lean_array_get_size(x_268);
x_271 = lean_usize_of_nat(x_270);
lean_dec(x_270);
x_272 = 0;
lean_inc(x_2);
x_273 = l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__2(x_271, x_272, x_268, x_2, x_3);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = l_Lean_IR_ExplicitBoxing_getVarType(x_267, x_2, x_275);
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
x_280 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_277, x_269);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_279);
x_281 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_278);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
lean_inc(x_269);
x_284 = l_Lean_IR_ExplicitBoxing_mkCast(x_267, x_277, x_269, x_2, x_283);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_287 = x_284;
} else {
 lean_dec_ref(x_284);
 x_287 = lean_box(0);
}
lean_inc(x_269);
lean_inc(x_282);
x_288 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_288, 0, x_266);
lean_ctor_set(x_288, 1, x_282);
lean_ctor_set(x_288, 2, x_269);
lean_ctor_set(x_288, 3, x_274);
x_289 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_289, 0, x_282);
lean_ctor_set(x_289, 1, x_269);
lean_ctor_set(x_289, 2, x_285);
lean_ctor_set(x_289, 3, x_288);
if (lean_is_scalar(x_287)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_287;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_286);
return x_290;
}
else
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_277);
lean_dec(x_2);
x_291 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_291, 0, x_266);
lean_ctor_set(x_291, 1, x_267);
lean_ctor_set(x_291, 2, x_269);
lean_ctor_set(x_291, 3, x_274);
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
x_301 = !lean_is_exclusive(x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_302 = lean_ctor_get(x_300, 0);
x_303 = lean_ctor_get(x_300, 1);
x_304 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_302, x_296);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
lean_free_object(x_300);
x_305 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_303);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
lean_inc(x_296);
x_308 = l_Lean_IR_ExplicitBoxing_mkCast(x_299, x_302, x_296, x_2, x_307);
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_306);
lean_ctor_set(x_294, 0, x_306);
x_311 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_311, 0, x_306);
lean_ctor_set(x_311, 1, x_296);
lean_ctor_set(x_311, 2, x_310);
lean_ctor_set(x_311, 3, x_1);
lean_ctor_set(x_308, 0, x_311);
return x_308;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_308, 0);
x_313 = lean_ctor_get(x_308, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_308);
lean_inc(x_306);
lean_ctor_set(x_294, 0, x_306);
x_314 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_314, 0, x_306);
lean_ctor_set(x_314, 1, x_296);
lean_ctor_set(x_314, 2, x_312);
lean_ctor_set(x_314, 3, x_1);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
return x_315;
}
}
else
{
lean_dec(x_302);
lean_dec(x_296);
lean_dec(x_2);
lean_ctor_set(x_300, 0, x_1);
return x_300;
}
}
else
{
lean_object* x_316; lean_object* x_317; uint8_t x_318; 
x_316 = lean_ctor_get(x_300, 0);
x_317 = lean_ctor_get(x_300, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_300);
x_318 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_316, x_296);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_319 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_317);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
lean_inc(x_296);
x_322 = l_Lean_IR_ExplicitBoxing_mkCast(x_299, x_316, x_296, x_2, x_321);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_322)) {
 lean_ctor_release(x_322, 0);
 lean_ctor_release(x_322, 1);
 x_325 = x_322;
} else {
 lean_dec_ref(x_322);
 x_325 = lean_box(0);
}
lean_inc(x_320);
lean_ctor_set(x_294, 0, x_320);
x_326 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_326, 0, x_320);
lean_ctor_set(x_326, 1, x_296);
lean_ctor_set(x_326, 2, x_323);
lean_ctor_set(x_326, 3, x_1);
if (lean_is_scalar(x_325)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_325;
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_324);
return x_327;
}
else
{
lean_object* x_328; 
lean_dec(x_316);
lean_dec(x_296);
lean_dec(x_2);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_1);
lean_ctor_set(x_328, 1, x_317);
return x_328;
}
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_329 = lean_ctor_get(x_294, 0);
lean_inc(x_329);
lean_dec(x_294);
x_330 = l_Lean_IR_ExplicitBoxing_getVarType(x_329, x_2, x_297);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_333 = x_330;
} else {
 lean_dec_ref(x_330);
 x_333 = lean_box(0);
}
x_334 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_331, x_296);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_333);
x_335 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_332);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
lean_inc(x_296);
x_338 = l_Lean_IR_ExplicitBoxing_mkCast(x_329, x_331, x_296, x_2, x_337);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_341 = x_338;
} else {
 lean_dec_ref(x_338);
 x_341 = lean_box(0);
}
lean_inc(x_336);
x_342 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_342, 0, x_336);
lean_ctor_set(x_1, 0, x_342);
x_343 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_343, 0, x_336);
lean_ctor_set(x_343, 1, x_296);
lean_ctor_set(x_343, 2, x_339);
lean_ctor_set(x_343, 3, x_1);
if (lean_is_scalar(x_341)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_341;
}
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_340);
return x_344;
}
else
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_331);
lean_dec(x_296);
lean_dec(x_2);
x_345 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_345, 0, x_329);
lean_ctor_set(x_1, 0, x_345);
if (lean_is_scalar(x_333)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_333;
}
lean_ctor_set(x_346, 0, x_1);
lean_ctor_set(x_346, 1, x_332);
return x_346;
}
}
}
else
{
uint8_t x_347; 
lean_dec(x_2);
x_347 = !lean_is_exclusive(x_295);
if (x_347 == 0)
{
lean_object* x_348; 
x_348 = lean_ctor_get(x_295, 0);
lean_dec(x_348);
lean_ctor_set(x_295, 0, x_1);
return x_295;
}
else
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_ctor_get(x_295, 1);
lean_inc(x_349);
lean_dec(x_295);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_1);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
else
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_1, 0);
lean_inc(x_351);
lean_dec(x_1);
x_352 = l_Lean_IR_ExplicitBoxing_getResultType(x_2, x_3);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = lean_ctor_get(x_351, 0);
lean_inc(x_355);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 x_356 = x_351;
} else {
 lean_dec_ref(x_351);
 x_356 = lean_box(0);
}
x_357 = l_Lean_IR_ExplicitBoxing_getVarType(x_355, x_2, x_354);
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
x_361 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_358, x_353);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_360);
x_362 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___rarg(x_359);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
lean_inc(x_353);
x_365 = l_Lean_IR_ExplicitBoxing_mkCast(x_355, x_358, x_353, x_2, x_364);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_368 = x_365;
} else {
 lean_dec_ref(x_365);
 x_368 = lean_box(0);
}
lean_inc(x_363);
if (lean_is_scalar(x_356)) {
 x_369 = lean_alloc_ctor(0, 1, 0);
} else {
 x_369 = x_356;
}
lean_ctor_set(x_369, 0, x_363);
x_370 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_370, 0, x_369);
x_371 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_371, 0, x_363);
lean_ctor_set(x_371, 1, x_353);
lean_ctor_set(x_371, 2, x_366);
lean_ctor_set(x_371, 3, x_370);
if (lean_is_scalar(x_368)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_368;
}
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_367);
return x_372;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_358);
lean_dec(x_353);
lean_dec(x_2);
if (lean_is_scalar(x_356)) {
 x_373 = lean_alloc_ctor(0, 1, 0);
} else {
 x_373 = x_356;
}
lean_ctor_set(x_373, 0, x_355);
x_374 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_374, 0, x_373);
if (lean_is_scalar(x_360)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_360;
}
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_359);
return x_375;
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_2);
x_376 = lean_ctor_get(x_352, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_377 = x_352;
} else {
 lean_dec_ref(x_352);
 x_377 = lean_box(0);
}
x_378 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_378, 0, x_351);
if (lean_is_scalar(x_377)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_377;
}
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_376);
return x_379;
}
}
}
case 12:
{
uint8_t x_380; 
x_380 = !lean_is_exclusive(x_1);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; 
x_381 = lean_ctor_get(x_1, 0);
x_382 = lean_ctor_get(x_1, 1);
x_383 = l_Lean_IR_ExplicitBoxing_getJPParams(x_381, x_2, x_3);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
lean_dec(x_383);
x_386 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lambda__1___boxed), 2, 1);
lean_closure_set(x_386, 0, x_384);
x_387 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_382, x_386, x_2, x_385);
lean_dec(x_382);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
x_390 = !lean_is_exclusive(x_388);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_388, 0);
x_392 = lean_ctor_get(x_388, 1);
lean_ctor_set(x_1, 1, x_391);
x_393 = l_Lean_IR_reshape(x_392, x_1);
lean_ctor_set(x_388, 1, x_389);
lean_ctor_set(x_388, 0, x_393);
return x_388;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_394 = lean_ctor_get(x_388, 0);
x_395 = lean_ctor_get(x_388, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_388);
lean_ctor_set(x_1, 1, x_394);
x_396 = l_Lean_IR_reshape(x_395, x_1);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_389);
return x_397;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_398 = lean_ctor_get(x_1, 0);
x_399 = lean_ctor_get(x_1, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_1);
x_400 = l_Lean_IR_ExplicitBoxing_getJPParams(x_398, x_2, x_3);
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
x_403 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lambda__1___boxed), 2, 1);
lean_closure_set(x_403, 0, x_401);
x_404 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_399, x_403, x_2, x_402);
lean_dec(x_399);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
x_407 = lean_ctor_get(x_405, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_405, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_409 = x_405;
} else {
 lean_dec_ref(x_405);
 x_409 = lean_box(0);
}
x_410 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_410, 0, x_398);
lean_ctor_set(x_410, 1, x_407);
x_411 = l_Lean_IR_reshape(x_408, x_410);
if (lean_is_scalar(x_409)) {
 x_412 = lean_alloc_ctor(0, 2, 0);
} else {
 x_412 = x_409;
}
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_406);
return x_412;
}
}
default: 
{
lean_object* x_413; 
lean_dec(x_2);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_1);
lean_ctor_set(x_413, 1, x_3);
return x_413;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__2(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_run___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_6, x_7);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_array_uget(x_5, x_6);
x_11 = 1;
x_12 = lean_usize_add(x_6, x_11);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
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
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_18, x_19);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_19);
lean_inc(x_4);
x_24 = l_Lean_IR_LocalContext_addParams(x_4, x_14);
lean_inc(x_1);
lean_inc(x_2);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_15);
lean_ctor_set(x_25, 3, x_2);
lean_ctor_set(x_25, 4, x_1);
x_26 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_16, x_25, x_23);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Array_append___rarg(x_8, x_29);
x_31 = l_Lean_IR_Decl_updateBody_x21(x_10, x_27);
x_32 = l_Lean_IR_Decl_elimDead(x_31);
x_33 = lean_array_push(x_30, x_32);
x_6 = x_12;
x_8 = x_33;
goto _start;
}
else
{
lean_object* x_35; 
x_35 = lean_array_push(x_8, x_10);
x_6 = x_12;
x_8 = x_35;
goto _start;
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_run___spec__1___at_Lean_IR_ExplicitBoxing_run___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_array_uget(x_4, x_5);
x_10 = 1;
x_11 = lean_usize_add(x_5, x_10);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 3);
lean_inc(x_15);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
x_17 = l_Lean_IR_MaxIndex_collectDecl(x_9, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_17, x_18);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_18);
lean_inc(x_3);
x_23 = l_Lean_IR_LocalContext_addParams(x_3, x_13);
lean_inc(x_1);
lean_inc(x_2);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_14);
lean_ctor_set(x_24, 3, x_2);
lean_ctor_set(x_24, 4, x_1);
x_25 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_15, x_24, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Array_append___rarg(x_7, x_28);
x_30 = l_Lean_IR_Decl_updateBody_x21(x_9, x_26);
x_31 = l_Lean_IR_Decl_elimDead(x_30);
x_32 = lean_array_push(x_29, x_31);
x_5 = x_11;
x_7 = x_32;
goto _start;
}
else
{
lean_object* x_34; 
x_34 = lean_array_push(x_7, x_9);
x_5 = x_11;
x_7 = x_34;
goto _start;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_box(0);
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_8 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_4, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
x_11 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_10);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_run___spec__1___at_Lean_IR_ExplicitBoxing_run___spec__2(x_1, x_2, x_3, x_2, x_12, x_13, x_14);
lean_dec(x_2);
x_16 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_run___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_run___spec__1(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_run___spec__1___at_Lean_IR_ExplicitBoxing_run___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExplicitBoxing_run___spec__1___at_Lean_IR_ExplicitBoxing_run___spec__2(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_explicitBoxing(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Runtime(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_FreeVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ElimDeadVars(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Boxing(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Runtime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ClosedTermCache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_FreeVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ElimDeadVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__1);
l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1);
l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__2 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__2();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__2);
l_Lean_IR_ExplicitBoxing_BoxingContext_f___default = _init_l_Lean_IR_ExplicitBoxing_BoxingContext_f___default();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_BoxingContext_f___default);
l_Lean_IR_ExplicitBoxing_BoxingContext_localCtx___default = _init_l_Lean_IR_ExplicitBoxing_BoxingContext_localCtx___default();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_BoxingContext_localCtx___default);
l_Lean_IR_ExplicitBoxing_BoxingContext_resultType___default = _init_l_Lean_IR_ExplicitBoxing_BoxingContext_resultType___default();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_BoxingContext_resultType___default);
l_Lean_IR_ExplicitBoxing_BoxingState_auxDecls___default = _init_l_Lean_IR_ExplicitBoxing_BoxingState_auxDecls___default();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_BoxingState_auxDecls___default);
l_Lean_IR_ExplicitBoxing_BoxingState_auxDeclCache___default = _init_l_Lean_IR_ExplicitBoxing_BoxingState_auxDeclCache___default();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_BoxingState_auxDeclCache___default);
l_Lean_IR_ExplicitBoxing_BoxingState_nextAuxId___default = _init_l_Lean_IR_ExplicitBoxing_BoxingState_nextAuxId___default();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_BoxingState_nextAuxId___default);
l_Lean_IR_ExplicitBoxing_getDecl___closed__1 = _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_getDecl___closed__1);
l_Lean_IR_ExplicitBoxing_getDecl___closed__2 = _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__2();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_getDecl___closed__2);
l_Lean_IR_ExplicitBoxing_mkCast___closed__1 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__1);
l_Lean_IR_ExplicitBoxing_mkCast___closed__2 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__2();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__2);
l_Lean_IR_ExplicitBoxing_mkCast___closed__3 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__3();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__3);
l_Lean_IR_ExplicitBoxing_mkCast___closed__4 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__4();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__4);
l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___spec__1___closed__1);
l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1 = _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1);
l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__2 = _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__2();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__2);
l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1 = _init_l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___closed__1);
l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_IR_ExplicitBoxing_visitFnBody___spec__2___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
