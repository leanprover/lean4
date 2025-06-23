// Lean compiler output
// Module: Lean.Compiler.IR.Boxing
// Imports: Lean.Runtime Lean.Compiler.ClosedTermCache Lean.Compiler.ExternAttr Lean.Compiler.IR.Basic Lean.Compiler.IR.CompilerM Lean.Compiler.IR.FreeVars Lean.Compiler.IR.ElimDeadVars Lean.Data.AssocList
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_getScrutineeType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__0(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersion(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_ExplicitBoxing_castArgsIfNeededAux_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getEnv(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_elimDead(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_requiresBoxedVersion___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_maxIndex(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getJPParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castResultIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getResultType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getVarType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___boxed(lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withVDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_eqvTypes___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_requiresBoxedVersion_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_visitFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withVDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getVarType___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lam__0(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__1;
static lean_object* l_Lean_IR_ExplicitBoxing_getDecl___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedParam;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___Lean_IR_ExplicitBoxing_mkCast_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_ExplicitBoxing_castArgsIfNeededAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0;
static lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withJDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_closureMaxArgs;
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_addBoxedVersions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_getDecl___closed__1;
static lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getScrutineeType(lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_run_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getScrutineeType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castVarIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_isBoxedName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_addBoxedVersions_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_IR_IRType_beq(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getJPParams(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_isBoxedName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getLocalContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getResultType___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_getScrutineeType_spec__0(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_visitFnBody_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getValue(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkCast___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getEnv___boxed(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_getDecl___closed__0;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_requiresBoxedVersion_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_getInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withJDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_IR_ExplicitBoxing_getJPParams___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_eqvTypes(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_getEnv___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___lam__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___Lean_IR_ExplicitBoxing_mkCast_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_boxed", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__0;
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
x_3 = l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__0;
x_4 = lean_string_dec_eq(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_requiresBoxedVersion_spec__0(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_15; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(1);
x_15 = l_Lean_IR_IRType_isScalar(x_7);
lean_dec(x_7);
if (x_15 == 0)
{
x_9 = x_6;
goto block_14;
}
else
{
x_9 = x_15;
goto block_14;
}
block_14:
{
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_8);
return x_13;
}
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_9; uint8_t x_10; lean_object* x_14; lean_object* x_15; lean_object* x_24; lean_object* x_30; 
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_24 = x_30;
goto block_29;
block_8:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_closureMaxArgs;
x_6 = lean_array_get_size(x_3);
lean_dec(x_3);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
return x_7;
}
else
{
lean_dec(x_3);
return x_4;
}
}
block_13:
{
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_isExtern(x_1, x_11);
x_3 = x_9;
x_4 = x_12;
goto block_8;
}
else
{
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
block_23:
{
uint8_t x_16; 
x_16 = l_Lean_IR_IRType_isScalar(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_14);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
x_9 = x_14;
x_10 = x_16;
goto block_13;
}
else
{
if (x_19 == 0)
{
lean_dec(x_18);
x_9 = x_14;
x_10 = x_16;
goto block_13;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_22 = l_Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_requiresBoxedVersion_spec__0(x_14, x_20, x_21);
x_9 = x_14;
x_10 = x_22;
goto block_13;
}
}
}
else
{
x_9 = x_14;
x_10 = x_16;
goto block_13;
}
}
block_29:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get_size(x_24);
x_27 = lean_nat_dec_lt(x_25, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_3 = x_24;
x_4 = x_27;
goto block_8;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
x_14 = x_24;
x_15 = x_28;
goto block_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_requiresBoxedVersion_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_requiresBoxedVersion_spec__0(x_1, x_4, x_5);
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
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_7 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = lean_box(0);
x_13 = lean_box(7);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unbox(x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_15);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_11, x_2, x_14);
x_2 = x_17;
x_3 = x_18;
x_4 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 1)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
x_16 = lean_nat_sub(x_4, x_15);
x_17 = lean_nat_sub(x_16, x_14);
lean_dec(x_16);
lean_inc(x_1);
x_18 = lean_array_get(x_1, x_2, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_array_fget(x_3, x_17);
lean_dec(x_17);
x_21 = l_Lean_IR_IRType_isScalar(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_push(x_13, x_23);
lean_ctor_set(x_6, 1, x_24);
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_free_object(x_6);
x_26 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_7);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_box(13);
lean_inc(x_28);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_19);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_array_push(x_12, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_28);
x_36 = lean_array_push(x_13, x_35);
lean_ctor_set(x_26, 1, x_36);
lean_ctor_set(x_26, 0, x_34);
x_5 = x_15;
x_6 = x_26;
x_7 = x_29;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
lean_dec(x_20);
x_41 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_box(13);
lean_inc(x_38);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_19);
lean_ctor_set(x_43, 2, x_41);
lean_ctor_set(x_43, 3, x_42);
x_44 = lean_array_push(x_12, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_38);
x_46 = lean_array_push(x_13, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_5 = x_15;
x_6 = x_47;
x_7 = x_39;
goto _start;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_49 = lean_ctor_get(x_6, 0);
x_50 = lean_ctor_get(x_6, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_6);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_sub(x_5, x_51);
lean_dec(x_5);
x_53 = lean_nat_sub(x_4, x_52);
x_54 = lean_nat_sub(x_53, x_51);
lean_dec(x_53);
lean_inc(x_1);
x_55 = lean_array_get(x_1, x_2, x_54);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_array_fget(x_3, x_54);
lean_dec(x_54);
x_58 = l_Lean_IR_IRType_isScalar(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_array_push(x_50, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_49);
lean_ctor_set(x_62, 1, x_61);
x_5 = x_52;
x_6 = x_62;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_64 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_7);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
lean_dec(x_57);
x_69 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_box(13);
lean_inc(x_65);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_56);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_array_push(x_49, x_71);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_65);
x_74 = lean_array_push(x_50, x_73);
if (lean_is_scalar(x_67)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_67;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
x_5 = x_52;
x_6 = x_75;
x_7 = x_66;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__0;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_56; lean_object* x_57; lean_object* x_75; 
x_56 = l_Lean_IR_instInhabitedParam;
x_75 = lean_ctor_get(x_1, 1);
lean_inc(x_75);
x_57 = x_75;
goto block_74;
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_IR_ExplicitBoxing_mkBoxedName(x_4);
x_8 = lean_box(7);
x_9 = l_Lean_IR_Decl_getInfo(x_1);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_5);
lean_ctor_set(x_10, 4, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
block_47:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_19);
x_20 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
x_21 = lean_box(13);
lean_inc(x_18);
lean_inc(x_17);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_21);
x_23 = lean_array_push(x_15, x_22);
x_24 = l_Lean_IR_IRType_isScalar(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_18);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_17);
x_26 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_IR_reshape(x_23, x_26);
x_3 = x_14;
x_4 = x_19;
x_5 = x_27;
x_6 = x_16;
goto block_12;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_16);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_box(7);
lean_ctor_set_tag(x_28, 9);
lean_ctor_set(x_28, 1, x_17);
lean_ctor_set(x_28, 0, x_18);
lean_inc(x_30);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_21);
x_34 = lean_array_push(x_23, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_36 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_IR_reshape(x_34, x_36);
x_3 = x_14;
x_4 = x_19;
x_5 = x_37;
x_6 = x_31;
goto block_12;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_28);
x_40 = lean_box(7);
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_18);
lean_ctor_set(x_41, 1, x_17);
lean_inc(x_38);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_21);
x_43 = lean_array_push(x_23, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_38);
x_45 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_IR_reshape(x_43, x_45);
x_3 = x_14;
x_4 = x_19;
x_5 = x_46;
x_6 = x_39;
goto block_12;
}
}
}
block_55:
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_13 = x_48;
x_14 = x_49;
x_15 = x_50;
x_16 = x_51;
x_17 = x_52;
x_18 = x_53;
x_19 = x_54;
goto block_47;
}
block_74:
{
size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_58 = lean_array_size(x_57);
x_59 = 0;
lean_inc(x_57);
x_60 = l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__0(x_58, x_59, x_57, x_2);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_array_get_size(x_61);
x_64 = l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1;
lean_inc(x_63);
x_65 = l_Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg(x_56, x_57, x_61, x_63, x_63, x_64, x_62);
lean_dec(x_63);
lean_dec(x_57);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_N_mkFresh(x_67);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_1, 2);
lean_inc(x_73);
x_48 = x_69;
x_49 = x_61;
x_50 = x_68;
x_51 = x_72;
x_52 = x_71;
x_53 = x_73;
goto block_55;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__0(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldM_loop___at___Lean_IR_ExplicitBoxing_mkBoxedVersionAux_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_addBoxedVersions_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_12);
lean_inc(x_1);
x_13 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_1, x_12);
if (x_13 == 0)
{
lean_dec(x_12);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_IR_ExplicitBoxing_mkBoxedVersion(x_12);
x_15 = lean_array_push(x_5, x_14);
x_6 = x_15;
goto block_10;
}
}
else
{
lean_dec(x_1);
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_addBoxedVersions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0;
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_1);
x_7 = l_Array_append___redArg(x_2, x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_1);
x_9 = l_Array_append___redArg(x_2, x_4);
return x_9;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_addBoxedVersions_spec__0(x_1, x_2, x_10, x_11, x_4);
x_13 = l_Array_append___redArg(x_2, x_12);
lean_dec(x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_addBoxedVersions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_addBoxedVersions_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_getScrutineeType_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_13; 
x_6 = lean_box(1);
x_13 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_IR_CtorInfo_isScalar(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
x_7 = x_1;
goto block_12;
}
else
{
x_7 = x_5;
goto block_12;
}
}
else
{
lean_dec(x_13);
x_7 = x_1;
goto block_12;
}
block_12:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = lean_unbox(x_6);
return x_11;
}
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getScrutineeType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_17; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_array_get_size(x_1);
x_17 = lean_nat_dec_lt(x_2, x_3);
if (x_17 == 0)
{
x_4 = x_17;
goto block_16;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_3);
if (x_19 == 0)
{
x_4 = x_17;
goto block_16;
}
else
{
if (x_19 == 0)
{
x_4 = x_17;
goto block_16;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_3);
x_22 = l_Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_getScrutineeType_spec__0(x_17, x_1, x_20, x_21);
if (x_22 == 0)
{
x_4 = x_17;
goto block_16;
}
else
{
lean_object* x_23; 
lean_dec(x_3);
x_23 = lean_box(7);
return x_23;
}
}
}
}
block_16:
{
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_box(7);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(256u);
x_7 = lean_nat_dec_lt(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(65536u);
x_9 = lean_nat_dec_lt(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_cstr_to_nat("4294967296");
x_11 = lean_nat_dec_lt(x_3, x_10);
lean_dec(x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_box(7);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_box(3);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_box(2);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_box(1);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_getScrutineeType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Lean_IR_ExplicitBoxing_getScrutineeType_spec__0(x_5, x_2, x_6, x_7);
lean_dec(x_2);
x_9 = lean_box(x_8);
return x_9;
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
uint8_t x_3; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_IR_IRType_isScalar(x_1);
x_8 = l_Lean_IR_IRType_isScalar(x_2);
x_9 = lean_box(1);
x_10 = lean_box(0);
if (x_7 == 0)
{
if (x_8 == 0)
{
uint8_t x_11; 
x_11 = lean_unbox(x_9);
x_3 = x_11;
goto block_6;
}
else
{
uint8_t x_12; 
x_12 = lean_unbox(x_10);
return x_12;
}
}
else
{
if (x_8 == 0)
{
uint8_t x_13; 
x_13 = lean_unbox(x_10);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_unbox(x_9);
x_3 = x_14;
goto block_6;
}
}
block_6:
{
uint8_t x_4; 
x_4 = l_Lean_IR_IRType_isScalar(x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
uint8_t x_5; 
x_5 = l_Lean_IR_IRType_beq(x_1, x_2);
return x_5;
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh(x_1, x_2);
lean_dec(x_1);
return x_3;
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
static lean_object* _init_l_Lean_IR_ExplicitBoxing_getJPParams___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
x_8 = l_Lean_IR_ExplicitBoxing_getJPParams___closed__0;
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
x_13 = l_Lean_IR_ExplicitBoxing_getJPParams___closed__0;
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
static lean_object* _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_ExplicitBoxing_getDecl___closed__1;
x_2 = lean_box(0);
x_3 = l_Lean_IR_ExplicitBoxing_getDecl___closed__0;
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 4);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_IR_findEnvDecl_x27(x_5, x_1, x_4);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_IR_LocalContext_addParams(x_7, x_2);
lean_ctor_set(x_4, 1, x_8);
x_9 = lean_apply_2(x_3, x_4, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_15 = l_Lean_IR_LocalContext_addParams(x_11, x_2);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_14);
x_17 = lean_apply_2(x_3, x_16, x_5);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitBoxing_withParams___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ExplicitBoxing_withParams(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withVDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_IR_LocalContext_addLocal(x_9, x_2, x_3, x_4);
lean_ctor_set(x_6, 1, x_10);
x_11 = lean_apply_2(x_5, x_6, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 2);
x_15 = lean_ctor_get(x_6, 3);
x_16 = lean_ctor_get(x_6, 4);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_17 = l_Lean_IR_LocalContext_addLocal(x_13, x_2, x_3, x_4);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_16);
x_19 = lean_apply_2(x_5, x_18, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withJDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_withJDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_IR_LocalContext_addJP(x_9, x_2, x_3, x_4);
lean_ctor_set(x_6, 1, x_10);
x_11 = lean_apply_2(x_5, x_6, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 2);
x_15 = lean_ctor_get(x_6, 3);
x_16 = lean_ctor_get(x_6, 4);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_17 = l_Lean_IR_LocalContext_addJP(x_13, x_2, x_3, x_4);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_16);
x_19 = lean_apply_2(x_5, x_18, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_isExpensiveConstantValueBoxing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_9; 
x_9 = l_Lean_IR_IRType_isScalar(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
switch (lean_obj_tag(x_2)) {
case 1:
{
x_5 = x_4;
goto block_8;
}
case 2:
{
x_5 = x_4;
goto block_8;
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
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
switch (lean_obj_tag(x_16)) {
case 6:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_array_get_size(x_17);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_15);
x_21 = lean_box(0);
lean_ctor_set(x_12, 0, x_21);
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
lean_dec(x_16);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
default: 
{
lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_15);
x_22 = lean_box(0);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_24);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
}
case 11:
{
lean_object* x_35; 
lean_dec(x_27);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_24);
return x_35;
}
default: 
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_27);
lean_dec(x_25);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_24);
return x_37;
}
}
}
}
}
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___Lean_IR_ExplicitBoxing_mkCast_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at___Lean_IR_ExplicitBoxing_mkCast_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_AssocList_find_x3f___at___Lean_IR_ExplicitBoxing_mkCast_spec__0___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ExplicitBoxing_mkCast___closed__0;
x_2 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_boxed_const", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ExplicitBoxing_mkCast___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_20, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_20, 3);
lean_inc(x_26);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_unsigned_to_nat(2u);
lean_inc(x_2);
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_IR_ExplicitBoxing_mkCast___closed__1;
lean_inc(x_3);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_2);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_31);
lean_inc(x_25);
lean_inc(x_32);
x_33 = l_Lean_AssocList_find_x3f___at___Lean_IR_ExplicitBoxing_mkCast_spec__0___redArg(x_32, x_25);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_20, 3);
lean_dec(x_35);
x_36 = lean_ctor_get(x_20, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_20, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_20, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_4);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_40 = lean_ctor_get(x_4, 0);
x_41 = lean_ctor_get(x_4, 4);
lean_dec(x_41);
x_42 = lean_ctor_get(x_4, 3);
lean_dec(x_42);
x_43 = lean_ctor_get(x_4, 2);
lean_dec(x_43);
x_44 = lean_ctor_get(x_4, 1);
lean_dec(x_44);
x_45 = l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
lean_inc(x_26);
x_46 = lean_name_append_index_after(x_45, x_26);
x_47 = l_Lean_Name_append(x_40, x_46);
x_48 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_47);
x_49 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_box(0);
lean_inc(x_32);
lean_ctor_set(x_4, 4, x_50);
lean_ctor_set(x_4, 3, x_32);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 1, x_48);
lean_ctor_set(x_4, 0, x_47);
x_51 = lean_array_push(x_24, x_4);
lean_inc(x_49);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_32);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_25);
x_53 = lean_nat_add(x_26, x_27);
lean_dec(x_26);
lean_ctor_set(x_20, 3, x_53);
lean_ctor_set(x_20, 2, x_52);
lean_ctor_set(x_20, 1, x_51);
lean_ctor_set(x_6, 0, x_49);
return x_6;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_4, 0);
lean_inc(x_54);
lean_dec(x_4);
x_55 = l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
lean_inc(x_26);
x_56 = lean_name_append_index_after(x_55, x_26);
x_57 = l_Lean_Name_append(x_54, x_56);
x_58 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_57);
x_59 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_box(0);
lean_inc(x_32);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_3);
lean_ctor_set(x_61, 3, x_32);
lean_ctor_set(x_61, 4, x_60);
x_62 = lean_array_push(x_24, x_61);
lean_inc(x_59);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_32);
lean_ctor_set(x_63, 1, x_59);
lean_ctor_set(x_63, 2, x_25);
x_64 = lean_nat_add(x_26, x_27);
lean_dec(x_26);
lean_ctor_set(x_20, 3, x_64);
lean_ctor_set(x_20, 2, x_63);
lean_ctor_set(x_20, 1, x_62);
lean_ctor_set(x_6, 0, x_59);
return x_6;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_20);
x_65 = lean_ctor_get(x_4, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_66 = x_4;
} else {
 lean_dec_ref(x_4);
 x_66 = lean_box(0);
}
x_67 = l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
lean_inc(x_26);
x_68 = lean_name_append_index_after(x_67, x_26);
x_69 = l_Lean_Name_append(x_65, x_68);
x_70 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_69);
x_71 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_box(0);
lean_inc(x_32);
if (lean_is_scalar(x_66)) {
 x_73 = lean_alloc_ctor(0, 5, 0);
} else {
 x_73 = x_66;
}
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_73, 2, x_3);
lean_ctor_set(x_73, 3, x_32);
lean_ctor_set(x_73, 4, x_72);
x_74 = lean_array_push(x_24, x_73);
lean_inc(x_71);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_32);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_25);
x_76 = lean_nat_add(x_26, x_27);
lean_dec(x_26);
x_77 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_77, 0, x_23);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_76);
lean_ctor_set(x_6, 1, x_77);
lean_ctor_set(x_6, 0, x_71);
return x_6;
}
}
else
{
lean_object* x_78; 
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
x_78 = lean_ctor_get(x_33, 0);
lean_inc(x_78);
lean_dec(x_33);
lean_ctor_set(x_6, 0, x_78);
return x_6;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_79 = lean_ctor_get(x_6, 1);
lean_inc(x_79);
lean_dec(x_6);
x_80 = lean_ctor_get(x_7, 0);
lean_inc(x_80);
lean_dec(x_7);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_79, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_79, 3);
lean_inc(x_84);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_unsigned_to_nat(2u);
lean_inc(x_2);
x_87 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_87, 0, x_2);
lean_ctor_set(x_87, 1, x_85);
x_88 = l_Lean_IR_ExplicitBoxing_mkCast___closed__1;
lean_inc(x_3);
x_89 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_3);
lean_ctor_set(x_89, 2, x_87);
lean_ctor_set(x_89, 3, x_88);
x_90 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_2);
lean_ctor_set(x_90, 2, x_80);
lean_ctor_set(x_90, 3, x_89);
lean_inc(x_83);
lean_inc(x_90);
x_91 = l_Lean_AssocList_find_x3f___at___Lean_IR_ExplicitBoxing_mkCast_spec__0___redArg(x_90, x_83);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 lean_ctor_release(x_79, 2);
 lean_ctor_release(x_79, 3);
 x_92 = x_79;
} else {
 lean_dec_ref(x_79);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_4, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 x_94 = x_4;
} else {
 lean_dec_ref(x_4);
 x_94 = lean_box(0);
}
x_95 = l_Lean_IR_ExplicitBoxing_mkCast___closed__3;
lean_inc(x_84);
x_96 = lean_name_append_index_after(x_95, x_84);
x_97 = l_Lean_Name_append(x_93, x_96);
x_98 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
lean_inc(x_97);
x_99 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_box(0);
lean_inc(x_90);
if (lean_is_scalar(x_94)) {
 x_101 = lean_alloc_ctor(0, 5, 0);
} else {
 x_101 = x_94;
}
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_3);
lean_ctor_set(x_101, 3, x_90);
lean_ctor_set(x_101, 4, x_100);
x_102 = lean_array_push(x_82, x_101);
lean_inc(x_99);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_90);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_83);
x_104 = lean_nat_add(x_84, x_85);
lean_dec(x_84);
if (lean_is_scalar(x_92)) {
 x_105 = lean_alloc_ctor(0, 4, 0);
} else {
 x_105 = x_92;
}
lean_ctor_set(x_105, 0, x_81);
lean_ctor_set(x_105, 1, x_102);
lean_ctor_set(x_105, 2, x_103);
lean_ctor_set(x_105, 3, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_90);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_4);
lean_dec(x_3);
x_107 = lean_ctor_get(x_91, 0);
lean_inc(x_107);
lean_dec(x_91);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_79);
return x_108;
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
x_10 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_8);
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_apply_3(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_IR_ExplicitBoxing_getVarType(x_6, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_8, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_4);
lean_inc(x_2);
x_14 = l_Lean_IR_ExplicitBoxing_mkCast(x_6, x_8, x_2, x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
x_17 = l_Lean_IR_ExplicitBoxing_castArgIfNeeded___lam__0(x_3, x_12, x_4, x_16);
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
lean_dec(x_8);
lean_dec(x_2);
x_25 = l_Lean_IR_ExplicitBoxing_castArgIfNeeded___lam__0(x_3, x_6, x_4, x_9);
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec(x_2);
x_26 = lean_apply_3(x_3, x_1, x_4, x_5);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_ExplicitBoxing_castArgsIfNeededAux_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_27; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_12 = x_5;
} else {
 lean_dec_ref(x_5);
 x_12 = lean_box(0);
}
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_15 = x_10;
} else {
 lean_dec_ref(x_10);
 x_15 = lean_box(0);
}
x_27 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = l_Lean_IR_ExplicitBoxing_getVarType(x_28, x_6, x_7);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_1);
lean_inc(x_13);
x_32 = lean_apply_1(x_1, x_13);
x_33 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_30, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_27, 0);
lean_dec(x_35);
x_36 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_6);
lean_inc(x_32);
x_39 = l_Lean_IR_ExplicitBoxing_mkCast(x_28, x_30, x_32, x_6, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(13);
lean_inc(x_37);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_32);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_27, 0, x_37);
x_44 = lean_array_push(x_14, x_27);
x_45 = lean_array_push(x_11, x_43);
x_16 = x_45;
x_17 = x_44;
x_18 = x_41;
goto block_26;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_27);
x_46 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_31);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_6);
lean_inc(x_32);
x_49 = l_Lean_IR_ExplicitBoxing_mkCast(x_28, x_30, x_32, x_6, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(13);
lean_inc(x_47);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_32);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_47);
x_55 = lean_array_push(x_14, x_54);
x_56 = lean_array_push(x_11, x_53);
x_16 = x_56;
x_17 = x_55;
x_18 = x_51;
goto block_26;
}
}
else
{
lean_object* x_57; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_28);
x_57 = lean_array_push(x_14, x_27);
x_16 = x_11;
x_17 = x_57;
x_18 = x_31;
goto block_26;
}
}
else
{
lean_object* x_58; 
x_58 = lean_array_push(x_14, x_27);
x_16 = x_11;
x_17 = x_58;
x_18 = x_7;
goto block_26;
}
block_26:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_13, x_19);
lean_dec(x_13);
if (lean_is_scalar(x_15)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_15;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
if (lean_is_scalar(x_12)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_12;
}
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_4, x_23);
x_4 = x_24;
x_5 = x_22;
x_7 = x_18;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__0;
x_2 = l_Lean_IR_ExplicitBoxing_mkCast___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1;
x_6 = lean_array_size(x_1);
x_7 = 0;
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_IR_ExplicitBoxing_castArgsIfNeededAux_spec__0(x_2, x_1, x_6, x_7, x_5, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_10, 1);
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_16);
lean_ctor_set(x_10, 1, x_12);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_23 = x_10;
} else {
 lean_dec_ref(x_10);
 x_23 = lean_box(0);
}
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_21);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_ExplicitBoxing_castArgsIfNeededAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_IR_ExplicitBoxing_castArgsIfNeededAux_spec__0(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = l_Lean_IR_instInhabitedParam;
x_7 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_2);
lean_inc(x_4);
x_8 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_1, x_7, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_apply_3(x_3, x_11, x_4, x_10);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_IR_reshape(x_12, x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l_Lean_IR_reshape(x_12, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_castArgsIfNeeded___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(7);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lam__0___boxed), 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lam__0(x_1);
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_IR_IRType_isScalar(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(7);
lean_inc(x_11);
x_13 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_4);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_box(7);
lean_inc(x_16);
x_19 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_4);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_3);
lean_ctor_set(x_21, 3, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
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
x_9 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_7);
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
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_boxArgsIfNeeded___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_43; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_19 = x_3;
} else {
 lean_dec_ref(x_3);
 x_19 = lean_box(0);
}
x_20 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0;
x_43 = l_Lean_IR_CtorInfo_isScalar(x_17);
if (x_43 == 0)
{
x_21 = x_43;
goto block_42;
}
else
{
uint8_t x_44; 
x_44 = l_Lean_IR_IRType_isScalar(x_2);
x_21 = x_44;
goto block_42;
}
block_42:
{
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_18, x_20, x_5, x_6);
lean_dec(x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
if (lean_is_scalar(x_19)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_19;
}
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_2);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_4);
x_30 = l_Lean_IR_reshape(x_27, x_29);
lean_ctor_set(x_23, 1, x_24);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
if (lean_is_scalar(x_19)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_19;
}
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_2);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_4);
x_35 = l_Lean_IR_reshape(x_32, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
x_37 = lean_ctor_get(x_17, 1);
lean_inc(x_37);
lean_dec(x_17);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_2);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_4);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_6);
return x_41;
}
}
}
case 2:
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_3);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_3, 2);
x_47 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0;
x_48 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_46, x_47, x_5, x_6);
lean_dec(x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
lean_ctor_set(x_3, 2, x_52);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_2);
lean_ctor_set(x_54, 2, x_3);
lean_ctor_set(x_54, 3, x_4);
x_55 = l_Lean_IR_reshape(x_53, x_54);
lean_ctor_set(x_49, 1, x_50);
lean_ctor_set(x_49, 0, x_55);
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_49, 0);
x_57 = lean_ctor_get(x_49, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_49);
lean_ctor_set(x_3, 2, x_56);
x_58 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_2);
lean_ctor_set(x_58, 2, x_3);
lean_ctor_set(x_58, 3, x_4);
x_59 = l_Lean_IR_reshape(x_57, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_50);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_61 = lean_ctor_get(x_3, 0);
x_62 = lean_ctor_get(x_3, 1);
x_63 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_64 = lean_ctor_get(x_3, 2);
lean_inc(x_64);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_3);
x_65 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0;
x_66 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_64, x_65, x_5, x_6);
lean_dec(x_64);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_71 = x_67;
} else {
 lean_dec_ref(x_67);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(2, 3, 1);
lean_ctor_set(x_72, 0, x_61);
lean_ctor_set(x_72, 1, x_62);
lean_ctor_set(x_72, 2, x_69);
lean_ctor_set_uint8(x_72, sizeof(void*)*3, x_63);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_2);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_4);
x_74 = l_Lean_IR_reshape(x_70, x_73);
if (lean_is_scalar(x_71)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_71;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_68);
return x_75;
}
}
case 6:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_94; 
x_76 = lean_ctor_get(x_3, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_78 = x_3;
} else {
 lean_dec_ref(x_3);
 x_78 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_76);
x_79 = l_Lean_IR_ExplicitBoxing_getDecl(x_76, x_5, x_6);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_94 = lean_ctor_get(x_80, 1);
lean_inc(x_94);
x_82 = x_94;
goto block_93;
block_93:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = l_Lean_IR_instInhabitedParam;
x_84 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_visitVDeclExpr___lam__2___boxed), 3, 2);
lean_closure_set(x_84, 0, x_83);
lean_closure_set(x_84, 1, x_82);
lean_inc(x_5);
x_85 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_77, x_84, x_5, x_81);
lean_dec(x_77);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
if (lean_is_scalar(x_78)) {
 x_90 = lean_alloc_ctor(6, 2, 0);
} else {
 x_90 = x_78;
}
lean_ctor_set(x_90, 0, x_76);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_ctor_get(x_80, 2);
lean_inc(x_91);
lean_dec(x_80);
x_92 = l_Lean_IR_ExplicitBoxing_castResultIfNeeded(x_1, x_2, x_90, x_91, x_4, x_5, x_87);
x_7 = x_89;
x_8 = x_92;
goto block_16;
}
}
case 7:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_122; 
x_95 = lean_ctor_get(x_3, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_3, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_97 = x_3;
} else {
 lean_dec_ref(x_3);
 x_97 = lean_box(0);
}
x_98 = l_Lean_IR_ExplicitBoxing_getEnv(x_5, x_6);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_5);
lean_inc(x_95);
x_101 = l_Lean_IR_ExplicitBoxing_getDecl(x_95, x_5, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0;
x_122 = l_Lean_IR_ExplicitBoxing_requiresBoxedVersion(x_99, x_102);
if (x_122 == 0)
{
x_105 = x_95;
goto block_121;
}
else
{
lean_object* x_123; 
x_123 = l_Lean_IR_ExplicitBoxing_mkBoxedName(x_95);
x_105 = x_123;
goto block_121;
}
block_121:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_96, x_104, x_5, x_103);
lean_dec(x_96);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = !lean_is_exclusive(x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_107, 0);
x_111 = lean_ctor_get(x_107, 1);
if (lean_is_scalar(x_97)) {
 x_112 = lean_alloc_ctor(7, 2, 0);
} else {
 x_112 = x_97;
}
lean_ctor_set(x_112, 0, x_105);
lean_ctor_set(x_112, 1, x_110);
x_113 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_2);
lean_ctor_set(x_113, 2, x_112);
lean_ctor_set(x_113, 3, x_4);
x_114 = l_Lean_IR_reshape(x_111, x_113);
lean_ctor_set(x_107, 1, x_108);
lean_ctor_set(x_107, 0, x_114);
return x_107;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_107, 0);
x_116 = lean_ctor_get(x_107, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_107);
if (lean_is_scalar(x_97)) {
 x_117 = lean_alloc_ctor(7, 2, 0);
} else {
 x_117 = x_97;
}
lean_ctor_set(x_117, 0, x_105);
lean_ctor_set(x_117, 1, x_115);
x_118 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_118, 0, x_1);
lean_ctor_set(x_118, 1, x_2);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_4);
x_119 = l_Lean_IR_reshape(x_116, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_108);
return x_120;
}
}
}
case 8:
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_3);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_125 = lean_ctor_get(x_3, 1);
x_126 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0;
x_127 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_125, x_126, x_5, x_6);
lean_dec(x_125);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
lean_ctor_set(x_3, 1, x_130);
x_132 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___redArg(x_1, x_2, x_3, x_4, x_129);
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_132, 0);
x_135 = l_Lean_IR_reshape(x_131, x_134);
lean_ctor_set(x_132, 0, x_135);
return x_132;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_132, 0);
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_132);
x_138 = l_Lean_IR_reshape(x_131, x_136);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_140 = lean_ctor_get(x_3, 0);
x_141 = lean_ctor_get(x_3, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_3);
x_142 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0;
x_143 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_141, x_142, x_5, x_6);
lean_dec(x_141);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_148, 0, x_140);
lean_ctor_set(x_148, 1, x_146);
x_149 = l_Lean_IR_ExplicitBoxing_unboxResultIfNeeded___redArg(x_1, x_2, x_148, x_4, x_145);
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
x_153 = l_Lean_IR_reshape(x_147, x_150);
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
default: 
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_5);
x_155 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_155, 0, x_1);
lean_ctor_set(x_155, 1, x_2);
lean_ctor_set(x_155, 2, x_3);
lean_ctor_set(x_155, 3, x_4);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_6);
return x_156;
}
}
block_16:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_IR_reshape(x_7, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = l_Lean_IR_reshape(x_7, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitVDeclExpr___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_visitVDeclExpr___lam__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_visitFnBody_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_box(0);
x_10 = lean_array_uset(x_3, x_2, x_9);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_4);
x_20 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_19, x_4, x_5);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set(x_8, 1, x_21);
x_11 = x_8;
x_12 = x_22;
goto block_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
lean_inc(x_4);
x_25 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_24, x_4, x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_26);
x_11 = x_28;
x_12 = x_27;
goto block_17;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_8, 0);
lean_inc(x_4);
x_31 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_30, x_4, x_5);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_ctor_set(x_8, 0, x_32);
x_11 = x_8;
x_12 = x_33;
goto block_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_8, 0);
lean_inc(x_34);
lean_dec(x_8);
lean_inc(x_4);
x_35 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_34, x_4, x_5);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_11 = x_38;
x_12 = x_37;
goto block_17;
}
}
block_17:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_10, x_2, x_11);
x_2 = x_14;
x_3 = x_15;
x_5 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_4);
lean_ctor_set(x_9, 5, x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 3, x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_apply_3(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
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
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_87 = lean_ctor_get(x_1, 0);
x_88 = lean_ctor_get(x_1, 1);
x_89 = lean_ctor_get(x_1, 2);
x_90 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_91 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_90, x_2, x_3);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_IR_ExplicitBoxing_getVarType(x_89, x_2, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_box(5);
x_98 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_95, x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_99 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_96);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_2);
x_102 = l_Lean_IR_ExplicitBoxing_mkCast(x_89, x_95, x_97, x_2, x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_100);
x_105 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0(x_87, x_88, x_92, x_100, x_2, x_104);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_105, 0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 3, x_107);
lean_ctor_set(x_1, 2, x_103);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_100);
lean_ctor_set(x_105, 0, x_1);
return x_105;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_105, 0);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_105);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 3, x_108);
lean_ctor_set(x_1, 2, x_103);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_100);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
else
{
lean_object* x_111; 
lean_dec(x_95);
lean_free_object(x_1);
x_111 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0(x_87, x_88, x_92, x_89, x_2, x_96);
lean_dec(x_2);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_112 = lean_ctor_get(x_1, 0);
x_113 = lean_ctor_get(x_1, 1);
x_114 = lean_ctor_get(x_1, 2);
x_115 = lean_ctor_get(x_1, 3);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_1);
lean_inc(x_2);
x_116 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_115, x_2, x_3);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_IR_ExplicitBoxing_getVarType(x_114, x_2, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_box(5);
x_123 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_120, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_124 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_121);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_2);
x_127 = l_Lean_IR_ExplicitBoxing_mkCast(x_114, x_120, x_122, x_2, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_125);
x_130 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0(x_112, x_113, x_117, x_125, x_2, x_129);
lean_dec(x_2);
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
x_134 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_122);
lean_ctor_set(x_134, 2, x_128);
lean_ctor_set(x_134, 3, x_131);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
return x_135;
}
else
{
lean_object* x_136; 
lean_dec(x_120);
x_136 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0(x_112, x_113, x_117, x_114, x_2, x_121);
lean_dec(x_2);
return x_136;
}
}
}
case 5:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_137 = lean_ctor_get(x_1, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_1, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_1, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_1, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_1, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_1, 5);
lean_inc(x_142);
lean_dec(x_1);
lean_inc(x_2);
x_143 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_142, x_2, x_3);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lean_IR_ExplicitBoxing_getVarType(x_140, x_2, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_147, x_141);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_150 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_148);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
lean_inc(x_2);
lean_inc(x_141);
x_153 = l_Lean_IR_ExplicitBoxing_mkCast(x_140, x_147, x_141, x_2, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_151);
lean_inc(x_141);
x_156 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__1(x_137, x_138, x_139, x_141, x_144, x_151, x_2, x_155);
lean_dec(x_2);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_156, 0);
x_159 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_159, 0, x_151);
lean_ctor_set(x_159, 1, x_141);
lean_ctor_set(x_159, 2, x_154);
lean_ctor_set(x_159, 3, x_158);
lean_ctor_set(x_156, 0, x_159);
return x_156;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_156, 0);
x_161 = lean_ctor_get(x_156, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_156);
x_162 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_162, 0, x_151);
lean_ctor_set(x_162, 1, x_141);
lean_ctor_set(x_162, 2, x_154);
lean_ctor_set(x_162, 3, x_160);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
else
{
lean_object* x_164; 
lean_dec(x_147);
x_164 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__1(x_137, x_138, x_139, x_141, x_144, x_140, x_2, x_148);
lean_dec(x_2);
return x_164;
}
}
case 9:
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_1);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = lean_ctor_get(x_1, 1);
x_167 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_166, x_2, x_3);
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_167, 0);
lean_ctor_set(x_1, 1, x_169);
lean_ctor_set(x_167, 0, x_1);
return x_167;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_167, 0);
x_171 = lean_ctor_get(x_167, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_167);
lean_ctor_set(x_1, 1, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_1);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_173 = lean_ctor_get(x_1, 0);
x_174 = lean_ctor_get(x_1, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_1);
x_175 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_174, x_2, x_3);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
x_179 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_179, 0, x_173);
lean_ctor_set(x_179, 1, x_176);
if (lean_is_scalar(x_178)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_178;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_177);
return x_180;
}
}
case 10:
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_1);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; size_t x_186; size_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_182 = lean_ctor_get(x_1, 0);
x_183 = lean_ctor_get(x_1, 1);
x_184 = lean_ctor_get(x_1, 3);
x_185 = lean_ctor_get(x_1, 2);
lean_dec(x_185);
x_186 = lean_array_size(x_184);
x_187 = 0;
lean_inc(x_2);
lean_inc(x_184);
x_188 = l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_visitFnBody_spec__0(x_186, x_187, x_184, x_2, x_3);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_IR_ExplicitBoxing_getVarType(x_183, x_2, x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_184);
lean_dec(x_184);
x_195 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_192, x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_196 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_193);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
lean_inc(x_2);
lean_inc(x_194);
x_199 = l_Lean_IR_ExplicitBoxing_mkCast(x_183, x_192, x_194, x_2, x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
lean_inc(x_197);
lean_inc(x_194);
x_202 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2(x_182, x_194, x_189, x_197, x_2, x_201);
lean_dec(x_2);
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_202, 0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 3, x_204);
lean_ctor_set(x_1, 2, x_200);
lean_ctor_set(x_1, 1, x_194);
lean_ctor_set(x_1, 0, x_197);
lean_ctor_set(x_202, 0, x_1);
return x_202;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_202, 0);
x_206 = lean_ctor_get(x_202, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_202);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 3, x_205);
lean_ctor_set(x_1, 2, x_200);
lean_ctor_set(x_1, 1, x_194);
lean_ctor_set(x_1, 0, x_197);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_1);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
else
{
lean_object* x_208; 
lean_dec(x_192);
lean_free_object(x_1);
x_208 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2(x_182, x_194, x_189, x_183, x_2, x_193);
lean_dec(x_2);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; size_t x_212; size_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_209 = lean_ctor_get(x_1, 0);
x_210 = lean_ctor_get(x_1, 1);
x_211 = lean_ctor_get(x_1, 3);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_1);
x_212 = lean_array_size(x_211);
x_213 = 0;
lean_inc(x_2);
lean_inc(x_211);
x_214 = l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_visitFnBody_spec__0(x_212, x_213, x_211, x_2, x_3);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = l_Lean_IR_ExplicitBoxing_getVarType(x_210, x_2, x_216);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = l_Lean_IR_ExplicitBoxing_getScrutineeType(x_211);
lean_dec(x_211);
x_221 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_218, x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_222 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_219);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
lean_inc(x_2);
lean_inc(x_220);
x_225 = l_Lean_IR_ExplicitBoxing_mkCast(x_210, x_218, x_220, x_2, x_224);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
lean_inc(x_223);
lean_inc(x_220);
x_228 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2(x_209, x_220, x_215, x_223, x_2, x_227);
lean_dec(x_2);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_231 = x_228;
} else {
 lean_dec_ref(x_228);
 x_231 = lean_box(0);
}
x_232 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_232, 0, x_223);
lean_ctor_set(x_232, 1, x_220);
lean_ctor_set(x_232, 2, x_226);
lean_ctor_set(x_232, 3, x_229);
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_231;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_230);
return x_233;
}
else
{
lean_object* x_234; 
lean_dec(x_218);
x_234 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2(x_209, x_220, x_215, x_210, x_2, x_219);
lean_dec(x_2);
return x_234;
}
}
}
case 11:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_235 = lean_ctor_get(x_1, 0);
lean_inc(x_235);
lean_dec(x_1);
x_236 = l_Lean_IR_ExplicitBoxing_getResultType(x_2, x_3);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_visitFnBody___lam__3___boxed), 3, 0);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_240 = lean_ctor_get(x_235, 0);
lean_inc(x_240);
lean_dec(x_235);
x_241 = l_Lean_IR_ExplicitBoxing_getVarType(x_240, x_2, x_238);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_IR_ExplicitBoxing_eqvTypes(x_242, x_237);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_245 = l___private_Lean_Compiler_IR_Boxing_0__Lean_IR_ExplicitBoxing_M_mkFresh___redArg(x_243);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
lean_inc(x_2);
lean_inc(x_237);
x_248 = l_Lean_IR_ExplicitBoxing_mkCast(x_240, x_242, x_237, x_2, x_247);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
lean_inc(x_246);
x_251 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__4(x_239, x_246, x_2, x_250);
x_252 = !lean_is_exclusive(x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_251, 0);
x_254 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_254, 0, x_246);
lean_ctor_set(x_254, 1, x_237);
lean_ctor_set(x_254, 2, x_249);
lean_ctor_set(x_254, 3, x_253);
lean_ctor_set(x_251, 0, x_254);
return x_251;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = lean_ctor_get(x_251, 0);
x_256 = lean_ctor_get(x_251, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_251);
x_257 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_257, 0, x_246);
lean_ctor_set(x_257, 1, x_237);
lean_ctor_set(x_257, 2, x_249);
lean_ctor_set(x_257, 3, x_255);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
else
{
lean_object* x_259; 
lean_dec(x_242);
lean_dec(x_237);
x_259 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__4(x_239, x_240, x_2, x_243);
return x_259;
}
}
else
{
lean_object* x_260; 
lean_dec(x_239);
lean_dec(x_237);
x_260 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__3(x_235, x_2, x_238);
lean_dec(x_2);
return x_260;
}
}
case 12:
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_1);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_262 = lean_ctor_get(x_1, 0);
x_263 = lean_ctor_get(x_1, 1);
x_264 = l_Lean_IR_ExplicitBoxing_getJPParams(x_262, x_2, x_3);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = l_Lean_IR_instInhabitedParam;
x_268 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_visitFnBody___lam__5___boxed), 3, 2);
lean_closure_set(x_268, 0, x_267);
lean_closure_set(x_268, 1, x_265);
x_269 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_263, x_268, x_2, x_266);
lean_dec(x_263);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = !lean_is_exclusive(x_270);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_270, 0);
x_274 = lean_ctor_get(x_270, 1);
lean_ctor_set(x_1, 1, x_273);
x_275 = l_Lean_IR_reshape(x_274, x_1);
lean_ctor_set(x_270, 1, x_271);
lean_ctor_set(x_270, 0, x_275);
return x_270;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_270, 0);
x_277 = lean_ctor_get(x_270, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_270);
lean_ctor_set(x_1, 1, x_276);
x_278 = l_Lean_IR_reshape(x_277, x_1);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_271);
return x_279;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_280 = lean_ctor_get(x_1, 0);
x_281 = lean_ctor_get(x_1, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_1);
x_282 = l_Lean_IR_ExplicitBoxing_getJPParams(x_280, x_2, x_3);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = l_Lean_IR_instInhabitedParam;
x_286 = lean_alloc_closure((void*)(l_Lean_IR_ExplicitBoxing_visitFnBody___lam__5___boxed), 3, 2);
lean_closure_set(x_286, 0, x_285);
lean_closure_set(x_286, 1, x_283);
x_287 = l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux(x_281, x_286, x_2, x_284);
lean_dec(x_281);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = lean_ctor_get(x_288, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_288, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_292 = x_288;
} else {
 lean_dec_ref(x_288);
 x_292 = lean_box(0);
}
x_293 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_293, 0, x_280);
lean_ctor_set(x_293, 1, x_290);
x_294 = l_Lean_IR_reshape(x_291, x_293);
if (lean_is_scalar(x_292)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_292;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_289);
return x_295;
}
}
default: 
{
lean_object* x_296; 
lean_dec(x_2);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_1);
lean_ctor_set(x_296, 1, x_3);
return x_296;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_visitFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitBoxing_visitFnBody_spec__0(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_visitFnBody___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitBoxing_visitFnBody___lam__5(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_run_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_5, x_6);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 3);
lean_inc(x_18);
lean_inc(x_14);
x_19 = l_Lean_IR_Decl_maxIndex(x_14);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_19, x_20);
lean_dec(x_19);
x_22 = l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0;
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_20);
lean_inc(x_1);
x_25 = l_Lean_IR_LocalContext_addParams(x_1, x_16);
lean_dec(x_16);
lean_inc(x_3);
lean_inc(x_2);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_17);
lean_ctor_set(x_26, 3, x_2);
lean_ctor_set(x_26, 4, x_3);
x_27 = l_Lean_IR_ExplicitBoxing_visitFnBody(x_18, x_26, x_24);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Array_append___redArg(x_7, x_30);
lean_dec(x_30);
x_32 = l_Lean_IR_Decl_updateBody_x21(x_14, x_29);
x_33 = l_Lean_IR_Decl_elimDead(x_32);
x_34 = lean_array_push(x_31, x_33);
x_8 = x_34;
goto block_12;
}
else
{
lean_object* x_35; 
x_35 = lean_array_push(x_7, x_14);
x_8 = x_35;
goto block_12;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_5, x_9);
x_5 = x_10;
x_7 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitBoxing_run(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0;
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_4);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_box(0);
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_run_spec__0(x_10, x_2, x_1, x_2, x_11, x_12, x_4);
lean_dec(x_2);
x_14 = l_Lean_IR_ExplicitBoxing_addBoxedVersions(x_1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_run_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitBoxing_run_spec__0(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_IR_getEnv___redArg(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_IR_ExplicitBoxing_run(x_5, x_1);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = l_Lean_IR_ExplicitBoxing_run(x_7, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_explicitBoxing(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_explicitBoxing___redArg(x_1, x_3);
return x_4;
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
lean_object* initialize_Lean_Runtime(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_FreeVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_ElimDeadVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_AssocList(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Boxing(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
res = initialize_Lean_Data_AssocList(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__0 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedName___closed__0);
l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__0 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__0);
l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1 = _init_l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkBoxedVersionAux___closed__1);
l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0 = _init_l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_addBoxedVersions___closed__0);
l_Lean_IR_ExplicitBoxing_getJPParams___closed__0 = _init_l_Lean_IR_ExplicitBoxing_getJPParams___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_getJPParams___closed__0);
l_Lean_IR_ExplicitBoxing_getDecl___closed__0 = _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_getDecl___closed__0);
l_Lean_IR_ExplicitBoxing_getDecl___closed__1 = _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_getDecl___closed__1);
l_Lean_IR_ExplicitBoxing_getDecl___closed__2 = _init_l_Lean_IR_ExplicitBoxing_getDecl___closed__2();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_getDecl___closed__2);
l_Lean_IR_ExplicitBoxing_mkCast___closed__0 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__0);
l_Lean_IR_ExplicitBoxing_mkCast___closed__1 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__1);
l_Lean_IR_ExplicitBoxing_mkCast___closed__2 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__2();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__2);
l_Lean_IR_ExplicitBoxing_mkCast___closed__3 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__3();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__3);
l_Lean_IR_ExplicitBoxing_mkCast___closed__4 = _init_l_Lean_IR_ExplicitBoxing_mkCast___closed__4();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_mkCast___closed__4);
l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__0 = _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__0);
l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1 = _init_l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_castArgsIfNeededAux___closed__1);
l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0 = _init_l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitBoxing_visitVDeclExpr___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
