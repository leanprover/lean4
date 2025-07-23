// Lean compiler output
// Module: Lean.Compiler.IR.Checker
// Imports: Lean.Compiler.IR.CompilerM Lean.Compiler.IR.Format
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorFields;
static lean_object* l_Lean_IR_Checker_maxCtorFields___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_max_ctor_scalars_size(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_usize_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_usizeSize;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_IR_Checker_getDecl___closed__2;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_mkIndexSet_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorScalarsSize;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_max_ctor_fields(lean_object*);
static lean_object* l_Lean_IR_Checker_checkType___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_max_ctor_tag(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_mkIndexSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Checker_checkFullApp___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_usizeSize___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkVar___closed__2;
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__6;
static lean_object* l_Lean_IR_Checker_checkExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__1;
lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkObjType___closed__0;
static lean_object* l_Lean_IR_Checker_checkType___closed__1;
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_markIndex___closed__0;
static lean_object* l_Lean_IR_Checker_withParams___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorTag___boxed(lean_object*);
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__2;
lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__0;
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorFields___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__0;
uint8_t l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_466_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkVar___closed__1;
static lean_object* l_Lean_IR_Checker_maxCtorTag___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_markIndex___closed__1;
static lean_object* l_Lean_IR_Checker_checkExpr___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorTag;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkEqTypes___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_maxCtorScalarsSize___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__1;
LEAN_EXPORT uint8_t l_Lean_IR_Checker_throwCheckerError___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_getDecl___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__0;
static lean_object* l_Lean_IR_Checker_checkJP___closed__0;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_getDecl___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_IR_Checker_withParams___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___lam__0___boxed(lean_object*);
static lean_object* l_Lean_IR_Checker_checkVar___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__3;
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkScalarType___closed__0;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorScalarsSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkJP___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorFields___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_max_ctor_fields(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorFields___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_max_ctor_fields(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorFields() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Checker_maxCtorFields___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorScalarsSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_max_ctor_scalars_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorScalarsSize___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_max_ctor_scalars_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorScalarsSize() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Checker_maxCtorScalarsSize___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorTag___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_max_ctor_tag(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorTag___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_max_ctor_tag(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_maxCtorTag() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Checker_maxCtorTag___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_usize_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_usizeSize___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_usize_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_usizeSize() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Checker_usizeSize___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___redArg(x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Checker_throwCheckerError___redArg___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to compile definition, compiler IR check failed at '", 59, 59);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'. Error: ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_21; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_IR_Checker_throwCheckerError___redArg___lam__0___boxed), 1, 0);
x_21 = lean_ctor_get(x_7, 0);
lean_inc(x_21);
lean_dec_ref(x_7);
x_9 = x_21;
goto block_20;
block_20:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = l_Lean_IR_Checker_throwCheckerError___redArg___closed__0;
x_11 = 1;
x_12 = l_Lean_Name_toString(x_9, x_11, x_8);
x_13 = lean_string_append(x_10, x_12);
lean_dec_ref(x_12);
x_14 = l_Lean_IR_Checker_throwCheckerError___redArg___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_1);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_MessageData_ofFormat(x_17);
x_19 = l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___redArg(x_18, x_4, x_5, x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_throwCheckerError___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Checker_throwCheckerError___redArg___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_throwCheckerError___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_throwCheckerError(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_Checker_markIndex___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("variable / joinpoint index ", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_markIndex___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" has already been used", 22, 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_st_ref_get(x_3, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_mkIndexSet_spec__0___redArg(x_1, x_18);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec_ref(x_2);
x_21 = lean_st_ref_take(x_3, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_box(0);
x_25 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_mkIndexSet_spec__0___redArg(x_1, x_22);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_mkIndexSet_spec__1___redArg(x_1, x_24, x_22);
x_7 = x_23;
x_8 = x_24;
x_9 = x_3;
x_10 = x_26;
goto block_16;
}
else
{
lean_dec(x_1);
x_7 = x_23;
x_8 = x_24;
x_9 = x_3;
x_10 = x_22;
goto block_16;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lean_IR_Checker_markIndex___closed__0;
x_28 = l_Nat_reprFast(x_1);
x_29 = lean_string_append(x_27, x_28);
lean_dec_ref(x_28);
x_30 = l_Lean_IR_Checker_markIndex___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Lean_IR_Checker_throwCheckerError___redArg(x_31, x_2, x_3, x_4, x_5, x_19);
lean_dec_ref(x_31);
return x_32;
}
block_16:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_set(x_9, x_10, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markVar(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markJP(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_Checker_getDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Checker_throwCheckerError___redArg___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_getDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("depends on declaration '", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_getDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', which has no executable code; consider marking definition as 'noncomputable'", 79, 79);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_12);
lean_inc(x_1);
x_13 = l_Lean_IR_findEnvDecl_x27(x_11, x_1, x_12);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_7);
x_14 = l_Lean_IR_Checker_getDecl___closed__0;
x_15 = l_Lean_IR_Checker_getDecl___closed__1;
x_16 = 1;
x_17 = l_Lean_Name_toString(x_1, x_16, x_14);
x_18 = lean_string_append(x_15, x_17);
lean_dec_ref(x_17);
x_19 = l_Lean_IR_Checker_getDecl___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_IR_Checker_throwCheckerError___redArg(x_20, x_2, x_3, x_4, x_5, x_10);
lean_dec_ref(x_20);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec_ref(x_13);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_26);
lean_inc(x_1);
x_27 = l_Lean_IR_findEnvDecl_x27(x_25, x_1, x_26);
lean_dec_ref(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = l_Lean_IR_Checker_getDecl___closed__0;
x_29 = l_Lean_IR_Checker_getDecl___closed__1;
x_30 = 1;
x_31 = l_Lean_Name_toString(x_1, x_30, x_28);
x_32 = lean_string_append(x_29, x_31);
lean_dec_ref(x_31);
x_33 = l_Lean_IR_Checker_getDecl___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = l_Lean_IR_Checker_throwCheckerError___redArg(x_34, x_2, x_3, x_4, x_5, x_24);
lean_dec_ref(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec_ref(x_27);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_24);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_getDecl(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkVar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown variable '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x_", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = l_Lean_IR_LocalContext_isLocalVar(x_19, x_1);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_IR_LocalContext_isParam(x_19, x_1);
lean_dec(x_19);
x_7 = x_21;
goto block_18;
}
else
{
lean_dec(x_19);
x_7 = x_20;
goto block_18;
}
block_18:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_IR_Checker_checkVar___closed__0;
x_9 = l_Lean_IR_Checker_checkVar___closed__1;
x_10 = l_Nat_reprFast(x_1);
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
x_12 = lean_string_append(x_8, x_11);
lean_dec_ref(x_11);
x_13 = l_Lean_IR_Checker_checkVar___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lean_IR_Checker_throwCheckerError___redArg(x_14, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkVar(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkJP___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown join point '", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkJP___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("block_", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_IR_LocalContext_isJP(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_Lean_IR_Checker_checkJP___closed__0;
x_10 = l_Lean_IR_Checker_checkJP___closed__1;
x_11 = l_Nat_reprFast(x_1);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = lean_string_append(x_9, x_12);
lean_dec_ref(x_12);
x_14 = l_Lean_IR_Checker_checkVar___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_Checker_throwCheckerError___redArg(x_15, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkJP(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_IR_Checker_checkVar(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
lean_inc_ref(x_5);
x_12 = l_Lean_IR_Checker_checkArg(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_13;
x_9 = x_14;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_12;
}
}
else
{
lean_object* x_18; 
lean_dec_ref(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_1);
x_9 = lean_box(0);
x_10 = lean_nat_dec_lt(x_7, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
lean_dec_ref(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(x_1, x_14, x_15, x_9, x_2, x_3, x_4, x_5, x_6);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkArgs(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkEqTypes___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected type '{ty₁}' != '{ty₂}'", 38, 34);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_466_(x_1, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_IR_Checker_checkEqTypes___closed__0;
x_10 = l_Lean_IR_Checker_throwCheckerError___redArg(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_checkEqTypes(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected type '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_9 = lean_apply_1(x_2, x_1);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = l_Lean_IR_Checker_checkType___closed__0;
x_12 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_13 = lean_unsigned_to_nat(120u);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_format_pretty(x_12, x_13, x_14, x_14);
x_16 = lean_string_append(x_11, x_15);
lean_dec_ref(x_15);
x_17 = l_Lean_IR_Checker_checkVar___closed__2;
x_18 = lean_string_append(x_16, x_17);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_19; 
x_19 = l_Lean_IR_Checker_throwCheckerError___redArg(x_18, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = l_Lean_IR_Checker_checkType___closed__1;
x_22 = lean_string_append(x_18, x_21);
x_23 = lean_string_append(x_22, x_20);
x_24 = l_Lean_IR_Checker_throwCheckerError___redArg(x_23, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_4);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_Checker_checkType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkObjType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("object expected", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_IR_IRType_isObj(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = l_Lean_IR_Checker_checkObjType___closed__0;
x_9 = l_Lean_IR_Checker_checkType___closed__0;
x_10 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_11 = lean_unsigned_to_nat(120u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_format_pretty(x_10, x_11, x_12, x_12);
x_14 = lean_string_append(x_9, x_13);
lean_dec_ref(x_13);
x_15 = l_Lean_IR_Checker_checkVar___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_Checker_checkType___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_8);
x_20 = l_Lean_IR_Checker_throwCheckerError___redArg(x_19, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkObjType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkScalarType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scalar expected", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_IR_IRType_isScalar(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = l_Lean_IR_Checker_checkScalarType___closed__0;
x_9 = l_Lean_IR_Checker_checkType___closed__0;
x_10 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_11 = lean_unsigned_to_nat(120u);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_format_pretty(x_10, x_11, x_12, x_12);
x_14 = lean_string_append(x_9, x_13);
lean_dec_ref(x_13);
x_15 = l_Lean_IR_Checker_checkVar___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_Checker_checkType___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_8);
x_20 = l_Lean_IR_Checker_throwCheckerError___redArg(x_19, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkScalarType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_IR_LocalContext_getType(x_7, x_1);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_Lean_IR_Checker_checkVar___closed__0;
x_10 = l_Lean_IR_Checker_checkVar___closed__1;
x_11 = l_Nat_reprFast(x_1);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = lean_string_append(x_9, x_12);
lean_dec_ref(x_12);
x_14 = l_Lean_IR_Checker_checkVar___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_Lean_IR_Checker_throwCheckerError___redArg(x_15, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec_ref(x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_getType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_4);
x_9 = l_Lean_IR_Checker_getType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_13 = lean_apply_1(x_2, x_11);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_9);
x_15 = l_Lean_IR_Checker_checkType___closed__0;
x_16 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_11);
x_17 = lean_unsigned_to_nat(120u);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_format_pretty(x_16, x_17, x_18, x_18);
x_20 = lean_string_append(x_15, x_19);
lean_dec_ref(x_19);
x_21 = l_Lean_IR_Checker_checkVar___closed__2;
x_22 = lean_string_append(x_20, x_21);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_23; 
x_23 = l_Lean_IR_Checker_throwCheckerError___redArg(x_22, x_4, x_5, x_6, x_7, x_12);
lean_dec_ref(x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = l_Lean_IR_Checker_checkType___closed__1;
x_26 = lean_string_append(x_22, x_25);
x_27 = lean_string_append(x_26, x_24);
x_28 = l_Lean_IR_Checker_throwCheckerError___redArg(x_27, x_4, x_5, x_6, x_7, x_12);
lean_dec_ref(x_27);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_11);
lean_dec_ref(x_4);
x_29 = lean_box(0);
lean_ctor_set(x_9, 0, x_29);
return x_9;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
lean_inc(x_30);
x_32 = lean_apply_1(x_2, x_30);
x_33 = lean_unbox(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = l_Lean_IR_Checker_checkType___closed__0;
x_35 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_30);
x_36 = lean_unsigned_to_nat(120u);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_format_pretty(x_35, x_36, x_37, x_37);
x_39 = lean_string_append(x_34, x_38);
lean_dec_ref(x_38);
x_40 = l_Lean_IR_Checker_checkVar___closed__2;
x_41 = lean_string_append(x_39, x_40);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_42; 
x_42 = l_Lean_IR_Checker_throwCheckerError___redArg(x_41, x_4, x_5, x_6, x_7, x_31);
lean_dec_ref(x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_3, 0);
x_44 = l_Lean_IR_Checker_checkType___closed__1;
x_45 = lean_string_append(x_41, x_44);
x_46 = lean_string_append(x_45, x_43);
x_47 = l_Lean_IR_Checker_throwCheckerError___redArg(x_46, x_4, x_5, x_6, x_7, x_31);
lean_dec_ref(x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_30);
lean_dec_ref(x_4);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_31);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_50 = !lean_is_exclusive(x_9);
if (x_50 == 0)
{
return x_9;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_9, 0);
x_52 = lean_ctor_get(x_9, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_9);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_Checker_checkVarType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_2);
x_7 = l_Lean_IR_Checker_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_IR_IRType_isObj(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_7);
x_12 = l_Lean_IR_Checker_checkObjType___closed__0;
x_13 = l_Lean_IR_Checker_checkType___closed__0;
x_14 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_9);
x_15 = lean_unsigned_to_nat(120u);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_format_pretty(x_14, x_15, x_16, x_16);
x_18 = lean_string_append(x_13, x_17);
lean_dec_ref(x_17);
x_19 = l_Lean_IR_Checker_checkVar___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_IR_Checker_checkType___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_12);
x_24 = l_Lean_IR_Checker_throwCheckerError___redArg(x_23, x_2, x_3, x_4, x_5, x_10);
lean_dec_ref(x_23);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_9);
lean_dec_ref(x_2);
x_25 = lean_box(0);
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = l_Lean_IR_IRType_isObj(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = l_Lean_IR_Checker_checkObjType___closed__0;
x_30 = l_Lean_IR_Checker_checkType___closed__0;
x_31 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_26);
x_32 = lean_unsigned_to_nat(120u);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_format_pretty(x_31, x_32, x_33, x_33);
x_35 = lean_string_append(x_30, x_34);
lean_dec_ref(x_34);
x_36 = l_Lean_IR_Checker_checkVar___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Lean_IR_Checker_checkType___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_39, x_29);
x_41 = l_Lean_IR_Checker_throwCheckerError___redArg(x_40, x_2, x_3, x_4, x_5, x_27);
lean_dec_ref(x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_26);
lean_dec_ref(x_2);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_27);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec_ref(x_2);
x_44 = !lean_is_exclusive(x_7);
if (x_44 == 0)
{
return x_7;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_7, 0);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_7);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkObjVar(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_2);
x_7 = l_Lean_IR_Checker_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_IR_IRType_isScalar(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_7);
x_12 = l_Lean_IR_Checker_checkScalarType___closed__0;
x_13 = l_Lean_IR_Checker_checkType___closed__0;
x_14 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_9);
x_15 = lean_unsigned_to_nat(120u);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_format_pretty(x_14, x_15, x_16, x_16);
x_18 = lean_string_append(x_13, x_17);
lean_dec_ref(x_17);
x_19 = l_Lean_IR_Checker_checkVar___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_IR_Checker_checkType___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_12);
x_24 = l_Lean_IR_Checker_throwCheckerError___redArg(x_23, x_2, x_3, x_4, x_5, x_10);
lean_dec_ref(x_23);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_9);
lean_dec_ref(x_2);
x_25 = lean_box(0);
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = l_Lean_IR_IRType_isScalar(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = l_Lean_IR_Checker_checkScalarType___closed__0;
x_30 = l_Lean_IR_Checker_checkType___closed__0;
x_31 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_26);
x_32 = lean_unsigned_to_nat(120u);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_format_pretty(x_31, x_32, x_33, x_33);
x_35 = lean_string_append(x_30, x_34);
lean_dec_ref(x_34);
x_36 = l_Lean_IR_Checker_checkVar___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Lean_IR_Checker_checkType___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_string_append(x_39, x_29);
x_41 = l_Lean_IR_Checker_throwCheckerError___redArg(x_40, x_2, x_3, x_4, x_5, x_27);
lean_dec_ref(x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_26);
lean_dec_ref(x_2);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_27);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec_ref(x_2);
x_44 = !lean_is_exclusive(x_7);
if (x_44 == 0)
{
return x_7;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_7, 0);
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_7);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkScalarVar(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Checker_checkFullApp___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("incorrect number of arguments to '", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" provided, ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkFullApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" expected", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc_ref(x_3);
lean_inc(x_1);
x_8 = l_Lean_IR_Checker_getDecl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_34; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_array_get_size(x_2);
x_34 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_34);
lean_dec(x_9);
x_12 = x_34;
goto block_33;
block_33:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_12);
lean_dec_ref(x_12);
x_14 = lean_nat_dec_eq(x_11, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_15 = lean_box(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_IR_Checker_checkFullApp___lam__0___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_Lean_IR_Checker_checkFullApp___closed__0;
x_18 = 1;
x_19 = l_Lean_Name_toString(x_1, x_18, x_16);
x_20 = lean_string_append(x_17, x_19);
lean_dec_ref(x_19);
x_21 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Nat_reprFast(x_11);
x_24 = lean_string_append(x_22, x_23);
lean_dec_ref(x_23);
x_25 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = l_Nat_reprFast(x_13);
x_28 = lean_string_append(x_26, x_27);
lean_dec_ref(x_27);
x_29 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_30 = lean_string_append(x_28, x_29);
x_31 = l_Lean_IR_Checker_throwCheckerError___redArg(x_30, x_3, x_4, x_5, x_6, x_10);
lean_dec_ref(x_30);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_32 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_4, x_5, x_6, x_10);
return x_32;
}
}
}
else
{
uint8_t x_35; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_IR_Checker_checkFullApp___lam__0(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_checkFullApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("too many arguments to partial application '", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', num. args: ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", arity: ", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc_ref(x_3);
lean_inc(x_1);
x_8 = l_Lean_IR_Checker_getDecl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_31; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_IR_Checker_getDecl___closed__0;
x_12 = lean_array_get_size(x_2);
x_31 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_31);
lean_dec(x_9);
x_13 = x_31;
goto block_30;
block_30:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_13);
lean_dec_ref(x_13);
x_15 = lean_nat_dec_lt(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = l_Lean_IR_Checker_checkPartialApp___closed__0;
x_17 = 1;
x_18 = l_Lean_Name_toString(x_1, x_17, x_11);
x_19 = lean_string_append(x_16, x_18);
lean_dec_ref(x_18);
x_20 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_Nat_reprFast(x_12);
x_23 = lean_string_append(x_21, x_22);
lean_dec_ref(x_22);
x_24 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_Nat_reprFast(x_14);
x_27 = lean_string_append(x_25, x_26);
lean_dec_ref(x_26);
x_28 = l_Lean_IR_Checker_throwCheckerError___redArg(x_27, x_3, x_4, x_5, x_6, x_10);
lean_dec_ref(x_27);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_1);
x_29 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_4, x_5, x_6, x_10);
return x_29;
}
}
}
else
{
uint8_t x_32; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
return x_8;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_checkPartialApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("constructor '", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has too many scalar fields", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has too many fields", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tag for constructor '", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is too big, this is a limitation of the current runtime", 57, 57);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid proj index", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected IR type '", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_50; uint8_t x_51; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_9);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_10 = x_2;
} else {
 lean_dec_ref(x_2);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 4);
lean_inc(x_15);
x_16 = l_Lean_IR_Checker_getDecl___closed__0;
x_50 = l_Lean_IR_Checker_maxCtorTag;
x_51 = lean_nat_dec_lt(x_50, x_12);
lean_dec(x_12);
if (x_51 == 0)
{
x_17 = x_51;
goto block_49;
}
else
{
uint8_t x_52; 
x_52 = l_Lean_IR_CtorInfo_isRef(x_8);
x_17 = x_52;
goto block_49;
}
block_49:
{
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_IR_Checker_maxCtorFields;
x_19 = lean_nat_dec_lt(x_18, x_13);
lean_dec(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = l_Lean_IR_Checker_maxCtorScalarsSize;
x_21 = l_Lean_IR_Checker_usizeSize;
x_22 = lean_nat_mul(x_14, x_21);
lean_dec(x_14);
x_23 = lean_nat_add(x_15, x_22);
lean_dec(x_22);
lean_dec(x_15);
x_24 = lean_nat_dec_lt(x_20, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_11);
x_25 = l_Lean_IR_CtorInfo_isRef(x_8);
lean_dec_ref(x_8);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_9);
lean_dec_ref(x_3);
lean_dec(x_1);
x_26 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_10;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_10);
lean_inc_ref(x_3);
x_28 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_IR_Checker_checkArgs(x_9, x_3, x_4, x_5, x_6, x_29);
lean_dec_ref(x_9);
return x_30;
}
else
{
lean_dec_ref(x_9);
lean_dec_ref(x_3);
return x_28;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
x_31 = l_Lean_IR_Checker_checkExpr___closed__0;
x_32 = l_Lean_Name_toString(x_11, x_24, x_16);
x_33 = lean_string_append(x_31, x_32);
lean_dec_ref(x_32);
x_34 = l_Lean_IR_Checker_checkExpr___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Lean_IR_Checker_throwCheckerError___redArg(x_35, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
x_37 = l_Lean_IR_Checker_checkExpr___closed__0;
x_38 = l_Lean_Name_toString(x_11, x_19, x_16);
x_39 = lean_string_append(x_37, x_38);
lean_dec_ref(x_38);
x_40 = l_Lean_IR_Checker_checkExpr___closed__2;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_Lean_IR_Checker_throwCheckerError___redArg(x_41, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
x_43 = l_Lean_IR_Checker_checkExpr___closed__3;
x_44 = l_Lean_Name_toString(x_11, x_17, x_16);
x_45 = lean_string_append(x_43, x_44);
lean_dec_ref(x_44);
x_46 = l_Lean_IR_Checker_checkExpr___closed__4;
x_47 = lean_string_append(x_45, x_46);
x_48 = l_Lean_IR_Checker_throwCheckerError___redArg(x_47, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_47);
return x_48;
}
}
}
case 1:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_2, 1);
lean_inc(x_53);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_54 = l_Lean_IR_Checker_checkObjVar(x_53, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6, x_55);
return x_56;
}
else
{
lean_dec_ref(x_3);
lean_dec(x_1);
return x_54;
}
}
case 2:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_2, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_58);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_59 = l_Lean_IR_Checker_checkObjVar(x_57, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec_ref(x_59);
lean_inc_ref(x_3);
x_61 = l_Lean_IR_Checker_checkArgs(x_58, x_3, x_4, x_5, x_6, x_60);
lean_dec_ref(x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6, x_62);
return x_63;
}
else
{
lean_dec_ref(x_3);
lean_dec(x_1);
return x_61;
}
}
else
{
lean_dec_ref(x_58);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_59;
}
}
case 3:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_66 = l_Lean_IR_Checker_getType(x_65, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
switch (lean_obj_tag(x_67)) {
case 7:
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_64);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec_ref(x_66);
x_69 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6, x_68);
return x_69;
}
case 8:
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_64);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec_ref(x_66);
x_71 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6, x_70);
return x_71;
}
case 10:
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_66);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_66, 1);
x_74 = lean_ctor_get(x_66, 0);
lean_dec(x_74);
x_75 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_75);
lean_dec_ref(x_67);
x_76 = lean_array_get_size(x_75);
x_77 = lean_nat_dec_lt(x_64, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_75);
lean_free_object(x_66);
lean_dec(x_64);
lean_dec(x_1);
x_78 = l_Lean_IR_Checker_checkExpr___closed__5;
x_79 = l_Lean_IR_Checker_throwCheckerError___redArg(x_78, x_3, x_4, x_5, x_6, x_73);
return x_79;
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_array_fget(x_75, x_64);
lean_dec(x_64);
lean_dec_ref(x_75);
x_81 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_466_(x_80, x_1);
lean_dec(x_1);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_free_object(x_66);
x_82 = l_Lean_IR_Checker_checkEqTypes___closed__0;
x_83 = l_Lean_IR_Checker_throwCheckerError___redArg(x_82, x_3, x_4, x_5, x_6, x_73);
return x_83;
}
else
{
lean_object* x_84; 
lean_dec_ref(x_3);
x_84 = lean_box(0);
lean_ctor_set(x_66, 0, x_84);
return x_66;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_66, 1);
lean_inc(x_85);
lean_dec(x_66);
x_86 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_86);
lean_dec_ref(x_67);
x_87 = lean_array_get_size(x_86);
x_88 = lean_nat_dec_lt(x_64, x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_86);
lean_dec(x_64);
lean_dec(x_1);
x_89 = l_Lean_IR_Checker_checkExpr___closed__5;
x_90 = l_Lean_IR_Checker_throwCheckerError___redArg(x_89, x_3, x_4, x_5, x_6, x_85);
return x_90;
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_array_fget(x_86, x_64);
lean_dec(x_64);
lean_dec_ref(x_86);
x_92 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_466_(x_91, x_1);
lean_dec(x_1);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = l_Lean_IR_Checker_checkEqTypes___closed__0;
x_94 = l_Lean_IR_Checker_throwCheckerError___redArg(x_93, x_3, x_4, x_5, x_6, x_85);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_3);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_85);
return x_96;
}
}
}
}
case 11:
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_66);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_98 = lean_ctor_get(x_66, 1);
x_99 = lean_ctor_get(x_66, 0);
lean_dec(x_99);
x_100 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_100);
lean_dec_ref(x_67);
x_101 = lean_array_get_size(x_100);
x_102 = lean_nat_dec_lt(x_64, x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_100);
lean_free_object(x_66);
lean_dec(x_64);
lean_dec(x_1);
x_103 = l_Lean_IR_Checker_checkExpr___closed__5;
x_104 = l_Lean_IR_Checker_throwCheckerError___redArg(x_103, x_3, x_4, x_5, x_6, x_98);
return x_104;
}
else
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_array_fget(x_100, x_64);
lean_dec(x_64);
lean_dec_ref(x_100);
x_106 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_466_(x_105, x_1);
lean_dec(x_1);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_free_object(x_66);
x_107 = l_Lean_IR_Checker_checkEqTypes___closed__0;
x_108 = l_Lean_IR_Checker_throwCheckerError___redArg(x_107, x_3, x_4, x_5, x_6, x_98);
return x_108;
}
else
{
lean_object* x_109; 
lean_dec_ref(x_3);
x_109 = lean_box(0);
lean_ctor_set(x_66, 0, x_109);
return x_66;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_66, 1);
lean_inc(x_110);
lean_dec(x_66);
x_111 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_111);
lean_dec_ref(x_67);
x_112 = lean_array_get_size(x_111);
x_113 = lean_nat_dec_lt(x_64, x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec_ref(x_111);
lean_dec(x_64);
lean_dec(x_1);
x_114 = l_Lean_IR_Checker_checkExpr___closed__5;
x_115 = l_Lean_IR_Checker_throwCheckerError___redArg(x_114, x_3, x_4, x_5, x_6, x_110);
return x_115;
}
else
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_array_fget(x_111, x_64);
lean_dec(x_64);
lean_dec_ref(x_111);
x_117 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_466_(x_116, x_1);
lean_dec(x_1);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = l_Lean_IR_Checker_checkEqTypes___closed__0;
x_119 = l_Lean_IR_Checker_throwCheckerError___redArg(x_118, x_3, x_4, x_5, x_6, x_110);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_3);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_110);
return x_121;
}
}
}
}
default: 
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_64);
lean_dec(x_1);
x_122 = lean_ctor_get(x_66, 1);
lean_inc(x_122);
lean_dec_ref(x_66);
x_123 = l_Lean_IR_Checker_checkExpr___closed__6;
x_124 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_67);
x_125 = lean_unsigned_to_nat(120u);
x_126 = lean_unsigned_to_nat(0u);
x_127 = lean_format_pretty(x_124, x_125, x_126, x_126);
x_128 = lean_string_append(x_123, x_127);
lean_dec_ref(x_127);
x_129 = l_Lean_IR_Checker_checkVar___closed__2;
x_130 = lean_string_append(x_128, x_129);
x_131 = l_Lean_IR_Checker_throwCheckerError___redArg(x_130, x_3, x_4, x_5, x_6, x_122);
lean_dec_ref(x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_64);
lean_dec_ref(x_3);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_66);
if (x_132 == 0)
{
return x_66;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_66, 0);
x_134 = lean_ctor_get(x_66, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_66);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
case 4:
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_2, 1);
lean_inc(x_136);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_137 = l_Lean_IR_Checker_checkObjVar(x_136, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_137) == 0)
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_137, 1);
x_140 = lean_ctor_get(x_137, 0);
lean_dec(x_140);
x_141 = lean_box(5);
x_142 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_466_(x_1, x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_free_object(x_137);
x_143 = l_Lean_IR_Checker_checkType___closed__0;
x_144 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_145 = lean_unsigned_to_nat(120u);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_format_pretty(x_144, x_145, x_146, x_146);
x_148 = lean_string_append(x_143, x_147);
lean_dec_ref(x_147);
x_149 = l_Lean_IR_Checker_checkVar___closed__2;
x_150 = lean_string_append(x_148, x_149);
x_151 = l_Lean_IR_Checker_throwCheckerError___redArg(x_150, x_3, x_4, x_5, x_6, x_139);
lean_dec_ref(x_150);
return x_151;
}
else
{
lean_object* x_152; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_152 = lean_box(0);
lean_ctor_set(x_137, 0, x_152);
return x_137;
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_ctor_get(x_137, 1);
lean_inc(x_153);
lean_dec(x_137);
x_154 = lean_box(5);
x_155 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_466_(x_1, x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_156 = l_Lean_IR_Checker_checkType___closed__0;
x_157 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_158 = lean_unsigned_to_nat(120u);
x_159 = lean_unsigned_to_nat(0u);
x_160 = lean_format_pretty(x_157, x_158, x_159, x_159);
x_161 = lean_string_append(x_156, x_160);
lean_dec_ref(x_160);
x_162 = l_Lean_IR_Checker_checkVar___closed__2;
x_163 = lean_string_append(x_161, x_162);
x_164 = l_Lean_IR_Checker_throwCheckerError___redArg(x_163, x_3, x_4, x_5, x_6, x_153);
lean_dec_ref(x_163);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_165 = lean_box(0);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_153);
return x_166;
}
}
}
else
{
lean_dec_ref(x_3);
lean_dec(x_1);
return x_137;
}
}
case 5:
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_2, 2);
lean_inc(x_167);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_168 = l_Lean_IR_Checker_checkObjVar(x_167, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec_ref(x_168);
x_170 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_4, x_5, x_6, x_169);
return x_170;
}
else
{
lean_dec_ref(x_3);
lean_dec(x_1);
return x_168;
}
}
case 6:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_1);
x_171 = lean_ctor_get(x_2, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_172);
lean_dec_ref(x_2);
x_173 = l_Lean_IR_Checker_checkFullApp(x_171, x_172, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_172);
return x_173;
}
case 7:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_2, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_175);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_176 = l_Lean_IR_Checker_checkPartialApp(x_174, x_175, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_175);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec_ref(x_176);
x_178 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6, x_177);
return x_178;
}
else
{
lean_dec_ref(x_3);
lean_dec(x_1);
return x_176;
}
}
case 8:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_2, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_180);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_181 = l_Lean_IR_Checker_checkObjVar(x_179, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec_ref(x_181);
lean_inc_ref(x_3);
x_183 = l_Lean_IR_Checker_checkArgs(x_180, x_3, x_4, x_5, x_6, x_182);
lean_dec_ref(x_180);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6, x_184);
return x_185;
}
else
{
lean_dec_ref(x_3);
lean_dec(x_1);
return x_183;
}
}
else
{
lean_dec_ref(x_180);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_181;
}
}
case 9:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_2, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_2, 1);
lean_inc(x_187);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_188 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec_ref(x_188);
lean_inc_ref(x_3);
lean_inc(x_187);
x_190 = l_Lean_IR_Checker_checkScalarVar(x_187, x_3, x_4, x_5, x_6, x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec_ref(x_190);
lean_inc_ref(x_3);
x_192 = l_Lean_IR_Checker_getType(x_187, x_3, x_4, x_5, x_6, x_191);
if (lean_obj_tag(x_192) == 0)
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_192, 0);
x_195 = lean_ctor_get(x_192, 1);
x_196 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_466_(x_194, x_186);
lean_dec(x_186);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_free_object(x_192);
x_197 = l_Lean_IR_Checker_checkType___closed__0;
x_198 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_194);
x_199 = lean_unsigned_to_nat(120u);
x_200 = lean_unsigned_to_nat(0u);
x_201 = lean_format_pretty(x_198, x_199, x_200, x_200);
x_202 = lean_string_append(x_197, x_201);
lean_dec_ref(x_201);
x_203 = l_Lean_IR_Checker_checkVar___closed__2;
x_204 = lean_string_append(x_202, x_203);
x_205 = l_Lean_IR_Checker_throwCheckerError___redArg(x_204, x_3, x_4, x_5, x_6, x_195);
lean_dec_ref(x_204);
return x_205;
}
else
{
lean_object* x_206; 
lean_dec(x_194);
lean_dec_ref(x_3);
x_206 = lean_box(0);
lean_ctor_set(x_192, 0, x_206);
return x_192;
}
}
else
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_207 = lean_ctor_get(x_192, 0);
x_208 = lean_ctor_get(x_192, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_192);
x_209 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_466_(x_207, x_186);
lean_dec(x_186);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_210 = l_Lean_IR_Checker_checkType___closed__0;
x_211 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_207);
x_212 = lean_unsigned_to_nat(120u);
x_213 = lean_unsigned_to_nat(0u);
x_214 = lean_format_pretty(x_211, x_212, x_213, x_213);
x_215 = lean_string_append(x_210, x_214);
lean_dec_ref(x_214);
x_216 = l_Lean_IR_Checker_checkVar___closed__2;
x_217 = lean_string_append(x_215, x_216);
x_218 = l_Lean_IR_Checker_throwCheckerError___redArg(x_217, x_3, x_4, x_5, x_6, x_208);
lean_dec_ref(x_217);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_207);
lean_dec_ref(x_3);
x_219 = lean_box(0);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_208);
return x_220;
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_186);
lean_dec_ref(x_3);
x_221 = !lean_is_exclusive(x_192);
if (x_221 == 0)
{
return x_192;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_192, 0);
x_223 = lean_ctor_get(x_192, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_192);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
lean_dec(x_187);
lean_dec(x_186);
lean_dec_ref(x_3);
return x_190;
}
}
else
{
lean_dec(x_187);
lean_dec(x_186);
lean_dec_ref(x_3);
return x_188;
}
}
case 10:
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_2, 0);
lean_inc(x_225);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_226 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec_ref(x_226);
x_228 = l_Lean_IR_Checker_checkObjVar(x_225, x_3, x_4, x_5, x_6, x_227);
return x_228;
}
else
{
lean_dec(x_225);
lean_dec_ref(x_3);
return x_226;
}
}
case 11:
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_229);
lean_dec_ref(x_2);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; 
lean_dec_ref(x_229);
lean_dec_ref(x_3);
lean_dec(x_1);
x_230 = lean_box(0);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_7);
return x_231;
}
else
{
lean_object* x_232; 
lean_dec_ref(x_229);
x_232 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6, x_7);
return x_232;
}
}
default: 
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_2, 0);
lean_inc(x_233);
lean_dec_ref(x_2);
lean_inc_ref(x_3);
x_234 = l_Lean_IR_Checker_checkObjVar(x_233, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_234) == 0)
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_234);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_236 = lean_ctor_get(x_234, 1);
x_237 = lean_ctor_get(x_234, 0);
lean_dec(x_237);
x_238 = lean_box(1);
x_239 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_466_(x_1, x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_free_object(x_234);
x_240 = l_Lean_IR_Checker_checkType___closed__0;
x_241 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_242 = lean_unsigned_to_nat(120u);
x_243 = lean_unsigned_to_nat(0u);
x_244 = lean_format_pretty(x_241, x_242, x_243, x_243);
x_245 = lean_string_append(x_240, x_244);
lean_dec_ref(x_244);
x_246 = l_Lean_IR_Checker_checkVar___closed__2;
x_247 = lean_string_append(x_245, x_246);
x_248 = l_Lean_IR_Checker_throwCheckerError___redArg(x_247, x_3, x_4, x_5, x_6, x_236);
lean_dec_ref(x_247);
return x_248;
}
else
{
lean_object* x_249; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_249 = lean_box(0);
lean_ctor_set(x_234, 0, x_249);
return x_234;
}
}
else
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_250 = lean_ctor_get(x_234, 1);
lean_inc(x_250);
lean_dec(x_234);
x_251 = lean_box(1);
x_252 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_466_(x_1, x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_253 = l_Lean_IR_Checker_checkType___closed__0;
x_254 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_255 = lean_unsigned_to_nat(120u);
x_256 = lean_unsigned_to_nat(0u);
x_257 = lean_format_pretty(x_254, x_255, x_256, x_256);
x_258 = lean_string_append(x_253, x_257);
lean_dec_ref(x_257);
x_259 = l_Lean_IR_Checker_checkVar___closed__2;
x_260 = lean_string_append(x_258, x_259);
x_261 = l_Lean_IR_Checker_throwCheckerError___redArg(x_260, x_3, x_4, x_5, x_6, x_250);
lean_dec_ref(x_260);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_262 = lean_box(0);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_250);
return x_263;
}
}
}
else
{
lean_dec_ref(x_3);
lean_dec(x_1);
return x_234;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_checkExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = l_Lean_IR_Checker_markIndex(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = l_Lean_IR_LocalContext_addParam(x_1, x_2);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_IR_LocalContext_addParam(x_1, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_IR_Checker_withParams___closed__1;
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_17 = lean_ctor_get(x_10, 1);
lean_dec(x_17);
x_18 = l_Lean_IR_Checker_withParams___closed__2;
x_19 = l_Lean_IR_Checker_withParams___closed__3;
lean_inc_ref(x_13);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_13);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_14);
lean_ctor_set(x_10, 4, x_23);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_25);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_22);
lean_ctor_set(x_8, 1, x_19);
x_26 = l_ReaderT_instMonad___redArg(x_8);
x_27 = l_ReaderT_instMonad___redArg(x_26);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_30);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_array_get_size(x_1);
x_38 = lean_nat_dec_lt(x_36, x_37);
if (x_38 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_27);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_31 = x_28;
x_32 = x_7;
goto block_35;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_37, x_37);
if (x_39 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_27);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_31 = x_28;
x_32 = x_7;
goto block_35;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__0___boxed), 7, 0);
x_41 = 0;
x_42 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_43 = l_Array_foldlMUnsafe_fold___redArg(x_27, x_40, x_1, x_41, x_42, x_28);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_44 = lean_apply_5(x_43, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_31 = x_45;
x_32 = x_46;
goto block_35;
}
else
{
uint8_t x_47; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 0);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_44);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_30);
x_34 = lean_apply_5(x_2, x_33, x_4, x_5, x_6, x_32);
return x_34;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_51 = lean_ctor_get(x_10, 0);
x_52 = lean_ctor_get(x_10, 2);
x_53 = lean_ctor_get(x_10, 3);
x_54 = lean_ctor_get(x_10, 4);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_10);
x_55 = l_Lean_IR_Checker_withParams___closed__2;
x_56 = l_Lean_IR_Checker_withParams___closed__3;
lean_inc_ref(x_51);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_57, 0, x_51);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_58, 0, x_51);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_60, 0, x_54);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_61, 0, x_53);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_62, 0, x_52);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_55);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set(x_63, 3, x_61);
lean_ctor_set(x_63, 4, x_60);
lean_ctor_set(x_8, 1, x_56);
lean_ctor_set(x_8, 0, x_63);
x_64 = l_ReaderT_instMonad___redArg(x_8);
x_65 = l_ReaderT_instMonad___redArg(x_64);
x_66 = lean_ctor_get(x_3, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_68);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_array_get_size(x_1);
x_76 = lean_nat_dec_lt(x_74, x_75);
if (x_76 == 0)
{
lean_dec(x_75);
lean_dec_ref(x_65);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_69 = x_66;
x_70 = x_7;
goto block_73;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_75, x_75);
if (x_77 == 0)
{
lean_dec(x_75);
lean_dec_ref(x_65);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_69 = x_66;
x_70 = x_7;
goto block_73;
}
else
{
lean_object* x_78; size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__0___boxed), 7, 0);
x_79 = 0;
x_80 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_81 = l_Array_foldlMUnsafe_fold___redArg(x_65, x_78, x_1, x_79, x_80, x_66);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_82 = lean_apply_5(x_81, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec_ref(x_82);
x_69 = x_83;
x_70 = x_84;
goto block_73;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_68);
lean_dec_ref(x_67);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_87 = x_82;
} else {
 lean_dec_ref(x_82);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
block_73:
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_68);
x_72 = lean_apply_5(x_2, x_71, x_4, x_5, x_6, x_70);
return x_72;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_89 = lean_ctor_get(x_8, 0);
lean_inc(x_89);
lean_dec(x_8);
x_90 = lean_ctor_get(x_89, 0);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_89, 2);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_89, 3);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_89, 4);
lean_inc_ref(x_93);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 x_94 = x_89;
} else {
 lean_dec_ref(x_89);
 x_94 = lean_box(0);
}
x_95 = l_Lean_IR_Checker_withParams___closed__2;
x_96 = l_Lean_IR_Checker_withParams___closed__3;
lean_inc_ref(x_90);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_97, 0, x_90);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_98, 0, x_90);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_100, 0, x_93);
x_101 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_101, 0, x_92);
x_102 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_102, 0, x_91);
if (lean_is_scalar(x_94)) {
 x_103 = lean_alloc_ctor(0, 5, 0);
} else {
 x_103 = x_94;
}
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_95);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set(x_103, 4, x_100);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_96);
x_105 = l_ReaderT_instMonad___redArg(x_104);
x_106 = l_ReaderT_instMonad___redArg(x_105);
x_107 = lean_ctor_get(x_3, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_109);
x_115 = lean_unsigned_to_nat(0u);
x_116 = lean_array_get_size(x_1);
x_117 = lean_nat_dec_lt(x_115, x_116);
if (x_117 == 0)
{
lean_dec(x_116);
lean_dec_ref(x_106);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_110 = x_107;
x_111 = x_7;
goto block_114;
}
else
{
uint8_t x_118; 
x_118 = lean_nat_dec_le(x_116, x_116);
if (x_118 == 0)
{
lean_dec(x_116);
lean_dec_ref(x_106);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_110 = x_107;
x_111 = x_7;
goto block_114;
}
else
{
lean_object* x_119; size_t x_120; size_t x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__0___boxed), 7, 0);
x_120 = 0;
x_121 = lean_usize_of_nat(x_116);
lean_dec(x_116);
x_122 = l_Array_foldlMUnsafe_fold___redArg(x_106, x_119, x_1, x_120, x_121, x_107);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_123 = lean_apply_5(x_122, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec_ref(x_123);
x_110 = x_124;
x_111 = x_125;
goto block_114;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec_ref(x_109);
lean_dec_ref(x_108);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_128 = x_123;
} else {
 lean_dec_ref(x_123);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
block_114:
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_108);
lean_ctor_set(x_112, 2, x_109);
x_113 = lean_apply_5(x_2, x_112, x_4, x_5, x_6, x_111);
return x_113;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_withParams___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_inc_ref(x_5);
x_13 = l_Lean_IR_Checker_markIndex(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_IR_LocalContext_addParam(x_4, x_11);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_15;
x_9 = x_14;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec_ref(x_11);
lean_dec_ref(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec_ref(x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_17; 
x_17 = lean_usize_dec_eq(x_2, x_3);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc_ref(x_5);
x_20 = l_Lean_IR_Checker_checkFnBody(x_19, x_5, x_6, x_7, x_8, x_9);
x_10 = x_20;
goto block_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
lean_inc_ref(x_5);
x_22 = l_Lean_IR_Checker_checkFnBody(x_21, x_5, x_6, x_7, x_8, x_9);
x_10 = x_22;
goto block_16;
}
}
else
{
lean_object* x_23; 
lean_dec_ref(x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
block_16:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
x_9 = x_12;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
lean_inc_ref(x_20);
lean_inc(x_19);
x_22 = l_Lean_IR_Checker_checkExpr(x_19, x_20, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc_ref(x_2);
lean_inc(x_18);
x_24 = l_Lean_IR_Checker_markIndex(x_18, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = l_Lean_IR_LocalContext_addLocal(x_27, x_18, x_19, x_20);
lean_ctor_set(x_2, 0, x_28);
x_1 = x_21;
x_6 = x_25;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ctor_get(x_2, 2);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_2);
x_33 = l_Lean_IR_LocalContext_addLocal(x_30, x_18, x_19, x_20);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
x_1 = x_21;
x_2 = x_34;
x_6 = x_25;
goto _start;
}
}
else
{
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_2);
return x_24;
}
}
else
{
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_2);
return x_22;
}
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 3);
lean_inc(x_39);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
lean_inc(x_36);
x_40 = l_Lean_IR_Checker_markIndex(x_36, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_44);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_get_size(x_37);
x_56 = lean_nat_dec_lt(x_54, x_55);
if (x_56 == 0)
{
lean_dec(x_55);
lean_dec_ref(x_2);
lean_inc(x_42);
x_45 = x_42;
x_46 = x_41;
goto block_53;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_55, x_55);
if (x_57 == 0)
{
lean_dec(x_55);
lean_dec_ref(x_2);
lean_inc(x_42);
x_45 = x_42;
x_46 = x_41;
goto block_53;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_55);
lean_dec(x_55);
lean_inc(x_42);
x_60 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(x_37, x_58, x_59, x_42, x_2, x_3, x_4, x_5, x_41);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_45 = x_61;
x_46 = x_62;
goto block_53;
}
else
{
uint8_t x_63; 
lean_dec_ref(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
x_63 = !lean_is_exclusive(x_60);
if (x_63 == 0)
{
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
block_53:
{
lean_object* x_47; lean_object* x_48; 
lean_inc_ref(x_44);
lean_inc_ref(x_43);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_44);
lean_inc(x_38);
x_48 = l_Lean_IR_Checker_checkFnBody(x_38, x_47, x_3, x_4, x_5, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = l_Lean_IR_LocalContext_addJP(x_42, x_36, x_37, x_38);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set(x_51, 2, x_44);
x_1 = x_39;
x_2 = x_51;
x_6 = x_49;
goto _start;
}
else
{
lean_dec_ref(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
return x_48;
}
}
}
else
{
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_dec_ref(x_2);
return x_40;
}
}
case 2:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 3);
lean_inc(x_69);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_70 = l_Lean_IR_Checker_checkVar(x_67, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec_ref(x_70);
lean_inc_ref(x_2);
x_72 = l_Lean_IR_Checker_checkArg(x_68, x_2, x_3, x_4, x_5, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec_ref(x_72);
x_1 = x_69;
x_6 = x_73;
goto _start;
}
else
{
lean_dec(x_69);
lean_dec_ref(x_2);
return x_72;
}
}
else
{
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_2);
return x_70;
}
}
case 3:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_1, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 2);
lean_inc(x_76);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_77 = l_Lean_IR_Checker_checkVar(x_75, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec_ref(x_77);
x_1 = x_76;
x_6 = x_78;
goto _start;
}
else
{
lean_dec(x_76);
lean_dec_ref(x_2);
return x_77;
}
}
case 4:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_1, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_1, 3);
lean_inc(x_82);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_83 = l_Lean_IR_Checker_checkVar(x_80, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec_ref(x_83);
lean_inc_ref(x_2);
x_85 = l_Lean_IR_Checker_checkVar(x_81, x_2, x_3, x_4, x_5, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec_ref(x_85);
x_1 = x_82;
x_6 = x_86;
goto _start;
}
else
{
lean_dec(x_82);
lean_dec_ref(x_2);
return x_85;
}
}
else
{
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_2);
return x_83;
}
}
case 5:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 3);
lean_inc(x_89);
x_90 = lean_ctor_get(x_1, 5);
lean_inc(x_90);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_91 = l_Lean_IR_Checker_checkVar(x_88, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec_ref(x_91);
lean_inc_ref(x_2);
x_93 = l_Lean_IR_Checker_checkVar(x_89, x_2, x_3, x_4, x_5, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec_ref(x_93);
x_1 = x_90;
x_6 = x_94;
goto _start;
}
else
{
lean_dec(x_90);
lean_dec_ref(x_2);
return x_93;
}
}
else
{
lean_dec(x_90);
lean_dec(x_89);
lean_dec_ref(x_2);
return x_91;
}
}
case 8:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_1, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_1, 1);
lean_inc(x_97);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_98 = l_Lean_IR_Checker_checkVar(x_96, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec_ref(x_98);
x_1 = x_97;
x_6 = x_99;
goto _start;
}
else
{
lean_dec(x_97);
lean_dec_ref(x_2);
return x_98;
}
}
case 9:
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_1, 1);
lean_inc(x_101);
lean_dec_ref(x_1);
x_1 = x_101;
goto _start;
}
case 10:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_1, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_104);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_105 = l_Lean_IR_Checker_checkVar(x_103, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_107 = lean_ctor_get(x_105, 1);
x_108 = lean_ctor_get(x_105, 0);
lean_dec(x_108);
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_array_get_size(x_104);
x_111 = lean_box(0);
x_112 = lean_nat_dec_lt(x_109, x_110);
if (x_112 == 0)
{
lean_dec(x_110);
lean_dec_ref(x_104);
lean_dec_ref(x_2);
lean_ctor_set(x_105, 0, x_111);
return x_105;
}
else
{
uint8_t x_113; 
x_113 = lean_nat_dec_le(x_110, x_110);
if (x_113 == 0)
{
lean_dec(x_110);
lean_dec_ref(x_104);
lean_dec_ref(x_2);
lean_ctor_set(x_105, 0, x_111);
return x_105;
}
else
{
size_t x_114; size_t x_115; lean_object* x_116; 
lean_free_object(x_105);
x_114 = 0;
x_115 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_116 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(x_104, x_114, x_115, x_111, x_2, x_3, x_4, x_5, x_107);
lean_dec_ref(x_104);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
lean_dec(x_105);
x_118 = lean_unsigned_to_nat(0u);
x_119 = lean_array_get_size(x_104);
x_120 = lean_box(0);
x_121 = lean_nat_dec_lt(x_118, x_119);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_119);
lean_dec_ref(x_104);
lean_dec_ref(x_2);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_117);
return x_122;
}
else
{
uint8_t x_123; 
x_123 = lean_nat_dec_le(x_119, x_119);
if (x_123 == 0)
{
lean_object* x_124; 
lean_dec(x_119);
lean_dec_ref(x_104);
lean_dec_ref(x_2);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_117);
return x_124;
}
else
{
size_t x_125; size_t x_126; lean_object* x_127; 
x_125 = 0;
x_126 = lean_usize_of_nat(x_119);
lean_dec(x_119);
x_127 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(x_104, x_125, x_126, x_120, x_2, x_3, x_4, x_5, x_117);
lean_dec_ref(x_104);
return x_127;
}
}
}
}
else
{
lean_dec_ref(x_104);
lean_dec_ref(x_2);
return x_105;
}
}
case 11:
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_1, 0);
lean_inc(x_128);
lean_dec_ref(x_1);
x_129 = l_Lean_IR_Checker_checkArg(x_128, x_2, x_3, x_4, x_5, x_6);
return x_129;
}
case 12:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_1, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_131);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_132 = l_Lean_IR_Checker_checkJP(x_130, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = l_Lean_IR_Checker_checkArgs(x_131, x_2, x_3, x_4, x_5, x_133);
lean_dec_ref(x_131);
return x_134;
}
else
{
lean_dec_ref(x_131);
lean_dec_ref(x_2);
return x_132;
}
}
case 13:
{
lean_object* x_135; lean_object* x_136; 
lean_dec_ref(x_2);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_6);
return x_136;
}
default: 
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_1, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_1, 2);
lean_inc(x_138);
lean_dec(x_1);
x_7 = x_137;
x_8 = x_138;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
goto block_17;
}
}
block_17:
{
lean_object* x_14; 
lean_inc_ref(x_9);
x_14 = l_Lean_IR_Checker_checkVar(x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec_ref(x_14);
x_1 = x_8;
x_2 = x_9;
x_3 = x_10;
x_4 = x_11;
x_5 = x_12;
x_6 = x_15;
goto _start;
}
else
{
lean_dec_ref(x_9);
lean_dec(x_8);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkFnBody(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_7);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_12 = x_9;
x_13 = x_6;
goto block_16;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_18, x_18);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_12 = x_9;
x_13 = x_6;
goto block_16;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(x_7, x_21, x_22, x_9, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_12 = x_24;
x_13 = x_25;
goto block_16;
}
else
{
uint8_t x_26; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_11);
x_15 = l_Lean_IR_Checker_checkFnBody(x_8, x_14, x_3, x_4, x_5, x_13);
return x_15;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_1);
x_31 = lean_box(0);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get_size(x_30);
x_34 = lean_nat_dec_lt(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_6);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_33, x_33);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_33);
lean_dec_ref(x_30);
lean_dec_ref(x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_6);
return x_37;
}
else
{
lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = 0;
x_40 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_41 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(x_30, x_39, x_40, x_38, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_30);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_31);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_31);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkDecl(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_box(1);
x_7 = lean_st_mk_ref(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc_ref(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_10, 2, x_1);
x_11 = l_Lean_IR_Checker_checkDecl(x_2, x_10, x_8, x_3, x_4, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_st_ref_get(x_8, x_13);
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_dec(x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_checkDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
x_11 = l_Lean_IR_checkDecl(x_1, x_10, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_5 = x_12;
x_8 = x_13;
goto _start;
}
else
{
lean_dec_ref(x_1);
return x_11;
}
}
else
{
lean_object* x_17; 
lean_dec_ref(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_1);
x_7 = lean_box(0);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec_ref(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
lean_inc_ref(x_1);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0(x_1, x_1, x_12, x_13, x_7, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_checkDecls(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Checker(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_Checker_maxCtorFields___closed__0 = _init_l_Lean_IR_Checker_maxCtorFields___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorFields___closed__0);
l_Lean_IR_Checker_maxCtorFields = _init_l_Lean_IR_Checker_maxCtorFields();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorFields);
l_Lean_IR_Checker_maxCtorScalarsSize___closed__0 = _init_l_Lean_IR_Checker_maxCtorScalarsSize___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorScalarsSize___closed__0);
l_Lean_IR_Checker_maxCtorScalarsSize = _init_l_Lean_IR_Checker_maxCtorScalarsSize();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorScalarsSize);
l_Lean_IR_Checker_maxCtorTag___closed__0 = _init_l_Lean_IR_Checker_maxCtorTag___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorTag___closed__0);
l_Lean_IR_Checker_maxCtorTag = _init_l_Lean_IR_Checker_maxCtorTag();
lean_mark_persistent(l_Lean_IR_Checker_maxCtorTag);
l_Lean_IR_Checker_usizeSize___closed__0 = _init_l_Lean_IR_Checker_usizeSize___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_usizeSize___closed__0);
l_Lean_IR_Checker_usizeSize = _init_l_Lean_IR_Checker_usizeSize();
lean_mark_persistent(l_Lean_IR_Checker_usizeSize);
l_Lean_IR_Checker_throwCheckerError___redArg___closed__0 = _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_throwCheckerError___redArg___closed__0);
l_Lean_IR_Checker_throwCheckerError___redArg___closed__1 = _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_throwCheckerError___redArg___closed__1);
l_Lean_IR_Checker_markIndex___closed__0 = _init_l_Lean_IR_Checker_markIndex___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___closed__0);
l_Lean_IR_Checker_markIndex___closed__1 = _init_l_Lean_IR_Checker_markIndex___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___closed__1);
l_Lean_IR_Checker_getDecl___closed__0 = _init_l_Lean_IR_Checker_getDecl___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_getDecl___closed__0);
l_Lean_IR_Checker_getDecl___closed__1 = _init_l_Lean_IR_Checker_getDecl___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_getDecl___closed__1);
l_Lean_IR_Checker_getDecl___closed__2 = _init_l_Lean_IR_Checker_getDecl___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_getDecl___closed__2);
l_Lean_IR_Checker_checkVar___closed__0 = _init_l_Lean_IR_Checker_checkVar___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_checkVar___closed__0);
l_Lean_IR_Checker_checkVar___closed__1 = _init_l_Lean_IR_Checker_checkVar___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkVar___closed__1);
l_Lean_IR_Checker_checkVar___closed__2 = _init_l_Lean_IR_Checker_checkVar___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkVar___closed__2);
l_Lean_IR_Checker_checkJP___closed__0 = _init_l_Lean_IR_Checker_checkJP___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_checkJP___closed__0);
l_Lean_IR_Checker_checkJP___closed__1 = _init_l_Lean_IR_Checker_checkJP___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkJP___closed__1);
l_Lean_IR_Checker_checkEqTypes___closed__0 = _init_l_Lean_IR_Checker_checkEqTypes___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_checkEqTypes___closed__0);
l_Lean_IR_Checker_checkType___closed__0 = _init_l_Lean_IR_Checker_checkType___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_checkType___closed__0);
l_Lean_IR_Checker_checkType___closed__1 = _init_l_Lean_IR_Checker_checkType___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkType___closed__1);
l_Lean_IR_Checker_checkObjType___closed__0 = _init_l_Lean_IR_Checker_checkObjType___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_checkObjType___closed__0);
l_Lean_IR_Checker_checkScalarType___closed__0 = _init_l_Lean_IR_Checker_checkScalarType___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_checkScalarType___closed__0);
l_Lean_IR_Checker_checkFullApp___closed__0 = _init_l_Lean_IR_Checker_checkFullApp___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__0);
l_Lean_IR_Checker_checkFullApp___closed__1 = _init_l_Lean_IR_Checker_checkFullApp___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__1);
l_Lean_IR_Checker_checkFullApp___closed__2 = _init_l_Lean_IR_Checker_checkFullApp___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__2);
l_Lean_IR_Checker_checkFullApp___closed__3 = _init_l_Lean_IR_Checker_checkFullApp___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_checkFullApp___closed__3);
l_Lean_IR_Checker_checkPartialApp___closed__0 = _init_l_Lean_IR_Checker_checkPartialApp___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_checkPartialApp___closed__0);
l_Lean_IR_Checker_checkPartialApp___closed__1 = _init_l_Lean_IR_Checker_checkPartialApp___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkPartialApp___closed__1);
l_Lean_IR_Checker_checkPartialApp___closed__2 = _init_l_Lean_IR_Checker_checkPartialApp___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkPartialApp___closed__2);
l_Lean_IR_Checker_checkExpr___closed__0 = _init_l_Lean_IR_Checker_checkExpr___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__0);
l_Lean_IR_Checker_checkExpr___closed__1 = _init_l_Lean_IR_Checker_checkExpr___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__1);
l_Lean_IR_Checker_checkExpr___closed__2 = _init_l_Lean_IR_Checker_checkExpr___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__2);
l_Lean_IR_Checker_checkExpr___closed__3 = _init_l_Lean_IR_Checker_checkExpr___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__3);
l_Lean_IR_Checker_checkExpr___closed__4 = _init_l_Lean_IR_Checker_checkExpr___closed__4();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__4);
l_Lean_IR_Checker_checkExpr___closed__5 = _init_l_Lean_IR_Checker_checkExpr___closed__5();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__5);
l_Lean_IR_Checker_checkExpr___closed__6 = _init_l_Lean_IR_Checker_checkExpr___closed__6();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__6);
l_Lean_IR_Checker_withParams___closed__0 = _init_l_Lean_IR_Checker_withParams___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__0);
l_Lean_IR_Checker_withParams___closed__1 = _init_l_Lean_IR_Checker_withParams___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__1);
l_Lean_IR_Checker_withParams___closed__2 = _init_l_Lean_IR_Checker_withParams___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__2);
l_Lean_IR_Checker_withParams___closed__3 = _init_l_Lean_IR_Checker_withParams___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
