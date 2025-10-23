// Lean compiler output
// Module: Lean.Compiler.IR.Checker
// Imports: public import Lean.Compiler.IR.CompilerM
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_Checker_markIndex_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorFields;
static lean_object* l_Lean_IR_Checker_maxCtorFields___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_max_ctor_scalars_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_usize_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_usizeSize;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorScalarsSize;
uint8_t l_Lean_IR_instBEqIRType_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_Checker_markIndex_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_max_ctor_fields(lean_object*);
static lean_object* l_Lean_IR_Checker_checkType___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_max_ctor_tag(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_IR_Checker_checkType___closed__2;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_CheckerContext_ctorIdx___boxed(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4;
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_usizeSize___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_Checker_markIndex_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
static lean_object* l_Lean_IR_Checker_checkVar___closed__2;
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__6;
static lean_object* l_Lean_IR_Checker_checkExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkObjType___closed__0;
static lean_object* l_Lean_IR_Checker_checkType___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__1;
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
static lean_object* l_Lean_IR_Checker_markIndex___closed__0;
static lean_object* l_Lean_IR_Checker_withParams___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorTag___boxed(lean_object*);
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__0;
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorFields___boxed(lean_object*);
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__0;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3;
static lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__2;
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
static lean_object* l_Lean_IR_Checker_checkVar___closed__1;
static lean_object* l_Lean_IR_Checker_maxCtorTag___closed__0;
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_Checker_markIndex_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_markIndex___closed__1;
static lean_object* l_Lean_IR_Checker_checkExpr___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorTag;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkEqTypes___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_maxCtorScalarsSize___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_CheckerContext_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Alt_body(lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_CheckerState_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_CheckerState_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_instToFormatIRType___private__1(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_getDecl___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__0;
static lean_object* l_Lean_IR_Checker_checkJP___closed__0;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_getDecl___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_IR_Checker_withParams___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkVar___closed__0;
static lean_object* l_Lean_IR_Checker_withParams___closed__3;
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_Checker_markIndex_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkScalarType___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorScalarsSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2;
static lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0;
static lean_object* l_Lean_IR_Checker_checkJP___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_CheckerContext_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_CheckerContext_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Checker_CheckerContext_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_CheckerState_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_CheckerState_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Checker_CheckerState_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3;
x_4 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5;
x_3 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_2, 2);
x_8 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2;
x_9 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__6;
lean_inc(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_7);
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0(x_1, x_2, x_3);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___redArg(x_2, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to compile definition, compiler IR check failed at `", 59, 59);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_throwCheckerError___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`. Error: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_throwCheckerError___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Lean_IR_Decl_name(x_7);
x_9 = l_Lean_IR_Checker_throwCheckerError___redArg___closed__1;
x_10 = 0;
x_11 = l_Lean_MessageData_ofConstName(x_8, x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_IR_Checker_throwCheckerError___redArg___closed__3;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_stringToMessageData(x_1);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___redArg(x_16, x_4, x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_throwCheckerError___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_throwCheckerError___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_throwCheckerError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_throwCheckerError(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_Checker_markIndex_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = lean_nat_dec_lt(x_1, x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_1, x_3);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
else
{
x_2 = x_4;
goto _start;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_Checker_markIndex_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_Checker_markIndex_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_Checker_markIndex_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 4);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
x_10 = lean_nat_dec_lt(x_1, x_5);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_1, x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_Checker_markIndex_spec__1___redArg(x_1, x_2, x_8);
x_13 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 4);
lean_inc(x_19);
x_20 = lean_unsigned_to_nat(3u);
x_21 = lean_nat_mul(x_20, x_14);
x_22 = lean_nat_dec_lt(x_21, x_15);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_23 = lean_nat_add(x_13, x_14);
x_24 = lean_nat_add(x_23, x_15);
lean_dec(x_15);
lean_dec(x_23);
if (lean_is_scalar(x_9)) {
 x_25 = lean_alloc_ctor(0, 5, 0);
} else {
 x_25 = x_9;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
lean_ctor_set(x_25, 2, x_6);
lean_ctor_set(x_25, 3, x_7);
lean_ctor_set(x_25, 4, x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_26 = x_12;
} else {
 lean_dec_ref(x_12);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
x_29 = lean_ctor_get(x_18, 2);
x_30 = lean_ctor_get(x_18, 3);
x_31 = lean_ctor_get(x_18, 4);
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_nat_mul(x_33, x_32);
x_35 = lean_nat_dec_lt(x_27, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_46; 
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 x_36 = x_18;
} else {
 lean_dec_ref(x_18);
 x_36 = lean_box(0);
}
x_37 = lean_nat_add(x_13, x_14);
x_38 = lean_nat_add(x_37, x_15);
lean_dec(x_15);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_30, 0);
lean_inc(x_53);
x_46 = x_53;
goto block_52;
}
else
{
lean_object* x_54; 
x_54 = lean_unsigned_to_nat(0u);
x_46 = x_54;
goto block_52;
}
block_45:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_nat_add(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
if (lean_is_scalar(x_36)) {
 x_43 = lean_alloc_ctor(0, 5, 0);
} else {
 x_43 = x_36;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_16);
lean_ctor_set(x_43, 2, x_17);
lean_ctor_set(x_43, 3, x_31);
lean_ctor_set(x_43, 4, x_19);
if (lean_is_scalar(x_26)) {
 x_44 = lean_alloc_ctor(0, 5, 0);
} else {
 x_44 = x_26;
}
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_28);
lean_ctor_set(x_44, 2, x_29);
lean_ctor_set(x_44, 3, x_39);
lean_ctor_set(x_44, 4, x_43);
return x_44;
}
block_52:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_nat_add(x_37, x_46);
lean_dec(x_46);
lean_dec(x_37);
if (lean_is_scalar(x_9)) {
 x_48 = lean_alloc_ctor(0, 5, 0);
} else {
 x_48 = x_9;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_5);
lean_ctor_set(x_48, 2, x_6);
lean_ctor_set(x_48, 3, x_7);
lean_ctor_set(x_48, 4, x_30);
x_49 = lean_nat_add(x_13, x_32);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
x_39 = x_48;
x_40 = x_49;
x_41 = x_50;
goto block_45;
}
else
{
lean_object* x_51; 
x_51 = lean_unsigned_to_nat(0u);
x_39 = x_48;
x_40 = x_49;
x_41 = x_51;
goto block_45;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_9);
x_55 = lean_nat_add(x_13, x_14);
x_56 = lean_nat_add(x_55, x_15);
lean_dec(x_15);
x_57 = lean_nat_add(x_55, x_27);
lean_dec(x_55);
lean_inc_ref(x_7);
if (lean_is_scalar(x_26)) {
 x_58 = lean_alloc_ctor(0, 5, 0);
} else {
 x_58 = x_26;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_5);
lean_ctor_set(x_58, 2, x_6);
lean_ctor_set(x_58, 3, x_7);
lean_ctor_set(x_58, 4, x_18);
x_59 = !lean_is_exclusive(x_7);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_7, 4);
lean_dec(x_60);
x_61 = lean_ctor_get(x_7, 3);
lean_dec(x_61);
x_62 = lean_ctor_get(x_7, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_7, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_7, 0);
lean_dec(x_64);
lean_ctor_set(x_7, 4, x_19);
lean_ctor_set(x_7, 3, x_58);
lean_ctor_set(x_7, 2, x_17);
lean_ctor_set(x_7, 1, x_16);
lean_ctor_set(x_7, 0, x_56);
return x_7;
}
else
{
lean_object* x_65; 
lean_dec(x_7);
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_16);
lean_ctor_set(x_65, 2, x_17);
lean_ctor_set(x_65, 3, x_58);
lean_ctor_set(x_65, 4, x_19);
return x_65;
}
}
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_12, 3);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_12);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_12, 4);
x_69 = lean_ctor_get(x_12, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_12, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_66, 1);
x_73 = lean_ctor_get(x_66, 2);
x_74 = lean_ctor_get(x_66, 4);
lean_dec(x_74);
x_75 = lean_ctor_get(x_66, 3);
lean_dec(x_75);
x_76 = lean_ctor_get(x_66, 0);
lean_dec(x_76);
x_77 = lean_unsigned_to_nat(3u);
lean_inc_n(x_68, 2);
lean_ctor_set(x_66, 4, x_68);
lean_ctor_set(x_66, 3, x_68);
lean_ctor_set(x_66, 2, x_6);
lean_ctor_set(x_66, 1, x_5);
lean_ctor_set(x_66, 0, x_13);
lean_inc(x_68);
lean_ctor_set(x_12, 3, x_68);
lean_ctor_set(x_12, 0, x_13);
if (lean_is_scalar(x_9)) {
 x_78 = lean_alloc_ctor(0, 5, 0);
} else {
 x_78 = x_9;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
lean_ctor_set(x_78, 2, x_73);
lean_ctor_set(x_78, 3, x_66);
lean_ctor_set(x_78, 4, x_12);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_66, 1);
x_80 = lean_ctor_get(x_66, 2);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_66);
x_81 = lean_unsigned_to_nat(3u);
lean_inc_n(x_68, 2);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_13);
lean_ctor_set(x_82, 1, x_5);
lean_ctor_set(x_82, 2, x_6);
lean_ctor_set(x_82, 3, x_68);
lean_ctor_set(x_82, 4, x_68);
lean_inc(x_68);
lean_ctor_set(x_12, 3, x_68);
lean_ctor_set(x_12, 0, x_13);
if (lean_is_scalar(x_9)) {
 x_83 = lean_alloc_ctor(0, 5, 0);
} else {
 x_83 = x_9;
}
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_79);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_83, 4, x_12);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_12, 4);
x_85 = lean_ctor_get(x_12, 1);
x_86 = lean_ctor_get(x_12, 2);
lean_inc(x_84);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_12);
x_87 = lean_ctor_get(x_66, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_66, 2);
lean_inc(x_88);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 lean_ctor_release(x_66, 3);
 lean_ctor_release(x_66, 4);
 x_89 = x_66;
} else {
 lean_dec_ref(x_66);
 x_89 = lean_box(0);
}
x_90 = lean_unsigned_to_nat(3u);
lean_inc_n(x_84, 2);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 5, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_13);
lean_ctor_set(x_91, 1, x_5);
lean_ctor_set(x_91, 2, x_6);
lean_ctor_set(x_91, 3, x_84);
lean_ctor_set(x_91, 4, x_84);
lean_inc(x_84);
x_92 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_92, 0, x_13);
lean_ctor_set(x_92, 1, x_85);
lean_ctor_set(x_92, 2, x_86);
lean_ctor_set(x_92, 3, x_84);
lean_ctor_set(x_92, 4, x_84);
if (lean_is_scalar(x_9)) {
 x_93 = lean_alloc_ctor(0, 5, 0);
} else {
 x_93 = x_9;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_87);
lean_ctor_set(x_93, 2, x_88);
lean_ctor_set(x_93, 3, x_91);
lean_ctor_set(x_93, 4, x_92);
return x_93;
}
}
else
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_12, 4);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_12);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_12, 1);
x_97 = lean_ctor_get(x_12, 2);
x_98 = lean_ctor_get(x_12, 4);
lean_dec(x_98);
x_99 = lean_ctor_get(x_12, 3);
lean_dec(x_99);
x_100 = lean_ctor_get(x_12, 0);
lean_dec(x_100);
x_101 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_12, 4, x_66);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 0, x_13);
if (lean_is_scalar(x_9)) {
 x_102 = lean_alloc_ctor(0, 5, 0);
} else {
 x_102 = x_9;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_96);
lean_ctor_set(x_102, 2, x_97);
lean_ctor_set(x_102, 3, x_12);
lean_ctor_set(x_102, 4, x_94);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_12, 1);
x_104 = lean_ctor_get(x_12, 2);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_12);
x_105 = lean_unsigned_to_nat(3u);
x_106 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_106, 0, x_13);
lean_ctor_set(x_106, 1, x_5);
lean_ctor_set(x_106, 2, x_6);
lean_ctor_set(x_106, 3, x_66);
lean_ctor_set(x_106, 4, x_66);
if (lean_is_scalar(x_9)) {
 x_107 = lean_alloc_ctor(0, 5, 0);
} else {
 x_107 = x_9;
}
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_103);
lean_ctor_set(x_107, 2, x_104);
lean_ctor_set(x_107, 3, x_106);
lean_ctor_set(x_107, 4, x_94);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_109 = lean_alloc_ctor(0, 5, 0);
} else {
 x_109 = x_9;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_5);
lean_ctor_set(x_109, 2, x_6);
lean_ctor_set(x_109, 3, x_94);
lean_ctor_set(x_109, 4, x_12);
return x_109;
}
}
}
}
else
{
lean_object* x_110; 
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_9)) {
 x_110 = lean_alloc_ctor(0, 5, 0);
} else {
 x_110 = x_9;
}
lean_ctor_set(x_110, 0, x_4);
lean_ctor_set(x_110, 1, x_1);
lean_ctor_set(x_110, 2, x_2);
lean_ctor_set(x_110, 3, x_7);
lean_ctor_set(x_110, 4, x_8);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_4);
x_111 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_Checker_markIndex_spec__1___redArg(x_1, x_2, x_7);
x_112 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_113 = lean_ctor_get(x_8, 0);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 2);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 3);
lean_inc(x_117);
x_118 = lean_ctor_get(x_111, 4);
lean_inc(x_118);
x_119 = lean_unsigned_to_nat(3u);
x_120 = lean_nat_mul(x_119, x_113);
x_121 = lean_nat_dec_lt(x_120, x_114);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
x_122 = lean_nat_add(x_112, x_114);
lean_dec(x_114);
x_123 = lean_nat_add(x_122, x_113);
lean_dec(x_122);
if (lean_is_scalar(x_9)) {
 x_124 = lean_alloc_ctor(0, 5, 0);
} else {
 x_124 = x_9;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_5);
lean_ctor_set(x_124, 2, x_6);
lean_ctor_set(x_124, 3, x_111);
lean_ctor_set(x_124, 4, x_8);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 lean_ctor_release(x_111, 4);
 x_125 = x_111;
} else {
 lean_dec_ref(x_111);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_117, 0);
x_127 = lean_ctor_get(x_118, 0);
x_128 = lean_ctor_get(x_118, 1);
x_129 = lean_ctor_get(x_118, 2);
x_130 = lean_ctor_get(x_118, 3);
x_131 = lean_ctor_get(x_118, 4);
x_132 = lean_unsigned_to_nat(2u);
x_133 = lean_nat_mul(x_132, x_126);
x_134 = lean_nat_dec_lt(x_127, x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_145; lean_object* x_146; 
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 lean_ctor_release(x_118, 4);
 x_135 = x_118;
} else {
 lean_dec_ref(x_118);
 x_135 = lean_box(0);
}
x_136 = lean_nat_add(x_112, x_114);
lean_dec(x_114);
x_137 = lean_nat_add(x_136, x_113);
lean_dec(x_136);
x_145 = lean_nat_add(x_112, x_126);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_130, 0);
lean_inc(x_153);
x_146 = x_153;
goto block_152;
}
else
{
lean_object* x_154; 
x_154 = lean_unsigned_to_nat(0u);
x_146 = x_154;
goto block_152;
}
block_144:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_nat_add(x_139, x_140);
lean_dec(x_140);
lean_dec(x_139);
if (lean_is_scalar(x_135)) {
 x_142 = lean_alloc_ctor(0, 5, 0);
} else {
 x_142 = x_135;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_5);
lean_ctor_set(x_142, 2, x_6);
lean_ctor_set(x_142, 3, x_131);
lean_ctor_set(x_142, 4, x_8);
if (lean_is_scalar(x_125)) {
 x_143 = lean_alloc_ctor(0, 5, 0);
} else {
 x_143 = x_125;
}
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_128);
lean_ctor_set(x_143, 2, x_129);
lean_ctor_set(x_143, 3, x_138);
lean_ctor_set(x_143, 4, x_142);
return x_143;
}
block_152:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_nat_add(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (lean_is_scalar(x_9)) {
 x_148 = lean_alloc_ctor(0, 5, 0);
} else {
 x_148 = x_9;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_115);
lean_ctor_set(x_148, 2, x_116);
lean_ctor_set(x_148, 3, x_117);
lean_ctor_set(x_148, 4, x_130);
x_149 = lean_nat_add(x_112, x_113);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_131, 0);
lean_inc(x_150);
x_138 = x_148;
x_139 = x_149;
x_140 = x_150;
goto block_144;
}
else
{
lean_object* x_151; 
x_151 = lean_unsigned_to_nat(0u);
x_138 = x_148;
x_139 = x_149;
x_140 = x_151;
goto block_144;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
lean_dec(x_9);
x_155 = lean_nat_add(x_112, x_114);
lean_dec(x_114);
x_156 = lean_nat_add(x_155, x_113);
lean_dec(x_155);
x_157 = lean_nat_add(x_112, x_113);
x_158 = lean_nat_add(x_157, x_127);
lean_dec(x_157);
lean_inc_ref(x_8);
if (lean_is_scalar(x_125)) {
 x_159 = lean_alloc_ctor(0, 5, 0);
} else {
 x_159 = x_125;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_5);
lean_ctor_set(x_159, 2, x_6);
lean_ctor_set(x_159, 3, x_118);
lean_ctor_set(x_159, 4, x_8);
x_160 = !lean_is_exclusive(x_8);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_8, 4);
lean_dec(x_161);
x_162 = lean_ctor_get(x_8, 3);
lean_dec(x_162);
x_163 = lean_ctor_get(x_8, 2);
lean_dec(x_163);
x_164 = lean_ctor_get(x_8, 1);
lean_dec(x_164);
x_165 = lean_ctor_get(x_8, 0);
lean_dec(x_165);
lean_ctor_set(x_8, 4, x_159);
lean_ctor_set(x_8, 3, x_117);
lean_ctor_set(x_8, 2, x_116);
lean_ctor_set(x_8, 1, x_115);
lean_ctor_set(x_8, 0, x_156);
return x_8;
}
else
{
lean_object* x_166; 
lean_dec(x_8);
x_166 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_166, 0, x_156);
lean_ctor_set(x_166, 1, x_115);
lean_ctor_set(x_166, 2, x_116);
lean_ctor_set(x_166, 3, x_117);
lean_ctor_set(x_166, 4, x_159);
return x_166;
}
}
}
}
else
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_111, 3);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_111);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_169 = lean_ctor_get(x_111, 4);
x_170 = lean_ctor_get(x_111, 1);
x_171 = lean_ctor_get(x_111, 2);
x_172 = lean_ctor_get(x_111, 3);
lean_dec(x_172);
x_173 = lean_ctor_get(x_111, 0);
lean_dec(x_173);
x_174 = lean_unsigned_to_nat(3u);
lean_inc(x_169);
lean_ctor_set(x_111, 3, x_169);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 0, x_112);
if (lean_is_scalar(x_9)) {
 x_175 = lean_alloc_ctor(0, 5, 0);
} else {
 x_175 = x_9;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_170);
lean_ctor_set(x_175, 2, x_171);
lean_ctor_set(x_175, 3, x_167);
lean_ctor_set(x_175, 4, x_111);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_111, 4);
x_177 = lean_ctor_get(x_111, 1);
x_178 = lean_ctor_get(x_111, 2);
lean_inc(x_176);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_111);
x_179 = lean_unsigned_to_nat(3u);
lean_inc(x_176);
x_180 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_180, 0, x_112);
lean_ctor_set(x_180, 1, x_5);
lean_ctor_set(x_180, 2, x_6);
lean_ctor_set(x_180, 3, x_176);
lean_ctor_set(x_180, 4, x_176);
if (lean_is_scalar(x_9)) {
 x_181 = lean_alloc_ctor(0, 5, 0);
} else {
 x_181 = x_9;
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_177);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set(x_181, 3, x_167);
lean_ctor_set(x_181, 4, x_180);
return x_181;
}
}
else
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_111, 4);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_111);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_184 = lean_ctor_get(x_111, 1);
x_185 = lean_ctor_get(x_111, 2);
x_186 = lean_ctor_get(x_111, 4);
lean_dec(x_186);
x_187 = lean_ctor_get(x_111, 3);
lean_dec(x_187);
x_188 = lean_ctor_get(x_111, 0);
lean_dec(x_188);
x_189 = !lean_is_exclusive(x_182);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_190 = lean_ctor_get(x_182, 1);
x_191 = lean_ctor_get(x_182, 2);
x_192 = lean_ctor_get(x_182, 4);
lean_dec(x_192);
x_193 = lean_ctor_get(x_182, 3);
lean_dec(x_193);
x_194 = lean_ctor_get(x_182, 0);
lean_dec(x_194);
x_195 = lean_unsigned_to_nat(3u);
lean_ctor_set(x_182, 4, x_167);
lean_ctor_set(x_182, 3, x_167);
lean_ctor_set(x_182, 2, x_185);
lean_ctor_set(x_182, 1, x_184);
lean_ctor_set(x_182, 0, x_112);
lean_ctor_set(x_111, 4, x_167);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 0, x_112);
if (lean_is_scalar(x_9)) {
 x_196 = lean_alloc_ctor(0, 5, 0);
} else {
 x_196 = x_9;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 3, x_182);
lean_ctor_set(x_196, 4, x_111);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_182, 1);
x_198 = lean_ctor_get(x_182, 2);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_182);
x_199 = lean_unsigned_to_nat(3u);
x_200 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_200, 0, x_112);
lean_ctor_set(x_200, 1, x_184);
lean_ctor_set(x_200, 2, x_185);
lean_ctor_set(x_200, 3, x_167);
lean_ctor_set(x_200, 4, x_167);
lean_ctor_set(x_111, 4, x_167);
lean_ctor_set(x_111, 2, x_6);
lean_ctor_set(x_111, 1, x_5);
lean_ctor_set(x_111, 0, x_112);
if (lean_is_scalar(x_9)) {
 x_201 = lean_alloc_ctor(0, 5, 0);
} else {
 x_201 = x_9;
}
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_197);
lean_ctor_set(x_201, 2, x_198);
lean_ctor_set(x_201, 3, x_200);
lean_ctor_set(x_201, 4, x_111);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_202 = lean_ctor_get(x_111, 1);
x_203 = lean_ctor_get(x_111, 2);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_111);
x_204 = lean_ctor_get(x_182, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_182, 2);
lean_inc(x_205);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 lean_ctor_release(x_182, 3);
 lean_ctor_release(x_182, 4);
 x_206 = x_182;
} else {
 lean_dec_ref(x_182);
 x_206 = lean_box(0);
}
x_207 = lean_unsigned_to_nat(3u);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 5, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_112);
lean_ctor_set(x_208, 1, x_202);
lean_ctor_set(x_208, 2, x_203);
lean_ctor_set(x_208, 3, x_167);
lean_ctor_set(x_208, 4, x_167);
x_209 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_209, 0, x_112);
lean_ctor_set(x_209, 1, x_5);
lean_ctor_set(x_209, 2, x_6);
lean_ctor_set(x_209, 3, x_167);
lean_ctor_set(x_209, 4, x_167);
if (lean_is_scalar(x_9)) {
 x_210 = lean_alloc_ctor(0, 5, 0);
} else {
 x_210 = x_9;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_204);
lean_ctor_set(x_210, 2, x_205);
lean_ctor_set(x_210, 3, x_208);
lean_ctor_set(x_210, 4, x_209);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_unsigned_to_nat(2u);
if (lean_is_scalar(x_9)) {
 x_212 = lean_alloc_ctor(0, 5, 0);
} else {
 x_212 = x_9;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_5);
lean_ctor_set(x_212, 2, x_6);
lean_ctor_set(x_212, 3, x_111);
lean_ctor_set(x_212, 4, x_182);
return x_212;
}
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_1);
lean_ctor_set(x_214, 2, x_2);
lean_ctor_set(x_214, 3, x_3);
lean_ctor_set(x_214, 4, x_3);
return x_214;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_Checker_markIndex_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_Checker_markIndex_spec__1___redArg(x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_Checker_markIndex___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("variable / join point index ", 28, 28);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_get(x_3);
x_15 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_Checker_markIndex_spec__0___redArg(x_1, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_st_ref_take(x_3);
x_17 = lean_box(0);
x_18 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_Checker_markIndex_spec__0___redArg(x_1, x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Std_DTreeMap_Internal_Impl_insert___at___Lean_IR_Checker_markIndex_spec__1___redArg(x_1, x_17, x_16);
x_7 = x_17;
x_8 = x_3;
x_9 = lean_box(0);
x_10 = x_19;
goto block_13;
}
else
{
lean_dec(x_1);
x_7 = x_17;
x_8 = x_3;
x_9 = lean_box(0);
x_10 = x_16;
goto block_13;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l_Lean_IR_Checker_markIndex___closed__0;
x_21 = l_Nat_reprFast(x_1);
x_22 = lean_string_append(x_20, x_21);
lean_dec_ref(x_21);
x_23 = l_Lean_IR_Checker_markIndex___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Lean_IR_Checker_throwCheckerError___redArg(x_24, x_2, x_3, x_4, x_5);
lean_dec_ref(x_24);
return x_25;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_st_ref_set(x_8, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_Checker_markIndex_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_Checker_markIndex_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___Lean_IR_Checker_markIndex_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_markJP(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_Checker_getDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("depends on declaration '", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_getDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', which has no executable code; consider marking definition as 'noncomputable'", 79, 79);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_10 = l_Lean_IR_findEnvDecl_x27(x_8, x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l_Lean_IR_Checker_getDecl___closed__0;
x_12 = 1;
x_13 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_1, x_12);
x_14 = lean_string_append(x_11, x_13);
lean_dec_ref(x_13);
x_15 = l_Lean_IR_Checker_getDecl___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_Checker_throwCheckerError___redArg(x_16, x_2, x_3, x_4, x_5);
lean_dec_ref(x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_ctor_set_tag(x_10, 0);
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_getDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = l_Lean_IR_LocalContext_isLocalVar(x_19, x_1);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_IR_LocalContext_isParam(x_19, x_1);
x_7 = x_21;
goto block_18;
}
else
{
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
x_15 = l_Lean_IR_Checker_throwCheckerError___redArg(x_14, x_2, x_3, x_4, x_5);
lean_dec_ref(x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_IR_LocalContext_isJP(x_7, x_1);
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
x_16 = l_Lean_IR_Checker_throwCheckerError___redArg(x_15, x_2, x_3, x_4, x_5);
lean_dec_ref(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkJP(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_IR_Checker_checkVar(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_IR_Checker_checkArg(x_11, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_13;
goto _start;
}
else
{
return x_12;
}
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
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
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(x_1, x_14, x_15, x_9, x_2, x_3, x_4, x_5);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkArgs(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_IR_instBEqIRType_beq(x_1, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_IR_Checker_checkEqTypes___closed__0;
x_10 = l_Lean_IR_Checker_throwCheckerError___redArg(x_9, x_3, x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_checkEqTypes(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
x_1 = l_Std_Format_defWidth;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_12 = l_Lean_IR_instToFormatIRType___private__1(x_1);
x_13 = l_Lean_IR_Checker_checkType___closed__1;
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Std_Format_pretty(x_12, x_13, x_14, x_14);
x_16 = lean_string_append(x_11, x_15);
lean_dec_ref(x_15);
x_17 = l_Lean_IR_Checker_checkVar___closed__2;
x_18 = lean_string_append(x_16, x_17);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_19; 
x_19 = l_Lean_IR_Checker_throwCheckerError___redArg(x_18, x_4, x_5, x_6, x_7);
lean_dec_ref(x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = l_Lean_IR_Checker_checkType___closed__2;
x_22 = lean_string_append(x_18, x_21);
x_23 = lean_string_append(x_22, x_20);
x_24 = l_Lean_IR_Checker_throwCheckerError___redArg(x_23, x_4, x_5, x_6, x_7);
lean_dec_ref(x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_Checker_checkType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_IR_IRType_isObj(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = l_Lean_IR_Checker_checkObjType___closed__0;
x_9 = l_Lean_IR_Checker_checkType___closed__0;
x_10 = l_Lean_IR_instToFormatIRType___private__1(x_1);
x_11 = l_Lean_IR_Checker_checkType___closed__1;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Std_Format_pretty(x_10, x_11, x_12, x_12);
x_14 = lean_string_append(x_9, x_13);
lean_dec_ref(x_13);
x_15 = l_Lean_IR_Checker_checkVar___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_Checker_checkType___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_8);
x_20 = l_Lean_IR_Checker_throwCheckerError___redArg(x_19, x_2, x_3, x_4, x_5);
lean_dec_ref(x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkObjType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_IR_IRType_isScalar(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = l_Lean_IR_Checker_checkScalarType___closed__0;
x_9 = l_Lean_IR_Checker_checkType___closed__0;
x_10 = l_Lean_IR_instToFormatIRType___private__1(x_1);
x_11 = l_Lean_IR_Checker_checkType___closed__1;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Std_Format_pretty(x_10, x_11, x_12, x_12);
x_14 = lean_string_append(x_9, x_13);
lean_dec_ref(x_13);
x_15 = l_Lean_IR_Checker_checkVar___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Lean_IR_Checker_checkType___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_8);
x_20 = l_Lean_IR_Checker_throwCheckerError___redArg(x_19, x_2, x_3, x_4, x_5);
lean_dec_ref(x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkScalarType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_IR_LocalContext_getType(x_7, x_1);
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
x_16 = l_Lean_IR_Checker_throwCheckerError___redArg(x_15, x_2, x_3, x_4, x_5);
lean_dec_ref(x_15);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_ctor_set_tag(x_8, 0);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_getType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_Checker_getType(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_9);
x_14 = l_Lean_IR_Checker_checkType___closed__0;
x_15 = l_Lean_IR_instToFormatIRType___private__1(x_11);
x_16 = l_Lean_IR_Checker_checkType___closed__1;
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Std_Format_pretty(x_15, x_16, x_17, x_17);
x_19 = lean_string_append(x_14, x_18);
lean_dec_ref(x_18);
x_20 = l_Lean_IR_Checker_checkVar___closed__2;
x_21 = lean_string_append(x_19, x_20);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_22; 
x_22 = l_Lean_IR_Checker_throwCheckerError___redArg(x_21, x_4, x_5, x_6, x_7);
lean_dec_ref(x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = l_Lean_IR_Checker_checkType___closed__2;
x_25 = lean_string_append(x_21, x_24);
x_26 = lean_string_append(x_25, x_23);
x_27 = l_Lean_IR_Checker_throwCheckerError___redArg(x_26, x_4, x_5, x_6, x_7);
lean_dec_ref(x_26);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_11);
x_28 = lean_box(0);
lean_ctor_set(x_9, 0, x_28);
return x_9;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
lean_dec(x_9);
lean_inc(x_29);
x_30 = lean_apply_1(x_2, x_29);
x_31 = lean_unbox(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = l_Lean_IR_Checker_checkType___closed__0;
x_33 = l_Lean_IR_instToFormatIRType___private__1(x_29);
x_34 = l_Lean_IR_Checker_checkType___closed__1;
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Std_Format_pretty(x_33, x_34, x_35, x_35);
x_37 = lean_string_append(x_32, x_36);
lean_dec_ref(x_36);
x_38 = l_Lean_IR_Checker_checkVar___closed__2;
x_39 = lean_string_append(x_37, x_38);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_40; 
x_40 = l_Lean_IR_Checker_throwCheckerError___redArg(x_39, x_4, x_5, x_6, x_7);
lean_dec_ref(x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_3, 0);
x_42 = l_Lean_IR_Checker_checkType___closed__2;
x_43 = lean_string_append(x_39, x_42);
x_44 = lean_string_append(x_43, x_41);
x_45 = l_Lean_IR_Checker_throwCheckerError___redArg(x_44, x_4, x_5, x_6, x_7);
lean_dec_ref(x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_29);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec_ref(x_2);
x_48 = !lean_is_exclusive(x_9);
if (x_48 == 0)
{
return x_9;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_9, 0);
lean_inc(x_49);
lean_dec(x_9);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_Checker_checkVarType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_getType(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_IR_IRType_isObj(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_7);
x_11 = l_Lean_IR_Checker_checkObjType___closed__0;
x_12 = l_Lean_IR_Checker_checkType___closed__0;
x_13 = l_Lean_IR_instToFormatIRType___private__1(x_9);
x_14 = l_Lean_IR_Checker_checkType___closed__1;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Std_Format_pretty(x_13, x_14, x_15, x_15);
x_17 = lean_string_append(x_12, x_16);
lean_dec_ref(x_16);
x_18 = l_Lean_IR_Checker_checkVar___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_IR_Checker_checkType___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_11);
x_23 = l_Lean_IR_Checker_throwCheckerError___redArg(x_22, x_2, x_3, x_4, x_5);
lean_dec_ref(x_22);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_9);
x_24 = lean_box(0);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = l_Lean_IR_IRType_isObj(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = l_Lean_IR_Checker_checkObjType___closed__0;
x_28 = l_Lean_IR_Checker_checkType___closed__0;
x_29 = l_Lean_IR_instToFormatIRType___private__1(x_25);
x_30 = l_Lean_IR_Checker_checkType___closed__1;
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Std_Format_pretty(x_29, x_30, x_31, x_31);
x_33 = lean_string_append(x_28, x_32);
lean_dec_ref(x_32);
x_34 = l_Lean_IR_Checker_checkVar___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Lean_IR_Checker_checkType___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_27);
x_39 = l_Lean_IR_Checker_throwCheckerError___redArg(x_38, x_2, x_3, x_4, x_5);
lean_dec_ref(x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_25);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
return x_7;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_7, 0);
lean_inc(x_43);
lean_dec(x_7);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkObjVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_getType(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_IR_IRType_isScalar(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_7);
x_11 = l_Lean_IR_Checker_checkScalarType___closed__0;
x_12 = l_Lean_IR_Checker_checkType___closed__0;
x_13 = l_Lean_IR_instToFormatIRType___private__1(x_9);
x_14 = l_Lean_IR_Checker_checkType___closed__1;
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Std_Format_pretty(x_13, x_14, x_15, x_15);
x_17 = lean_string_append(x_12, x_16);
lean_dec_ref(x_16);
x_18 = l_Lean_IR_Checker_checkVar___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_IR_Checker_checkType___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_11);
x_23 = l_Lean_IR_Checker_throwCheckerError___redArg(x_22, x_2, x_3, x_4, x_5);
lean_dec_ref(x_22);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_9);
x_24 = lean_box(0);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = l_Lean_IR_IRType_isScalar(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = l_Lean_IR_Checker_checkScalarType___closed__0;
x_28 = l_Lean_IR_Checker_checkType___closed__0;
x_29 = l_Lean_IR_instToFormatIRType___private__1(x_25);
x_30 = l_Lean_IR_Checker_checkType___closed__1;
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Std_Format_pretty(x_29, x_30, x_31, x_31);
x_33 = lean_string_append(x_28, x_32);
lean_dec_ref(x_32);
x_34 = l_Lean_IR_Checker_checkVar___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Lean_IR_Checker_checkType___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_27);
x_39 = l_Lean_IR_Checker_throwCheckerError___redArg(x_38, x_2, x_3, x_4, x_5);
lean_dec_ref(x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_25);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
return x_7;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_7, 0);
lean_inc(x_43);
lean_dec(x_7);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_Checker_checkScalarVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_IR_Checker_getDecl(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_array_get_size(x_2);
x_11 = l_Lean_IR_Decl_params(x_9);
lean_dec(x_9);
x_12 = lean_array_get_size(x_11);
lean_dec_ref(x_11);
x_13 = lean_nat_dec_eq(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = l_Lean_IR_Checker_checkFullApp___closed__0;
x_15 = 1;
x_16 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_1, x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec_ref(x_16);
x_18 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Nat_reprFast(x_10);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Nat_reprFast(x_12);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Lean_IR_Checker_throwCheckerError___redArg(x_27, x_3, x_4, x_5, x_6);
lean_dec_ref(x_27);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_29 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_4, x_5, x_6);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_8);
if (x_30 == 0)
{
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
lean_dec(x_8);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_checkFullApp(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_IR_Checker_getDecl(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_array_get_size(x_2);
x_11 = l_Lean_IR_Decl_params(x_9);
lean_dec(x_9);
x_12 = lean_array_get_size(x_11);
lean_dec_ref(x_11);
x_13 = lean_nat_dec_lt(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = l_Lean_IR_Checker_checkPartialApp___closed__0;
x_15 = 1;
x_16 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_1, x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec_ref(x_16);
x_18 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Nat_reprFast(x_10);
x_21 = lean_string_append(x_19, x_20);
lean_dec_ref(x_20);
x_22 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Nat_reprFast(x_12);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = l_Lean_IR_Checker_throwCheckerError___redArg(x_25, x_3, x_4, x_5, x_6);
lean_dec_ref(x_25);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_27 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_4, x_5, x_6);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_8);
if (x_28 == 0)
{
return x_8;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_checkPartialApp(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_47; uint8_t x_48; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_8, 2);
x_13 = lean_ctor_get(x_8, 3);
x_14 = lean_ctor_get(x_8, 4);
x_47 = l_Lean_IR_Checker_maxCtorTag;
x_48 = lean_nat_dec_lt(x_47, x_11);
if (x_48 == 0)
{
x_15 = x_48;
goto block_46;
}
else
{
uint8_t x_49; 
x_49 = l_Lean_IR_CtorInfo_isRef(x_8);
x_15 = x_49;
goto block_46;
}
block_46:
{
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_IR_Checker_maxCtorFields;
x_17 = lean_nat_dec_lt(x_16, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = l_Lean_IR_Checker_maxCtorScalarsSize;
x_19 = l_Lean_IR_Checker_usizeSize;
x_20 = lean_nat_mul(x_13, x_19);
x_21 = lean_nat_add(x_14, x_20);
lean_dec(x_20);
x_22 = lean_nat_dec_lt(x_18, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_IR_CtorInfo_isRef(x_8);
lean_dec_ref(x_8);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_9);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec_ref(x_26);
x_27 = l_Lean_IR_Checker_checkArgs(x_9, x_3, x_4, x_5, x_6);
lean_dec_ref(x_9);
return x_27;
}
else
{
lean_dec_ref(x_9);
return x_26;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
x_28 = l_Lean_IR_Checker_checkExpr___closed__0;
x_29 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_10, x_22);
x_30 = lean_string_append(x_28, x_29);
lean_dec_ref(x_29);
x_31 = l_Lean_IR_Checker_checkExpr___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Lean_IR_Checker_throwCheckerError___redArg(x_32, x_3, x_4, x_5, x_6);
lean_dec_ref(x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
x_34 = l_Lean_IR_Checker_checkExpr___closed__0;
x_35 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_10, x_17);
x_36 = lean_string_append(x_34, x_35);
lean_dec_ref(x_35);
x_37 = l_Lean_IR_Checker_checkExpr___closed__2;
x_38 = lean_string_append(x_36, x_37);
x_39 = l_Lean_IR_Checker_throwCheckerError___redArg(x_38, x_3, x_4, x_5, x_6);
lean_dec_ref(x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
x_40 = l_Lean_IR_Checker_checkExpr___closed__3;
x_41 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_10, x_15);
x_42 = lean_string_append(x_40, x_41);
lean_dec_ref(x_41);
x_43 = l_Lean_IR_Checker_checkExpr___closed__4;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_Lean_IR_Checker_throwCheckerError___redArg(x_44, x_3, x_4, x_5, x_6);
lean_dec_ref(x_44);
return x_45;
}
}
}
case 1:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_2, 1);
lean_inc(x_50);
lean_dec_ref(x_2);
x_51 = l_Lean_IR_Checker_checkObjVar(x_50, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
lean_dec_ref(x_51);
x_52 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_52;
}
else
{
lean_dec(x_1);
return x_51;
}
}
case 2:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_54);
lean_dec_ref(x_2);
x_55 = l_Lean_IR_Checker_checkObjVar(x_53, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
lean_dec_ref(x_55);
x_56 = l_Lean_IR_Checker_checkArgs(x_54, x_3, x_4, x_5, x_6);
lean_dec_ref(x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
lean_dec_ref(x_56);
x_57 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_57;
}
else
{
lean_dec(x_1);
return x_56;
}
}
else
{
lean_dec_ref(x_54);
lean_dec(x_1);
return x_55;
}
}
case 3:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
lean_dec_ref(x_2);
x_60 = l_Lean_IR_Checker_getType(x_59, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
switch (lean_obj_tag(x_62)) {
case 7:
{
lean_object* x_63; 
lean_free_object(x_60);
lean_dec(x_58);
x_63 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_63;
}
case 8:
{
lean_object* x_64; 
lean_free_object(x_60);
lean_dec(x_58);
x_64 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_64;
}
case 10:
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_array_get_size(x_65);
x_67 = lean_nat_dec_lt(x_58, x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_65);
lean_free_object(x_60);
lean_dec(x_58);
lean_dec(x_1);
x_68 = l_Lean_IR_Checker_checkExpr___closed__5;
x_69 = l_Lean_IR_Checker_throwCheckerError___redArg(x_68, x_3, x_4, x_5, x_6);
return x_69;
}
else
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_array_fget(x_65, x_58);
lean_dec(x_58);
lean_dec_ref(x_65);
x_71 = l_Lean_IR_instBEqIRType_beq(x_70, x_1);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_free_object(x_60);
x_72 = l_Lean_IR_Checker_checkEqTypes___closed__0;
x_73 = l_Lean_IR_Checker_throwCheckerError___redArg(x_72, x_3, x_4, x_5, x_6);
return x_73;
}
else
{
lean_object* x_74; 
x_74 = lean_box(0);
lean_ctor_set(x_60, 0, x_74);
return x_60;
}
}
}
case 11:
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_75);
lean_dec_ref(x_62);
x_76 = lean_array_get_size(x_75);
x_77 = lean_nat_dec_lt(x_58, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_75);
lean_free_object(x_60);
lean_dec(x_58);
lean_dec(x_1);
x_78 = l_Lean_IR_Checker_checkExpr___closed__5;
x_79 = l_Lean_IR_Checker_throwCheckerError___redArg(x_78, x_3, x_4, x_5, x_6);
return x_79;
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_array_fget(x_75, x_58);
lean_dec(x_58);
lean_dec_ref(x_75);
x_81 = l_Lean_IR_instBEqIRType_beq(x_80, x_1);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_free_object(x_60);
x_82 = l_Lean_IR_Checker_checkEqTypes___closed__0;
x_83 = l_Lean_IR_Checker_throwCheckerError___redArg(x_82, x_3, x_4, x_5, x_6);
return x_83;
}
else
{
lean_object* x_84; 
x_84 = lean_box(0);
lean_ctor_set(x_60, 0, x_84);
return x_60;
}
}
}
default: 
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_60);
lean_dec(x_58);
lean_dec(x_1);
x_85 = l_Lean_IR_Checker_checkExpr___closed__6;
x_86 = l_Lean_IR_instToFormatIRType___private__1(x_62);
x_87 = l_Lean_IR_Checker_checkType___closed__1;
x_88 = lean_unsigned_to_nat(0u);
x_89 = l_Std_Format_pretty(x_86, x_87, x_88, x_88);
x_90 = lean_string_append(x_85, x_89);
lean_dec_ref(x_89);
x_91 = l_Lean_IR_Checker_checkVar___closed__2;
x_92 = lean_string_append(x_90, x_91);
x_93 = l_Lean_IR_Checker_throwCheckerError___redArg(x_92, x_3, x_4, x_5, x_6);
lean_dec_ref(x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_60, 0);
lean_inc(x_94);
lean_dec(x_60);
switch (lean_obj_tag(x_94)) {
case 7:
{
lean_object* x_95; 
lean_dec(x_58);
x_95 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_95;
}
case 8:
{
lean_object* x_96; 
lean_dec(x_58);
x_96 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_96;
}
case 10:
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc_ref(x_97);
lean_dec_ref(x_94);
x_98 = lean_array_get_size(x_97);
x_99 = lean_nat_dec_lt(x_58, x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec_ref(x_97);
lean_dec(x_58);
lean_dec(x_1);
x_100 = l_Lean_IR_Checker_checkExpr___closed__5;
x_101 = l_Lean_IR_Checker_throwCheckerError___redArg(x_100, x_3, x_4, x_5, x_6);
return x_101;
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_array_fget(x_97, x_58);
lean_dec(x_58);
lean_dec_ref(x_97);
x_103 = l_Lean_IR_instBEqIRType_beq(x_102, x_1);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Lean_IR_Checker_checkEqTypes___closed__0;
x_105 = l_Lean_IR_Checker_throwCheckerError___redArg(x_104, x_3, x_4, x_5, x_6);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
case 11:
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_94, 1);
lean_inc_ref(x_108);
lean_dec_ref(x_94);
x_109 = lean_array_get_size(x_108);
x_110 = lean_nat_dec_lt(x_58, x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_108);
lean_dec(x_58);
lean_dec(x_1);
x_111 = l_Lean_IR_Checker_checkExpr___closed__5;
x_112 = l_Lean_IR_Checker_throwCheckerError___redArg(x_111, x_3, x_4, x_5, x_6);
return x_112;
}
else
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_array_fget(x_108, x_58);
lean_dec(x_58);
lean_dec_ref(x_108);
x_114 = l_Lean_IR_instBEqIRType_beq(x_113, x_1);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = l_Lean_IR_Checker_checkEqTypes___closed__0;
x_116 = l_Lean_IR_Checker_throwCheckerError___redArg(x_115, x_3, x_4, x_5, x_6);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
}
default: 
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_58);
lean_dec(x_1);
x_119 = l_Lean_IR_Checker_checkExpr___closed__6;
x_120 = l_Lean_IR_instToFormatIRType___private__1(x_94);
x_121 = l_Lean_IR_Checker_checkType___closed__1;
x_122 = lean_unsigned_to_nat(0u);
x_123 = l_Std_Format_pretty(x_120, x_121, x_122, x_122);
x_124 = lean_string_append(x_119, x_123);
lean_dec_ref(x_123);
x_125 = l_Lean_IR_Checker_checkVar___closed__2;
x_126 = lean_string_append(x_124, x_125);
x_127 = l_Lean_IR_Checker_throwCheckerError___redArg(x_126, x_3, x_4, x_5, x_6);
lean_dec_ref(x_126);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_58);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_60);
if (x_128 == 0)
{
return x_60;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_60, 0);
lean_inc(x_129);
lean_dec(x_60);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
case 4:
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_2, 1);
lean_inc(x_131);
lean_dec_ref(x_2);
x_132 = l_Lean_IR_Checker_checkObjVar(x_131, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_132, 0);
lean_dec(x_134);
x_135 = lean_box(5);
lean_inc(x_1);
x_136 = l_Lean_IR_instBEqIRType_beq(x_1, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_free_object(x_132);
x_137 = l_Lean_IR_Checker_checkType___closed__0;
x_138 = l_Lean_IR_instToFormatIRType___private__1(x_1);
x_139 = l_Lean_IR_Checker_checkType___closed__1;
x_140 = lean_unsigned_to_nat(0u);
x_141 = l_Std_Format_pretty(x_138, x_139, x_140, x_140);
x_142 = lean_string_append(x_137, x_141);
lean_dec_ref(x_141);
x_143 = l_Lean_IR_Checker_checkVar___closed__2;
x_144 = lean_string_append(x_142, x_143);
x_145 = l_Lean_IR_Checker_throwCheckerError___redArg(x_144, x_3, x_4, x_5, x_6);
lean_dec_ref(x_144);
return x_145;
}
else
{
lean_object* x_146; 
lean_dec(x_1);
x_146 = lean_box(0);
lean_ctor_set(x_132, 0, x_146);
return x_132;
}
}
else
{
lean_object* x_147; uint8_t x_148; 
lean_dec(x_132);
x_147 = lean_box(5);
lean_inc(x_1);
x_148 = l_Lean_IR_instBEqIRType_beq(x_1, x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_149 = l_Lean_IR_Checker_checkType___closed__0;
x_150 = l_Lean_IR_instToFormatIRType___private__1(x_1);
x_151 = l_Lean_IR_Checker_checkType___closed__1;
x_152 = lean_unsigned_to_nat(0u);
x_153 = l_Std_Format_pretty(x_150, x_151, x_152, x_152);
x_154 = lean_string_append(x_149, x_153);
lean_dec_ref(x_153);
x_155 = l_Lean_IR_Checker_checkVar___closed__2;
x_156 = lean_string_append(x_154, x_155);
x_157 = l_Lean_IR_Checker_throwCheckerError___redArg(x_156, x_3, x_4, x_5, x_6);
lean_dec_ref(x_156);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_1);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
}
}
else
{
lean_dec(x_1);
return x_132;
}
}
case 5:
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_2, 2);
lean_inc(x_160);
lean_dec_ref(x_2);
x_161 = l_Lean_IR_Checker_checkObjVar(x_160, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
lean_dec_ref(x_161);
x_162 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_4, x_5, x_6);
return x_162;
}
else
{
lean_dec(x_1);
return x_161;
}
}
case 6:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_1);
x_163 = lean_ctor_get(x_2, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_164);
lean_dec_ref(x_2);
x_165 = l_Lean_IR_Checker_checkFullApp(x_163, x_164, x_3, x_4, x_5, x_6);
lean_dec_ref(x_164);
return x_165;
}
case 7:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_2, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_167);
lean_dec_ref(x_2);
x_168 = l_Lean_IR_Checker_checkPartialApp(x_166, x_167, x_3, x_4, x_5, x_6);
lean_dec_ref(x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
lean_dec_ref(x_168);
x_169 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_169;
}
else
{
lean_dec(x_1);
return x_168;
}
}
case 8:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_2, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_171);
lean_dec_ref(x_2);
x_172 = l_Lean_IR_Checker_checkObjVar(x_170, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
lean_dec_ref(x_172);
x_173 = l_Lean_IR_Checker_checkArgs(x_171, x_3, x_4, x_5, x_6);
lean_dec_ref(x_171);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
lean_dec_ref(x_173);
x_174 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_174;
}
else
{
lean_dec(x_1);
return x_173;
}
}
else
{
lean_dec_ref(x_171);
lean_dec(x_1);
return x_172;
}
}
case 9:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_2, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_2, 1);
lean_inc(x_176);
lean_dec_ref(x_2);
x_177 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
lean_dec_ref(x_177);
lean_inc(x_176);
x_178 = l_Lean_IR_Checker_checkScalarVar(x_176, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
lean_dec_ref(x_178);
x_179 = l_Lean_IR_Checker_getType(x_176, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
x_182 = l_Lean_IR_instBEqIRType_beq(x_181, x_175);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_free_object(x_179);
x_183 = l_Lean_IR_Checker_checkType___closed__0;
x_184 = l_Lean_IR_instToFormatIRType___private__1(x_181);
x_185 = l_Lean_IR_Checker_checkType___closed__1;
x_186 = lean_unsigned_to_nat(0u);
x_187 = l_Std_Format_pretty(x_184, x_185, x_186, x_186);
x_188 = lean_string_append(x_183, x_187);
lean_dec_ref(x_187);
x_189 = l_Lean_IR_Checker_checkVar___closed__2;
x_190 = lean_string_append(x_188, x_189);
x_191 = l_Lean_IR_Checker_throwCheckerError___redArg(x_190, x_3, x_4, x_5, x_6);
lean_dec_ref(x_190);
return x_191;
}
else
{
lean_object* x_192; 
lean_dec(x_181);
x_192 = lean_box(0);
lean_ctor_set(x_179, 0, x_192);
return x_179;
}
}
else
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_ctor_get(x_179, 0);
lean_inc(x_193);
lean_dec(x_179);
lean_inc(x_193);
x_194 = l_Lean_IR_instBEqIRType_beq(x_193, x_175);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_195 = l_Lean_IR_Checker_checkType___closed__0;
x_196 = l_Lean_IR_instToFormatIRType___private__1(x_193);
x_197 = l_Lean_IR_Checker_checkType___closed__1;
x_198 = lean_unsigned_to_nat(0u);
x_199 = l_Std_Format_pretty(x_196, x_197, x_198, x_198);
x_200 = lean_string_append(x_195, x_199);
lean_dec_ref(x_199);
x_201 = l_Lean_IR_Checker_checkVar___closed__2;
x_202 = lean_string_append(x_200, x_201);
x_203 = l_Lean_IR_Checker_throwCheckerError___redArg(x_202, x_3, x_4, x_5, x_6);
lean_dec_ref(x_202);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_193);
x_204 = lean_box(0);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
}
}
else
{
uint8_t x_206; 
lean_dec(x_175);
x_206 = !lean_is_exclusive(x_179);
if (x_206 == 0)
{
return x_179;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_179, 0);
lean_inc(x_207);
lean_dec(x_179);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_207);
return x_208;
}
}
}
else
{
lean_dec(x_176);
lean_dec(x_175);
return x_178;
}
}
else
{
lean_dec(x_176);
lean_dec(x_175);
return x_177;
}
}
case 10:
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_2, 0);
lean_inc(x_209);
lean_dec_ref(x_2);
x_210 = l_Lean_IR_Checker_checkScalarType(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; 
lean_dec_ref(x_210);
x_211 = l_Lean_IR_Checker_checkObjVar(x_209, x_3, x_4, x_5, x_6);
return x_211;
}
else
{
lean_dec(x_209);
return x_210;
}
}
case 11:
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_212);
lean_dec_ref(x_2);
if (lean_obj_tag(x_212) == 0)
{
uint8_t x_213; 
lean_dec(x_1);
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_212, 0);
lean_dec(x_214);
x_215 = lean_box(0);
lean_ctor_set(x_212, 0, x_215);
return x_212;
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_212);
x_216 = lean_box(0);
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_216);
return x_217;
}
}
else
{
lean_object* x_218; 
lean_dec_ref(x_212);
x_218 = l_Lean_IR_Checker_checkObjType(x_1, x_3, x_4, x_5, x_6);
return x_218;
}
}
default: 
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_2, 0);
lean_inc(x_219);
lean_dec_ref(x_2);
x_220 = l_Lean_IR_Checker_checkObjVar(x_219, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_220) == 0)
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_ctor_get(x_220, 0);
lean_dec(x_222);
x_223 = lean_box(1);
lean_inc(x_1);
x_224 = l_Lean_IR_instBEqIRType_beq(x_1, x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_free_object(x_220);
x_225 = l_Lean_IR_Checker_checkType___closed__0;
x_226 = l_Lean_IR_instToFormatIRType___private__1(x_1);
x_227 = l_Lean_IR_Checker_checkType___closed__1;
x_228 = lean_unsigned_to_nat(0u);
x_229 = l_Std_Format_pretty(x_226, x_227, x_228, x_228);
x_230 = lean_string_append(x_225, x_229);
lean_dec_ref(x_229);
x_231 = l_Lean_IR_Checker_checkVar___closed__2;
x_232 = lean_string_append(x_230, x_231);
x_233 = l_Lean_IR_Checker_throwCheckerError___redArg(x_232, x_3, x_4, x_5, x_6);
lean_dec_ref(x_232);
return x_233;
}
else
{
lean_object* x_234; 
lean_dec(x_1);
x_234 = lean_box(0);
lean_ctor_set(x_220, 0, x_234);
return x_220;
}
}
else
{
lean_object* x_235; uint8_t x_236; 
lean_dec(x_220);
x_235 = lean_box(1);
lean_inc(x_1);
x_236 = l_Lean_IR_instBEqIRType_beq(x_1, x_235);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_237 = l_Lean_IR_Checker_checkType___closed__0;
x_238 = l_Lean_IR_instToFormatIRType___private__1(x_1);
x_239 = l_Lean_IR_Checker_checkType___closed__1;
x_240 = lean_unsigned_to_nat(0u);
x_241 = l_Std_Format_pretty(x_238, x_239, x_240, x_240);
x_242 = lean_string_append(x_237, x_241);
lean_dec_ref(x_241);
x_243 = l_Lean_IR_Checker_checkVar___closed__2;
x_244 = lean_string_append(x_242, x_243);
x_245 = l_Lean_IR_Checker_throwCheckerError___redArg(x_244, x_3, x_4, x_5, x_6);
lean_dec_ref(x_244);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_1);
x_246 = lean_box(0);
x_247 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_247, 0, x_246);
return x_247;
}
}
}
else
{
lean_dec(x_1);
return x_220;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_checkExpr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = l_Lean_IR_Checker_markIndex(x_8, x_3, x_4, x_5, x_6);
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
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_13 = l_Lean_IR_LocalContext_addParam(x_1, x_2);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
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
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_inc(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_31 = x_28;
x_32 = lean_box(0);
goto block_35;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_37, x_37);
if (x_39 == 0)
{
lean_dec(x_37);
lean_inc(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_31 = x_28;
x_32 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__0___boxed), 7, 0);
x_41 = 0;
x_42 = lean_usize_of_nat(x_37);
lean_dec(x_37);
lean_inc(x_28);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_27, x_40, x_1, x_41, x_42, x_28);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_44 = lean_apply_5(x_43, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_31 = x_45;
x_32 = lean_box(0);
goto block_35;
}
else
{
uint8_t x_46; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
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
x_34 = lean_apply_5(x_2, x_33, x_4, x_5, x_6, lean_box(0));
return x_34;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_49 = lean_ctor_get(x_10, 0);
x_50 = lean_ctor_get(x_10, 2);
x_51 = lean_ctor_get(x_10, 3);
x_52 = lean_ctor_get(x_10, 4);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_10);
x_53 = l_Lean_IR_Checker_withParams___closed__2;
x_54 = l_Lean_IR_Checker_withParams___closed__3;
lean_inc_ref(x_49);
x_55 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_55, 0, x_49);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_56, 0, x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_58, 0, x_52);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_59, 0, x_51);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_60, 0, x_50);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_59);
lean_ctor_set(x_61, 4, x_58);
lean_ctor_set(x_8, 1, x_54);
lean_ctor_set(x_8, 0, x_61);
x_62 = l_ReaderT_instMonad___redArg(x_8);
x_63 = l_ReaderT_instMonad___redArg(x_62);
x_64 = lean_ctor_get(x_3, 0);
x_65 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_66);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_array_get_size(x_1);
x_74 = lean_nat_dec_lt(x_72, x_73);
if (x_74 == 0)
{
lean_dec(x_73);
lean_inc(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_67 = x_64;
x_68 = lean_box(0);
goto block_71;
}
else
{
uint8_t x_75; 
x_75 = lean_nat_dec_le(x_73, x_73);
if (x_75 == 0)
{
lean_dec(x_73);
lean_inc(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_67 = x_64;
x_68 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__0___boxed), 7, 0);
x_77 = 0;
x_78 = lean_usize_of_nat(x_73);
lean_dec(x_73);
lean_inc(x_64);
x_79 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_63, x_76, x_1, x_77, x_78, x_64);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_80 = lean_apply_5(x_79, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_67 = x_81;
x_68 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_82);
return x_84;
}
}
}
block_71:
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_65);
lean_ctor_set(x_69, 2, x_66);
x_70 = lean_apply_5(x_2, x_69, x_4, x_5, x_6, lean_box(0));
return x_70;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_85 = lean_ctor_get(x_8, 0);
lean_inc(x_85);
lean_dec(x_8);
x_86 = lean_ctor_get(x_85, 0);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_85, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_85, 4);
lean_inc(x_89);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 lean_ctor_release(x_85, 2);
 lean_ctor_release(x_85, 3);
 lean_ctor_release(x_85, 4);
 x_90 = x_85;
} else {
 lean_dec_ref(x_85);
 x_90 = lean_box(0);
}
x_91 = l_Lean_IR_Checker_withParams___closed__2;
x_92 = l_Lean_IR_Checker_withParams___closed__3;
lean_inc_ref(x_86);
x_93 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_93, 0, x_86);
x_94 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_94, 0, x_86);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_96, 0, x_89);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_97, 0, x_88);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_98, 0, x_87);
if (lean_is_scalar(x_90)) {
 x_99 = lean_alloc_ctor(0, 5, 0);
} else {
 x_99 = x_90;
}
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_91);
lean_ctor_set(x_99, 2, x_98);
lean_ctor_set(x_99, 3, x_97);
lean_ctor_set(x_99, 4, x_96);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_92);
x_101 = l_ReaderT_instMonad___redArg(x_100);
x_102 = l_ReaderT_instMonad___redArg(x_101);
x_103 = lean_ctor_get(x_3, 0);
x_104 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_105);
x_111 = lean_unsigned_to_nat(0u);
x_112 = lean_array_get_size(x_1);
x_113 = lean_nat_dec_lt(x_111, x_112);
if (x_113 == 0)
{
lean_dec(x_112);
lean_inc(x_103);
lean_dec_ref(x_102);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_106 = x_103;
x_107 = lean_box(0);
goto block_110;
}
else
{
uint8_t x_114; 
x_114 = lean_nat_dec_le(x_112, x_112);
if (x_114 == 0)
{
lean_dec(x_112);
lean_inc(x_103);
lean_dec_ref(x_102);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_106 = x_103;
x_107 = lean_box(0);
goto block_110;
}
else
{
lean_object* x_115; size_t x_116; size_t x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__0___boxed), 7, 0);
x_116 = 0;
x_117 = lean_usize_of_nat(x_112);
lean_dec(x_112);
lean_inc(x_103);
x_118 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_102, x_115, x_1, x_116, x_117, x_103);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_119 = lean_apply_5(x_118, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_106 = x_120;
x_107 = lean_box(0);
goto block_110;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_105);
lean_dec_ref(x_104);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_121);
return x_123;
}
}
}
block_110:
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_104);
lean_ctor_set(x_108, 2, x_105);
x_109 = lean_apply_5(x_2, x_108, x_4, x_5, x_6, lean_box(0));
return x_109;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_withParams___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_Checker_withParams(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_13 = l_Lean_IR_Checker_markIndex(x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec_ref(x_13);
x_14 = l_Lean_IR_LocalContext_addParam(x_4, x_11);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_14;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec_ref(x_11);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Lean_IR_Alt_body(x_11);
lean_dec_ref(x_11);
lean_inc_ref(x_5);
x_13 = l_Lean_IR_Checker_checkFnBody(x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_14;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_13;
}
}
else
{
lean_object* x_18; 
lean_dec_ref(x_5);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_dec_ref(x_1);
lean_inc_ref(x_19);
lean_inc(x_18);
x_21 = l_Lean_IR_Checker_checkExpr(x_18, x_19, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec_ref(x_21);
lean_inc(x_17);
x_22 = l_Lean_IR_Checker_markIndex(x_17, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec_ref(x_22);
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = l_Lean_IR_LocalContext_addLocal(x_24, x_17, x_18, x_19);
lean_ctor_set(x_2, 0, x_25);
x_1 = x_20;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_30 = l_Lean_IR_LocalContext_addLocal(x_27, x_17, x_18, x_19);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_29);
x_1 = x_20;
x_2 = x_31;
goto _start;
}
}
else
{
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_2);
return x_22;
}
}
else
{
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_2);
return x_21;
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
lean_dec_ref(x_1);
lean_inc(x_33);
x_37 = l_Lean_IR_Checker_markIndex(x_33, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec_ref(x_37);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_40);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_array_get_size(x_34);
x_51 = lean_nat_dec_lt(x_49, x_50);
if (x_51 == 0)
{
lean_dec(x_50);
lean_dec_ref(x_2);
lean_inc(x_38);
x_41 = x_38;
x_42 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_52; 
x_52 = lean_nat_dec_le(x_50, x_50);
if (x_52 == 0)
{
lean_dec(x_50);
lean_dec_ref(x_2);
lean_inc(x_38);
x_41 = x_38;
x_42 = lean_box(0);
goto block_48;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
x_53 = 0;
x_54 = lean_usize_of_nat(x_50);
lean_dec(x_50);
lean_inc(x_38);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(x_34, x_53, x_54, x_38, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_41 = x_56;
x_42 = lean_box(0);
goto block_48;
}
else
{
uint8_t x_57; 
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
block_48:
{
lean_object* x_43; lean_object* x_44; 
lean_inc_ref(x_40);
lean_inc_ref(x_39);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_40);
lean_inc(x_35);
x_44 = l_Lean_IR_Checker_checkFnBody(x_35, x_43, x_3, x_4, x_5);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_44);
x_45 = l_Lean_IR_LocalContext_addJP(x_38, x_33, x_34, x_35);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_40);
x_1 = x_36;
x_2 = x_46;
goto _start;
}
else
{
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
return x_44;
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_2);
return x_37;
}
}
case 2:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 3);
lean_inc(x_62);
lean_dec_ref(x_1);
x_63 = l_Lean_IR_Checker_checkVar(x_60, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
lean_dec_ref(x_63);
x_64 = l_Lean_IR_Checker_checkArg(x_61, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_1 = x_62;
goto _start;
}
else
{
lean_dec(x_62);
lean_dec_ref(x_2);
return x_64;
}
}
else
{
lean_dec(x_62);
lean_dec(x_61);
lean_dec_ref(x_2);
return x_63;
}
}
case 3:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 2);
lean_inc(x_67);
lean_dec_ref(x_1);
x_68 = l_Lean_IR_Checker_checkVar(x_66, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_68) == 0)
{
lean_dec_ref(x_68);
x_1 = x_67;
goto _start;
}
else
{
lean_dec(x_67);
lean_dec_ref(x_2);
return x_68;
}
}
case 4:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 3);
lean_inc(x_72);
lean_dec_ref(x_1);
x_73 = l_Lean_IR_Checker_checkVar(x_70, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
lean_dec_ref(x_73);
x_74 = l_Lean_IR_Checker_checkVar(x_71, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_74) == 0)
{
lean_dec_ref(x_74);
x_1 = x_72;
goto _start;
}
else
{
lean_dec(x_72);
lean_dec_ref(x_2);
return x_74;
}
}
else
{
lean_dec(x_72);
lean_dec(x_71);
lean_dec_ref(x_2);
return x_73;
}
}
case 5:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_1, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_1, 5);
lean_inc(x_78);
lean_dec_ref(x_1);
x_79 = l_Lean_IR_Checker_checkVar(x_76, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
lean_dec_ref(x_79);
x_80 = l_Lean_IR_Checker_checkVar(x_77, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_80) == 0)
{
lean_dec_ref(x_80);
x_1 = x_78;
goto _start;
}
else
{
lean_dec(x_78);
lean_dec_ref(x_2);
return x_80;
}
}
else
{
lean_dec(x_78);
lean_dec(x_77);
lean_dec_ref(x_2);
return x_79;
}
}
case 8:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
lean_dec_ref(x_1);
x_84 = l_Lean_IR_Checker_checkVar(x_82, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_84) == 0)
{
lean_dec_ref(x_84);
x_1 = x_83;
goto _start;
}
else
{
lean_dec(x_83);
lean_dec_ref(x_2);
return x_84;
}
}
case 9:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_1, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_87);
lean_dec_ref(x_1);
x_88 = l_Lean_IR_Checker_checkVar(x_86, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_88, 0);
lean_dec(x_90);
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_array_get_size(x_87);
x_93 = lean_box(0);
x_94 = lean_nat_dec_lt(x_91, x_92);
if (x_94 == 0)
{
lean_dec(x_92);
lean_dec_ref(x_87);
lean_dec_ref(x_2);
lean_ctor_set(x_88, 0, x_93);
return x_88;
}
else
{
uint8_t x_95; 
x_95 = lean_nat_dec_le(x_92, x_92);
if (x_95 == 0)
{
lean_dec(x_92);
lean_dec_ref(x_87);
lean_dec_ref(x_2);
lean_ctor_set(x_88, 0, x_93);
return x_88;
}
else
{
size_t x_96; size_t x_97; lean_object* x_98; 
lean_free_object(x_88);
x_96 = 0;
x_97 = lean_usize_of_nat(x_92);
lean_dec(x_92);
x_98 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(x_87, x_96, x_97, x_93, x_2, x_3, x_4, x_5);
lean_dec_ref(x_87);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_88);
x_99 = lean_unsigned_to_nat(0u);
x_100 = lean_array_get_size(x_87);
x_101 = lean_box(0);
x_102 = lean_nat_dec_lt(x_99, x_100);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_100);
lean_dec_ref(x_87);
lean_dec_ref(x_2);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_101);
return x_103;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_100, x_100);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_100);
lean_dec_ref(x_87);
lean_dec_ref(x_2);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_101);
return x_105;
}
else
{
size_t x_106; size_t x_107; lean_object* x_108; 
x_106 = 0;
x_107 = lean_usize_of_nat(x_100);
lean_dec(x_100);
x_108 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(x_87, x_106, x_107, x_101, x_2, x_3, x_4, x_5);
lean_dec_ref(x_87);
return x_108;
}
}
}
}
else
{
lean_dec_ref(x_87);
lean_dec_ref(x_2);
return x_88;
}
}
case 10:
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_1, 0);
lean_inc(x_109);
lean_dec_ref(x_1);
x_110 = l_Lean_IR_Checker_checkArg(x_109, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_110;
}
case 11:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_112);
lean_dec_ref(x_1);
x_113 = l_Lean_IR_Checker_checkJP(x_111, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
lean_dec_ref(x_113);
x_114 = l_Lean_IR_Checker_checkArgs(x_112, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_112);
return x_114;
}
else
{
lean_dec_ref(x_112);
lean_dec_ref(x_2);
return x_113;
}
}
case 12:
{
lean_object* x_115; lean_object* x_116; 
lean_dec_ref(x_2);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
default: 
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_1, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_1, 2);
lean_inc(x_118);
lean_dec(x_1);
x_7 = x_117;
x_8 = x_118;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = lean_box(0);
goto block_16;
}
}
block_16:
{
lean_object* x_14; 
x_14 = l_Lean_IR_Checker_checkVar(x_7, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_dec_ref(x_14);
x_1 = x_8;
x_2 = x_9;
x_3 = x_10;
x_4 = x_11;
x_5 = x_12;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
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
x_7 = l_Lean_IR_Checker_checkFnBody(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_13 = lean_box(0);
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
x_13 = lean_box(0);
goto block_16;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(x_7, x_21, x_22, x_9, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_12 = x_24;
x_13 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_25; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_8);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
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
x_15 = l_Lean_IR_Checker_checkFnBody(x_8, x_14, x_3, x_4, x_5);
return x_15;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_28);
lean_dec_ref(x_1);
x_29 = lean_box(0);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_28);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_31);
lean_dec_ref(x_28);
lean_dec_ref(x_2);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_29);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_31, x_31);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_31);
lean_dec_ref(x_28);
lean_dec_ref(x_2);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_29);
return x_35;
}
else
{
lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = 0;
x_38 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_39 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(x_28, x_37, x_38, x_36, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_28);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_29);
return x_39;
}
else
{
lean_object* x_42; 
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_29);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
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
x_7 = l_Lean_IR_Checker_checkDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box(1);
x_7 = lean_st_mk_ref(x_6);
lean_inc_ref(x_2);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_1);
x_9 = l_Lean_IR_Checker_checkDecl(x_2, x_8, x_7, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_st_ref_get(x_7);
lean_dec(x_7);
lean_dec(x_11);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_st_ref_get(x_7);
lean_dec(x_7);
lean_dec(x_13);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
}
else
{
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_checkDecl(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_1);
x_11 = l_Lean_IR_checkDecl(x_1, x_10, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_12;
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
lean_object* x_16; 
lean_dec_ref(x_1);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_5);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_7);
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
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_7);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
lean_inc_ref(x_1);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0(x_1, x_1, x_12, x_13, x_7, x_2, x_3);
lean_dec_ref(x_1);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0(x_1, x_2, x_9, x_10, x_5, x_6, x_7);
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
x_5 = l_Lean_IR_checkDecls(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Checker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
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
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__0);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__1);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__2);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__3);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__4);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__5);
l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__6 = _init_l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__6();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_IR_Checker_throwCheckerError_spec__0_spec__0___closed__6);
l_Lean_IR_Checker_throwCheckerError___redArg___closed__0 = _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_throwCheckerError___redArg___closed__0);
l_Lean_IR_Checker_throwCheckerError___redArg___closed__1 = _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_throwCheckerError___redArg___closed__1);
l_Lean_IR_Checker_throwCheckerError___redArg___closed__2 = _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_throwCheckerError___redArg___closed__2);
l_Lean_IR_Checker_throwCheckerError___redArg___closed__3 = _init_l_Lean_IR_Checker_throwCheckerError___redArg___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_throwCheckerError___redArg___closed__3);
l_Lean_IR_Checker_markIndex___closed__0 = _init_l_Lean_IR_Checker_markIndex___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___closed__0);
l_Lean_IR_Checker_markIndex___closed__1 = _init_l_Lean_IR_Checker_markIndex___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___closed__1);
l_Lean_IR_Checker_getDecl___closed__0 = _init_l_Lean_IR_Checker_getDecl___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_getDecl___closed__0);
l_Lean_IR_Checker_getDecl___closed__1 = _init_l_Lean_IR_Checker_getDecl___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_getDecl___closed__1);
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
l_Lean_IR_Checker_checkType___closed__2 = _init_l_Lean_IR_Checker_checkType___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_checkType___closed__2);
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
