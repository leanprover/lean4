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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__27;
static lean_object* l_Lean_IR_Checker_withParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getUSizeSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorFields;
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_maxCtorFields___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_max_ctor_scalars_size(lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__28;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_IR_Checker_markIndex___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_usize_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_usizeSize;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorScalarsSize;
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkEqTypes___redArg___closed__0;
static lean_object* l_Lean_IR_Checker_withParams___closed__4;
static lean_object* l_Lean_IR_Checker_markIndex___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___redArg(lean_object*, lean_object*);
lean_object* lean_get_max_ctor_fields(lean_object*);
lean_object* lean_get_max_ctor_tag(lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__11;
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkType___redArg___closed__0;
static lean_object* l_Lean_IR_Checker_withParams___closed__9;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__8;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Checker_checkFullApp___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_usizeSize___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__20;
static lean_object* l_Lean_IR_Checker_checkVar___closed__2;
static lean_object* l_Lean_IR_Checker_withParams___closed__17;
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkObjType___redArg___closed__0;
static lean_object* l_Lean_IR_Checker_checkExpr___closed__6;
static lean_object* l_Lean_IR_Checker_checkExpr___closed__3;
static lean_object* l_Lean_IR_Checker_withParams___closed__29;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__24;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__25;
static lean_object* l_Lean_IR_Checker_withParams___closed__1;
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorTag___boxed(lean_object*);
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__2;
lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__0;
static lean_object* l_Lean_IR_Checker_withParams___closed__22;
static lean_object* l_Lean_IR_Checker_withParams___closed__16;
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__14;
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorFields___boxed(lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__0;
static lean_object* l_Lean_IR_Checker_withParams___closed__30;
static lean_object* l_Lean_IR_Checker_withParams___closed__5;
uint8_t l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkPartialApp___closed__3;
lean_object* l_ExceptT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkVar___closed__1;
static lean_object* l_Lean_IR_Checker_maxCtorTag___closed__0;
lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__19;
static lean_object* l_Lean_IR_Checker_checkExpr___closed__7;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__21;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_maxCtorTag;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__18;
static lean_object* l_Lean_IR_Checker_withParams___closed__26;
static lean_object* l_Lean_IR_Checker_withParams___closed__23;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__12;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__7;
static lean_object* l_Lean_IR_Checker_maxCtorScalarsSize___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_markIndex___redArg___closed__0;
static lean_object* l_Lean_IR_Checker_checkScalarType___redArg___closed__0;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_getDecl___closed__0;
static lean_object* l_Lean_IR_checkDecl___closed__1;
lean_object* l_ExceptT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__0;
static lean_object* l_Lean_IR_Checker_checkJP___closed__0;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_getDecl___closed__1;
static lean_object* l_Lean_IR_checkDecl___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_IR_Checker_withParams___closed__13;
static lean_object* l_Lean_IR_Checker_withParams___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkVar___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__3;
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Checker_checkExpr___lam__1(uint8_t, lean_object*);
static lean_object* l_Lean_IR_Checker_checkEqTypes___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__10;
static lean_object* l_Lean_IR_Checker_withParams___closed__15;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkFullApp___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_checkType___redArg___closed__1;
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getMaxCtorScalarsSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Checker_getDecl___lam__0(lean_object*);
static lean_object* l_Lean_IR_Checker_checkJP___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
static lean_object* l_Lean_IR_Checker_checkExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Checker_withParams___closed__6;
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_2, x_5);
if (x_9 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___redArg(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_Checker_markIndex___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_markIndex___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("variable / joinpoint index ", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_markIndex___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" has already been used", 22, 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___redArg(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_2, x_1, x_4);
x_6 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_3, 0);
lean_dec(x_9);
x_10 = l_Lean_IR_Checker_markIndex___redArg___closed__1;
x_11 = l_Nat_reprFast(x_1);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = l_Lean_IR_Checker_markIndex___redArg___closed__2;
x_14 = lean_string_append(x_12, x_13);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_16 = l_Lean_IR_Checker_markIndex___redArg___closed__1;
x_17 = l_Nat_reprFast(x_1);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = l_Lean_IR_Checker_markIndex___redArg___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markIndex___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at___Lean_IR_Checker_markIndex_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markIndex___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markIndex(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Checker_markIndex___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markIndex___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Checker_markIndex___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markIndex___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_markJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_markJP(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Checker_getDecl___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
lean_inc(x_1);
x_6 = l_Lean_IR_findEnvDecl_x27(x_4, x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_alloc_closure((void*)(l_Lean_IR_Checker_getDecl___lam__0___boxed), 1, 0);
x_8 = l_Lean_IR_Checker_getDecl___closed__0;
x_9 = 1;
x_10 = l_Lean_Name_toString(x_1, x_9, x_7);
x_11 = lean_string_append(x_8, x_10);
lean_dec(x_10);
x_12 = l_Lean_IR_Checker_getDecl___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getDecl___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Checker_getDecl___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_2, 1);
x_18 = l_Lean_IR_LocalContext_isLocalVar(x_17, x_1);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_IR_LocalContext_isParam(x_17, x_1);
x_4 = x_19;
goto block_16;
}
else
{
x_4 = x_18;
goto block_16;
}
block_16:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = l_Lean_IR_Checker_checkVar___closed__0;
x_6 = l_Lean_IR_Checker_checkVar___closed__1;
x_7 = l_Nat_reprFast(x_1);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_string_append(x_5, x_8);
lean_dec(x_8);
x_10 = l_Lean_IR_Checker_checkVar___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_LocalContext_isJP(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lean_IR_Checker_checkJP___closed__0;
x_7 = l_Lean_IR_Checker_checkJP___closed__1;
x_8 = l_Nat_reprFast(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_6, x_9);
lean_dec(x_9);
x_11 = l_Lean_IR_Checker_checkVar___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkJP___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkJP(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_Checker_checkVar(x_4, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
x_9 = l_Lean_IR_Checker_checkArg(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_10);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_12;
x_6 = x_11;
goto _start;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_box(0);
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_5, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(x_1, x_13, x_14, x_6, x_2, x_3);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkArgs_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkArgs(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkEqTypes___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected type '{ty₁}' != '{ty₂}'", 38, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkEqTypes___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_checkEqTypes___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_IR_Checker_checkEqTypes___redArg___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_1, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_Checker_checkEqTypes___redArg___closed__1;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkEqTypes___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkEqTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkEqTypes(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkType___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected type '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkType___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_10; uint8_t x_11; 
lean_inc(x_1);
x_10 = lean_apply_1(x_2, x_1);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_13 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_14 = lean_unsigned_to_nat(120u);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_format_pretty(x_13, x_14, x_15, x_15);
x_17 = lean_string_append(x_12, x_16);
lean_dec(x_16);
x_18 = l_Lean_IR_Checker_checkVar___closed__2;
x_19 = lean_string_append(x_17, x_18);
if (lean_obj_tag(x_3) == 0)
{
x_5 = x_19;
x_6 = x_4;
goto block_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = l_Lean_IR_Checker_checkType___redArg___closed__1;
x_22 = lean_string_append(x_19, x_21);
x_23 = lean_string_append(x_22, x_20);
x_5 = x_23;
x_6 = x_4;
goto block_9;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_11 = lean_apply_1(x_2, x_1);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_14 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_15 = lean_unsigned_to_nat(120u);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_format_pretty(x_14, x_15, x_16, x_16);
x_18 = lean_string_append(x_13, x_17);
lean_dec(x_17);
x_19 = l_Lean_IR_Checker_checkVar___closed__2;
x_20 = lean_string_append(x_18, x_19);
if (lean_obj_tag(x_3) == 0)
{
x_6 = x_20;
x_7 = x_5;
goto block_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = l_Lean_IR_Checker_checkType___redArg___closed__1;
x_23 = lean_string_append(x_20, x_22);
x_24 = lean_string_append(x_23, x_21);
x_6 = x_24;
x_7 = x_5;
goto block_10;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkType___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_Checker_checkType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkObjType___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("object expected", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_IRType_isObj(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = l_Lean_IR_Checker_checkObjType___redArg___closed__0;
x_5 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_6 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_7 = lean_unsigned_to_nat(120u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_5, x_9);
lean_dec(x_9);
x_11 = l_Lean_IR_Checker_checkVar___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Lean_IR_Checker_checkType___redArg___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_4);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_2);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkObjType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkScalarType___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scalar expected", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_IRType_isScalar(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = l_Lean_IR_Checker_checkScalarType___redArg___closed__0;
x_5 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_6 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_7 = lean_unsigned_to_nat(120u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_5, x_9);
lean_dec(x_9);
x_11 = l_Lean_IR_Checker_checkVar___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Lean_IR_Checker_checkType___redArg___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_4);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_2);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkScalarType___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkScalarType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_IR_LocalContext_getType(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lean_IR_Checker_checkVar___closed__0;
x_7 = l_Lean_IR_Checker_checkVar___closed__1;
x_8 = l_Nat_reprFast(x_1);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_6, x_9);
lean_dec(x_9);
x_11 = l_Lean_IR_Checker_checkVar___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_getType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_getType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_IR_Checker_getType(x_1, x_4, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_20 = x_12;
} else {
 lean_dec_ref(x_12);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec(x_12);
lean_inc(x_26);
x_27 = lean_apply_1(x_2, x_26);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_11);
x_29 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_30 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_26);
x_31 = lean_unsigned_to_nat(120u);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_format_pretty(x_30, x_31, x_32, x_32);
x_34 = lean_string_append(x_29, x_33);
lean_dec(x_33);
x_35 = l_Lean_IR_Checker_checkVar___closed__2;
x_36 = lean_string_append(x_34, x_35);
if (lean_obj_tag(x_3) == 0)
{
x_6 = x_36;
x_7 = x_24;
goto block_10;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_3, 0);
x_38 = l_Lean_IR_Checker_checkType___redArg___closed__1;
x_39 = lean_string_append(x_36, x_38);
x_40 = lean_string_append(x_39, x_37);
x_6 = x_40;
x_7 = x_24;
goto block_10;
}
}
else
{
lean_object* x_41; 
lean_dec(x_26);
x_41 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_11, 0, x_41);
return x_11;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_dec(x_11);
x_43 = lean_ctor_get(x_12, 0);
lean_inc(x_43);
lean_dec(x_12);
lean_inc(x_43);
x_44 = lean_apply_1(x_2, x_43);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_47 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_43);
x_48 = lean_unsigned_to_nat(120u);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_format_pretty(x_47, x_48, x_49, x_49);
x_51 = lean_string_append(x_46, x_50);
lean_dec(x_50);
x_52 = l_Lean_IR_Checker_checkVar___closed__2;
x_53 = lean_string_append(x_51, x_52);
if (lean_obj_tag(x_3) == 0)
{
x_6 = x_53;
x_7 = x_42;
goto block_10;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_3, 0);
x_55 = l_Lean_IR_Checker_checkType___redArg___closed__1;
x_56 = lean_string_append(x_53, x_55);
x_57 = lean_string_append(x_56, x_54);
x_6 = x_57;
x_7 = x_42;
goto block_10;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_43);
x_58 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_42);
return x_59;
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkVarType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_Checker_checkVarType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_Checker_getType(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_13 = x_5;
} else {
 lean_dec_ref(x_5);
 x_13 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_14 = lean_alloc_ctor(0, 1, 0);
} else {
 x_14 = x_13;
}
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = l_Lean_IR_IRType_isObj(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = l_Lean_IR_Checker_checkObjType___redArg___closed__0;
x_22 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_23 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_19);
x_24 = lean_unsigned_to_nat(120u);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_format_pretty(x_23, x_24, x_25, x_25);
x_27 = lean_string_append(x_22, x_26);
lean_dec(x_26);
x_28 = l_Lean_IR_Checker_checkVar___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_IR_Checker_checkType___redArg___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_string_append(x_31, x_21);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_32);
return x_4;
}
else
{
lean_object* x_33; 
lean_free_object(x_5);
lean_dec(x_19);
x_33 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_4, 0, x_33);
return x_4;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
lean_dec(x_5);
x_35 = l_Lean_IR_IRType_isObj(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_36 = l_Lean_IR_Checker_checkObjType___redArg___closed__0;
x_37 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_38 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_34);
x_39 = lean_unsigned_to_nat(120u);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_format_pretty(x_38, x_39, x_40, x_40);
x_42 = lean_string_append(x_37, x_41);
lean_dec(x_41);
x_43 = l_Lean_IR_Checker_checkVar___closed__2;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_Lean_IR_Checker_checkType___redArg___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_string_append(x_46, x_36);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_4, 0, x_48);
return x_4;
}
else
{
lean_object* x_49; 
lean_dec(x_34);
x_49 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_4, 0, x_49);
return x_4;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_4, 1);
lean_inc(x_50);
lean_dec(x_4);
x_51 = lean_ctor_get(x_5, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_52 = x_5;
} else {
 lean_dec_ref(x_5);
 x_52 = lean_box(0);
}
x_53 = l_Lean_IR_IRType_isObj(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = l_Lean_IR_Checker_checkObjType___redArg___closed__0;
x_55 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_56 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_51);
x_57 = lean_unsigned_to_nat(120u);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_format_pretty(x_56, x_57, x_58, x_58);
x_60 = lean_string_append(x_55, x_59);
lean_dec(x_59);
x_61 = l_Lean_IR_Checker_checkVar___closed__2;
x_62 = lean_string_append(x_60, x_61);
x_63 = l_Lean_IR_Checker_checkType___redArg___closed__1;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_54);
if (lean_is_scalar(x_52)) {
 x_66 = lean_alloc_ctor(0, 1, 0);
} else {
 x_66 = x_52;
 lean_ctor_set_tag(x_66, 0);
}
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_50);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_52);
lean_dec(x_51);
x_68 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_50);
return x_69;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkObjVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkObjVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_Checker_getType(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_13 = x_5;
} else {
 lean_dec_ref(x_5);
 x_13 = lean_box(0);
}
if (lean_is_scalar(x_13)) {
 x_14 = lean_alloc_ctor(0, 1, 0);
} else {
 x_14 = x_13;
}
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_4, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = l_Lean_IR_IRType_isScalar(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = l_Lean_IR_Checker_checkScalarType___redArg___closed__0;
x_22 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_23 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_19);
x_24 = lean_unsigned_to_nat(120u);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_format_pretty(x_23, x_24, x_25, x_25);
x_27 = lean_string_append(x_22, x_26);
lean_dec(x_26);
x_28 = l_Lean_IR_Checker_checkVar___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_IR_Checker_checkType___redArg___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_string_append(x_31, x_21);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_32);
return x_4;
}
else
{
lean_object* x_33; 
lean_free_object(x_5);
lean_dec(x_19);
x_33 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_4, 0, x_33);
return x_4;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
lean_dec(x_5);
x_35 = l_Lean_IR_IRType_isScalar(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_36 = l_Lean_IR_Checker_checkScalarType___redArg___closed__0;
x_37 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_38 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_34);
x_39 = lean_unsigned_to_nat(120u);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_format_pretty(x_38, x_39, x_40, x_40);
x_42 = lean_string_append(x_37, x_41);
lean_dec(x_41);
x_43 = l_Lean_IR_Checker_checkVar___closed__2;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_Lean_IR_Checker_checkType___redArg___closed__1;
x_46 = lean_string_append(x_44, x_45);
x_47 = lean_string_append(x_46, x_36);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_4, 0, x_48);
return x_4;
}
else
{
lean_object* x_49; 
lean_dec(x_34);
x_49 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_4, 0, x_49);
return x_4;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_4, 1);
lean_inc(x_50);
lean_dec(x_4);
x_51 = lean_ctor_get(x_5, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_52 = x_5;
} else {
 lean_dec_ref(x_5);
 x_52 = lean_box(0);
}
x_53 = l_Lean_IR_IRType_isScalar(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = l_Lean_IR_Checker_checkScalarType___redArg___closed__0;
x_55 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_56 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_51);
x_57 = lean_unsigned_to_nat(120u);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_format_pretty(x_56, x_57, x_58, x_58);
x_60 = lean_string_append(x_55, x_59);
lean_dec(x_59);
x_61 = l_Lean_IR_Checker_checkVar___closed__2;
x_62 = lean_string_append(x_60, x_61);
x_63 = l_Lean_IR_Checker_checkType___redArg___closed__1;
x_64 = lean_string_append(x_62, x_63);
x_65 = lean_string_append(x_64, x_54);
if (lean_is_scalar(x_52)) {
 x_66 = lean_alloc_ctor(0, 1, 0);
} else {
 x_66 = x_52;
 lean_ctor_set_tag(x_66, 0);
}
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_50);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_52);
lean_dec(x_51);
x_68 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_50);
return x_69;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkScalarVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Checker_checkScalarVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_IR_Checker_getDecl(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_14 = x_6;
} else {
 lean_dec_ref(x_6);
 x_14 = lean_box(0);
}
if (lean_is_scalar(x_14)) {
 x_15 = lean_alloc_ctor(0, 1, 0);
} else {
 x_15 = x_14;
}
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_45; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_18 = x_5;
} else {
 lean_dec_ref(x_5);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_20 = x_6;
} else {
 lean_dec_ref(x_6);
 x_20 = lean_box(0);
}
x_21 = lean_array_get_size(x_2);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_dec(x_19);
x_22 = x_45;
goto block_44;
block_44:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_array_get_size(x_22);
lean_dec(x_22);
x_24 = lean_nat_dec_eq(x_21, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_3);
x_25 = lean_box(x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_IR_Checker_checkFullApp___lam__0___boxed), 2, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = l_Lean_IR_Checker_checkFullApp___closed__0;
x_28 = 1;
x_29 = l_Lean_Name_toString(x_1, x_28, x_26);
x_30 = lean_string_append(x_27, x_29);
lean_dec(x_29);
x_31 = l_Lean_IR_Checker_checkFullApp___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_Nat_reprFast(x_21);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = l_Lean_IR_Checker_checkFullApp___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = l_Nat_reprFast(x_23);
x_38 = lean_string_append(x_36, x_37);
lean_dec(x_37);
x_39 = l_Lean_IR_Checker_checkFullApp___closed__3;
x_40 = lean_string_append(x_38, x_39);
if (lean_is_scalar(x_20)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_20;
 lean_ctor_set_tag(x_41, 0);
}
lean_ctor_set(x_41, 0, x_40);
if (lean_is_scalar(x_18)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_18;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_17);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_1);
x_43 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_17);
lean_dec(x_3);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_IR_Checker_checkFullApp___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFullApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkFullApp(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Checker_getDecl___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("too many arguments to partial application '", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', num. args: ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkPartialApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", arity: ", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_IR_Checker_getDecl(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_14 = x_6;
} else {
 lean_dec_ref(x_6);
 x_14 = lean_box(0);
}
if (lean_is_scalar(x_14)) {
 x_15 = lean_alloc_ctor(0, 1, 0);
} else {
 x_15 = x_14;
}
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_42; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_18 = x_5;
} else {
 lean_dec_ref(x_5);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_20 = x_6;
} else {
 lean_dec_ref(x_6);
 x_20 = lean_box(0);
}
x_21 = l_Lean_IR_Checker_checkPartialApp___closed__0;
x_22 = lean_array_get_size(x_2);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_dec(x_19);
x_23 = x_42;
goto block_41;
block_41:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_array_get_size(x_23);
lean_dec(x_23);
x_25 = lean_nat_dec_lt(x_22, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_3);
x_26 = l_Lean_IR_Checker_checkPartialApp___closed__1;
x_27 = 1;
x_28 = l_Lean_Name_toString(x_1, x_27, x_21);
x_29 = lean_string_append(x_26, x_28);
lean_dec(x_28);
x_30 = l_Lean_IR_Checker_checkPartialApp___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_Nat_reprFast(x_22);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_IR_Checker_checkPartialApp___closed__3;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Nat_reprFast(x_24);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
if (lean_is_scalar(x_20)) {
 x_38 = lean_alloc_ctor(0, 1, 0);
} else {
 x_38 = x_20;
 lean_ctor_set_tag(x_38, 0);
}
lean_ctor_set(x_38, 0, x_37);
if (lean_is_scalar(x_18)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_18;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_17);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_1);
x_40 = l_Lean_IR_Checker_checkArgs(x_2, x_3, x_17);
lean_dec(x_3);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkPartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_checkPartialApp(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Checker_checkExpr___lam__1(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_checkExpr___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_checkExpr___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected IR type '", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_55; uint8_t x_56; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 4);
lean_inc(x_12);
x_13 = l_Lean_IR_Checker_checkPartialApp___closed__0;
x_55 = l_Lean_IR_Checker_maxCtorTag;
x_56 = lean_nat_dec_lt(x_55, x_9);
lean_dec(x_9);
if (x_56 == 0)
{
x_14 = x_56;
goto block_54;
}
else
{
uint8_t x_57; 
x_57 = l_Lean_IR_CtorInfo_isRef(x_5);
x_14 = x_57;
goto block_54;
}
block_54:
{
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_IR_Checker_maxCtorFields;
x_16 = lean_nat_dec_lt(x_15, x_10);
lean_dec(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = l_Lean_IR_Checker_maxCtorScalarsSize;
x_18 = l_Lean_IR_Checker_usizeSize;
x_19 = lean_nat_mul(x_11, x_18);
lean_dec(x_11);
x_20 = lean_nat_add(x_12, x_19);
lean_dec(x_19);
lean_dec(x_12);
x_21 = lean_nat_dec_lt(x_17, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_8);
x_22 = l_Lean_IR_CtorInfo_isRef(x_5);
lean_dec(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_23 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
if (lean_is_scalar(x_7)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_7;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
x_25 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_3);
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_IR_Checker_checkArgs(x_6, x_3, x_27);
lean_dec(x_3);
lean_dec(x_6);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_29 = lean_box(x_14);
x_30 = lean_alloc_closure((void*)(l_Lean_IR_Checker_checkExpr___lam__1___boxed), 2, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = l_Lean_IR_Checker_checkExpr___closed__0;
x_32 = l_Lean_Name_toString(x_8, x_21, x_30);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lean_IR_Checker_checkExpr___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
if (lean_is_scalar(x_7)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_7;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_4);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_38 = lean_box(x_14);
x_39 = lean_alloc_closure((void*)(l_Lean_IR_Checker_checkExpr___lam__1___boxed), 2, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = l_Lean_IR_Checker_checkExpr___closed__0;
x_41 = l_Lean_Name_toString(x_8, x_16, x_39);
x_42 = lean_string_append(x_40, x_41);
lean_dec(x_41);
x_43 = l_Lean_IR_Checker_checkExpr___closed__2;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
if (lean_is_scalar(x_7)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_7;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_4);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_47 = l_Lean_IR_Checker_checkExpr___closed__3;
x_48 = l_Lean_Name_toString(x_8, x_14, x_13);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_50 = l_Lean_IR_Checker_checkExpr___closed__4;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
if (lean_is_scalar(x_7)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_7;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
return x_53;
}
}
}
case 1:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
lean_dec(x_2);
x_59 = l_Lean_IR_Checker_checkObjVar(x_58, x_3, x_4);
lean_dec(x_3);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_dec(x_60);
lean_dec(x_1);
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_61);
return x_62;
}
}
case 2:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_2, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_2, 2);
lean_inc(x_64);
lean_dec(x_2);
x_65 = l_Lean_IR_Checker_checkObjVar(x_63, x_3, x_4);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_3);
lean_dec(x_1);
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_IR_Checker_checkArgs(x_64, x_3, x_67);
lean_dec(x_3);
lean_dec(x_64);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_dec(x_69);
lean_dec(x_1);
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_70);
return x_71;
}
}
}
case 3:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_2, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_2, 1);
lean_inc(x_73);
lean_dec(x_2);
x_74 = l_Lean_IR_Checker_getType(x_73, x_3, x_4);
lean_dec(x_3);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
lean_dec(x_72);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_74, 0);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_75);
if (x_78 == 0)
{
return x_74;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_74, 0, x_80);
return x_74;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
lean_dec(x_74);
x_82 = lean_ctor_get(x_75, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_83 = x_75;
} else {
 lean_dec_ref(x_75);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 1, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_75);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_75, 0);
switch (lean_obj_tag(x_87)) {
case 7:
{
lean_object* x_88; lean_object* x_89; 
lean_free_object(x_75);
lean_dec(x_72);
x_88 = lean_ctor_get(x_74, 1);
lean_inc(x_88);
lean_dec(x_74);
x_89 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_88);
return x_89;
}
case 8:
{
lean_object* x_90; lean_object* x_91; 
lean_free_object(x_75);
lean_dec(x_72);
x_90 = lean_ctor_get(x_74, 1);
lean_inc(x_90);
lean_dec(x_74);
x_91 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_90);
return x_91;
}
case 10:
{
uint8_t x_92; 
lean_free_object(x_75);
x_92 = !lean_is_exclusive(x_74);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_74, 0);
lean_dec(x_93);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec(x_87);
x_95 = lean_array_get_size(x_94);
x_96 = lean_nat_dec_lt(x_72, x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_94);
lean_dec(x_72);
lean_dec(x_1);
x_97 = l_Lean_IR_Checker_checkExpr___closed__6;
lean_ctor_set(x_74, 0, x_97);
return x_74;
}
else
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_array_fget(x_94, x_72);
lean_dec(x_72);
lean_dec(x_94);
x_99 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_98, x_1);
lean_dec(x_1);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = l_Lean_IR_Checker_checkEqTypes___redArg___closed__1;
lean_ctor_set(x_74, 0, x_100);
return x_74;
}
else
{
lean_object* x_101; 
x_101 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_74, 0, x_101);
return x_74;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_102 = lean_ctor_get(x_74, 1);
lean_inc(x_102);
lean_dec(x_74);
x_103 = lean_ctor_get(x_87, 1);
lean_inc(x_103);
lean_dec(x_87);
x_104 = lean_array_get_size(x_103);
x_105 = lean_nat_dec_lt(x_72, x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_103);
lean_dec(x_72);
lean_dec(x_1);
x_106 = l_Lean_IR_Checker_checkExpr___closed__6;
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_102);
return x_107;
}
else
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_array_fget(x_103, x_72);
lean_dec(x_72);
lean_dec(x_103);
x_109 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_108, x_1);
lean_dec(x_1);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = l_Lean_IR_Checker_checkEqTypes___redArg___closed__1;
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_102);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_102);
return x_113;
}
}
}
}
case 11:
{
uint8_t x_114; 
lean_free_object(x_75);
x_114 = !lean_is_exclusive(x_74);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_115 = lean_ctor_get(x_74, 0);
lean_dec(x_115);
x_116 = lean_ctor_get(x_87, 1);
lean_inc(x_116);
lean_dec(x_87);
x_117 = lean_array_get_size(x_116);
x_118 = lean_nat_dec_lt(x_72, x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
lean_dec(x_116);
lean_dec(x_72);
lean_dec(x_1);
x_119 = l_Lean_IR_Checker_checkExpr___closed__6;
lean_ctor_set(x_74, 0, x_119);
return x_74;
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_array_fget(x_116, x_72);
lean_dec(x_72);
lean_dec(x_116);
x_121 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_120, x_1);
lean_dec(x_1);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = l_Lean_IR_Checker_checkEqTypes___redArg___closed__1;
lean_ctor_set(x_74, 0, x_122);
return x_74;
}
else
{
lean_object* x_123; 
x_123 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_74, 0, x_123);
return x_74;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_74, 1);
lean_inc(x_124);
lean_dec(x_74);
x_125 = lean_ctor_get(x_87, 1);
lean_inc(x_125);
lean_dec(x_87);
x_126 = lean_array_get_size(x_125);
x_127 = lean_nat_dec_lt(x_72, x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_125);
lean_dec(x_72);
lean_dec(x_1);
x_128 = l_Lean_IR_Checker_checkExpr___closed__6;
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_124);
return x_129;
}
else
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_array_fget(x_125, x_72);
lean_dec(x_72);
lean_dec(x_125);
x_131 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_130, x_1);
lean_dec(x_1);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = l_Lean_IR_Checker_checkEqTypes___redArg___closed__1;
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_124);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_124);
return x_135;
}
}
}
}
default: 
{
uint8_t x_136; 
lean_dec(x_72);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_74);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_137 = lean_ctor_get(x_74, 0);
lean_dec(x_137);
x_138 = l_Lean_IR_Checker_checkExpr___closed__7;
x_139 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_87);
x_140 = lean_unsigned_to_nat(120u);
x_141 = lean_unsigned_to_nat(0u);
x_142 = lean_format_pretty(x_139, x_140, x_141, x_141);
x_143 = lean_string_append(x_138, x_142);
lean_dec(x_142);
x_144 = l_Lean_IR_Checker_checkVar___closed__2;
x_145 = lean_string_append(x_143, x_144);
lean_ctor_set_tag(x_75, 0);
lean_ctor_set(x_75, 0, x_145);
return x_74;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_146 = lean_ctor_get(x_74, 1);
lean_inc(x_146);
lean_dec(x_74);
x_147 = l_Lean_IR_Checker_checkExpr___closed__7;
x_148 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_87);
x_149 = lean_unsigned_to_nat(120u);
x_150 = lean_unsigned_to_nat(0u);
x_151 = lean_format_pretty(x_148, x_149, x_150, x_150);
x_152 = lean_string_append(x_147, x_151);
lean_dec(x_151);
x_153 = l_Lean_IR_Checker_checkVar___closed__2;
x_154 = lean_string_append(x_152, x_153);
lean_ctor_set_tag(x_75, 0);
lean_ctor_set(x_75, 0, x_154);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_75);
lean_ctor_set(x_155, 1, x_146);
return x_155;
}
}
}
}
else
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_75, 0);
lean_inc(x_156);
lean_dec(x_75);
switch (lean_obj_tag(x_156)) {
case 7:
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_72);
x_157 = lean_ctor_get(x_74, 1);
lean_inc(x_157);
lean_dec(x_74);
x_158 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_157);
return x_158;
}
case 8:
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_72);
x_159 = lean_ctor_get(x_74, 1);
lean_inc(x_159);
lean_dec(x_74);
x_160 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_159);
return x_160;
}
case 10:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_161 = lean_ctor_get(x_74, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_162 = x_74;
} else {
 lean_dec_ref(x_74);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_156, 1);
lean_inc(x_163);
lean_dec(x_156);
x_164 = lean_array_get_size(x_163);
x_165 = lean_nat_dec_lt(x_72, x_164);
lean_dec(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_163);
lean_dec(x_72);
lean_dec(x_1);
x_166 = l_Lean_IR_Checker_checkExpr___closed__6;
if (lean_is_scalar(x_162)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_162;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_161);
return x_167;
}
else
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_array_fget(x_163, x_72);
lean_dec(x_72);
lean_dec(x_163);
x_169 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_168, x_1);
lean_dec(x_1);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = l_Lean_IR_Checker_checkEqTypes___redArg___closed__1;
if (lean_is_scalar(x_162)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_162;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_161);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
if (lean_is_scalar(x_162)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_162;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_161);
return x_173;
}
}
}
case 11:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_174 = lean_ctor_get(x_74, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_175 = x_74;
} else {
 lean_dec_ref(x_74);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_156, 1);
lean_inc(x_176);
lean_dec(x_156);
x_177 = lean_array_get_size(x_176);
x_178 = lean_nat_dec_lt(x_72, x_177);
lean_dec(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_176);
lean_dec(x_72);
lean_dec(x_1);
x_179 = l_Lean_IR_Checker_checkExpr___closed__6;
if (lean_is_scalar(x_175)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_175;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_174);
return x_180;
}
else
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_array_fget(x_176, x_72);
lean_dec(x_72);
lean_dec(x_176);
x_182 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_181, x_1);
lean_dec(x_1);
lean_dec(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = l_Lean_IR_Checker_checkEqTypes___redArg___closed__1;
if (lean_is_scalar(x_175)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_175;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_174);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
if (lean_is_scalar(x_175)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_175;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_174);
return x_186;
}
}
}
default: 
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_72);
lean_dec(x_1);
x_187 = lean_ctor_get(x_74, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_188 = x_74;
} else {
 lean_dec_ref(x_74);
 x_188 = lean_box(0);
}
x_189 = l_Lean_IR_Checker_checkExpr___closed__7;
x_190 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_156);
x_191 = lean_unsigned_to_nat(120u);
x_192 = lean_unsigned_to_nat(0u);
x_193 = lean_format_pretty(x_190, x_191, x_192, x_192);
x_194 = lean_string_append(x_189, x_193);
lean_dec(x_193);
x_195 = l_Lean_IR_Checker_checkVar___closed__2;
x_196 = lean_string_append(x_194, x_195);
x_197 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_197, 0, x_196);
if (lean_is_scalar(x_188)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_188;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_187);
return x_198;
}
}
}
}
}
case 4:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_2, 1);
lean_inc(x_199);
lean_dec(x_2);
x_200 = l_Lean_IR_Checker_checkObjVar(x_199, x_3, x_4);
lean_dec(x_3);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
if (lean_obj_tag(x_201) == 0)
{
lean_dec(x_201);
lean_dec(x_1);
return x_200;
}
else
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_200);
if (x_202 == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_200, 0);
lean_dec(x_203);
x_204 = !lean_is_exclusive(x_201);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_205 = lean_ctor_get(x_201, 0);
lean_dec(x_205);
x_206 = lean_box(5);
x_207 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_1, x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_208 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_209 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_210 = lean_unsigned_to_nat(120u);
x_211 = lean_unsigned_to_nat(0u);
x_212 = lean_format_pretty(x_209, x_210, x_211, x_211);
x_213 = lean_string_append(x_208, x_212);
lean_dec(x_212);
x_214 = l_Lean_IR_Checker_checkVar___closed__2;
x_215 = lean_string_append(x_213, x_214);
lean_ctor_set_tag(x_201, 0);
lean_ctor_set(x_201, 0, x_215);
return x_200;
}
else
{
lean_object* x_216; 
lean_free_object(x_201);
lean_dec(x_1);
x_216 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_200, 0, x_216);
return x_200;
}
}
else
{
lean_object* x_217; uint8_t x_218; 
lean_dec(x_201);
x_217 = lean_box(5);
x_218 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_1, x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_219 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_220 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_221 = lean_unsigned_to_nat(120u);
x_222 = lean_unsigned_to_nat(0u);
x_223 = lean_format_pretty(x_220, x_221, x_222, x_222);
x_224 = lean_string_append(x_219, x_223);
lean_dec(x_223);
x_225 = l_Lean_IR_Checker_checkVar___closed__2;
x_226 = lean_string_append(x_224, x_225);
x_227 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_200, 0, x_227);
return x_200;
}
else
{
lean_object* x_228; 
lean_dec(x_1);
x_228 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_200, 0, x_228);
return x_200;
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_229 = lean_ctor_get(x_200, 1);
lean_inc(x_229);
lean_dec(x_200);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_230 = x_201;
} else {
 lean_dec_ref(x_201);
 x_230 = lean_box(0);
}
x_231 = lean_box(5);
x_232 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_1, x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_233 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_234 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_235 = lean_unsigned_to_nat(120u);
x_236 = lean_unsigned_to_nat(0u);
x_237 = lean_format_pretty(x_234, x_235, x_236, x_236);
x_238 = lean_string_append(x_233, x_237);
lean_dec(x_237);
x_239 = l_Lean_IR_Checker_checkVar___closed__2;
x_240 = lean_string_append(x_238, x_239);
if (lean_is_scalar(x_230)) {
 x_241 = lean_alloc_ctor(0, 1, 0);
} else {
 x_241 = x_230;
 lean_ctor_set_tag(x_241, 0);
}
lean_ctor_set(x_241, 0, x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_229);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_230);
lean_dec(x_1);
x_243 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_229);
return x_244;
}
}
}
}
case 5:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_2, 2);
lean_inc(x_245);
lean_dec(x_2);
x_246 = l_Lean_IR_Checker_checkObjVar(x_245, x_3, x_4);
lean_dec(x_3);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
if (lean_obj_tag(x_247) == 0)
{
lean_dec(x_247);
lean_dec(x_1);
return x_246;
}
else
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = l_Lean_IR_Checker_checkScalarType___redArg(x_1, x_248);
return x_249;
}
}
case 6:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_1);
x_250 = lean_ctor_get(x_2, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_2, 1);
lean_inc(x_251);
lean_dec(x_2);
x_252 = l_Lean_IR_Checker_checkFullApp(x_250, x_251, x_3, x_4);
lean_dec(x_251);
return x_252;
}
case 7:
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_253 = lean_ctor_get(x_2, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_2, 1);
lean_inc(x_254);
lean_dec(x_2);
x_255 = l_Lean_IR_Checker_checkPartialApp(x_253, x_254, x_3, x_4);
lean_dec(x_254);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
if (lean_obj_tag(x_256) == 0)
{
lean_dec(x_256);
lean_dec(x_1);
return x_255;
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_257);
return x_258;
}
}
case 8:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_259 = lean_ctor_get(x_2, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_2, 1);
lean_inc(x_260);
lean_dec(x_2);
x_261 = l_Lean_IR_Checker_checkObjVar(x_259, x_3, x_4);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
if (lean_obj_tag(x_262) == 0)
{
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_3);
lean_dec(x_1);
return x_261;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = l_Lean_IR_Checker_checkArgs(x_260, x_3, x_263);
lean_dec(x_3);
lean_dec(x_260);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
if (lean_obj_tag(x_265) == 0)
{
lean_dec(x_265);
lean_dec(x_1);
return x_264;
}
else
{
lean_object* x_266; lean_object* x_267; 
lean_dec(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_266);
return x_267;
}
}
}
case 9:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_268 = lean_ctor_get(x_2, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_2, 1);
lean_inc(x_269);
lean_dec(x_2);
x_270 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_4);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
lean_dec(x_271);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_3);
return x_270;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
lean_inc(x_269);
x_273 = l_Lean_IR_Checker_checkScalarVar(x_269, x_3, x_272);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
if (lean_obj_tag(x_274) == 0)
{
lean_dec(x_274);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_3);
return x_273;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = l_Lean_IR_Checker_getType(x_269, x_3, x_275);
lean_dec(x_3);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
if (lean_obj_tag(x_277) == 0)
{
uint8_t x_278; 
lean_dec(x_268);
x_278 = !lean_is_exclusive(x_276);
if (x_278 == 0)
{
lean_object* x_279; uint8_t x_280; 
x_279 = lean_ctor_get(x_276, 0);
lean_dec(x_279);
x_280 = !lean_is_exclusive(x_277);
if (x_280 == 0)
{
return x_276;
}
else
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_277, 0);
lean_inc(x_281);
lean_dec(x_277);
x_282 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_276, 0, x_282);
return x_276;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_283 = lean_ctor_get(x_276, 1);
lean_inc(x_283);
lean_dec(x_276);
x_284 = lean_ctor_get(x_277, 0);
lean_inc(x_284);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 x_285 = x_277;
} else {
 lean_dec_ref(x_277);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(0, 1, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_284);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_283);
return x_287;
}
}
else
{
uint8_t x_288; 
x_288 = !lean_is_exclusive(x_276);
if (x_288 == 0)
{
lean_object* x_289; uint8_t x_290; 
x_289 = lean_ctor_get(x_276, 0);
lean_dec(x_289);
x_290 = !lean_is_exclusive(x_277);
if (x_290 == 0)
{
lean_object* x_291; uint8_t x_292; 
x_291 = lean_ctor_get(x_277, 0);
x_292 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_291, x_268);
lean_dec(x_268);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_293 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_294 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_291);
x_295 = lean_unsigned_to_nat(120u);
x_296 = lean_unsigned_to_nat(0u);
x_297 = lean_format_pretty(x_294, x_295, x_296, x_296);
x_298 = lean_string_append(x_293, x_297);
lean_dec(x_297);
x_299 = l_Lean_IR_Checker_checkVar___closed__2;
x_300 = lean_string_append(x_298, x_299);
lean_ctor_set_tag(x_277, 0);
lean_ctor_set(x_277, 0, x_300);
return x_276;
}
else
{
lean_object* x_301; 
lean_free_object(x_277);
lean_dec(x_291);
x_301 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_276, 0, x_301);
return x_276;
}
}
else
{
lean_object* x_302; uint8_t x_303; 
x_302 = lean_ctor_get(x_277, 0);
lean_inc(x_302);
lean_dec(x_277);
x_303 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_302, x_268);
lean_dec(x_268);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_304 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_305 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_302);
x_306 = lean_unsigned_to_nat(120u);
x_307 = lean_unsigned_to_nat(0u);
x_308 = lean_format_pretty(x_305, x_306, x_307, x_307);
x_309 = lean_string_append(x_304, x_308);
lean_dec(x_308);
x_310 = l_Lean_IR_Checker_checkVar___closed__2;
x_311 = lean_string_append(x_309, x_310);
x_312 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_276, 0, x_312);
return x_276;
}
else
{
lean_object* x_313; 
lean_dec(x_302);
x_313 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_276, 0, x_313);
return x_276;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_314 = lean_ctor_get(x_276, 1);
lean_inc(x_314);
lean_dec(x_276);
x_315 = lean_ctor_get(x_277, 0);
lean_inc(x_315);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 x_316 = x_277;
} else {
 lean_dec_ref(x_277);
 x_316 = lean_box(0);
}
x_317 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_315, x_268);
lean_dec(x_268);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_318 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_319 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_315);
x_320 = lean_unsigned_to_nat(120u);
x_321 = lean_unsigned_to_nat(0u);
x_322 = lean_format_pretty(x_319, x_320, x_321, x_321);
x_323 = lean_string_append(x_318, x_322);
lean_dec(x_322);
x_324 = l_Lean_IR_Checker_checkVar___closed__2;
x_325 = lean_string_append(x_323, x_324);
if (lean_is_scalar(x_316)) {
 x_326 = lean_alloc_ctor(0, 1, 0);
} else {
 x_326 = x_316;
 lean_ctor_set_tag(x_326, 0);
}
lean_ctor_set(x_326, 0, x_325);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_314);
return x_327;
}
else
{
lean_object* x_328; lean_object* x_329; 
lean_dec(x_316);
lean_dec(x_315);
x_328 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_314);
return x_329;
}
}
}
}
}
}
case 10:
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_2, 0);
lean_inc(x_330);
lean_dec(x_2);
x_331 = l_Lean_IR_Checker_checkScalarType___redArg(x_1, x_4);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
if (lean_obj_tag(x_332) == 0)
{
lean_dec(x_332);
lean_dec(x_330);
lean_dec(x_3);
return x_331;
}
else
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = l_Lean_IR_Checker_checkObjVar(x_330, x_3, x_333);
lean_dec(x_3);
return x_334;
}
}
case 11:
{
lean_object* x_335; 
lean_dec(x_3);
x_335 = lean_ctor_get(x_2, 0);
lean_inc(x_335);
lean_dec(x_2);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_335);
lean_dec(x_1);
x_336 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_4);
return x_337;
}
else
{
lean_object* x_338; 
lean_dec(x_335);
x_338 = l_Lean_IR_Checker_checkObjType___redArg(x_1, x_4);
return x_338;
}
}
default: 
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_2, 0);
lean_inc(x_339);
lean_dec(x_2);
x_340 = l_Lean_IR_Checker_checkObjVar(x_339, x_3, x_4);
lean_dec(x_3);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
if (lean_obj_tag(x_341) == 0)
{
lean_dec(x_341);
lean_dec(x_1);
return x_340;
}
else
{
uint8_t x_342; 
x_342 = !lean_is_exclusive(x_340);
if (x_342 == 0)
{
lean_object* x_343; uint8_t x_344; 
x_343 = lean_ctor_get(x_340, 0);
lean_dec(x_343);
x_344 = !lean_is_exclusive(x_341);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_345 = lean_ctor_get(x_341, 0);
lean_dec(x_345);
x_346 = lean_box(1);
x_347 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_1, x_346);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_348 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_349 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_350 = lean_unsigned_to_nat(120u);
x_351 = lean_unsigned_to_nat(0u);
x_352 = lean_format_pretty(x_349, x_350, x_351, x_351);
x_353 = lean_string_append(x_348, x_352);
lean_dec(x_352);
x_354 = l_Lean_IR_Checker_checkVar___closed__2;
x_355 = lean_string_append(x_353, x_354);
lean_ctor_set_tag(x_341, 0);
lean_ctor_set(x_341, 0, x_355);
return x_340;
}
else
{
lean_object* x_356; 
lean_free_object(x_341);
lean_dec(x_1);
x_356 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_340, 0, x_356);
return x_340;
}
}
else
{
lean_object* x_357; uint8_t x_358; 
lean_dec(x_341);
x_357 = lean_box(1);
x_358 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_1, x_357);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_359 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_360 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_361 = lean_unsigned_to_nat(120u);
x_362 = lean_unsigned_to_nat(0u);
x_363 = lean_format_pretty(x_360, x_361, x_362, x_362);
x_364 = lean_string_append(x_359, x_363);
lean_dec(x_363);
x_365 = l_Lean_IR_Checker_checkVar___closed__2;
x_366 = lean_string_append(x_364, x_365);
x_367 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_340, 0, x_367);
return x_340;
}
else
{
lean_object* x_368; 
lean_dec(x_1);
x_368 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_340, 0, x_368);
return x_340;
}
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; 
x_369 = lean_ctor_get(x_340, 1);
lean_inc(x_369);
lean_dec(x_340);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 x_370 = x_341;
} else {
 lean_dec_ref(x_341);
 x_370 = lean_box(0);
}
x_371 = lean_box(1);
x_372 = l_Lean_IR_beqIRType____x40_Lean_Compiler_IR_Basic___hyg_464_(x_1, x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_373 = l_Lean_IR_Checker_checkType___redArg___closed__0;
x_374 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_1);
x_375 = lean_unsigned_to_nat(120u);
x_376 = lean_unsigned_to_nat(0u);
x_377 = lean_format_pretty(x_374, x_375, x_376, x_376);
x_378 = lean_string_append(x_373, x_377);
lean_dec(x_377);
x_379 = l_Lean_IR_Checker_checkVar___closed__2;
x_380 = lean_string_append(x_378, x_379);
if (lean_is_scalar(x_370)) {
 x_381 = lean_alloc_ctor(0, 1, 0);
} else {
 x_381 = x_370;
 lean_ctor_set_tag(x_381, 0);
}
lean_ctor_set(x_381, 0, x_380);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_369);
return x_382;
}
else
{
lean_object* x_383; lean_object* x_384; 
lean_dec(x_370);
lean_dec(x_1);
x_383 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_369);
return x_384;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkExpr___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_IR_Checker_checkExpr___lam__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = l_Lean_IR_Checker_markIndex___redArg(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_15 = x_7;
} else {
 lean_dec_ref(x_7);
 x_15 = lean_box(0);
}
if (lean_is_scalar(x_15)) {
 x_16 = lean_alloc_ctor(0, 1, 0);
} else {
 x_16 = x_15;
}
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_6, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_7, 0);
lean_dec(x_21);
x_22 = l_Lean_IR_LocalContext_addParam(x_1, x_2);
lean_ctor_set(x_7, 0, x_22);
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
x_23 = l_Lean_IR_LocalContext_addParam(x_1, x_2);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_6, 0, x_24);
return x_6;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_dec(x_6);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_26 = x_7;
} else {
 lean_dec_ref(x_7);
 x_26 = lean_box(0);
}
x_27 = l_Lean_IR_LocalContext_addParam(x_1, x_2);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_Checker_withParams___closed__1;
x_2 = l_Lean_IR_Checker_withParams___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_Checker_withParams___closed__5;
x_2 = l_Lean_IR_Checker_withParams___closed__4;
x_3 = l_Lean_IR_Checker_withParams___closed__3;
x_4 = l_Lean_IR_Checker_withParams___closed__2;
x_5 = l_Lean_IR_Checker_withParams___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_Checker_withParams___closed__6;
x_2 = l_Lean_IR_Checker_withParams___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__9;
x_2 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__9;
x_2 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__9;
x_2 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__9;
x_2 = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__9;
x_2 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_Checker_withParams___closed__10;
x_2 = l_Lean_IR_Checker_withParams___closed__14;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__9;
x_2 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_Checker_withParams___closed__13;
x_2 = l_Lean_IR_Checker_withParams___closed__12;
x_3 = l_Lean_IR_Checker_withParams___closed__11;
x_4 = l_Lean_IR_Checker_withParams___closed__16;
x_5 = l_Lean_IR_Checker_withParams___closed__15;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__9;
x_2 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_Checker_withParams___closed__18;
x_2 = l_Lean_IR_Checker_withParams___closed__17;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__19;
x_2 = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__19;
x_2 = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__19;
x_2 = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__19;
x_2 = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__19;
x_2 = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_Checker_withParams___closed__20;
x_2 = l_Lean_IR_Checker_withParams___closed__24;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__19;
x_2 = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_Checker_withParams___closed__23;
x_2 = l_Lean_IR_Checker_withParams___closed__22;
x_3 = l_Lean_IR_Checker_withParams___closed__21;
x_4 = l_Lean_IR_Checker_withParams___closed__26;
x_5 = l_Lean_IR_Checker_withParams___closed__25;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__19;
x_2 = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_Checker_withParams___closed__28;
x_2 = l_Lean_IR_Checker_withParams___closed__27;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Checker_withParams___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_Checker_withParams___closed__29;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_5 = l_Lean_IR_Checker_withParams___closed__30;
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_1);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_9 = x_7;
x_10 = x_4;
goto block_13;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_15, x_15);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_1);
x_9 = x_7;
x_10 = x_4;
goto block_13;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_alloc_closure((void*)(l_Lean_IR_Checker_withParams___lam__0___boxed), 4, 0);
x_19 = 0;
x_20 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_21 = l_Array_foldlMUnsafe_fold___redArg(x_5, x_18, x_1, x_19, x_20, x_7);
x_22 = lean_apply_2(x_21, x_3, x_4);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_31 = x_23;
} else {
 lean_dec_ref(x_23);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 1, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
x_9 = x_35;
x_10 = x_34;
goto block_13;
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_8);
x_12 = lean_apply_2(x_2, x_11, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_withParams___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Checker_withParams___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = l_Lean_IR_Checker_markIndex___redArg(x_8, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_18 = x_10;
} else {
 lean_dec_ref(x_10);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
lean_dec(x_10);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = l_Lean_IR_LocalContext_addParam(x_4, x_7);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_2 = x_24;
x_4 = x_22;
x_5 = x_21;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_2, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_4);
x_16 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_5);
x_18 = l_Lean_IR_Checker_checkFnBody(x_17, x_5, x_6);
x_7 = x_18;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_5);
x_20 = l_Lean_IR_Checker_checkFnBody(x_19, x_5, x_6);
x_7 = x_20;
goto block_14;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_4);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
block_14:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_8);
lean_dec(x_5);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
x_6 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_2);
lean_inc(x_15);
lean_inc(x_14);
x_17 = l_Lean_IR_Checker_checkExpr(x_14, x_15, x_2, x_3);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_13);
x_20 = l_Lean_IR_Checker_markIndex___redArg(x_13, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
return x_20;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = l_Lean_IR_LocalContext_addLocal(x_24, x_13, x_14, x_15);
lean_ctor_set(x_2, 1, x_25);
x_1 = x_16;
x_3 = x_22;
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
x_30 = l_Lean_IR_LocalContext_addLocal(x_28, x_13, x_14, x_15);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_29);
x_1 = x_16;
x_2 = x_31;
x_3 = x_22;
goto _start;
}
}
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
lean_dec(x_1);
lean_inc(x_33);
x_37 = l_Lean_IR_Checker_markIndex___redArg(x_33, x_3);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_2);
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_43 = x_2;
} else {
 lean_dec_ref(x_2);
 x_43 = lean_box(0);
}
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_get_size(x_34);
x_56 = lean_nat_dec_lt(x_54, x_55);
if (x_56 == 0)
{
lean_dec(x_55);
lean_inc(x_41);
x_44 = x_41;
x_45 = x_39;
goto block_53;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_55, x_55);
if (x_57 == 0)
{
lean_dec(x_55);
lean_inc(x_41);
x_44 = x_41;
x_45 = x_39;
goto block_53;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_55);
lean_dec(x_55);
lean_inc(x_41);
x_60 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg(x_34, x_58, x_59, x_41, x_39);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
return x_60;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_60, 0, x_66);
return x_60;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_ctor_get(x_61, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_60, 1);
lean_inc(x_72);
lean_dec(x_60);
x_73 = lean_ctor_get(x_61, 0);
lean_inc(x_73);
lean_dec(x_61);
x_44 = x_73;
x_45 = x_72;
goto block_53;
}
}
}
block_53:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_inc(x_42);
lean_inc(x_40);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 3, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_42);
lean_inc(x_35);
x_47 = l_Lean_IR_Checker_checkFnBody(x_35, x_46, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_dec(x_48);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_IR_LocalContext_addJP(x_41, x_33, x_34, x_35);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_42);
x_1 = x_36;
x_2 = x_51;
x_3 = x_49;
goto _start;
}
}
}
}
case 2:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_1, 3);
lean_inc(x_76);
lean_dec(x_1);
x_77 = l_Lean_IR_Checker_checkVar(x_74, x_2, x_3);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_2);
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_IR_Checker_checkArg(x_75, x_2, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_dec(x_81);
lean_dec(x_76);
lean_dec(x_2);
return x_80;
}
else
{
lean_object* x_82; 
lean_dec(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_1 = x_76;
x_3 = x_82;
goto _start;
}
}
}
case 3:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_1, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_1, 2);
lean_inc(x_85);
lean_dec(x_1);
x_86 = l_Lean_IR_Checker_checkVar(x_84, x_2, x_3);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_2);
return x_86;
}
else
{
lean_object* x_88; 
lean_dec(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_1 = x_85;
x_3 = x_88;
goto _start;
}
}
case 4:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_1, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_1, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_1, 3);
lean_inc(x_92);
lean_dec(x_1);
x_93 = l_Lean_IR_Checker_checkVar(x_90, x_2, x_3);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
return x_93;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_IR_Checker_checkVar(x_91, x_2, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
lean_dec(x_97);
lean_dec(x_92);
lean_dec(x_2);
return x_96;
}
else
{
lean_object* x_98; 
lean_dec(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_1 = x_92;
x_3 = x_98;
goto _start;
}
}
}
case 5:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_1, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_1, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_1, 5);
lean_inc(x_102);
lean_dec(x_1);
x_103 = l_Lean_IR_Checker_checkVar(x_100, x_2, x_3);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_2);
return x_103;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_IR_Checker_checkVar(x_101, x_2, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_2);
return x_106;
}
else
{
lean_object* x_108; 
lean_dec(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_1 = x_102;
x_3 = x_108;
goto _start;
}
}
}
case 8:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_1, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_1, 1);
lean_inc(x_111);
lean_dec(x_1);
x_112 = l_Lean_IR_Checker_checkVar(x_110, x_2, x_3);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_2);
return x_112;
}
else
{
lean_object* x_114; 
lean_dec(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_1 = x_111;
x_3 = x_114;
goto _start;
}
}
case 9:
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_1, 1);
lean_inc(x_116);
lean_dec(x_1);
x_1 = x_116;
goto _start;
}
case 10:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_1, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_1, 3);
lean_inc(x_119);
lean_dec(x_1);
x_120 = l_Lean_IR_Checker_checkVar(x_118, x_2, x_3);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_2);
return x_120;
}
else
{
uint8_t x_122; 
lean_dec(x_121);
x_122 = !lean_is_exclusive(x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_123 = lean_ctor_get(x_120, 1);
x_124 = lean_ctor_get(x_120, 0);
lean_dec(x_124);
x_125 = lean_unsigned_to_nat(0u);
x_126 = lean_array_get_size(x_119);
x_127 = lean_box(0);
x_128 = lean_nat_dec_lt(x_125, x_126);
if (x_128 == 0)
{
lean_object* x_129; 
lean_dec(x_126);
lean_dec(x_119);
lean_dec(x_2);
x_129 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_120, 0, x_129);
return x_120;
}
else
{
uint8_t x_130; 
x_130 = lean_nat_dec_le(x_126, x_126);
if (x_130 == 0)
{
lean_object* x_131; 
lean_dec(x_126);
lean_dec(x_119);
lean_dec(x_2);
x_131 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
lean_ctor_set(x_120, 0, x_131);
return x_120;
}
else
{
size_t x_132; size_t x_133; lean_object* x_134; 
lean_free_object(x_120);
x_132 = 0;
x_133 = lean_usize_of_nat(x_126);
lean_dec(x_126);
x_134 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(x_119, x_132, x_133, x_127, x_2, x_123);
lean_dec(x_119);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_120, 1);
lean_inc(x_135);
lean_dec(x_120);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_array_get_size(x_119);
x_138 = lean_box(0);
x_139 = lean_nat_dec_lt(x_136, x_137);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_137);
lean_dec(x_119);
lean_dec(x_2);
x_140 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_135);
return x_141;
}
else
{
uint8_t x_142; 
x_142 = lean_nat_dec_le(x_137, x_137);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_137);
lean_dec(x_119);
lean_dec(x_2);
x_143 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_135);
return x_144;
}
else
{
size_t x_145; size_t x_146; lean_object* x_147; 
x_145 = 0;
x_146 = lean_usize_of_nat(x_137);
lean_dec(x_137);
x_147 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(x_119, x_145, x_146, x_138, x_2, x_135);
lean_dec(x_119);
return x_147;
}
}
}
}
}
case 11:
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_1, 0);
lean_inc(x_148);
lean_dec(x_1);
x_149 = l_Lean_IR_Checker_checkArg(x_148, x_2, x_3);
lean_dec(x_2);
return x_149;
}
case 12:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_1, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_1, 1);
lean_inc(x_151);
lean_dec(x_1);
x_152 = l_Lean_IR_Checker_checkJP(x_150, x_2, x_3);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_2);
return x_152;
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_IR_Checker_checkArgs(x_151, x_2, x_154);
lean_dec(x_2);
lean_dec(x_151);
return x_155;
}
}
case 13:
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_2);
x_156 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_3);
return x_157;
}
default: 
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_1, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_1, 2);
lean_inc(x_159);
lean_dec(x_1);
x_4 = x_158;
x_5 = x_159;
x_6 = x_2;
x_7 = x_3;
goto block_12;
}
}
block_12:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_IR_Checker_checkVar(x_4, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
else
{
lean_object* x_10; 
lean_dec(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_1 = x_5;
x_2 = x_6;
x_3 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Checker_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_9 = x_2;
} else {
 lean_dec_ref(x_2);
 x_9 = lean_box(0);
}
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_4);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_4);
x_10 = x_7;
x_11 = x_3;
goto block_14;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_16, x_16);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_4);
x_10 = x_7;
x_11 = x_3;
goto block_14;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_21 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg(x_4, x_19, x_20, x_7, x_3);
lean_dec(x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 1, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
lean_dec(x_22);
x_10 = x_34;
x_11 = x_33;
goto block_14;
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
if (lean_is_scalar(x_9)) {
 x_12 = lean_alloc_ctor(0, 3, 0);
} else {
 x_12 = x_9;
}
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_8);
x_13 = l_Lean_IR_Checker_checkFnBody(x_5, x_12, x_11);
return x_13;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
lean_dec(x_2);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_array_get_size(x_35);
x_43 = lean_nat_dec_lt(x_41, x_42);
if (x_43 == 0)
{
lean_dec(x_42);
lean_dec(x_36);
lean_dec(x_35);
x_37 = x_3;
goto block_40;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_42, x_42);
if (x_44 == 0)
{
lean_dec(x_42);
lean_dec(x_36);
lean_dec(x_35);
x_37 = x_3;
goto block_40;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = 0;
x_46 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_47 = l_Array_foldlMUnsafe_fold___at___Lean_IR_Checker_checkFnBody_spec__0___redArg(x_35, x_45, x_46, x_36, x_3);
lean_dec(x_35);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_47, 0, x_53);
return x_47;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_56 = x_48;
} else {
 lean_dec_ref(x_48);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_48);
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
lean_dec(x_47);
x_37 = x_59;
goto block_40;
}
}
}
block_40:
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_IR_Checker_markIndex___redArg___closed__0;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
static lean_object* _init_l_Lean_IR_checkDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to compile definition, compiler IR check failed at '", 59, 59);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_checkDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'. Error: ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_1);
lean_inc(x_2);
x_13 = l_Lean_IR_Checker_checkDecl(x_2, x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_30; 
lean_free_object(x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_16 = x_14;
} else {
 lean_dec_ref(x_14);
 x_16 = lean_box(0);
}
x_17 = l_Lean_IR_Checker_checkPartialApp___closed__0;
x_18 = l_Lean_IR_checkDecl___closed__0;
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
lean_dec(x_2);
x_19 = x_30;
goto block_29;
block_29:
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = 1;
x_21 = l_Lean_Name_toString(x_19, x_20, x_17);
x_22 = lean_string_append(x_18, x_21);
lean_dec(x_21);
x_23 = l_Lean_IR_checkDecl___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_15);
lean_dec(x_15);
if (lean_is_scalar(x_16)) {
 x_26 = lean_alloc_ctor(3, 1, 0);
} else {
 x_26 = x_16;
 lean_ctor_set_tag(x_26, 3);
}
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_MessageData_ofFormat(x_26);
x_28 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(x_27, x_3, x_4, x_9);
return x_28;
}
}
else
{
lean_object* x_31; 
lean_dec(x_14);
lean_dec(x_2);
x_31 = lean_box(0);
lean_ctor_set(x_6, 0, x_31);
return x_6;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_1);
lean_inc(x_2);
x_37 = l_Lean_IR_Checker_checkDecl(x_2, x_36, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_54; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = l_Lean_IR_Checker_checkPartialApp___closed__0;
x_42 = l_Lean_IR_checkDecl___closed__0;
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
lean_dec(x_2);
x_43 = x_54;
goto block_53;
block_53:
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = 1;
x_45 = l_Lean_Name_toString(x_43, x_44, x_41);
x_46 = lean_string_append(x_42, x_45);
lean_dec(x_45);
x_47 = l_Lean_IR_checkDecl___closed__1;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_39);
lean_dec(x_39);
if (lean_is_scalar(x_40)) {
 x_50 = lean_alloc_ctor(3, 1, 0);
} else {
 x_50 = x_40;
 lean_ctor_set_tag(x_50, 3);
}
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_MessageData_ofFormat(x_50);
x_52 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(x_51, x_3, x_4, x_33);
return x_52;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_38);
lean_dec(x_2);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_33);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_checkDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_5);
x_10 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_11 = l_Lean_IR_checkDecl(x_1, x_10, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_5 = x_12;
x_8 = x_13;
goto _start;
}
else
{
lean_dec(x_1);
return x_11;
}
}
else
{
lean_object* x_17; 
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_inc(x_1);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_IR_checkDecls_spec__0(x_1, x_1, x_12, x_13, x_7, x_2, x_3, x_4);
lean_dec(x_1);
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
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_checkDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_checkDecls(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
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
l_Lean_IR_Checker_markIndex___redArg___closed__0 = _init_l_Lean_IR_Checker_markIndex___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___redArg___closed__0);
l_Lean_IR_Checker_markIndex___redArg___closed__1 = _init_l_Lean_IR_Checker_markIndex___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___redArg___closed__1);
l_Lean_IR_Checker_markIndex___redArg___closed__2 = _init_l_Lean_IR_Checker_markIndex___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_markIndex___redArg___closed__2);
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
l_Lean_IR_Checker_checkEqTypes___redArg___closed__0 = _init_l_Lean_IR_Checker_checkEqTypes___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_checkEqTypes___redArg___closed__0);
l_Lean_IR_Checker_checkEqTypes___redArg___closed__1 = _init_l_Lean_IR_Checker_checkEqTypes___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkEqTypes___redArg___closed__1);
l_Lean_IR_Checker_checkType___redArg___closed__0 = _init_l_Lean_IR_Checker_checkType___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_checkType___redArg___closed__0);
l_Lean_IR_Checker_checkType___redArg___closed__1 = _init_l_Lean_IR_Checker_checkType___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_checkType___redArg___closed__1);
l_Lean_IR_Checker_checkObjType___redArg___closed__0 = _init_l_Lean_IR_Checker_checkObjType___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_checkObjType___redArg___closed__0);
l_Lean_IR_Checker_checkScalarType___redArg___closed__0 = _init_l_Lean_IR_Checker_checkScalarType___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_checkScalarType___redArg___closed__0);
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
l_Lean_IR_Checker_checkPartialApp___closed__3 = _init_l_Lean_IR_Checker_checkPartialApp___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_checkPartialApp___closed__3);
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
l_Lean_IR_Checker_checkExpr___closed__7 = _init_l_Lean_IR_Checker_checkExpr___closed__7();
lean_mark_persistent(l_Lean_IR_Checker_checkExpr___closed__7);
l_Lean_IR_Checker_withParams___closed__0 = _init_l_Lean_IR_Checker_withParams___closed__0();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__0);
l_Lean_IR_Checker_withParams___closed__1 = _init_l_Lean_IR_Checker_withParams___closed__1();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__1);
l_Lean_IR_Checker_withParams___closed__2 = _init_l_Lean_IR_Checker_withParams___closed__2();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__2);
l_Lean_IR_Checker_withParams___closed__3 = _init_l_Lean_IR_Checker_withParams___closed__3();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__3);
l_Lean_IR_Checker_withParams___closed__4 = _init_l_Lean_IR_Checker_withParams___closed__4();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__4);
l_Lean_IR_Checker_withParams___closed__5 = _init_l_Lean_IR_Checker_withParams___closed__5();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__5);
l_Lean_IR_Checker_withParams___closed__6 = _init_l_Lean_IR_Checker_withParams___closed__6();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__6);
l_Lean_IR_Checker_withParams___closed__7 = _init_l_Lean_IR_Checker_withParams___closed__7();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__7);
l_Lean_IR_Checker_withParams___closed__8 = _init_l_Lean_IR_Checker_withParams___closed__8();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__8);
l_Lean_IR_Checker_withParams___closed__9 = _init_l_Lean_IR_Checker_withParams___closed__9();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__9);
l_Lean_IR_Checker_withParams___closed__10 = _init_l_Lean_IR_Checker_withParams___closed__10();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__10);
l_Lean_IR_Checker_withParams___closed__11 = _init_l_Lean_IR_Checker_withParams___closed__11();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__11);
l_Lean_IR_Checker_withParams___closed__12 = _init_l_Lean_IR_Checker_withParams___closed__12();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__12);
l_Lean_IR_Checker_withParams___closed__13 = _init_l_Lean_IR_Checker_withParams___closed__13();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__13);
l_Lean_IR_Checker_withParams___closed__14 = _init_l_Lean_IR_Checker_withParams___closed__14();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__14);
l_Lean_IR_Checker_withParams___closed__15 = _init_l_Lean_IR_Checker_withParams___closed__15();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__15);
l_Lean_IR_Checker_withParams___closed__16 = _init_l_Lean_IR_Checker_withParams___closed__16();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__16);
l_Lean_IR_Checker_withParams___closed__17 = _init_l_Lean_IR_Checker_withParams___closed__17();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__17);
l_Lean_IR_Checker_withParams___closed__18 = _init_l_Lean_IR_Checker_withParams___closed__18();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__18);
l_Lean_IR_Checker_withParams___closed__19 = _init_l_Lean_IR_Checker_withParams___closed__19();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__19);
l_Lean_IR_Checker_withParams___closed__20 = _init_l_Lean_IR_Checker_withParams___closed__20();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__20);
l_Lean_IR_Checker_withParams___closed__21 = _init_l_Lean_IR_Checker_withParams___closed__21();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__21);
l_Lean_IR_Checker_withParams___closed__22 = _init_l_Lean_IR_Checker_withParams___closed__22();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__22);
l_Lean_IR_Checker_withParams___closed__23 = _init_l_Lean_IR_Checker_withParams___closed__23();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__23);
l_Lean_IR_Checker_withParams___closed__24 = _init_l_Lean_IR_Checker_withParams___closed__24();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__24);
l_Lean_IR_Checker_withParams___closed__25 = _init_l_Lean_IR_Checker_withParams___closed__25();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__25);
l_Lean_IR_Checker_withParams___closed__26 = _init_l_Lean_IR_Checker_withParams___closed__26();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__26);
l_Lean_IR_Checker_withParams___closed__27 = _init_l_Lean_IR_Checker_withParams___closed__27();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__27);
l_Lean_IR_Checker_withParams___closed__28 = _init_l_Lean_IR_Checker_withParams___closed__28();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__28);
l_Lean_IR_Checker_withParams___closed__29 = _init_l_Lean_IR_Checker_withParams___closed__29();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__29);
l_Lean_IR_Checker_withParams___closed__30 = _init_l_Lean_IR_Checker_withParams___closed__30();
lean_mark_persistent(l_Lean_IR_Checker_withParams___closed__30);
l_Lean_IR_checkDecl___closed__0 = _init_l_Lean_IR_checkDecl___closed__0();
lean_mark_persistent(l_Lean_IR_checkDecl___closed__0);
l_Lean_IR_checkDecl___closed__1 = _init_l_Lean_IR_checkDecl___closed__1();
lean_mark_persistent(l_Lean_IR_checkDecl___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
