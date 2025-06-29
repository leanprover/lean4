// Lean compiler output
// Module: Lean.Compiler.IR.RC
// Imports: Lean.Runtime Lean.Compiler.IR.CompilerM Lean.Compiler.IR.LiveVars
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitRC_visitFnBody_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_erase___at_____private_Lean_Compiler_IR_LiveVars_0__Lean_IR_LiveVars_bindVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_visitFnBody(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addDec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateRefUsingCtorInfo(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitRC_getDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addInc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___lam__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_IR_LiveVars_collectExpr(lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_IR_ExplicitRC_getJPParams_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitRC_getJPParams___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPParams(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_processVDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedParam;
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_updateVarInfoWithParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ExplicitRC_getJPParams_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateRefUsingCtorInfo___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_visitDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_instInhabitedVarInfo;
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_mkLiveVarSet(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitRC_getDecl___closed__1;
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitRC_updateVarInfoWithParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isScalarBoxedInTaggedPtr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateVarInfo(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitRC_instInhabitedVarInfo___closed__0;
lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBefore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_Arg_beq(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPLiveVars(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxSmallNat;
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitRC_mustConsume(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitRC_getVarInfo___closed__0;
LEAN_EXPORT uint8_t l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
static lean_object* l_Lean_IR_ExplicitRC_getDecl___closed__0;
extern lean_object* l_Lean_IR_instInhabitedArg;
LEAN_EXPORT uint8_t l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_explicitRC_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_explicitRC_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_IR_Decl_updateBody_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isScalarBoxedInTaggedPtr___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LiveVars_updateJPLiveVarMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_consumeExpr___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitRC_updateVarInfoWithParams_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_consumeExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getVarInfo___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitRC_getJPParams___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_explicitRC___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_explicitRC(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isPersistent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_explicitRC___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_mustConsume___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addDec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitRC_getDecl___closed__3;
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBefore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPLiveVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_updateVarInfoWithParams___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitRC_visitFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getEnv___redArg(lean_object*);
lean_object* l_Lean_IR_LiveVars_collectFnBody(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at_____private_Lean_Compiler_IR_LiveVars_0__Lean_IR_LiveVars_collectJP_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExplicitRC_getVarInfo___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ExplicitRC_getVarInfo_spec__1(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isPersistent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getVarInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_ExplicitRC_instInhabitedVarInfo___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 0, 3);
x_3 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 0, x_3);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 1, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 2, x_5);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ExplicitRC_instInhabitedVarInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_ExplicitRC_instInhabitedVarInfo___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitRC_getDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.IR.RC", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitRC_getDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ExplicitRC.getDecl", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitRC_getDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitRC_getDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ExplicitRC_getDecl___closed__2;
x_2 = lean_unsigned_to_nat(17u);
x_3 = lean_unsigned_to_nat(36u);
x_4 = l_Lean_IR_ExplicitRC_getDecl___closed__1;
x_5 = l_Lean_IR_ExplicitRC_getDecl___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_findEnvDecl_x27(x_3, x_2, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_ExplicitRC_getDecl___closed__3;
x_7 = l_panic___at___Lean_IR_Decl_updateBody_x21_spec__0(x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_11; 
lean_inc(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ExplicitRC_getVarInfo_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ExplicitRC_instInhabitedVarInfo;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ExplicitRC_getVarInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ExplicitRC.getVarInfo", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitRC_getVarInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ExplicitRC_getDecl___closed__2;
x_2 = lean_unsigned_to_nat(17u);
x_3 = lean_unsigned_to_nat(41u);
x_4 = l_Lean_IR_ExplicitRC_getVarInfo___closed__0;
x_5 = l_Lean_IR_ExplicitRC_getDecl___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getVarInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_IR_ExplicitRC_getVarInfo___closed__1;
x_6 = l_panic___at___Lean_IR_ExplicitRC_getVarInfo_spec__1(x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getVarInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_panic___at___Lean_IR_ExplicitRC_getJPParams_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ExplicitRC_getJPParams_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at___Lean_IR_ExplicitRC_getJPParams_spec__0___closed__0;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ExplicitRC_getJPParams___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ExplicitRC.getJPParams", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ExplicitRC_getJPParams___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ExplicitRC_getDecl___closed__2;
x_2 = lean_unsigned_to_nat(15u);
x_3 = lean_unsigned_to_nat(46u);
x_4 = l_Lean_IR_ExplicitRC_getJPParams___closed__0;
x_5 = l_Lean_IR_ExplicitRC_getDecl___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = l_Lean_IR_LocalContext_getJPParams(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_IR_ExplicitRC_getJPParams___closed__1;
x_6 = l_panic___at___Lean_IR_ExplicitRC_getJPParams_spec__0(x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitRC_getJPParams(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPLiveVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_RBNode_find___at_____private_Lean_Compiler_IR_LiveVars_0__Lean_IR_LiveVars_collectJP_spec__0___redArg(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_getJPLiveVars___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitRC_getJPLiveVars(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExplicitRC_mustConsume(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_4 = lean_ctor_get_uint8(x_3, 0);
if (x_4 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_3, 2);
lean_dec(x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_mustConsume___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_ExplicitRC_mustConsume(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addInc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_8 = lean_ctor_get_uint8(x_7, 1);
lean_dec(x_7);
x_9 = lean_box(1);
x_10 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_3);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*3, x_11);
lean_ctor_set_uint8(x_10, sizeof(void*)*3 + 1, x_8);
return x_10;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addInc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitRC_addInc(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addDec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_5 = lean_ctor_get_uint8(x_4, 1);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_3);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_9);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_addDec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitRC_addDec(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateRefUsingCtorInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_IR_CtorInfo_isRef(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg(x_7, x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 4);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_ctor_set_uint8(x_17, 0, x_4);
x_19 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_7, x_2, x_17);
lean_ctor_set(x_1, 2, x_19);
return x_1;
}
else
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get_uint8(x_17, 1);
x_21 = lean_ctor_get_uint8(x_17, 2);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_22, 0, x_4);
lean_ctor_set_uint8(x_22, 1, x_20);
lean_ctor_set_uint8(x_22, 2, x_21);
x_23 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_7, x_2, x_22);
lean_ctor_set(x_1, 2, x_23);
return x_1;
}
}
else
{
lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_10, 0);
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_ctor_get_uint8(x_24, 1);
x_26 = lean_ctor_get_uint8(x_24, 2);
if (lean_is_exclusive(x_24)) {
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(0, 0, 3);
} else {
 x_28 = x_27;
}
lean_ctor_set_uint8(x_28, 0, x_4);
lean_ctor_set_uint8(x_28, 1, x_25);
lean_ctor_set_uint8(x_28, 2, x_26);
x_29 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_7, x_2, x_28);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_8);
lean_ctor_set(x_30, 4, x_9);
return x_30;
}
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateRefUsingCtorInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateRefUsingCtorInfo(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(x_1, x_2, x_3, x_5);
x_9 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(x_1, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = l_Lean_IR_ExplicitRC_mustConsume(x_2, x_6);
if (x_10 == 0)
{
x_3 = x_8;
x_4 = x_7;
goto _start;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_IR_ExplicitRC_getVarInfo(x_2, x_6);
x_13 = lean_ctor_get_uint8(x_12, 1);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(1u);
lean_inc(x_6);
x_15 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_8);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 1, x_13);
x_3 = x_15;
x_4 = x_7;
goto _start;
}
}
else
{
lean_dec(x_9);
x_3 = x_8;
x_4 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(x_3, x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 1)
{
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_nat_sub(x_4, x_5);
lean_inc(x_1);
x_9 = lean_array_get(x_1, x_2, x_8);
lean_dec(x_8);
x_10 = l_Lean_IR_Arg_beq(x_9, x_3);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_IR_instInhabitedArg;
x_4 = lean_array_get(x_3, x_1, x_2);
lean_inc(x_2);
x_5 = l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg(x_3, x_1, x_4, x_2, x_2);
lean_dec(x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Nat_allTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 1)
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_15; lean_object* x_16; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
x_15 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
x_16 = lean_array_fget(x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_nat_dec_eq(x_2, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_15);
x_12 = x_18;
goto block_14;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_inc(x_3);
x_19 = lean_apply_1(x_3, x_15);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
x_12 = x_18;
goto block_14;
}
else
{
x_5 = x_11;
goto _start;
}
}
}
else
{
lean_dec(x_15);
x_5 = x_11;
goto _start;
}
block_14:
{
if (x_12 == 0)
{
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_3);
return x_12;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
lean_inc(x_4);
x_5 = l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___redArg(x_2, x_1, x_3, x_4, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Nat_anyTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get(x_1, x_2, x_3);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_IR_instInhabitedParam;
x_5 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___lam__0___boxed), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 1)
{
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_16; lean_object* x_17; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_5, x_9);
x_16 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
x_17 = lean_array_fget(x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_nat_dec_eq(x_2, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_dec(x_16);
x_11 = x_19;
goto block_15;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_inc(x_3);
x_20 = lean_apply_1(x_3, x_16);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
x_11 = x_21;
goto block_15;
}
}
else
{
lean_dec(x_16);
x_5 = x_10;
goto _start;
}
block_15:
{
if (x_11 == 0)
{
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_nat_add(x_6, x_9);
lean_dec(x_6);
x_5 = x_10;
x_6 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_6 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___redArg(x_2, x_1, x_3, x_4, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 1)
{
lean_dec(x_6);
lean_dec(x_3);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
x_12 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
x_13 = lean_array_fget(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_IR_ExplicitRC_getVarInfo(x_2, x_14);
x_16 = lean_ctor_get_uint8(x_15, 0);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
x_6 = x_11;
goto _start;
}
else
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get_uint8(x_15, 1);
x_19 = lean_ctor_get_uint8(x_15, 2);
lean_dec(x_15);
x_20 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc(x_1, x_12);
if (x_20 == 0)
{
lean_dec(x_14);
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_inc(x_3);
x_28 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_getNumConsumptions(x_14, x_1, x_3);
if (x_19 == 0)
{
if (x_20 == 0)
{
goto block_35;
}
else
{
x_29 = x_20;
goto block_31;
}
}
else
{
goto block_35;
}
block_31:
{
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_nat_sub(x_28, x_10);
lean_dec(x_28);
x_21 = x_30;
goto block_26;
}
else
{
x_21 = x_28;
goto block_26;
}
}
block_33:
{
uint8_t x_32; 
lean_inc(x_3);
x_32 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParamAux(x_14, x_1, x_3);
x_29 = x_32;
goto block_31;
}
block_35:
{
lean_object* x_34; 
x_34 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(x_4, x_14);
if (lean_obj_tag(x_34) == 0)
{
goto block_33;
}
else
{
lean_dec(x_34);
if (x_20 == 0)
{
goto block_33;
}
else
{
x_29 = x_20;
goto block_31;
}
}
}
}
block_26:
{
uint8_t x_22; 
x_22 = lean_nat_dec_eq(x_21, x_8);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_7);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*3 + 1, x_18);
x_6 = x_11;
x_7 = x_23;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec(x_14);
x_6 = x_11;
goto _start;
}
}
}
}
else
{
lean_dec(x_12);
x_6 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_2);
lean_inc(x_6);
x_7 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___redArg(x_2, x_1, x_3, x_5, x_6, x_6, x_4);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBefore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_IR_instInhabitedParam;
x_7 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_3);
x_8 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux(x_1, x_2, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBefore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBefore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 1)
{
lean_dec(x_6);
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
x_12 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
x_13 = lean_array_fget(x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_26; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_26 = l_Lean_IR_ExplicitRC_mustConsume(x_4, x_14);
if (x_26 == 0)
{
lean_dec(x_12);
x_15 = x_26;
goto block_25;
}
else
{
uint8_t x_27; 
x_27 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isFirstOcc(x_1, x_12);
x_15 = x_27;
goto block_25;
}
block_25:
{
if (x_15 == 0)
{
lean_dec(x_14);
x_6 = x_11;
goto _start;
}
else
{
uint8_t x_17; 
lean_inc(x_2);
x_17 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isBorrowParam(x_14, x_1, x_2);
if (x_17 == 0)
{
lean_dec(x_14);
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(x_3, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = l_Lean_IR_ExplicitRC_getVarInfo(x_4, x_14);
x_21 = lean_ctor_get_uint8(x_20, 1);
lean_dec(x_20);
x_22 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_7);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_17);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_21);
x_6 = x_11;
x_7 = x_22;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec(x_14);
x_6 = x_11;
goto _start;
}
}
}
}
}
else
{
lean_dec(x_12);
x_6 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_2);
lean_inc(x_6);
x_7 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___redArg(x_2, x_3, x_5, x_1, x_6, x_6, x_4);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldTR_loop___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___lam__0___boxed), 1, 0);
x_6 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeAux(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_3, x_4);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_IR_IRType_isObj(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_15);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(x_1, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_IR_ExplicitRC_getVarInfo(x_2, x_15);
x_20 = lean_ctor_get_uint8(x_19, 1);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_6);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_17);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_20);
x_7 = x_22;
goto block_11;
}
else
{
lean_dec(x_18);
lean_dec(x_15);
x_7 = x_6;
goto block_11;
}
}
}
else
{
lean_dec(x_13);
x_7 = x_6;
goto block_11;
}
}
else
{
return x_6;
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
x_6 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_11 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams_spec__0(x_4, x_1, x_2, x_9, x_10, x_3);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isPersistent(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Array_isEmpty___redArg(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isPersistent___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isPersistent(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_consumeExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_RBNode_find___at___Lean_IR_ExplicitRC_getVarInfo_spec__0___redArg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get_uint8(x_7, 2);
lean_dec(x_7);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(1);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_consumeExpr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_consumeExpr(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isScalarBoxedInTaggedPtr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_10; uint8_t x_11; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_3, x_10);
if (x_11 == 0)
{
x_6 = x_11;
goto block_9;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_eq(x_5, x_10);
x_6 = x_12;
goto block_9;
}
block_9:
{
if (x_6 == 0)
{
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
return x_8;
}
}
}
case 11:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
x_15 = l_Lean_maxSmallNat;
x_16 = lean_nat_dec_le(x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
default: 
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isScalarBoxedInTaggedPtr___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isScalarBoxedInTaggedPtr(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateVarInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_18; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 x_10 = x_1;
} else {
 lean_dec_ref(x_1);
 x_10 = lean_box(0);
}
x_18 = l_Lean_IR_IRType_isObj(x_3);
if (x_18 == 0)
{
x_11 = x_18;
goto block_17;
}
else
{
uint8_t x_19; 
x_19 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isScalarBoxedInTaggedPtr(x_4);
if (x_19 == 0)
{
x_11 = x_18;
goto block_17;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_11 = x_21;
goto block_17;
}
}
block_17:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_isPersistent(x_4);
x_13 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_consumeExpr(x_7, x_4);
x_14 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_14, 0, x_11);
lean_ctor_set_uint8(x_14, 1, x_12);
lean_ctor_set_uint8(x_14, 2, x_13);
x_15 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_7, x_2, x_14);
if (lean_is_scalar(x_10)) {
 x_16 = lean_alloc_ctor(0, 5, 0);
} else {
 x_16 = x_10;
}
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_8);
lean_ctor_set(x_16, 4, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateVarInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateVarInfo(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_11; 
x_11 = l_Lean_IR_ExplicitRC_mustConsume(x_1, x_2);
if (x_11 == 0)
{
x_5 = x_11;
goto block_10;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_RBNode_findCore___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__0___redArg(x_4, x_2);
if (lean_obj_tag(x_12) == 0)
{
x_5 = x_11;
goto block_10;
}
else
{
lean_dec(x_12);
lean_dec(x_2);
return x_3;
}
}
block_10:
{
if (x_5 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_7 = lean_ctor_get_uint8(x_6, 1);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_3);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 1, x_7);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_processVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_2);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_4);
lean_ctor_set(x_13, 3, x_5);
x_14 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll(x_1, x_12, x_13, x_6);
lean_dec(x_12);
lean_dec(x_1);
x_7 = x_14;
goto block_11;
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
lean_inc(x_4);
lean_inc(x_2);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_4);
lean_ctor_set(x_16, 3, x_5);
x_17 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll(x_1, x_15, x_16, x_6);
lean_dec(x_15);
lean_dec(x_1);
x_7 = x_17;
goto block_11;
}
case 3:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
x_19 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_18);
x_20 = lean_ctor_get_uint8(x_19, 2);
lean_dec(x_19);
x_21 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded(x_1, x_18, x_5, x_6);
if (x_20 == 0)
{
lean_object* x_22; 
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_21);
x_7 = x_22;
goto block_11;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
lean_dec(x_1);
x_24 = lean_ctor_get_uint8(x_23, 1);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_26 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_20);
lean_ctor_set_uint8(x_26, sizeof(void*)*3 + 1, x_24);
lean_inc(x_4);
lean_inc(x_2);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set(x_27, 3, x_26);
x_7 = x_27;
goto block_11;
}
}
case 4:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
x_29 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded(x_1, x_28, x_5, x_6);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_4);
lean_ctor_set(x_30, 3, x_29);
x_7 = x_30;
goto block_11;
}
case 5:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_4, 2);
lean_inc(x_31);
x_32 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded(x_1, x_31, x_5, x_6);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_4);
lean_ctor_set(x_33, 3, x_32);
x_7 = x_33;
goto block_11;
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_inc(x_1);
x_41 = l_Lean_IR_ExplicitRC_getDecl(x_1, x_34);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_36 = x_42;
goto block_40;
block_40:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc(x_36);
x_37 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecAfterFullApp(x_1, x_35, x_36, x_5, x_6);
lean_inc(x_4);
lean_inc(x_2);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_3);
lean_ctor_set(x_38, 2, x_4);
lean_ctor_set(x_38, 3, x_37);
x_39 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBefore(x_1, x_35, x_36, x_38, x_6);
lean_dec(x_35);
lean_dec(x_1);
x_7 = x_39;
goto block_11;
}
}
case 7:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
lean_inc(x_4);
lean_inc(x_2);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_3);
lean_ctor_set(x_44, 2, x_4);
lean_ctor_set(x_44, 3, x_5);
x_45 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll(x_1, x_43, x_44, x_6);
lean_dec(x_43);
lean_dec(x_1);
x_7 = x_45;
goto block_11;
}
case 8:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_4, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_4, 1);
lean_inc(x_47);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_array_push(x_47, x_48);
lean_inc(x_4);
lean_inc(x_2);
x_50 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_3);
lean_ctor_set(x_50, 2, x_4);
lean_ctor_set(x_50, 3, x_5);
x_51 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBeforeConsumeAll(x_1, x_49, x_50, x_6);
lean_dec(x_49);
lean_dec(x_1);
x_7 = x_51;
goto block_11;
}
case 10:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_4, 0);
lean_inc(x_52);
x_53 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecIfNeeded(x_1, x_52, x_5, x_6);
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_2);
lean_ctor_set(x_54, 1, x_3);
lean_ctor_set(x_54, 2, x_4);
lean_ctor_set(x_54, 3, x_53);
x_7 = x_54;
goto block_11;
}
default: 
{
lean_object* x_55; 
lean_dec(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_2);
lean_ctor_set(x_55, 1, x_3);
lean_ctor_set(x_55, 2, x_4);
lean_ctor_set(x_55, 3, x_5);
x_7 = x_55;
goto block_11;
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_IR_LiveVars_collectExpr(x_4, x_6);
x_9 = l_Lean_RBNode_erase___at_____private_Lean_Compiler_IR_LiveVars_0__Lean_IR_LiveVars_bindVar_spec__0___redArg(x_2, x_8);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitRC_updateVarInfoWithParams_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_IR_IRType_isObj(x_9);
lean_dec(x_9);
if (x_8 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_11 = x_19;
goto block_17;
}
else
{
x_11 = x_5;
goto block_17;
}
block_17:
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, 1, x_5);
lean_ctor_set_uint8(x_12, 2, x_11);
x_13 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_4, x_7, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_13;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_updateVarInfoWithParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_9, x_9);
if (x_11 == 0)
{
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 4);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_18 = 0;
x_19 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_20 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitRC_updateVarInfoWithParams_spec__0(x_2, x_18, x_19, x_5);
lean_ctor_set(x_1, 2, x_20);
return x_1;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_21 = 0;
x_22 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_23 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitRC_updateVarInfoWithParams_spec__0(x_2, x_21, x_22, x_5);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_6);
lean_ctor_set(x_24, 4, x_7);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitRC_updateVarInfoWithParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_ExplicitRC_updateVarInfoWithParams_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_updateVarInfoWithParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitRC_updateVarInfoWithParams(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitRC_visitFnBody_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_box(0);
x_10 = lean_array_uset(x_6, x_5, x_9);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateRefUsingCtorInfo(x_1, x_2, x_18);
lean_inc(x_20);
x_21 = l_Lean_IR_ExplicitRC_visitFnBody(x_19, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(x_23, x_20, x_22, x_3);
lean_dec(x_20);
lean_dec(x_23);
lean_ctor_set(x_8, 1, x_24);
x_11 = x_8;
goto block_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateRefUsingCtorInfo(x_1, x_2, x_25);
lean_inc(x_27);
x_28 = l_Lean_IR_ExplicitRC_visitFnBody(x_26, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(x_30, x_27, x_29, x_3);
lean_dec(x_27);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
x_11 = x_32;
goto block_16;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_8, 0);
lean_inc(x_1);
x_35 = l_Lean_IR_ExplicitRC_visitFnBody(x_34, x_1);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(x_37, x_1, x_36, x_3);
lean_dec(x_37);
lean_ctor_set(x_8, 0, x_38);
x_11 = x_8;
goto block_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_8, 0);
lean_inc(x_39);
lean_dec(x_8);
lean_inc(x_1);
x_40 = l_Lean_IR_ExplicitRC_visitFnBody(x_39, x_1);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_RBNode_fold___at_____private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForAlt_spec__1(x_42, x_1, x_41, x_3);
lean_dec(x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_11 = x_44;
goto block_16;
}
}
block_16:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
x_14 = lean_array_uset(x_10, x_5, x_11);
x_5 = x_13;
x_6 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_visitFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_3);
x_7 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_updateVarInfo(x_2, x_3, x_4, x_5);
lean_inc(x_7);
x_8 = l_Lean_IR_ExplicitRC_visitFnBody(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_processVDecl(x_7, x_3, x_4, x_5, x_9, x_10);
return x_11;
}
case 1:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_17 = l_Lean_IR_ExplicitRC_updateVarInfoWithParams(x_2, x_14);
lean_inc(x_17);
x_18 = l_Lean_IR_ExplicitRC_visitFnBody(x_15, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_2, 3);
x_23 = lean_ctor_get(x_2, 4);
x_24 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams(x_17, x_14, x_19, x_20);
lean_dec(x_20);
lean_dec(x_17);
lean_inc(x_24);
lean_inc(x_13);
x_25 = l_Lean_IR_LiveVars_updateJPLiveVarMap(x_13, x_14, x_24, x_22);
lean_inc(x_24);
lean_inc(x_14);
lean_inc(x_13);
x_26 = l_Lean_IR_LocalContext_addJP(x_23, x_13, x_14, x_24);
lean_ctor_set(x_2, 4, x_26);
lean_ctor_set(x_2, 3, x_25);
x_27 = l_Lean_IR_ExplicitRC_visitFnBody(x_16, x_2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_1, 3, x_29);
lean_ctor_set(x_1, 2, x_24);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_1, 3, x_30);
lean_ctor_set(x_1, 2, x_24);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_ctor_get(x_2, 3);
x_37 = lean_ctor_get(x_2, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_38 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams(x_17, x_14, x_19, x_20);
lean_dec(x_20);
lean_dec(x_17);
lean_inc(x_38);
lean_inc(x_13);
x_39 = l_Lean_IR_LiveVars_updateJPLiveVarMap(x_13, x_14, x_38, x_36);
lean_inc(x_38);
lean_inc(x_14);
lean_inc(x_13);
x_40 = l_Lean_IR_LocalContext_addJP(x_37, x_13, x_14, x_38);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_33);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 3, x_39);
lean_ctor_set(x_41, 4, x_40);
x_42 = l_Lean_IR_ExplicitRC_visitFnBody(x_16, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set(x_1, 2, x_38);
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = lean_ctor_get(x_1, 1);
x_49 = lean_ctor_get(x_1, 2);
x_50 = lean_ctor_get(x_1, 3);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_1);
lean_inc(x_2);
x_51 = l_Lean_IR_ExplicitRC_updateVarInfoWithParams(x_2, x_48);
lean_inc(x_51);
x_52 = l_Lean_IR_ExplicitRC_visitFnBody(x_49, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 3);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 4);
lean_inc(x_59);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_60 = x_2;
} else {
 lean_dec_ref(x_2);
 x_60 = lean_box(0);
}
x_61 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams(x_51, x_48, x_53, x_54);
lean_dec(x_54);
lean_dec(x_51);
lean_inc(x_61);
lean_inc(x_47);
x_62 = l_Lean_IR_LiveVars_updateJPLiveVarMap(x_47, x_48, x_61, x_58);
lean_inc(x_61);
lean_inc(x_48);
lean_inc(x_47);
x_63 = l_Lean_IR_LocalContext_addJP(x_59, x_47, x_48, x_61);
if (lean_is_scalar(x_60)) {
 x_64 = lean_alloc_ctor(0, 5, 0);
} else {
 x_64 = x_60;
}
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 2, x_57);
lean_ctor_set(x_64, 3, x_62);
lean_ctor_set(x_64, 4, x_63);
x_65 = l_Lean_IR_ExplicitRC_visitFnBody(x_50, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_69, 0, x_47);
lean_ctor_set(x_69, 1, x_48);
lean_ctor_set(x_69, 2, x_61);
lean_ctor_set(x_69, 3, x_66);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
case 4:
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_1);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_1, 0);
x_73 = lean_ctor_get(x_1, 3);
x_74 = l_Lean_IR_ExplicitRC_visitFnBody(x_73, x_2);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_74, 1);
x_78 = lean_box(0);
lean_inc(x_72);
x_79 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_77, x_72, x_78);
lean_ctor_set(x_1, 3, x_76);
lean_ctor_set(x_74, 1, x_79);
lean_ctor_set(x_74, 0, x_1);
return x_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_74, 0);
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_74);
x_82 = lean_box(0);
lean_inc(x_72);
x_83 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_81, x_72, x_82);
lean_ctor_set(x_1, 3, x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_1);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_85 = lean_ctor_get(x_1, 0);
x_86 = lean_ctor_get(x_1, 1);
x_87 = lean_ctor_get(x_1, 2);
x_88 = lean_ctor_get(x_1, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_1);
x_89 = l_Lean_IR_ExplicitRC_visitFnBody(x_88, x_2);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
lean_inc(x_85);
x_94 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_91, x_85, x_93);
x_95 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_86);
lean_ctor_set(x_95, 2, x_87);
lean_ctor_set(x_95, 3, x_90);
if (lean_is_scalar(x_92)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_92;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
case 5:
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_1);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_1, 0);
x_99 = lean_ctor_get(x_1, 5);
x_100 = l_Lean_IR_ExplicitRC_visitFnBody(x_99, x_2);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
x_104 = lean_box(0);
lean_inc(x_98);
x_105 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_103, x_98, x_104);
lean_ctor_set(x_1, 5, x_102);
lean_ctor_set(x_100, 1, x_105);
lean_ctor_set(x_100, 0, x_1);
return x_100;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_100, 0);
x_107 = lean_ctor_get(x_100, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_100);
x_108 = lean_box(0);
lean_inc(x_98);
x_109 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_107, x_98, x_108);
lean_ctor_set(x_1, 5, x_106);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_111 = lean_ctor_get(x_1, 0);
x_112 = lean_ctor_get(x_1, 1);
x_113 = lean_ctor_get(x_1, 2);
x_114 = lean_ctor_get(x_1, 3);
x_115 = lean_ctor_get(x_1, 4);
x_116 = lean_ctor_get(x_1, 5);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_1);
x_117 = l_Lean_IR_ExplicitRC_visitFnBody(x_116, x_2);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
x_121 = lean_box(0);
lean_inc(x_111);
x_122 = l_Lean_RBNode_insert___at___Lean_IR_mkLiveVarSet_spec__0___redArg(x_119, x_111, x_121);
x_123 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_123, 0, x_111);
lean_ctor_set(x_123, 1, x_112);
lean_ctor_set(x_123, 2, x_113);
lean_ctor_set(x_123, 3, x_114);
lean_ctor_set(x_123, 4, x_115);
lean_ctor_set(x_123, 5, x_118);
if (lean_is_scalar(x_120)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_120;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
case 9:
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_1);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = lean_ctor_get(x_1, 1);
x_127 = l_Lean_IR_ExplicitRC_visitFnBody(x_126, x_2);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_127, 0);
lean_ctor_set(x_1, 1, x_129);
lean_ctor_set(x_127, 0, x_1);
return x_127;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_127, 0);
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_127);
lean_ctor_set(x_1, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_1);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_133 = lean_ctor_get(x_1, 0);
x_134 = lean_ctor_get(x_1, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_1);
x_135 = l_Lean_IR_ExplicitRC_visitFnBody(x_134, x_2);
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
x_139 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_139, 0, x_133);
lean_ctor_set(x_139, 1, x_136);
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
case 10:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_141 = lean_ctor_get(x_1, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_1, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_1, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_1, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_2, 3);
lean_inc(x_145);
x_146 = lean_box(0);
lean_inc(x_1);
x_147 = l_Lean_IR_LiveVars_collectFnBody(x_1, x_145, x_146);
x_148 = !lean_is_exclusive(x_1);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; size_t x_153; size_t x_154; lean_object* x_155; lean_object* x_156; 
x_149 = lean_ctor_get(x_1, 3);
lean_dec(x_149);
x_150 = lean_ctor_get(x_1, 2);
lean_dec(x_150);
x_151 = lean_ctor_get(x_1, 1);
lean_dec(x_151);
x_152 = lean_ctor_get(x_1, 0);
lean_dec(x_152);
x_153 = lean_array_size(x_144);
x_154 = 0;
lean_inc(x_142);
x_155 = l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitRC_visitFnBody_spec__0(x_2, x_142, x_147, x_153, x_154, x_144);
lean_ctor_set(x_1, 3, x_155);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_1);
lean_ctor_set(x_156, 1, x_147);
return x_156;
}
else
{
size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_1);
x_157 = lean_array_size(x_144);
x_158 = 0;
lean_inc(x_142);
x_159 = l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitRC_visitFnBody_spec__0(x_2, x_142, x_147, x_157, x_158, x_144);
x_160 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_160, 0, x_141);
lean_ctor_set(x_160, 1, x_142);
lean_ctor_set(x_160, 2, x_143);
lean_ctor_set(x_160, 3, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_147);
return x_161;
}
}
case 11:
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_1, 0);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_167; uint8_t x_168; uint8_t x_169; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec(x_162);
x_167 = l_Lean_IR_ExplicitRC_getVarInfo(x_2, x_163);
lean_dec(x_2);
x_168 = lean_ctor_get_uint8(x_167, 0);
x_169 = lean_ctor_get_uint8(x_167, 2);
if (x_168 == 0)
{
goto block_175;
}
else
{
if (x_169 == 0)
{
goto block_175;
}
else
{
lean_dec(x_167);
goto block_166;
}
}
block_166:
{
lean_object* x_164; lean_object* x_165; 
x_164 = l_Lean_IR_mkLiveVarSet(x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_1);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
block_175:
{
if (x_168 == 0)
{
lean_dec(x_167);
goto block_166;
}
else
{
uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get_uint8(x_167, 1);
lean_dec(x_167);
x_171 = lean_unsigned_to_nat(1u);
lean_inc(x_163);
x_172 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_172, 0, x_163);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_172, 2, x_1);
lean_ctor_set_uint8(x_172, sizeof(void*)*3, x_168);
lean_ctor_set_uint8(x_172, sizeof(void*)*3 + 1, x_170);
x_173 = l_Lean_IR_mkLiveVarSet(x_163);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_2);
x_176 = lean_box(0);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_1);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
case 12:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_178 = lean_ctor_get(x_1, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_1, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_2, 3);
lean_inc(x_180);
x_181 = l_Lean_IR_ExplicitRC_getJPLiveVars(x_2, x_178);
x_182 = l_Lean_IR_ExplicitRC_getJPParams(x_2, x_178);
lean_dec(x_178);
x_183 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addIncBefore(x_2, x_179, x_182, x_1, x_181);
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_2);
x_184 = lean_box(0);
lean_inc(x_183);
x_185 = l_Lean_IR_LiveVars_collectFnBody(x_183, x_180, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
case 13:
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_2);
x_187 = lean_box(0);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_1);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
default: 
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_2);
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_1);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitRC_visitFnBody_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at___Lean_IR_ExplicitRC_visitFnBody_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExplicitRC_visitDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 3);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set(x_7, 4, x_6);
x_8 = l_Lean_IR_ExplicitRC_updateVarInfoWithParams(x_7, x_4);
lean_inc(x_8);
x_9 = l_Lean_IR_ExplicitRC_visitFnBody(x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Compiler_IR_RC_0__Lean_IR_ExplicitRC_addDecForDeadParams(x_8, x_4, x_10, x_11);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_8);
x_13 = l_Lean_IR_Decl_updateBody_x21(x_3, x_12);
return x_13;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_explicitRC_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_5, x_4, x_8);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_IR_ExplicitRC_visitDecl(x_1, x_2, x_7);
x_11 = 1;
x_12 = lean_usize_add(x_4, x_11);
x_13 = lean_array_uset(x_9, x_4, x_10);
x_4 = x_12;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_explicitRC___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_IR_getEnv___redArg(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_array_size(x_1);
x_7 = 0;
lean_inc(x_1);
x_8 = l_Array_mapMUnsafe_map___at___Lean_IR_explicitRC_spec__0(x_5, x_1, x_6, x_7, x_1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_array_size(x_1);
x_12 = 0;
lean_inc(x_1);
x_13 = l_Array_mapMUnsafe_map___at___Lean_IR_explicitRC_spec__0(x_9, x_1, x_11, x_12, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_explicitRC(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_explicitRC___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_explicitRC_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___Lean_IR_explicitRC_spec__0(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_explicitRC___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_explicitRC(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Lean_Runtime(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_LiveVars(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_RC(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Runtime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_LiveVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ExplicitRC_instInhabitedVarInfo___closed__0 = _init_l_Lean_IR_ExplicitRC_instInhabitedVarInfo___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitRC_instInhabitedVarInfo___closed__0);
l_Lean_IR_ExplicitRC_instInhabitedVarInfo = _init_l_Lean_IR_ExplicitRC_instInhabitedVarInfo();
lean_mark_persistent(l_Lean_IR_ExplicitRC_instInhabitedVarInfo);
l_Lean_IR_ExplicitRC_getDecl___closed__0 = _init_l_Lean_IR_ExplicitRC_getDecl___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitRC_getDecl___closed__0);
l_Lean_IR_ExplicitRC_getDecl___closed__1 = _init_l_Lean_IR_ExplicitRC_getDecl___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitRC_getDecl___closed__1);
l_Lean_IR_ExplicitRC_getDecl___closed__2 = _init_l_Lean_IR_ExplicitRC_getDecl___closed__2();
lean_mark_persistent(l_Lean_IR_ExplicitRC_getDecl___closed__2);
l_Lean_IR_ExplicitRC_getDecl___closed__3 = _init_l_Lean_IR_ExplicitRC_getDecl___closed__3();
lean_mark_persistent(l_Lean_IR_ExplicitRC_getDecl___closed__3);
l_Lean_IR_ExplicitRC_getVarInfo___closed__0 = _init_l_Lean_IR_ExplicitRC_getVarInfo___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitRC_getVarInfo___closed__0);
l_Lean_IR_ExplicitRC_getVarInfo___closed__1 = _init_l_Lean_IR_ExplicitRC_getVarInfo___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitRC_getVarInfo___closed__1);
l_panic___at___Lean_IR_ExplicitRC_getJPParams_spec__0___closed__0 = _init_l_panic___at___Lean_IR_ExplicitRC_getJPParams_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_IR_ExplicitRC_getJPParams_spec__0___closed__0);
l_Lean_IR_ExplicitRC_getJPParams___closed__0 = _init_l_Lean_IR_ExplicitRC_getJPParams___closed__0();
lean_mark_persistent(l_Lean_IR_ExplicitRC_getJPParams___closed__0);
l_Lean_IR_ExplicitRC_getJPParams___closed__1 = _init_l_Lean_IR_ExplicitRC_getJPParams___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitRC_getJPParams___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
