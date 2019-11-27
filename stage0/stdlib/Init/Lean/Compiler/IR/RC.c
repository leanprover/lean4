// Lean compiler output
// Module: Init.Lean.Compiler.IR.RC
// Imports: Init.Lean.Runtime Init.Lean.Compiler.IR.CompilerM Init.Lean.Compiler.IR.LiveVars
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
lean_object* l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__5___boxed(lean_object*, lean_object*);
extern uint8_t l_String_anyAux___main___at_String_all___spec__1___closed__1;
uint8_t l_RBNode_isRed___rarg(lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_getDecl___boxed(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_IR_mkLiveVarSet___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_Arg_beq(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_getJPLiveVars(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___boxed(lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_Iterator_extract___closed__1;
lean_object* l_Lean_IR_ExplicitRC_getJPParams___boxed(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Compiler_IR_LiveVars_6__accumulate___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__4___rarg___boxed(lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_RC_12__isPersistent(lean_object*);
lean_object* l_Lean_IR_ExplicitRC_visitDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExplicitRC_visitFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LiveVars_collectExpr(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_RC_15__updateVarInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___lambda__1___boxed(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitRC_updateVarInfoWithParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_findCore___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__1(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_RC_13__consumeExpr(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_addDec(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_14__isScalarBoxedInTaggedPtr___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___lambda__1(lean_object*);
lean_object* l_RBNode_insert___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
lean_object* l_Lean_IR_explicitRC(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_IR_ExplicitRC_getVarInfo___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___boxed(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_RBNode_findCore___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Arg_Inhabited;
lean_object* l_Lean_IR_ExplicitRC_getVarInfo___closed__1;
lean_object* l___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_updateVarInfoWithParams___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_13__consumeExpr___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_getVarInfo___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_16__addDecIfNeeded(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_getJPParams(lean_object*, lean_object*);
lean_object* l_Lean_IR_LiveVars_collectFnBody___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__4___rarg(lean_object*);
lean_object* l_RBNode_erase___at___private_Init_Lean_Compiler_IR_LiveVars_8__bindVar___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_paramInh;
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_12__isPersistent___boxed(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2(lean_object*, lean_object*);
uint8_t l_Nat_anyAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl_x27(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_15__updateVarInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_addInc(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__5(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_9__addDecAfterFullApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__4___boxed(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__4(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_17__processVDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_findCore___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxSmallNat;
lean_object* l_Array_umapMAux___main___at_Lean_IR_explicitRC___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_getJPLiveVars___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_8__addIncBefore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_9__addDecAfterFullApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__2___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_9__addDecAfterFullApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_9__addDecAfterFullApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_addInc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at___private_Init_Lean_Compiler_IR_LiveVars_7__collectJP___spec__1(lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_getDecl(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitRC_updateVarInfoWithParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_RC_14__isScalarBoxedInTaggedPtr(lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_16__addDecIfNeeded___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___closed__1;
lean_object* l_RBNode_setBlack___rarg(lean_object*);
uint8_t l_Lean_IR_ExplicitRC_mustConsume(lean_object*, lean_object*);
lean_object* l_Lean_IR_mkLiveVarSet(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_getVarInfo(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_updateVarInfoWithParams(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_visitFnBody___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc(lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_IR_ExplicitRC_getVarInfo___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_visitFnBody(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Decl_Inhabited___closed__1;
lean_object* l_Lean_IR_explicitRC___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_17__processVDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_addDec___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExplicitRC_visitFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_mustConsume___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LiveVars_updateJPLiveVarMap(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExplicitRC_getDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_IR_findEnvDecl_x27(x_3, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Lean_IR_Decl_Inhabited___closed__1;
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
return x_7;
}
}
}
lean_object* l_Lean_IR_ExplicitRC_getDecl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitRC_getDecl(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_RBNode_find___main___at_Lean_IR_ExplicitRC_getVarInfo___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
x_9 = 1;
x_10 = l_Bool_DecidableEq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_nat_dec_lt(x_5, x_2);
x_12 = l_Bool_DecidableEq(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
x_1 = x_7;
goto _start;
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
lean_object* _init_l_Lean_IR_ExplicitRC_getVarInfo___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 1;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, 1, x_2);
lean_ctor_set_uint8(x_3, 2, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_ExplicitRC_getVarInfo(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_RBNode_find___main___at_Lean_IR_ExplicitRC_getVarInfo___spec__1(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitRC_getVarInfo___closed__1;
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
lean_object* l_RBNode_find___main___at_Lean_IR_ExplicitRC_getVarInfo___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_ExplicitRC_getVarInfo___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_ExplicitRC_getVarInfo___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_ExplicitRC_getJPParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
x_4 = l_Lean_IR_LocalContext_getJPParams(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = l_Array_empty___closed__1;
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
lean_object* l_Lean_IR_ExplicitRC_getJPParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitRC_getJPParams(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_ExplicitRC_getJPLiveVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_RBNode_find___main___at___private_Init_Lean_Compiler_IR_LiveVars_7__collectJP___spec__1(x_3, x_2);
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
lean_object* l_Lean_IR_ExplicitRC_getJPLiveVars___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitRC_getJPLiveVars(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_Lean_IR_ExplicitRC_mustConsume(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_4 = lean_ctor_get_uint8(x_3, 0);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_3, 2);
lean_dec(x_3);
return x_6;
}
}
}
lean_object* l_Lean_IR_ExplicitRC_mustConsume___boxed(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_IR_ExplicitRC_addInc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_5 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
x_8 = 1;
x_9 = l_Bool_DecidableEq(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_ctor_get_uint8(x_5, 1);
lean_dec(x_5);
x_11 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_3);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_10);
return x_11;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
}
}
lean_object* l_Lean_IR_ExplicitRC_addInc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExplicitRC_addInc(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_ExplicitRC_addDec(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_4 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_5 = lean_ctor_get_uint8(x_4, 1);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = 1;
x_8 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*3 + 1, x_5);
return x_8;
}
}
lean_object* l_Lean_IR_ExplicitRC_addDec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExplicitRC_addDec(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_nat_dec_lt(x_2, x_9);
x_13 = 1;
x_14 = l_Bool_DecidableEq(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; 
x_15 = lean_nat_dec_lt(x_9, x_2);
x_16 = l_Bool_DecidableEq(x_15, x_13);
if (x_16 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_17; 
x_17 = l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_17);
return x_1;
}
}
else
{
lean_object* x_18; 
x_18 = l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_18);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = lean_nat_dec_lt(x_2, x_20);
x_24 = 1;
x_25 = l_Bool_DecidableEq(x_23, x_24);
if (x_25 == 0)
{
uint8_t x_26; uint8_t x_27; 
x_26 = lean_nat_dec_lt(x_20, x_2);
x_27 = l_Bool_DecidableEq(x_26, x_24);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_6);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(x_22, x_2, x_3);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_21);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_6);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(x_19, x_2, x_3);
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_20);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set(x_32, 3, x_22);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_6);
return x_32;
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_1, 2);
x_37 = lean_ctor_get(x_1, 3);
x_38 = lean_nat_dec_lt(x_2, x_35);
x_39 = 1;
x_40 = l_Bool_DecidableEq(x_38, x_39);
if (x_40 == 0)
{
uint8_t x_41; uint8_t x_42; 
x_41 = lean_nat_dec_lt(x_35, x_2);
x_42 = l_Bool_DecidableEq(x_41, x_39);
if (x_42 == 0)
{
lean_dec(x_36);
lean_dec(x_35);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8_t x_43; uint8_t x_44; 
x_43 = l_RBNode_isRed___rarg(x_37);
x_44 = l_Bool_DecidableEq(x_43, x_39);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(x_37, x_2, x_3);
lean_ctor_set(x_1, 3, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(x_37, x_2, x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 3);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_46, 3);
lean_dec(x_50);
x_51 = lean_ctor_get(x_46, 0);
lean_dec(x_51);
x_52 = 0;
lean_ctor_set(x_46, 0, x_48);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_52);
x_53 = 1;
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_46, 1);
x_55 = lean_ctor_get(x_46, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = 0;
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_48);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_56);
x_58 = 1;
lean_ctor_set(x_1, 3, x_57);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_58);
return x_1;
}
}
else
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_48, sizeof(void*)*4);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_46);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_46, 1);
x_62 = lean_ctor_get(x_46, 2);
x_63 = lean_ctor_get(x_46, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_46, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_48);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_48, 0);
x_67 = lean_ctor_get(x_48, 1);
x_68 = lean_ctor_get(x_48, 2);
x_69 = lean_ctor_get(x_48, 3);
x_70 = 1;
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 2, x_36);
lean_ctor_set(x_48, 1, x_35);
lean_ctor_set(x_48, 0, x_34);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_70);
lean_ctor_set(x_46, 3, x_69);
lean_ctor_set(x_46, 2, x_68);
lean_ctor_set(x_46, 1, x_67);
lean_ctor_set(x_46, 0, x_66);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_70);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_48, 0);
x_72 = lean_ctor_get(x_48, 1);
x_73 = lean_ctor_get(x_48, 2);
x_74 = lean_ctor_get(x_48, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_48);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_34);
lean_ctor_set(x_76, 1, x_35);
lean_ctor_set(x_76, 2, x_36);
lean_ctor_set(x_76, 3, x_47);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_46, 3, x_74);
lean_ctor_set(x_46, 2, x_73);
lean_ctor_set(x_46, 1, x_72);
lean_ctor_set(x_46, 0, x_71);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_75);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_46, 1);
x_78 = lean_ctor_get(x_46, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_46);
x_79 = lean_ctor_get(x_48, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_48, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_48, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_48, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 x_83 = x_48;
} else {
 lean_dec_ref(x_48);
 x_83 = lean_box(0);
}
x_84 = 1;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 4, 1);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_34);
lean_ctor_set(x_85, 1, x_35);
lean_ctor_set(x_85, 2, x_36);
lean_ctor_set(x_85, 3, x_47);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_84);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_84);
lean_ctor_set(x_1, 3, x_86);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_46);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_46, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_46, 0);
lean_dec(x_89);
x_90 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_90);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_46, 1);
x_92 = lean_ctor_get(x_46, 2);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_46);
x_93 = 0;
x_94 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_94, 0, x_47);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set(x_94, 3, x_48);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_93);
lean_ctor_set(x_1, 3, x_94);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_46);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_46, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_47);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_47, 0);
x_100 = lean_ctor_get(x_47, 1);
x_101 = lean_ctor_get(x_47, 2);
x_102 = lean_ctor_get(x_47, 3);
x_103 = 1;
lean_ctor_set(x_47, 3, x_99);
lean_ctor_set(x_47, 2, x_36);
lean_ctor_set(x_47, 1, x_35);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_103);
lean_ctor_set(x_46, 0, x_102);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_103);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_47, 0);
x_105 = lean_ctor_get(x_47, 1);
x_106 = lean_ctor_get(x_47, 2);
x_107 = lean_ctor_get(x_47, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_47);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_34);
lean_ctor_set(x_109, 1, x_35);
lean_ctor_set(x_109, 2, x_36);
lean_ctor_set(x_109, 3, x_104);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_46, 0, x_107);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_108);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_46);
x_113 = lean_ctor_get(x_47, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_47, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_47, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_47, 3);
lean_inc(x_116);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_117 = x_47;
} else {
 lean_dec_ref(x_47);
 x_117 = lean_box(0);
}
x_118 = 1;
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(1, 4, 1);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_34);
lean_ctor_set(x_119, 1, x_35);
lean_ctor_set(x_119, 2, x_36);
lean_ctor_set(x_119, 3, x_113);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
x_120 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_110);
lean_ctor_set(x_120, 2, x_111);
lean_ctor_set(x_120, 3, x_112);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_120);
lean_ctor_set(x_1, 2, x_115);
lean_ctor_set(x_1, 1, x_114);
lean_ctor_set(x_1, 0, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_46, 3);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_46);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_46, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_46, 0);
lean_dec(x_124);
x_125 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_46, 1);
x_127 = lean_ctor_get(x_46, 2);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_46);
x_128 = 0;
x_129 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_129, 0, x_47);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_129, 2, x_127);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
lean_ctor_set(x_1, 3, x_129);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
uint8_t x_130; 
x_130 = lean_ctor_get_uint8(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8_t x_131; 
lean_free_object(x_1);
x_131 = !lean_is_exclusive(x_46);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_46, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_46, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_121);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_121, 0);
x_136 = lean_ctor_get(x_121, 1);
x_137 = lean_ctor_get(x_121, 2);
x_138 = lean_ctor_get(x_121, 3);
lean_inc(x_47);
lean_ctor_set(x_121, 3, x_47);
lean_ctor_set(x_121, 2, x_36);
lean_ctor_set(x_121, 1, x_35);
lean_ctor_set(x_121, 0, x_34);
x_139 = !lean_is_exclusive(x_47);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_47, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_47, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_47, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_47, 0);
lean_dec(x_143);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
lean_ctor_set(x_47, 3, x_138);
lean_ctor_set(x_47, 2, x_137);
lean_ctor_set(x_47, 1, x_136);
lean_ctor_set(x_47, 0, x_135);
lean_ctor_set(x_46, 3, x_47);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
else
{
lean_object* x_144; 
lean_dec(x_47);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_135);
lean_ctor_set(x_144, 1, x_136);
lean_ctor_set(x_144, 2, x_137);
lean_ctor_set(x_144, 3, x_138);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_144);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_121, 0);
x_146 = lean_ctor_get(x_121, 1);
x_147 = lean_ctor_get(x_121, 2);
x_148 = lean_ctor_get(x_121, 3);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_121);
lean_inc(x_47);
x_149 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_149, 0, x_34);
lean_ctor_set(x_149, 1, x_35);
lean_ctor_set(x_149, 2, x_36);
lean_ctor_set(x_149, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_150 = x_47;
} else {
 lean_dec_ref(x_47);
 x_150 = lean_box(0);
}
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 4, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_146);
lean_ctor_set(x_151, 2, x_147);
lean_ctor_set(x_151, 3, x_148);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_151);
lean_ctor_set(x_46, 0, x_149);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_152 = lean_ctor_get(x_46, 1);
x_153 = lean_ctor_get(x_46, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_46);
x_154 = lean_ctor_get(x_121, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_121, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_121, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_121, 3);
lean_inc(x_157);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 x_158 = x_121;
} else {
 lean_dec_ref(x_121);
 x_158 = lean_box(0);
}
lean_inc(x_47);
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 4, 1);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_34);
lean_ctor_set(x_159, 1, x_35);
lean_ctor_set(x_159, 2, x_36);
lean_ctor_set(x_159, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_160 = x_47;
} else {
 lean_dec_ref(x_47);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_154);
lean_ctor_set(x_161, 1, x_155);
lean_ctor_set(x_161, 2, x_156);
lean_ctor_set(x_161, 3, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_95);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_152);
lean_ctor_set(x_162, 2, x_153);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_130);
return x_162;
}
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_46);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_46, 3);
lean_dec(x_164);
x_165 = lean_ctor_get(x_46, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_47);
if (x_166 == 0)
{
uint8_t x_167; 
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_130);
x_167 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_167);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_168 = lean_ctor_get(x_47, 0);
x_169 = lean_ctor_get(x_47, 1);
x_170 = lean_ctor_get(x_47, 2);
x_171 = lean_ctor_get(x_47, 3);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_47);
x_172 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_169);
lean_ctor_set(x_172, 2, x_170);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_130);
x_173 = 0;
lean_ctor_set(x_46, 0, x_172);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_173);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_174 = lean_ctor_get(x_46, 1);
x_175 = lean_ctor_get(x_46, 2);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_46);
x_176 = lean_ctor_get(x_47, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_47, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_47, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_47, 3);
lean_inc(x_179);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_180 = x_47;
} else {
 lean_dec_ref(x_47);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 4, 1);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_176);
lean_ctor_set(x_181, 1, x_177);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set(x_181, 3, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_130);
x_182 = 0;
x_183 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_174);
lean_ctor_set(x_183, 2, x_175);
lean_ctor_set(x_183, 3, x_121);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_182);
lean_ctor_set(x_1, 3, x_183);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
}
}
}
}
}
}
}
else
{
uint8_t x_184; uint8_t x_185; 
x_184 = l_RBNode_isRed___rarg(x_34);
x_185 = l_Bool_DecidableEq(x_184, x_39);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(x_34, x_2, x_3);
lean_ctor_set(x_1, 0, x_186);
return x_1;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(x_34, x_2, x_3);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_187, 3);
lean_inc(x_189);
if (lean_obj_tag(x_189) == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_187, 3);
lean_dec(x_191);
x_192 = lean_ctor_get(x_187, 0);
lean_dec(x_192);
x_193 = 0;
lean_ctor_set(x_187, 0, x_189);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_193);
x_194 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_194);
return x_1;
}
else
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; 
x_195 = lean_ctor_get(x_187, 1);
x_196 = lean_ctor_get(x_187, 2);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_187);
x_197 = 0;
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_189);
lean_ctor_set(x_198, 1, x_195);
lean_ctor_set(x_198, 2, x_196);
lean_ctor_set(x_198, 3, x_189);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_197);
x_199 = 1;
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
uint8_t x_200; 
x_200 = lean_ctor_get_uint8(x_189, sizeof(void*)*4);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_187);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_202 = lean_ctor_get(x_187, 1);
x_203 = lean_ctor_get(x_187, 2);
x_204 = lean_ctor_get(x_187, 3);
lean_dec(x_204);
x_205 = lean_ctor_get(x_187, 0);
lean_dec(x_205);
x_206 = !lean_is_exclusive(x_189);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_207 = lean_ctor_get(x_189, 0);
x_208 = lean_ctor_get(x_189, 1);
x_209 = lean_ctor_get(x_189, 2);
x_210 = lean_ctor_get(x_189, 3);
x_211 = 1;
lean_ctor_set(x_189, 3, x_207);
lean_ctor_set(x_189, 2, x_203);
lean_ctor_set(x_189, 1, x_202);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_211);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_210);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_211);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_209);
lean_ctor_set(x_1, 1, x_208);
lean_ctor_set(x_1, 0, x_189);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_212 = lean_ctor_get(x_189, 0);
x_213 = lean_ctor_get(x_189, 1);
x_214 = lean_ctor_get(x_189, 2);
x_215 = lean_ctor_get(x_189, 3);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_189);
x_216 = 1;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_188);
lean_ctor_set(x_217, 1, x_202);
lean_ctor_set(x_217, 2, x_203);
lean_ctor_set(x_217, 3, x_212);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_215);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_216);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_214);
lean_ctor_set(x_1, 1, x_213);
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; 
x_218 = lean_ctor_get(x_187, 1);
x_219 = lean_ctor_get(x_187, 2);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_187);
x_220 = lean_ctor_get(x_189, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_189, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_189, 2);
lean_inc(x_222);
x_223 = lean_ctor_get(x_189, 3);
lean_inc(x_223);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 x_224 = x_189;
} else {
 lean_dec_ref(x_189);
 x_224 = lean_box(0);
}
x_225 = 1;
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(1, 4, 1);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_188);
lean_ctor_set(x_226, 1, x_218);
lean_ctor_set(x_226, 2, x_219);
lean_ctor_set(x_226, 3, x_220);
lean_ctor_set_uint8(x_226, sizeof(void*)*4, x_225);
x_227 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_227, 0, x_223);
lean_ctor_set(x_227, 1, x_35);
lean_ctor_set(x_227, 2, x_36);
lean_ctor_set(x_227, 3, x_37);
lean_ctor_set_uint8(x_227, sizeof(void*)*4, x_225);
lean_ctor_set(x_1, 3, x_227);
lean_ctor_set(x_1, 2, x_222);
lean_ctor_set(x_1, 1, x_221);
lean_ctor_set(x_1, 0, x_226);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
}
else
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_187);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_229 = lean_ctor_get(x_187, 3);
lean_dec(x_229);
x_230 = lean_ctor_get(x_187, 0);
lean_dec(x_230);
x_231 = 0;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_231);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_187, 1);
x_233 = lean_ctor_get(x_187, 2);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_187);
x_234 = 0;
x_235 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_235, 0, x_188);
lean_ctor_set(x_235, 1, x_232);
lean_ctor_set(x_235, 2, x_233);
lean_ctor_set(x_235, 3, x_189);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_234);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
}
}
}
else
{
uint8_t x_236; 
x_236 = lean_ctor_get_uint8(x_188, sizeof(void*)*4);
if (x_236 == 0)
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_187);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_238 = lean_ctor_get(x_187, 1);
x_239 = lean_ctor_get(x_187, 2);
x_240 = lean_ctor_get(x_187, 3);
x_241 = lean_ctor_get(x_187, 0);
lean_dec(x_241);
x_242 = !lean_is_exclusive(x_188);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = 1;
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_243);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_240);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_243);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_239);
lean_ctor_set(x_1, 1, x_238);
lean_ctor_set(x_1, 0, x_188);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; 
x_244 = lean_ctor_get(x_188, 0);
x_245 = lean_ctor_get(x_188, 1);
x_246 = lean_ctor_get(x_188, 2);
x_247 = lean_ctor_get(x_188, 3);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_188);
x_248 = 1;
x_249 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_249, 0, x_244);
lean_ctor_set(x_249, 1, x_245);
lean_ctor_set(x_249, 2, x_246);
lean_ctor_set(x_249, 3, x_247);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_248);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_240);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_248);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_239);
lean_ctor_set(x_1, 1, x_238);
lean_ctor_set(x_1, 0, x_249);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; 
x_250 = lean_ctor_get(x_187, 1);
x_251 = lean_ctor_get(x_187, 2);
x_252 = lean_ctor_get(x_187, 3);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_187);
x_253 = lean_ctor_get(x_188, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_188, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_188, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_188, 3);
lean_inc(x_256);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_257 = x_188;
} else {
 lean_dec_ref(x_188);
 x_257 = lean_box(0);
}
x_258 = 1;
if (lean_is_scalar(x_257)) {
 x_259 = lean_alloc_ctor(1, 4, 1);
} else {
 x_259 = x_257;
}
lean_ctor_set(x_259, 0, x_253);
lean_ctor_set(x_259, 1, x_254);
lean_ctor_set(x_259, 2, x_255);
lean_ctor_set(x_259, 3, x_256);
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_258);
x_260 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_260, 0, x_252);
lean_ctor_set(x_260, 1, x_35);
lean_ctor_set(x_260, 2, x_36);
lean_ctor_set(x_260, 3, x_37);
lean_ctor_set_uint8(x_260, sizeof(void*)*4, x_258);
lean_ctor_set(x_1, 3, x_260);
lean_ctor_set(x_1, 2, x_251);
lean_ctor_set(x_1, 1, x_250);
lean_ctor_set(x_1, 0, x_259);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_187, 3);
lean_inc(x_261);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_187);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_ctor_get(x_187, 3);
lean_dec(x_263);
x_264 = lean_ctor_get(x_187, 0);
lean_dec(x_264);
x_265 = 0;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_265);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_187, 1);
x_267 = lean_ctor_get(x_187, 2);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_187);
x_268 = 0;
x_269 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_269, 0, x_188);
lean_ctor_set(x_269, 1, x_266);
lean_ctor_set(x_269, 2, x_267);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
lean_ctor_set(x_1, 0, x_269);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
uint8_t x_270; 
x_270 = lean_ctor_get_uint8(x_261, sizeof(void*)*4);
if (x_270 == 0)
{
uint8_t x_271; 
lean_free_object(x_1);
x_271 = !lean_is_exclusive(x_187);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_272 = lean_ctor_get(x_187, 1);
x_273 = lean_ctor_get(x_187, 2);
x_274 = lean_ctor_get(x_187, 3);
lean_dec(x_274);
x_275 = lean_ctor_get(x_187, 0);
lean_dec(x_275);
x_276 = !lean_is_exclusive(x_261);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_277 = lean_ctor_get(x_261, 0);
x_278 = lean_ctor_get(x_261, 1);
x_279 = lean_ctor_get(x_261, 2);
x_280 = lean_ctor_get(x_261, 3);
lean_inc(x_188);
lean_ctor_set(x_261, 3, x_277);
lean_ctor_set(x_261, 2, x_273);
lean_ctor_set(x_261, 1, x_272);
lean_ctor_set(x_261, 0, x_188);
x_281 = !lean_is_exclusive(x_188);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_282 = lean_ctor_get(x_188, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_188, 2);
lean_dec(x_283);
x_284 = lean_ctor_get(x_188, 1);
lean_dec(x_284);
x_285 = lean_ctor_get(x_188, 0);
lean_dec(x_285);
lean_ctor_set_uint8(x_261, sizeof(void*)*4, x_236);
lean_ctor_set(x_188, 3, x_37);
lean_ctor_set(x_188, 2, x_36);
lean_ctor_set(x_188, 1, x_35);
lean_ctor_set(x_188, 0, x_280);
lean_ctor_set(x_187, 3, x_188);
lean_ctor_set(x_187, 2, x_279);
lean_ctor_set(x_187, 1, x_278);
lean_ctor_set(x_187, 0, x_261);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_270);
return x_187;
}
else
{
lean_object* x_286; 
lean_dec(x_188);
lean_ctor_set_uint8(x_261, sizeof(void*)*4, x_236);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_280);
lean_ctor_set(x_286, 1, x_35);
lean_ctor_set(x_286, 2, x_36);
lean_ctor_set(x_286, 3, x_37);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_236);
lean_ctor_set(x_187, 3, x_286);
lean_ctor_set(x_187, 2, x_279);
lean_ctor_set(x_187, 1, x_278);
lean_ctor_set(x_187, 0, x_261);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_270);
return x_187;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_287 = lean_ctor_get(x_261, 0);
x_288 = lean_ctor_get(x_261, 1);
x_289 = lean_ctor_get(x_261, 2);
x_290 = lean_ctor_get(x_261, 3);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_261);
lean_inc(x_188);
x_291 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_291, 0, x_188);
lean_ctor_set(x_291, 1, x_272);
lean_ctor_set(x_291, 2, x_273);
lean_ctor_set(x_291, 3, x_287);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_292 = x_188;
} else {
 lean_dec_ref(x_188);
 x_292 = lean_box(0);
}
lean_ctor_set_uint8(x_291, sizeof(void*)*4, x_236);
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 4, 1);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_35);
lean_ctor_set(x_293, 2, x_36);
lean_ctor_set(x_293, 3, x_37);
lean_ctor_set_uint8(x_293, sizeof(void*)*4, x_236);
lean_ctor_set(x_187, 3, x_293);
lean_ctor_set(x_187, 2, x_289);
lean_ctor_set(x_187, 1, x_288);
lean_ctor_set(x_187, 0, x_291);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_270);
return x_187;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_294 = lean_ctor_get(x_187, 1);
x_295 = lean_ctor_get(x_187, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_187);
x_296 = lean_ctor_get(x_261, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_261, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_261, 2);
lean_inc(x_298);
x_299 = lean_ctor_get(x_261, 3);
lean_inc(x_299);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 x_300 = x_261;
} else {
 lean_dec_ref(x_261);
 x_300 = lean_box(0);
}
lean_inc(x_188);
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 4, 1);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_188);
lean_ctor_set(x_301, 1, x_294);
lean_ctor_set(x_301, 2, x_295);
lean_ctor_set(x_301, 3, x_296);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_302 = x_188;
} else {
 lean_dec_ref(x_188);
 x_302 = lean_box(0);
}
lean_ctor_set_uint8(x_301, sizeof(void*)*4, x_236);
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 4, 1);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_299);
lean_ctor_set(x_303, 1, x_35);
lean_ctor_set(x_303, 2, x_36);
lean_ctor_set(x_303, 3, x_37);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_236);
x_304 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_297);
lean_ctor_set(x_304, 2, x_298);
lean_ctor_set(x_304, 3, x_303);
lean_ctor_set_uint8(x_304, sizeof(void*)*4, x_270);
return x_304;
}
}
else
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_187);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_306 = lean_ctor_get(x_187, 3);
lean_dec(x_306);
x_307 = lean_ctor_get(x_187, 0);
lean_dec(x_307);
x_308 = !lean_is_exclusive(x_188);
if (x_308 == 0)
{
uint8_t x_309; 
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_270);
x_309 = 0;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_309);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_310 = lean_ctor_get(x_188, 0);
x_311 = lean_ctor_get(x_188, 1);
x_312 = lean_ctor_get(x_188, 2);
x_313 = lean_ctor_get(x_188, 3);
lean_inc(x_313);
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_188);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_310);
lean_ctor_set(x_314, 1, x_311);
lean_ctor_set(x_314, 2, x_312);
lean_ctor_set(x_314, 3, x_313);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_270);
x_315 = 0;
lean_ctor_set(x_187, 0, x_314);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_315);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; lean_object* x_325; 
x_316 = lean_ctor_get(x_187, 1);
x_317 = lean_ctor_get(x_187, 2);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_187);
x_318 = lean_ctor_get(x_188, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_188, 1);
lean_inc(x_319);
x_320 = lean_ctor_get(x_188, 2);
lean_inc(x_320);
x_321 = lean_ctor_get(x_188, 3);
lean_inc(x_321);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_322 = x_188;
} else {
 lean_dec_ref(x_188);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_318);
lean_ctor_set(x_323, 1, x_319);
lean_ctor_set(x_323, 2, x_320);
lean_ctor_set(x_323, 3, x_321);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_270);
x_324 = 0;
x_325 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_316);
lean_ctor_set(x_325, 2, x_317);
lean_ctor_set(x_325, 3, x_261);
lean_ctor_set_uint8(x_325, sizeof(void*)*4, x_324);
lean_ctor_set(x_1, 0, x_325);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_331; uint8_t x_332; 
x_326 = lean_ctor_get(x_1, 0);
x_327 = lean_ctor_get(x_1, 1);
x_328 = lean_ctor_get(x_1, 2);
x_329 = lean_ctor_get(x_1, 3);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_1);
x_330 = lean_nat_dec_lt(x_2, x_327);
x_331 = 1;
x_332 = l_Bool_DecidableEq(x_330, x_331);
if (x_332 == 0)
{
uint8_t x_333; uint8_t x_334; 
x_333 = lean_nat_dec_lt(x_327, x_2);
x_334 = l_Bool_DecidableEq(x_333, x_331);
if (x_334 == 0)
{
lean_object* x_335; 
lean_dec(x_328);
lean_dec(x_327);
x_335 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_335, 0, x_326);
lean_ctor_set(x_335, 1, x_2);
lean_ctor_set(x_335, 2, x_3);
lean_ctor_set(x_335, 3, x_329);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_6);
return x_335;
}
else
{
uint8_t x_336; uint8_t x_337; 
x_336 = l_RBNode_isRed___rarg(x_329);
x_337 = l_Bool_DecidableEq(x_336, x_331);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; 
x_338 = l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(x_329, x_2, x_3);
x_339 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_339, 0, x_326);
lean_ctor_set(x_339, 1, x_327);
lean_ctor_set(x_339, 2, x_328);
lean_ctor_set(x_339, 3, x_338);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_6);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; 
x_340 = l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(x_329, x_2, x_3);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; 
x_342 = lean_ctor_get(x_340, 3);
lean_inc(x_342);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; 
x_343 = lean_ctor_get(x_340, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_340, 2);
lean_inc(x_344);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_345 = x_340;
} else {
 lean_dec_ref(x_340);
 x_345 = lean_box(0);
}
x_346 = 0;
if (lean_is_scalar(x_345)) {
 x_347 = lean_alloc_ctor(1, 4, 1);
} else {
 x_347 = x_345;
}
lean_ctor_set(x_347, 0, x_342);
lean_ctor_set(x_347, 1, x_343);
lean_ctor_set(x_347, 2, x_344);
lean_ctor_set(x_347, 3, x_342);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_346);
x_348 = 1;
x_349 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_349, 0, x_326);
lean_ctor_set(x_349, 1, x_327);
lean_ctor_set(x_349, 2, x_328);
lean_ctor_set(x_349, 3, x_347);
lean_ctor_set_uint8(x_349, sizeof(void*)*4, x_348);
return x_349;
}
else
{
uint8_t x_350; 
x_350 = lean_ctor_get_uint8(x_342, sizeof(void*)*4);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_351 = lean_ctor_get(x_340, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_340, 2);
lean_inc(x_352);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_353 = x_340;
} else {
 lean_dec_ref(x_340);
 x_353 = lean_box(0);
}
x_354 = lean_ctor_get(x_342, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_342, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_342, 2);
lean_inc(x_356);
x_357 = lean_ctor_get(x_342, 3);
lean_inc(x_357);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 lean_ctor_release(x_342, 2);
 lean_ctor_release(x_342, 3);
 x_358 = x_342;
} else {
 lean_dec_ref(x_342);
 x_358 = lean_box(0);
}
x_359 = 1;
if (lean_is_scalar(x_358)) {
 x_360 = lean_alloc_ctor(1, 4, 1);
} else {
 x_360 = x_358;
}
lean_ctor_set(x_360, 0, x_326);
lean_ctor_set(x_360, 1, x_327);
lean_ctor_set(x_360, 2, x_328);
lean_ctor_set(x_360, 3, x_341);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
if (lean_is_scalar(x_353)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_353;
}
lean_ctor_set(x_361, 0, x_354);
lean_ctor_set(x_361, 1, x_355);
lean_ctor_set(x_361, 2, x_356);
lean_ctor_set(x_361, 3, x_357);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_359);
x_362 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_351);
lean_ctor_set(x_362, 2, x_352);
lean_ctor_set(x_362, 3, x_361);
lean_ctor_set_uint8(x_362, sizeof(void*)*4, x_350);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; 
x_363 = lean_ctor_get(x_340, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_340, 2);
lean_inc(x_364);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_365 = x_340;
} else {
 lean_dec_ref(x_340);
 x_365 = lean_box(0);
}
x_366 = 0;
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(1, 4, 1);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_341);
lean_ctor_set(x_367, 1, x_363);
lean_ctor_set(x_367, 2, x_364);
lean_ctor_set(x_367, 3, x_342);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_366);
x_368 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_368, 0, x_326);
lean_ctor_set(x_368, 1, x_327);
lean_ctor_set(x_368, 2, x_328);
lean_ctor_set(x_368, 3, x_367);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_350);
return x_368;
}
}
}
else
{
uint8_t x_369; 
x_369 = lean_ctor_get_uint8(x_341, sizeof(void*)*4);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_370 = lean_ctor_get(x_340, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_340, 2);
lean_inc(x_371);
x_372 = lean_ctor_get(x_340, 3);
lean_inc(x_372);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_373 = x_340;
} else {
 lean_dec_ref(x_340);
 x_373 = lean_box(0);
}
x_374 = lean_ctor_get(x_341, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_341, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_341, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_341, 3);
lean_inc(x_377);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 x_378 = x_341;
} else {
 lean_dec_ref(x_341);
 x_378 = lean_box(0);
}
x_379 = 1;
if (lean_is_scalar(x_378)) {
 x_380 = lean_alloc_ctor(1, 4, 1);
} else {
 x_380 = x_378;
}
lean_ctor_set(x_380, 0, x_326);
lean_ctor_set(x_380, 1, x_327);
lean_ctor_set(x_380, 2, x_328);
lean_ctor_set(x_380, 3, x_374);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
if (lean_is_scalar(x_373)) {
 x_381 = lean_alloc_ctor(1, 4, 1);
} else {
 x_381 = x_373;
}
lean_ctor_set(x_381, 0, x_377);
lean_ctor_set(x_381, 1, x_370);
lean_ctor_set(x_381, 2, x_371);
lean_ctor_set(x_381, 3, x_372);
lean_ctor_set_uint8(x_381, sizeof(void*)*4, x_379);
x_382 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_375);
lean_ctor_set(x_382, 2, x_376);
lean_ctor_set(x_382, 3, x_381);
lean_ctor_set_uint8(x_382, sizeof(void*)*4, x_369);
return x_382;
}
else
{
lean_object* x_383; 
x_383 = lean_ctor_get(x_340, 3);
lean_inc(x_383);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; lean_object* x_389; 
x_384 = lean_ctor_get(x_340, 1);
lean_inc(x_384);
x_385 = lean_ctor_get(x_340, 2);
lean_inc(x_385);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_386 = x_340;
} else {
 lean_dec_ref(x_340);
 x_386 = lean_box(0);
}
x_387 = 0;
if (lean_is_scalar(x_386)) {
 x_388 = lean_alloc_ctor(1, 4, 1);
} else {
 x_388 = x_386;
}
lean_ctor_set(x_388, 0, x_341);
lean_ctor_set(x_388, 1, x_384);
lean_ctor_set(x_388, 2, x_385);
lean_ctor_set(x_388, 3, x_383);
lean_ctor_set_uint8(x_388, sizeof(void*)*4, x_387);
x_389 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_389, 0, x_326);
lean_ctor_set(x_389, 1, x_327);
lean_ctor_set(x_389, 2, x_328);
lean_ctor_set(x_389, 3, x_388);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_369);
return x_389;
}
else
{
uint8_t x_390; 
x_390 = lean_ctor_get_uint8(x_383, sizeof(void*)*4);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_391 = lean_ctor_get(x_340, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_340, 2);
lean_inc(x_392);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_393 = x_340;
} else {
 lean_dec_ref(x_340);
 x_393 = lean_box(0);
}
x_394 = lean_ctor_get(x_383, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_383, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_383, 2);
lean_inc(x_396);
x_397 = lean_ctor_get(x_383, 3);
lean_inc(x_397);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 lean_ctor_release(x_383, 2);
 lean_ctor_release(x_383, 3);
 x_398 = x_383;
} else {
 lean_dec_ref(x_383);
 x_398 = lean_box(0);
}
lean_inc(x_341);
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_326);
lean_ctor_set(x_399, 1, x_327);
lean_ctor_set(x_399, 2, x_328);
lean_ctor_set(x_399, 3, x_341);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 x_400 = x_341;
} else {
 lean_dec_ref(x_341);
 x_400 = lean_box(0);
}
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_369);
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 4, 1);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_394);
lean_ctor_set(x_401, 1, x_395);
lean_ctor_set(x_401, 2, x_396);
lean_ctor_set(x_401, 3, x_397);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_369);
if (lean_is_scalar(x_393)) {
 x_402 = lean_alloc_ctor(1, 4, 1);
} else {
 x_402 = x_393;
}
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_391);
lean_ctor_set(x_402, 2, x_392);
lean_ctor_set(x_402, 3, x_401);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_390);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; 
x_403 = lean_ctor_get(x_340, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_340, 2);
lean_inc(x_404);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_405 = x_340;
} else {
 lean_dec_ref(x_340);
 x_405 = lean_box(0);
}
x_406 = lean_ctor_get(x_341, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_341, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_341, 2);
lean_inc(x_408);
x_409 = lean_ctor_get(x_341, 3);
lean_inc(x_409);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 x_410 = x_341;
} else {
 lean_dec_ref(x_341);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_406);
lean_ctor_set(x_411, 1, x_407);
lean_ctor_set(x_411, 2, x_408);
lean_ctor_set(x_411, 3, x_409);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_390);
x_412 = 0;
if (lean_is_scalar(x_405)) {
 x_413 = lean_alloc_ctor(1, 4, 1);
} else {
 x_413 = x_405;
}
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_403);
lean_ctor_set(x_413, 2, x_404);
lean_ctor_set(x_413, 3, x_383);
lean_ctor_set_uint8(x_413, sizeof(void*)*4, x_412);
x_414 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_414, 0, x_326);
lean_ctor_set(x_414, 1, x_327);
lean_ctor_set(x_414, 2, x_328);
lean_ctor_set(x_414, 3, x_413);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_390);
return x_414;
}
}
}
}
}
}
}
else
{
uint8_t x_415; uint8_t x_416; 
x_415 = l_RBNode_isRed___rarg(x_326);
x_416 = l_Bool_DecidableEq(x_415, x_331);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; 
x_417 = l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(x_326, x_2, x_3);
x_418 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_327);
lean_ctor_set(x_418, 2, x_328);
lean_ctor_set(x_418, 3, x_329);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_6);
return x_418;
}
else
{
lean_object* x_419; lean_object* x_420; 
x_419 = l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(x_326, x_2, x_3);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; 
x_421 = lean_ctor_get(x_419, 3);
lean_inc(x_421);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; 
x_422 = lean_ctor_get(x_419, 1);
lean_inc(x_422);
x_423 = lean_ctor_get(x_419, 2);
lean_inc(x_423);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_424 = x_419;
} else {
 lean_dec_ref(x_419);
 x_424 = lean_box(0);
}
x_425 = 0;
if (lean_is_scalar(x_424)) {
 x_426 = lean_alloc_ctor(1, 4, 1);
} else {
 x_426 = x_424;
}
lean_ctor_set(x_426, 0, x_421);
lean_ctor_set(x_426, 1, x_422);
lean_ctor_set(x_426, 2, x_423);
lean_ctor_set(x_426, 3, x_421);
lean_ctor_set_uint8(x_426, sizeof(void*)*4, x_425);
x_427 = 1;
x_428 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_327);
lean_ctor_set(x_428, 2, x_328);
lean_ctor_set(x_428, 3, x_329);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
return x_428;
}
else
{
uint8_t x_429; 
x_429 = lean_ctor_get_uint8(x_421, sizeof(void*)*4);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_430 = lean_ctor_get(x_419, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_419, 2);
lean_inc(x_431);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_432 = x_419;
} else {
 lean_dec_ref(x_419);
 x_432 = lean_box(0);
}
x_433 = lean_ctor_get(x_421, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_421, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_421, 2);
lean_inc(x_435);
x_436 = lean_ctor_get(x_421, 3);
lean_inc(x_436);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 lean_ctor_release(x_421, 2);
 lean_ctor_release(x_421, 3);
 x_437 = x_421;
} else {
 lean_dec_ref(x_421);
 x_437 = lean_box(0);
}
x_438 = 1;
if (lean_is_scalar(x_437)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_437;
}
lean_ctor_set(x_439, 0, x_420);
lean_ctor_set(x_439, 1, x_430);
lean_ctor_set(x_439, 2, x_431);
lean_ctor_set(x_439, 3, x_433);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
if (lean_is_scalar(x_432)) {
 x_440 = lean_alloc_ctor(1, 4, 1);
} else {
 x_440 = x_432;
}
lean_ctor_set(x_440, 0, x_436);
lean_ctor_set(x_440, 1, x_327);
lean_ctor_set(x_440, 2, x_328);
lean_ctor_set(x_440, 3, x_329);
lean_ctor_set_uint8(x_440, sizeof(void*)*4, x_438);
x_441 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_434);
lean_ctor_set(x_441, 2, x_435);
lean_ctor_set(x_441, 3, x_440);
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_429);
return x_441;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; lean_object* x_446; lean_object* x_447; 
x_442 = lean_ctor_get(x_419, 1);
lean_inc(x_442);
x_443 = lean_ctor_get(x_419, 2);
lean_inc(x_443);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_444 = x_419;
} else {
 lean_dec_ref(x_419);
 x_444 = lean_box(0);
}
x_445 = 0;
if (lean_is_scalar(x_444)) {
 x_446 = lean_alloc_ctor(1, 4, 1);
} else {
 x_446 = x_444;
}
lean_ctor_set(x_446, 0, x_420);
lean_ctor_set(x_446, 1, x_442);
lean_ctor_set(x_446, 2, x_443);
lean_ctor_set(x_446, 3, x_421);
lean_ctor_set_uint8(x_446, sizeof(void*)*4, x_445);
x_447 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_327);
lean_ctor_set(x_447, 2, x_328);
lean_ctor_set(x_447, 3, x_329);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_429);
return x_447;
}
}
}
else
{
uint8_t x_448; 
x_448 = lean_ctor_get_uint8(x_420, sizeof(void*)*4);
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_449 = lean_ctor_get(x_419, 1);
lean_inc(x_449);
x_450 = lean_ctor_get(x_419, 2);
lean_inc(x_450);
x_451 = lean_ctor_get(x_419, 3);
lean_inc(x_451);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_452 = x_419;
} else {
 lean_dec_ref(x_419);
 x_452 = lean_box(0);
}
x_453 = lean_ctor_get(x_420, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_420, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_420, 2);
lean_inc(x_455);
x_456 = lean_ctor_get(x_420, 3);
lean_inc(x_456);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_457 = x_420;
} else {
 lean_dec_ref(x_420);
 x_457 = lean_box(0);
}
x_458 = 1;
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(1, 4, 1);
} else {
 x_459 = x_457;
}
lean_ctor_set(x_459, 0, x_453);
lean_ctor_set(x_459, 1, x_454);
lean_ctor_set(x_459, 2, x_455);
lean_ctor_set(x_459, 3, x_456);
lean_ctor_set_uint8(x_459, sizeof(void*)*4, x_458);
if (lean_is_scalar(x_452)) {
 x_460 = lean_alloc_ctor(1, 4, 1);
} else {
 x_460 = x_452;
}
lean_ctor_set(x_460, 0, x_451);
lean_ctor_set(x_460, 1, x_327);
lean_ctor_set(x_460, 2, x_328);
lean_ctor_set(x_460, 3, x_329);
lean_ctor_set_uint8(x_460, sizeof(void*)*4, x_458);
x_461 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_449);
lean_ctor_set(x_461, 2, x_450);
lean_ctor_set(x_461, 3, x_460);
lean_ctor_set_uint8(x_461, sizeof(void*)*4, x_448);
return x_461;
}
else
{
lean_object* x_462; 
x_462 = lean_ctor_get(x_419, 3);
lean_inc(x_462);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; lean_object* x_467; lean_object* x_468; 
x_463 = lean_ctor_get(x_419, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_419, 2);
lean_inc(x_464);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_465 = x_419;
} else {
 lean_dec_ref(x_419);
 x_465 = lean_box(0);
}
x_466 = 0;
if (lean_is_scalar(x_465)) {
 x_467 = lean_alloc_ctor(1, 4, 1);
} else {
 x_467 = x_465;
}
lean_ctor_set(x_467, 0, x_420);
lean_ctor_set(x_467, 1, x_463);
lean_ctor_set(x_467, 2, x_464);
lean_ctor_set(x_467, 3, x_462);
lean_ctor_set_uint8(x_467, sizeof(void*)*4, x_466);
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_327);
lean_ctor_set(x_468, 2, x_328);
lean_ctor_set(x_468, 3, x_329);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_448);
return x_468;
}
else
{
uint8_t x_469; 
x_469 = lean_ctor_get_uint8(x_462, sizeof(void*)*4);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_470 = lean_ctor_get(x_419, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_419, 2);
lean_inc(x_471);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_472 = x_419;
} else {
 lean_dec_ref(x_419);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_462, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_462, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_462, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_462, 3);
lean_inc(x_476);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 lean_ctor_release(x_462, 2);
 lean_ctor_release(x_462, 3);
 x_477 = x_462;
} else {
 lean_dec_ref(x_462);
 x_477 = lean_box(0);
}
lean_inc(x_420);
if (lean_is_scalar(x_477)) {
 x_478 = lean_alloc_ctor(1, 4, 1);
} else {
 x_478 = x_477;
}
lean_ctor_set(x_478, 0, x_420);
lean_ctor_set(x_478, 1, x_470);
lean_ctor_set(x_478, 2, x_471);
lean_ctor_set(x_478, 3, x_473);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_479 = x_420;
} else {
 lean_dec_ref(x_420);
 x_479 = lean_box(0);
}
lean_ctor_set_uint8(x_478, sizeof(void*)*4, x_448);
if (lean_is_scalar(x_479)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_479;
}
lean_ctor_set(x_480, 0, x_476);
lean_ctor_set(x_480, 1, x_327);
lean_ctor_set(x_480, 2, x_328);
lean_ctor_set(x_480, 3, x_329);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_448);
if (lean_is_scalar(x_472)) {
 x_481 = lean_alloc_ctor(1, 4, 1);
} else {
 x_481 = x_472;
}
lean_ctor_set(x_481, 0, x_478);
lean_ctor_set(x_481, 1, x_474);
lean_ctor_set(x_481, 2, x_475);
lean_ctor_set(x_481, 3, x_480);
lean_ctor_set_uint8(x_481, sizeof(void*)*4, x_469);
return x_481;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; lean_object* x_492; lean_object* x_493; 
x_482 = lean_ctor_get(x_419, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_419, 2);
lean_inc(x_483);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_484 = x_419;
} else {
 lean_dec_ref(x_419);
 x_484 = lean_box(0);
}
x_485 = lean_ctor_get(x_420, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_420, 1);
lean_inc(x_486);
x_487 = lean_ctor_get(x_420, 2);
lean_inc(x_487);
x_488 = lean_ctor_get(x_420, 3);
lean_inc(x_488);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_489 = x_420;
} else {
 lean_dec_ref(x_420);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 4, 1);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_485);
lean_ctor_set(x_490, 1, x_486);
lean_ctor_set(x_490, 2, x_487);
lean_ctor_set(x_490, 3, x_488);
lean_ctor_set_uint8(x_490, sizeof(void*)*4, x_469);
x_491 = 0;
if (lean_is_scalar(x_484)) {
 x_492 = lean_alloc_ctor(1, 4, 1);
} else {
 x_492 = x_484;
}
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_482);
lean_ctor_set(x_492, 2, x_483);
lean_ctor_set(x_492, 3, x_462);
lean_ctor_set_uint8(x_492, sizeof(void*)*4, x_491);
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_327);
lean_ctor_set(x_493, 2, x_328);
lean_ctor_set(x_493, 3, x_329);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_469);
return x_493;
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_RBNode_insert___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_4 = l_RBNode_isRed___rarg(x_1);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(x_1, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_RBNode_ins___main___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__2(x_1, x_2, x_3);
x_9 = l_RBNode_setBlack___rarg(x_8);
return x_9;
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_4 = l_Lean_IR_CtorInfo_isRef(x_3);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 2);
x_9 = l_RBNode_find___main___at_Lean_IR_ExplicitRC_getVarInfo___spec__1(x_8, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
lean_ctor_set_uint8(x_10, 0, x_12);
x_13 = l_RBNode_insert___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__1(x_8, x_2, x_10);
lean_ctor_set(x_1, 2, x_13);
return x_1;
}
else
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get_uint8(x_10, 1);
x_15 = lean_ctor_get_uint8(x_10, 2);
lean_dec(x_10);
x_16 = 0;
x_17 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_17, 0, x_16);
lean_ctor_set_uint8(x_17, 1, x_14);
lean_ctor_set_uint8(x_17, 2, x_15);
x_18 = l_RBNode_insert___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__1(x_8, x_2, x_17);
lean_ctor_set(x_1, 2, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
x_23 = lean_ctor_get(x_1, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_24 = l_RBNode_find___main___at_Lean_IR_ExplicitRC_getVarInfo___spec__1(x_21, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get_uint8(x_26, 1);
x_28 = lean_ctor_get_uint8(x_26, 2);
if (lean_is_exclusive(x_26)) {
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = 0;
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 0, 3);
} else {
 x_31 = x_29;
}
lean_ctor_set_uint8(x_31, 0, x_30);
lean_ctor_set_uint8(x_31, 1, x_27);
lean_ctor_set_uint8(x_31, 2, x_28);
x_32 = l_RBNode_insert___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__1(x_21, x_2, x_31);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_20);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_22);
lean_ctor_set(x_33, 4, x_23);
return x_33;
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
lean_object* l___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_RBNode_findCore___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
x_9 = 1;
x_10 = l_Bool_DecidableEq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_nat_dec_lt(x_5, x_2);
x_12 = l_Bool_DecidableEq(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_6);
lean_inc(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_6);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
x_1 = x_7;
goto _start;
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
lean_object* l_RBNode_fold___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 3);
x_9 = l_RBNode_fold___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__2(x_1, x_2, x_3, x_4, x_6);
x_10 = l_RBNode_findCore___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__1(x_2, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = l_Lean_IR_ExplicitRC_mustConsume(x_1, x_7);
x_12 = 1;
x_13 = l_Bool_DecidableEq(x_11, x_12);
if (x_13 == 0)
{
x_4 = x_9;
x_5 = x_8;
goto _start;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_7);
x_16 = lean_ctor_get_uint8(x_15, 1);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(1u);
lean_inc(x_7);
x_18 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_9);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 1, x_16);
x_4 = x_18;
x_5 = x_8;
goto _start;
}
}
else
{
uint8_t x_20; 
lean_dec(x_10);
x_20 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_20 == 0)
{
x_4 = x_9;
x_5 = x_8;
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_7);
x_23 = lean_ctor_get_uint8(x_22, 1);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = 1;
lean_inc(x_7);
x_26 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_9);
lean_ctor_set_uint8(x_26, sizeof(void*)*3, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*3 + 1, x_23);
x_4 = x_26;
x_5 = x_8;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Init_Lean_Compiler_IR_LiveVars_6__accumulate___closed__1;
x_6 = l_RBNode_fold___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__2(x_1, x_3, x_5, x_4, x_2);
return x_6;
}
}
lean_object* l_RBNode_findCore___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_findCore___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_RBNode_fold___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_RBNode_fold___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
uint8_t l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
x_9 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_10 = l_Lean_IR_Arg_Inhabited;
x_11 = lean_array_get(x_10, x_1, x_9);
lean_dec(x_9);
x_12 = l_Lean_IR_Arg_beq(x_11, x_2);
lean_dec(x_11);
if (x_12 == 0)
{
x_4 = x_8;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
x_14 = 1;
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = 0;
return x_15;
}
}
}
uint8_t l___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_IR_Arg_Inhabited;
x_4 = lean_array_get(x_3, x_1, x_2);
lean_inc(x_2);
x_5 = l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc___spec__1(x_1, x_4, x_2, x_2);
lean_dec(x_2);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_IR_Arg_Inhabited;
x_6 = lean_array_get(x_5, x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_nat_dec_eq(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_apply_1(x_3, x_4);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
return x_8;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
else
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = 0;
return x_13;
}
}
}
uint8_t l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___lambda__1___boxed), 4, 3);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_3);
x_5 = lean_array_get_size(x_2);
lean_dec(x_2);
lean_inc(x_5);
x_6 = l_Nat_anyAux___main(x_4, x_5, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_5, x_8);
x_10 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
x_11 = l_Lean_IR_Arg_Inhabited;
x_12 = lean_array_get(x_11, x_3, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_nat_dec_eq(x_2, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_10);
x_5 = x_9;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_IR_paramInh;
x_17 = lean_array_get(x_16, x_1, x_10);
lean_dec(x_10);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*2);
lean_dec(x_17);
if (x_18 == 0)
{
x_5 = x_9;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
x_20 = 1;
return x_20;
}
}
}
else
{
lean_dec(x_10);
x_5 = x_9;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_5);
x_22 = 0;
return x_22;
}
}
}
uint8_t l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
lean_inc(x_4);
x_5 = l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___spec__2(x_1, x_2, x_3, x_4, x_4);
lean_dec(x_4);
return x_5;
}
}
uint8_t l___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___spec__1(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_Arg_Inhabited;
x_7 = lean_array_get(x_6, x_1, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_nat_dec_eq(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_10 == 0)
{
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_13 = lean_apply_1(x_3, x_4);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
x_15 = 1;
x_16 = l_Bool_DecidableEq(x_14, x_15);
if (x_16 == 0)
{
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
return x_18;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_5);
return x_5;
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___lambda__1___boxed), 5, 3);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
lean_closure_set(x_4, 2, x_3);
x_5 = lean_array_get_size(x_2);
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_7 = l_Nat_foldAux___main___rarg(x_4, x_5, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_IR_Arg_Inhabited;
x_8 = lean_array_get(x_7, x_1, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_59; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_IR_ExplicitRC_getVarInfo(x_2, x_9);
x_59 = lean_ctor_get_uint8(x_10, 0);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_5);
x_60 = 1;
x_11 = x_60;
goto block_58;
}
else
{
uint8_t x_61; 
x_61 = l___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc(x_1, x_5);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = 1;
x_11 = x_62;
goto block_58;
}
else
{
uint8_t x_63; 
x_63 = 0;
x_11 = x_63;
goto block_58;
}
}
block_58:
{
uint8_t x_12; uint8_t x_13; 
x_12 = 1;
x_13 = l_Bool_DecidableEq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_9);
x_14 = l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions(x_9, x_1, x_3);
x_15 = lean_ctor_get_uint8(x_10, 2);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = l_String_Iterator_extract___closed__1;
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_18, x_19);
x_21 = l_Bool_DecidableEq(x_20, x_12);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_ctor_get_uint8(x_10, 1);
lean_dec(x_10);
x_23 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_6);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_23, sizeof(void*)*3 + 1, x_22);
return x_23;
}
else
{
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
return x_6;
}
}
else
{
lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_14, x_24);
x_26 = l_Bool_DecidableEq(x_25, x_12);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; 
x_27 = lean_ctor_get_uint8(x_10, 1);
lean_dec(x_10);
x_28 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_14);
lean_ctor_set(x_28, 2, x_6);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_28, sizeof(void*)*3 + 1, x_27);
return x_28;
}
else
{
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
return x_6;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l___private_Init_Lean_Compiler_IR_LiveVars_6__accumulate___closed__1;
lean_inc(x_9);
x_30 = l_RBNode_findCore___main___rarg(x_29, x_4, x_9);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; uint8_t x_32; 
lean_inc(x_9);
x_31 = l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux(x_9, x_1, x_3);
x_32 = l_Bool_DecidableEq(x_31, x_12);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_sub(x_14, x_33);
lean_dec(x_14);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_eq(x_34, x_35);
x_37 = l_Bool_DecidableEq(x_36, x_12);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; 
x_38 = lean_ctor_get_uint8(x_10, 1);
lean_dec(x_10);
x_39 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_39, 0, x_9);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_6);
lean_ctor_set_uint8(x_39, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_39, sizeof(void*)*3 + 1, x_38);
return x_39;
}
else
{
lean_dec(x_34);
lean_dec(x_10);
lean_dec(x_9);
return x_6;
}
}
else
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_dec_eq(x_14, x_40);
x_42 = l_Bool_DecidableEq(x_41, x_12);
if (x_42 == 0)
{
uint8_t x_43; lean_object* x_44; 
x_43 = lean_ctor_get_uint8(x_10, 1);
lean_dec(x_10);
x_44 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_14);
lean_ctor_set(x_44, 2, x_6);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_44, sizeof(void*)*3 + 1, x_43);
return x_44;
}
else
{
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
return x_6;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_1);
x_45 = l_String_Iterator_extract___closed__1;
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_sub(x_14, x_46);
lean_dec(x_14);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_eq(x_47, x_48);
x_50 = l_Bool_DecidableEq(x_49, x_12);
if (x_50 == 0)
{
uint8_t x_51; lean_object* x_52; 
x_51 = lean_ctor_get_uint8(x_10, 1);
lean_dec(x_10);
x_52 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_52, 0, x_9);
lean_ctor_set(x_52, 1, x_47);
lean_ctor_set(x_52, 2, x_6);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_52, sizeof(void*)*3 + 1, x_51);
return x_52;
}
else
{
lean_dec(x_47);
lean_dec(x_10);
lean_dec(x_9);
return x_6;
}
}
else
{
lean_object* x_53; uint8_t x_54; uint8_t x_55; 
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_nat_dec_eq(x_14, x_53);
x_55 = l_Bool_DecidableEq(x_54, x_12);
if (x_55 == 0)
{
uint8_t x_56; lean_object* x_57; 
x_56 = lean_ctor_get_uint8(x_10, 1);
lean_dec(x_10);
x_57 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_57, 0, x_9);
lean_ctor_set(x_57, 1, x_14);
lean_ctor_set(x_57, 2, x_6);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_57, sizeof(void*)*3 + 1, x_56);
return x_57;
}
else
{
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
return x_6;
}
}
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___lambda__1___boxed), 6, 4);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_5);
x_7 = lean_array_get_size(x_2);
lean_dec(x_2);
lean_inc(x_7);
x_8 = l_Nat_foldAux___main___rarg(x_6, x_7, x_7, x_4);
lean_dec(x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
x_12 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
x_13 = l_Lean_IR_Arg_Inhabited;
x_14 = lean_array_get(x_13, x_3, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_nat_dec_eq(x_2, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_17 == 0)
{
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_19; 
x_19 = lean_nat_add(x_7, x_10);
lean_dec(x_7);
x_6 = x_11;
x_7 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_Lean_IR_paramInh;
x_22 = lean_array_get(x_21, x_1, x_12);
lean_dec(x_12);
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*2);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_String_Iterator_extract___closed__1;
if (x_24 == 0)
{
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_26; 
x_26 = lean_nat_add(x_7, x_10);
lean_dec(x_7);
x_6 = x_11;
x_7 = x_26;
goto _start;
}
}
else
{
uint8_t x_28; 
x_28 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_28 == 0)
{
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_30; 
x_30 = lean_nat_add(x_7, x_10);
lean_dec(x_7);
x_6 = x_11;
x_7 = x_30;
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
else
{
lean_dec(x_6);
return x_7;
}
}
}
uint8_t l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_IR_paramInh;
x_4 = lean_array_get(x_3, x_1, x_2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_array_get_size(x_3);
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_7 = l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__3(x_1, x_2, x_3, x_4, x_5, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
uint8_t l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_5, x_8);
x_10 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
x_11 = l_Lean_IR_Arg_Inhabited;
x_12 = lean_array_get(x_11, x_3, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_nat_dec_eq(x_2, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_10);
x_5 = x_9;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_IR_paramInh;
x_17 = lean_array_get(x_16, x_1, x_10);
lean_dec(x_10);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*2);
lean_dec(x_17);
if (x_18 == 0)
{
x_5 = x_9;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
x_20 = 1;
return x_20;
}
}
}
else
{
lean_dec(x_10);
x_5 = x_9;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_5);
x_22 = 0;
return x_22;
}
}
}
uint8_t l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
lean_inc(x_4);
x_5 = l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__5(x_1, x_2, x_3, x_4, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_7, x_11);
x_13 = lean_nat_sub(x_6, x_7);
lean_dec(x_7);
x_14 = l_Lean_IR_Arg_Inhabited;
x_15 = lean_array_get(x_14, x_3, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_69; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_IR_ExplicitRC_getVarInfo(x_2, x_16);
x_69 = lean_ctor_get_uint8(x_17, 0);
if (x_69 == 0)
{
uint8_t x_70; 
lean_dec(x_13);
x_70 = 1;
x_18 = x_70;
goto block_68;
}
else
{
uint8_t x_71; 
x_71 = l___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc(x_3, x_13);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = 1;
x_18 = x_72;
goto block_68;
}
else
{
uint8_t x_73; 
x_73 = 0;
x_18 = x_73;
goto block_68;
}
}
block_68:
{
uint8_t x_19; uint8_t x_20; 
x_19 = 1;
x_20 = l_Bool_DecidableEq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
lean_inc(x_1);
x_21 = l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__2(x_1, x_16, x_3);
x_22 = lean_ctor_get_uint8(x_17, 2);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_String_Iterator_extract___closed__1;
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_24 = lean_nat_sub(x_21, x_11);
lean_dec(x_21);
x_25 = lean_nat_dec_eq(x_24, x_9);
x_26 = l_Bool_DecidableEq(x_25, x_19);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; 
x_27 = lean_ctor_get_uint8(x_17, 1);
lean_dec(x_17);
x_28 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_8);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_28, sizeof(void*)*3 + 1, x_27);
x_7 = x_12;
x_8 = x_28;
goto _start;
}
else
{
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
x_7 = x_12;
goto _start;
}
}
else
{
uint8_t x_31; uint8_t x_32; 
x_31 = lean_nat_dec_eq(x_21, x_9);
x_32 = l_Bool_DecidableEq(x_31, x_19);
if (x_32 == 0)
{
uint8_t x_33; lean_object* x_34; 
x_33 = lean_ctor_get_uint8(x_17, 1);
lean_dec(x_17);
x_34 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_34, 0, x_16);
lean_ctor_set(x_34, 1, x_21);
lean_ctor_set(x_34, 2, x_8);
lean_ctor_set_uint8(x_34, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_34, sizeof(void*)*3 + 1, x_33);
x_7 = x_12;
x_8 = x_34;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_16);
x_7 = x_12;
goto _start;
}
}
}
else
{
lean_object* x_37; 
x_37 = l_RBNode_findCore___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__1(x_4, x_16);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; uint8_t x_39; 
x_38 = l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__4(x_1, x_16, x_3);
x_39 = l_Bool_DecidableEq(x_38, x_19);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_40 = lean_nat_sub(x_21, x_11);
lean_dec(x_21);
x_41 = lean_nat_dec_eq(x_40, x_9);
x_42 = l_Bool_DecidableEq(x_41, x_19);
if (x_42 == 0)
{
uint8_t x_43; lean_object* x_44; 
x_43 = lean_ctor_get_uint8(x_17, 1);
lean_dec(x_17);
x_44 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_44, 0, x_16);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_8);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_44, sizeof(void*)*3 + 1, x_43);
x_7 = x_12;
x_8 = x_44;
goto _start;
}
else
{
lean_dec(x_40);
lean_dec(x_17);
lean_dec(x_16);
x_7 = x_12;
goto _start;
}
}
else
{
uint8_t x_47; uint8_t x_48; 
x_47 = lean_nat_dec_eq(x_21, x_9);
x_48 = l_Bool_DecidableEq(x_47, x_19);
if (x_48 == 0)
{
uint8_t x_49; lean_object* x_50; 
x_49 = lean_ctor_get_uint8(x_17, 1);
lean_dec(x_17);
x_50 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_50, 0, x_16);
lean_ctor_set(x_50, 1, x_21);
lean_ctor_set(x_50, 2, x_8);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 1, x_49);
x_7 = x_12;
x_8 = x_50;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_16);
x_7 = x_12;
goto _start;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_37);
x_53 = l_String_Iterator_extract___closed__1;
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_54 = lean_nat_sub(x_21, x_11);
lean_dec(x_21);
x_55 = lean_nat_dec_eq(x_54, x_9);
x_56 = l_Bool_DecidableEq(x_55, x_19);
if (x_56 == 0)
{
uint8_t x_57; lean_object* x_58; 
x_57 = lean_ctor_get_uint8(x_17, 1);
lean_dec(x_17);
x_58 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_58, 0, x_16);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_8);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_58, sizeof(void*)*3 + 1, x_57);
x_7 = x_12;
x_8 = x_58;
goto _start;
}
else
{
lean_dec(x_54);
lean_dec(x_17);
lean_dec(x_16);
x_7 = x_12;
goto _start;
}
}
else
{
uint8_t x_61; uint8_t x_62; 
x_61 = lean_nat_dec_eq(x_21, x_9);
x_62 = l_Bool_DecidableEq(x_61, x_19);
if (x_62 == 0)
{
uint8_t x_63; lean_object* x_64; 
x_63 = lean_ctor_get_uint8(x_17, 1);
lean_dec(x_17);
x_64 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_64, 0, x_16);
lean_ctor_set(x_64, 1, x_21);
lean_ctor_set(x_64, 2, x_8);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_19);
lean_ctor_set_uint8(x_64, sizeof(void*)*3 + 1, x_63);
x_7 = x_12;
x_8 = x_64;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_16);
x_7 = x_12;
goto _start;
}
}
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
x_7 = x_12;
goto _start;
}
}
}
else
{
lean_dec(x_13);
x_7 = x_12;
goto _start;
}
}
else
{
lean_dec(x_7);
lean_dec(x_1);
return x_8;
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_array_get_size(x_3);
lean_inc(x_7);
x_8 = l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__6(x_1, x_2, x_3, x_5, x_6, x_7, x_7, x_4);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_8__addIncBefore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__1(x_3, x_1, x_2, x_4, x_5);
return x_6;
}
}
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__2___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__4(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Compiler_IR_RC_8__addIncBefore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_9__addDecAfterFullApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
x_12 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
x_13 = l_Lean_IR_Arg_Inhabited;
x_14 = lean_array_get(x_13, x_2, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_IR_ExplicitRC_mustConsume(x_1, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_17 == 0)
{
lean_dec(x_15);
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_15);
x_20 = lean_ctor_get_uint8(x_19, 1);
lean_dec(x_19);
x_21 = 1;
x_22 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_7);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_20);
x_6 = x_11;
x_7 = x_22;
goto _start;
}
}
else
{
uint8_t x_24; 
x_24 = l___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc(x_2, x_12);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_25 == 0)
{
lean_dec(x_15);
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_27 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_15);
x_28 = lean_ctor_get_uint8(x_27, 1);
lean_dec(x_27);
x_29 = 1;
x_30 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_10);
lean_ctor_set(x_30, 2, x_7);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*3 + 1, x_28);
x_6 = x_11;
x_7 = x_30;
goto _start;
}
}
else
{
uint8_t x_32; 
x_32 = l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_5__isBorrowParam___spec__1(x_3, x_15, x_2);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_33 == 0)
{
lean_dec(x_15);
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; 
x_35 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_15);
x_36 = lean_ctor_get_uint8(x_35, 1);
lean_dec(x_35);
x_37 = 1;
x_38 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_10);
lean_ctor_set(x_38, 2, x_7);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*3 + 1, x_36);
x_6 = x_11;
x_7 = x_38;
goto _start;
}
}
else
{
lean_object* x_40; 
x_40 = l_RBNode_findCore___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__1(x_4, x_15);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; uint8_t x_42; 
x_41 = 1;
x_42 = l_Bool_DecidableEq(x_32, x_41);
if (x_42 == 0)
{
lean_dec(x_15);
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_44 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_15);
x_45 = lean_ctor_get_uint8(x_44, 1);
lean_dec(x_44);
x_46 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_46, 0, x_15);
lean_ctor_set(x_46, 1, x_10);
lean_ctor_set(x_46, 2, x_7);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_41);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 1, x_45);
x_6 = x_11;
x_7 = x_46;
goto _start;
}
}
else
{
uint8_t x_48; 
lean_dec(x_40);
x_48 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_48 == 0)
{
lean_dec(x_15);
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_50 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_15);
x_51 = lean_ctor_get_uint8(x_50, 1);
lean_dec(x_50);
x_52 = 1;
x_53 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_53, 0, x_15);
lean_ctor_set(x_53, 1, x_10);
lean_ctor_set(x_53, 2, x_7);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*3 + 1, x_51);
x_6 = x_11;
x_7 = x_53;
goto _start;
}
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
else
{
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_9__addDecAfterFullApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_2);
lean_inc(x_6);
x_7 = l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_9__addDecAfterFullApp___spec__1(x_1, x_2, x_3, x_5, x_6, x_6, x_4);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_9__addDecAfterFullApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_9__addDecAfterFullApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_9__addDecAfterFullApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Compiler_IR_RC_9__addDecAfterFullApp(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_5, x_9);
x_11 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
x_12 = l_Lean_IR_Arg_Inhabited;
x_13 = lean_array_get(x_12, x_2, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_nat_dec_eq(x_1, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_16 == 0)
{
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_18; 
x_18 = lean_nat_add(x_6, x_9);
lean_dec(x_6);
x_5 = x_10;
x_6 = x_18;
goto _start;
}
}
else
{
uint8_t x_20; 
x_20 = l_String_Iterator_extract___closed__1;
if (x_20 == 0)
{
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_22; 
x_22 = lean_nat_add(x_6, x_9);
lean_dec(x_6);
x_5 = x_10;
x_6 = x_22;
goto _start;
}
}
}
else
{
x_5 = x_10;
goto _start;
}
}
else
{
lean_dec(x_5);
return x_6;
}
}
}
uint8_t l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_2);
x_4 = l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___closed__1;
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_6 = l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__3(x_1, x_2, x_4, x_3, x_3, x_5);
lean_dec(x_3);
return x_6;
}
}
uint8_t l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
lean_dec(x_2);
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = 0;
return x_8;
}
}
}
uint8_t l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_array_get_size(x_1);
lean_inc(x_2);
x_3 = l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__5(x_2, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__4___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
x_12 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
x_13 = l_Lean_IR_Arg_Inhabited;
x_14 = lean_array_get(x_13, x_2, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_68; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_15);
x_68 = lean_ctor_get_uint8(x_16, 0);
if (x_68 == 0)
{
uint8_t x_69; 
lean_dec(x_12);
x_69 = 1;
x_17 = x_69;
goto block_67;
}
else
{
uint8_t x_70; 
x_70 = l___private_Init_Lean_Compiler_IR_RC_3__isFirstOcc(x_2, x_12);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = 1;
x_17 = x_71;
goto block_67;
}
else
{
uint8_t x_72; 
x_72 = 0;
x_17 = x_72;
goto block_67;
}
}
block_67:
{
uint8_t x_18; uint8_t x_19; 
x_18 = 1;
x_19 = l_Bool_DecidableEq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2(x_15, x_2);
x_21 = lean_ctor_get_uint8(x_16, 2);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_String_Iterator_extract___closed__1;
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_23 = lean_nat_sub(x_20, x_10);
lean_dec(x_20);
x_24 = lean_nat_dec_eq(x_23, x_8);
x_25 = l_Bool_DecidableEq(x_24, x_18);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
x_26 = lean_ctor_get_uint8(x_16, 1);
lean_dec(x_16);
x_27 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_7);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_27, sizeof(void*)*3 + 1, x_26);
x_6 = x_11;
x_7 = x_27;
goto _start;
}
else
{
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
x_6 = x_11;
goto _start;
}
}
else
{
uint8_t x_30; uint8_t x_31; 
x_30 = lean_nat_dec_eq(x_20, x_8);
x_31 = l_Bool_DecidableEq(x_30, x_18);
if (x_31 == 0)
{
uint8_t x_32; lean_object* x_33; 
x_32 = lean_ctor_get_uint8(x_16, 1);
lean_dec(x_16);
x_33 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_20);
lean_ctor_set(x_33, 2, x_7);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_33, sizeof(void*)*3 + 1, x_32);
x_6 = x_11;
x_7 = x_33;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
x_6 = x_11;
goto _start;
}
}
}
else
{
lean_object* x_36; 
x_36 = l_RBNode_findCore___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__1(x_3, x_15);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; uint8_t x_38; 
x_37 = l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__4___rarg(x_2);
x_38 = l_Bool_DecidableEq(x_37, x_18);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; uint8_t x_41; 
x_39 = lean_nat_sub(x_20, x_10);
lean_dec(x_20);
x_40 = lean_nat_dec_eq(x_39, x_8);
x_41 = l_Bool_DecidableEq(x_40, x_18);
if (x_41 == 0)
{
uint8_t x_42; lean_object* x_43; 
x_42 = lean_ctor_get_uint8(x_16, 1);
lean_dec(x_16);
x_43 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_7);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_43, sizeof(void*)*3 + 1, x_42);
x_6 = x_11;
x_7 = x_43;
goto _start;
}
else
{
lean_dec(x_39);
lean_dec(x_16);
lean_dec(x_15);
x_6 = x_11;
goto _start;
}
}
else
{
uint8_t x_46; uint8_t x_47; 
x_46 = lean_nat_dec_eq(x_20, x_8);
x_47 = l_Bool_DecidableEq(x_46, x_18);
if (x_47 == 0)
{
uint8_t x_48; lean_object* x_49; 
x_48 = lean_ctor_get_uint8(x_16, 1);
lean_dec(x_16);
x_49 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_49, 0, x_15);
lean_ctor_set(x_49, 1, x_20);
lean_ctor_set(x_49, 2, x_7);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_49, sizeof(void*)*3 + 1, x_48);
x_6 = x_11;
x_7 = x_49;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
x_6 = x_11;
goto _start;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_36);
x_52 = l_String_Iterator_extract___closed__1;
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; uint8_t x_55; 
x_53 = lean_nat_sub(x_20, x_10);
lean_dec(x_20);
x_54 = lean_nat_dec_eq(x_53, x_8);
x_55 = l_Bool_DecidableEq(x_54, x_18);
if (x_55 == 0)
{
uint8_t x_56; lean_object* x_57; 
x_56 = lean_ctor_get_uint8(x_16, 1);
lean_dec(x_16);
x_57 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_57, 0, x_15);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_57, 2, x_7);
lean_ctor_set_uint8(x_57, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_57, sizeof(void*)*3 + 1, x_56);
x_6 = x_11;
x_7 = x_57;
goto _start;
}
else
{
lean_dec(x_53);
lean_dec(x_16);
lean_dec(x_15);
x_6 = x_11;
goto _start;
}
}
else
{
uint8_t x_60; uint8_t x_61; 
x_60 = lean_nat_dec_eq(x_20, x_8);
x_61 = l_Bool_DecidableEq(x_60, x_18);
if (x_61 == 0)
{
uint8_t x_62; lean_object* x_63; 
x_62 = lean_ctor_get_uint8(x_16, 1);
lean_dec(x_16);
x_63 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_63, 0, x_15);
lean_ctor_set(x_63, 1, x_20);
lean_ctor_set(x_63, 2, x_7);
lean_ctor_set_uint8(x_63, sizeof(void*)*3, x_18);
lean_ctor_set_uint8(x_63, sizeof(void*)*3 + 1, x_62);
x_6 = x_11;
x_7 = x_63;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
x_6 = x_11;
goto _start;
}
}
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_15);
x_6 = x_11;
goto _start;
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
else
{
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_array_get_size(x_2);
x_6 = l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___closed__1;
lean_inc(x_5);
x_7 = l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__6(x_1, x_2, x_4, x_6, x_5, x_5, x_3);
lean_dec(x_5);
return x_7;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__1(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Nat_anyAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__5(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__4___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__4___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Compiler_IR_RC_4__isBorrowParamAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldAux___main___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
if (x_11 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_IR_IRType_isObj(x_12);
lean_dec(x_12);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_16 == 0)
{
lean_dec(x_10);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_10);
x_19 = lean_ctor_get_uint8(x_18, 1);
lean_dec(x_18);
x_20 = 1;
x_21 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_6);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*3 + 1, x_19);
x_5 = x_14;
x_6 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; 
x_23 = l_RBNode_findCore___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__1(x_3, x_10);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; uint8_t x_25; 
x_24 = 1;
x_25 = l_Bool_DecidableEq(x_15, x_24);
if (x_25 == 0)
{
lean_dec(x_10);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_10);
x_28 = lean_ctor_get_uint8(x_27, 1);
lean_dec(x_27);
x_29 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_13);
lean_ctor_set(x_29, 2, x_6);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*3 + 1, x_28);
x_5 = x_14;
x_6 = x_29;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_23);
x_31 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_31 == 0)
{
lean_dec(x_10);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_33 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_10);
x_34 = lean_ctor_get_uint8(x_33, 1);
lean_dec(x_33);
x_35 = 1;
x_36 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_36, 0, x_10);
lean_ctor_set(x_36, 1, x_13);
lean_ctor_set(x_36, 2, x_6);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*3 + 1, x_34);
x_5 = x_14;
x_6 = x_36;
goto _start;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_12);
x_38 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_38 == 0)
{
lean_dec(x_10);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; 
x_40 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_10);
x_41 = lean_ctor_get_uint8(x_40, 1);
lean_dec(x_40);
x_42 = 1;
x_43 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_43, 0, x_10);
lean_ctor_set(x_43, 1, x_13);
lean_ctor_set(x_43, 2, x_6);
lean_ctor_set_uint8(x_43, sizeof(void*)*3, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*3 + 1, x_41);
x_5 = x_14;
x_6 = x_43;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams___spec__1(x_1, x_2, x_4, x_2, x_5, x_3);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
uint8_t l___private_Init_Lean_Compiler_IR_RC_12__isPersistent(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_Array_isEmpty___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_12__isPersistent___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Compiler_IR_RC_12__isPersistent(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l___private_Init_Lean_Compiler_IR_RC_13__consumeExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_RBNode_find___main___at_Lean_IR_ExplicitRC_getVarInfo___spec__1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get_uint8(x_6, 2);
lean_dec(x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_13__consumeExpr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Compiler_IR_RC_13__consumeExpr(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l___private_Init_Lean_Compiler_IR_RC_14__isScalarBoxedInTaggedPtr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 4);
x_8 = lean_nat_dec_eq(x_7, x_4);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_nat_dec_eq(x_10, x_4);
return x_11;
}
}
}
case 11:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
x_14 = l_Lean_maxSmallNat;
x_15 = lean_nat_dec_le(x_13, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
default: 
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_14__isScalarBoxedInTaggedPtr___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Compiler_IR_RC_14__isScalarBoxedInTaggedPtr(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_15__updateVarInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = l_Lean_IR_IRType_isObj(x_3);
x_8 = l___private_Init_Lean_Compiler_IR_RC_12__isPersistent(x_4);
x_9 = l___private_Init_Lean_Compiler_IR_RC_13__consumeExpr(x_6, x_4);
if (x_7 == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_11, 0, x_10);
lean_ctor_set_uint8(x_11, 1, x_8);
lean_ctor_set_uint8(x_11, 2, x_9);
x_12 = l_RBNode_insert___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__1(x_6, x_2, x_11);
lean_ctor_set(x_1, 2, x_12);
return x_1;
}
else
{
uint8_t x_13; 
x_13 = l___private_Init_Lean_Compiler_IR_RC_14__isScalarBoxedInTaggedPtr(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_14, 0, x_7);
lean_ctor_set_uint8(x_14, 1, x_8);
lean_ctor_set_uint8(x_14, 2, x_9);
x_15 = l_RBNode_insert___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__1(x_6, x_2, x_14);
lean_ctor_set(x_1, 2, x_15);
return x_1;
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_17, 0, x_16);
lean_ctor_set_uint8(x_17, 1, x_8);
lean_ctor_set_uint8(x_17, 2, x_9);
x_18 = l_RBNode_insert___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__1(x_6, x_2, x_17);
lean_ctor_set(x_1, 2, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
x_23 = lean_ctor_get(x_1, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_24 = l_Lean_IR_IRType_isObj(x_3);
x_25 = l___private_Init_Lean_Compiler_IR_RC_12__isPersistent(x_4);
x_26 = l___private_Init_Lean_Compiler_IR_RC_13__consumeExpr(x_21, x_4);
if (x_24 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = 0;
x_28 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_28, 0, x_27);
lean_ctor_set_uint8(x_28, 1, x_25);
lean_ctor_set_uint8(x_28, 2, x_26);
x_29 = l_RBNode_insert___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__1(x_21, x_2, x_28);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_29);
lean_ctor_set(x_30, 3, x_22);
lean_ctor_set(x_30, 4, x_23);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = l___private_Init_Lean_Compiler_IR_RC_14__isScalarBoxedInTaggedPtr(x_4);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_32, 0, x_24);
lean_ctor_set_uint8(x_32, 1, x_25);
lean_ctor_set_uint8(x_32, 2, x_26);
x_33 = l_RBNode_insert___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__1(x_21, x_2, x_32);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_20);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_22);
lean_ctor_set(x_34, 4, x_23);
return x_34;
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = 0;
x_36 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, 1, x_25);
lean_ctor_set_uint8(x_36, 2, x_26);
x_37 = l_RBNode_insert___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__1(x_21, x_2, x_36);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_19);
lean_ctor_set(x_38, 1, x_20);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_22);
lean_ctor_set(x_38, 4, x_23);
return x_38;
}
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_15__updateVarInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Compiler_IR_RC_15__updateVarInfo(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_16__addDecIfNeeded(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_IR_ExplicitRC_mustConsume(x_1, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_6 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_8 = lean_ctor_get_uint8(x_7, 1);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = 1;
x_11 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_3);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_8);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = l_RBNode_findCore___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__1(x_4, x_2);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; uint8_t x_14; 
x_13 = 1;
x_14 = l_Bool_DecidableEq(x_5, x_13);
if (x_14 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_16 = lean_ctor_get_uint8(x_15, 1);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_3);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_13);
lean_ctor_set_uint8(x_18, sizeof(void*)*3 + 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_19 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_21 = lean_ctor_get_uint8(x_20, 1);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = 1;
x_24 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_3);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*3 + 1, x_21);
return x_24;
}
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_16__addDecIfNeeded___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Compiler_IR_RC_16__addDecIfNeeded(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_17__processVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_6);
lean_inc(x_4);
x_7 = l_Lean_IR_LiveVars_collectExpr(x_4, x_6);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc(x_2);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set(x_9, 3, x_5);
x_10 = l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__1(x_1, x_8, x_9, x_6);
lean_dec(x_6);
lean_dec(x_8);
x_11 = l_RBNode_erase___at___private_Init_Lean_Compiler_IR_LiveVars_8__bindVar___spec__1(x_2, x_7);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_4, 2);
lean_inc(x_13);
lean_inc(x_2);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_14, 3, x_5);
x_15 = l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__1(x_1, x_13, x_14, x_6);
lean_dec(x_6);
lean_dec(x_13);
x_16 = l_RBNode_erase___at___private_Init_Lean_Compiler_IR_LiveVars_8__bindVar___spec__1(x_2, x_7);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_18);
x_19 = l___private_Init_Lean_Compiler_IR_RC_16__addDecIfNeeded(x_1, x_18, x_5, x_6);
lean_dec(x_6);
x_20 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_18);
lean_dec(x_18);
x_21 = lean_ctor_get_uint8(x_20, 2);
lean_dec(x_20);
x_22 = 1;
x_23 = l_Bool_DecidableEq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_2);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_4);
lean_ctor_set(x_24, 3, x_19);
x_25 = l_RBNode_erase___at___private_Init_Lean_Compiler_IR_LiveVars_8__bindVar___spec__1(x_2, x_7);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = l_Lean_IR_ExplicitRC_getVarInfo(x_1, x_2);
x_29 = lean_ctor_get_uint8(x_28, 1);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_31 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_22);
lean_ctor_set_uint8(x_31, sizeof(void*)*3 + 1, x_29);
lean_inc(x_2);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_4);
lean_ctor_set(x_32, 3, x_31);
x_33 = l_RBNode_erase___at___private_Init_Lean_Compiler_IR_LiveVars_8__bindVar___spec__1(x_2, x_7);
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_2);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_3);
lean_ctor_set(x_35, 2, x_4);
lean_ctor_set(x_35, 3, x_19);
x_36 = l_RBNode_erase___at___private_Init_Lean_Compiler_IR_LiveVars_8__bindVar___spec__1(x_2, x_7);
lean_dec(x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
case 4:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
x_39 = l___private_Init_Lean_Compiler_IR_RC_16__addDecIfNeeded(x_1, x_38, x_5, x_6);
lean_dec(x_6);
lean_inc(x_2);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_3);
lean_ctor_set(x_40, 2, x_4);
lean_ctor_set(x_40, 3, x_39);
x_41 = l_RBNode_erase___at___private_Init_Lean_Compiler_IR_LiveVars_8__bindVar___spec__1(x_2, x_7);
lean_dec(x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
case 5:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_4, 2);
lean_inc(x_43);
x_44 = l___private_Init_Lean_Compiler_IR_RC_16__addDecIfNeeded(x_1, x_43, x_5, x_6);
lean_dec(x_6);
lean_inc(x_2);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_2);
lean_ctor_set(x_45, 1, x_3);
lean_ctor_set(x_45, 2, x_4);
lean_ctor_set(x_45, 3, x_44);
x_46 = l_RBNode_erase___at___private_Init_Lean_Compiler_IR_LiveVars_8__bindVar___spec__1(x_2, x_7);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
case 6:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_4, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
x_50 = l_Lean_IR_ExplicitRC_getDecl(x_1, x_48);
lean_dec(x_48);
x_51 = l_Lean_IR_Decl_params(x_50);
lean_dec(x_50);
x_52 = l___private_Init_Lean_Compiler_IR_RC_9__addDecAfterFullApp(x_1, x_49, x_51, x_5, x_6);
lean_inc(x_2);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 2, x_4);
lean_ctor_set(x_53, 3, x_52);
x_54 = l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__1(x_51, x_1, x_49, x_53, x_6);
lean_dec(x_6);
lean_dec(x_49);
x_55 = l_RBNode_erase___at___private_Init_Lean_Compiler_IR_LiveVars_8__bindVar___spec__1(x_2, x_7);
lean_dec(x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
case 7:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_4, 1);
lean_inc(x_57);
lean_inc(x_2);
x_58 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_3);
lean_ctor_set(x_58, 2, x_4);
lean_ctor_set(x_58, 3, x_5);
x_59 = l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__1(x_1, x_57, x_58, x_6);
lean_dec(x_6);
lean_dec(x_57);
x_60 = l_RBNode_erase___at___private_Init_Lean_Compiler_IR_LiveVars_8__bindVar___spec__1(x_2, x_7);
lean_dec(x_2);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
case 8:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_4, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_4, 1);
lean_inc(x_63);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_array_push(x_63, x_64);
lean_inc(x_2);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_2);
lean_ctor_set(x_66, 1, x_3);
lean_ctor_set(x_66, 2, x_4);
lean_ctor_set(x_66, 3, x_5);
x_67 = l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__1(x_1, x_65, x_66, x_6);
lean_dec(x_6);
lean_dec(x_65);
x_68 = l_RBNode_erase___at___private_Init_Lean_Compiler_IR_LiveVars_8__bindVar___spec__1(x_2, x_7);
lean_dec(x_2);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
case 10:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_4, 0);
lean_inc(x_70);
x_71 = l___private_Init_Lean_Compiler_IR_RC_16__addDecIfNeeded(x_1, x_70, x_5, x_6);
lean_dec(x_6);
lean_inc(x_2);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_2);
lean_ctor_set(x_72, 1, x_3);
lean_ctor_set(x_72, 2, x_4);
lean_ctor_set(x_72, 3, x_71);
x_73 = l_RBNode_erase___at___private_Init_Lean_Compiler_IR_LiveVars_8__bindVar___spec__1(x_2, x_7);
lean_dec(x_2);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
default: 
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_6);
lean_inc(x_2);
x_75 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_75, 0, x_2);
lean_ctor_set(x_75, 1, x_3);
lean_ctor_set(x_75, 2, x_4);
lean_ctor_set(x_75, 3, x_5);
x_76 = l_RBNode_erase___at___private_Init_Lean_Compiler_IR_LiveVars_8__bindVar___spec__1(x_2, x_7);
lean_dec(x_2);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
lean_object* l___private_Init_Lean_Compiler_IR_RC_17__processVDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Compiler_IR_RC_17__processVDecl(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitRC_updateVarInfoWithParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = l_Lean_IR_IRType_isObj(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_dec(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
if (x_11 == 0)
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_14 = 0;
x_15 = 1;
x_16 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_16, 0, x_10);
lean_ctor_set_uint8(x_16, 1, x_14);
lean_ctor_set_uint8(x_16, 2, x_15);
x_17 = l_RBNode_insert___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__1(x_4, x_8, x_16);
x_3 = x_13;
x_4 = x_17;
goto _start;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_20, 0, x_10);
lean_ctor_set_uint8(x_20, 1, x_19);
lean_ctor_set_uint8(x_20, 2, x_19);
x_21 = l_RBNode_insert___at___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo___spec__1(x_4, x_8, x_20);
x_3 = x_13;
x_4 = x_21;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_ExplicitRC_updateVarInfoWithParams(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitRC_updateVarInfoWithParams___spec__1(x_2, x_2, x_5, x_4);
lean_ctor_set(x_1, 2, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitRC_updateVarInfoWithParams___spec__1(x_2, x_2, x_12, x_9);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
return x_14;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExplicitRC_updateVarInfoWithParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_ExplicitRC_updateVarInfoWithParams___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_ExplicitRC_updateVarInfoWithParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitRC_updateVarInfoWithParams(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExplicitRC_visitFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l___private_Init_Lean_Compiler_IR_RC_1__updateRefUsingCtorInfo(x_1, x_2, x_16);
lean_inc(x_18);
x_19 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_17, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Init_Lean_Compiler_IR_LiveVars_6__accumulate___closed__1;
x_23 = l_RBNode_fold___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__2(x_18, x_21, x_22, x_20, x_3);
lean_dec(x_21);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
x_25 = x_24;
x_26 = lean_array_fset(x_13, x_4, x_25);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_10, 0);
lean_inc(x_28);
lean_inc(x_1);
x_29 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_28, x_1);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Init_Lean_Compiler_IR_LiveVars_6__accumulate___closed__1;
x_33 = l_RBNode_fold___main___at___private_Init_Lean_Compiler_IR_RC_2__addDecForAlt___spec__2(x_1, x_31, x_32, x_30, x_3);
lean_dec(x_31);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = x_34;
x_36 = lean_array_fset(x_13, x_4, x_35);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_36;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_ExplicitRC_visitFnBody___main(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Init_Lean_Compiler_IR_RC_15__updateVarInfo(x_2, x_3, x_4, x_5);
lean_inc(x_7);
x_8 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Init_Lean_Compiler_IR_RC_17__processVDecl(x_7, x_3, x_4, x_5, x_9, x_10);
lean_dec(x_7);
return x_11;
}
case 1:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_17 = l_Lean_IR_ExplicitRC_updateVarInfoWithParams(x_2, x_14);
x_18 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_15, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams___spec__1(x_2, x_14, x_20, x_14, x_21, x_19);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
lean_inc(x_13);
x_25 = l_Lean_IR_LiveVars_updateJPLiveVarMap(x_13, x_14, x_22, x_24);
lean_ctor_set(x_2, 3, x_25);
x_26 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_16, x_2);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_1, 3, x_28);
lean_ctor_set(x_1, 2, x_22);
lean_ctor_set(x_26, 0, x_1);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_1, 3, x_29);
lean_ctor_set(x_1, 2, x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_2, 3);
x_36 = lean_ctor_get(x_2, 4);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_2);
lean_inc(x_22);
lean_inc(x_13);
x_37 = l_Lean_IR_LiveVars_updateJPLiveVarMap(x_13, x_14, x_22, x_35);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_37);
lean_ctor_set(x_38, 4, x_36);
x_39 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_16, x_38);
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
lean_ctor_set(x_1, 3, x_40);
lean_ctor_set(x_1, 2, x_22);
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get(x_1, 1);
x_46 = lean_ctor_get(x_1, 2);
x_47 = lean_ctor_get(x_1, 3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_1);
lean_inc(x_2);
x_48 = l_Lean_IR_ExplicitRC_updateVarInfoWithParams(x_2, x_45);
x_49 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_46, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams___spec__1(x_2, x_45, x_51, x_45, x_52, x_50);
lean_dec(x_51);
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 4);
lean_inc(x_58);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_59 = x_2;
} else {
 lean_dec_ref(x_2);
 x_59 = lean_box(0);
}
lean_inc(x_53);
lean_inc(x_44);
x_60 = l_Lean_IR_LiveVars_updateJPLiveVarMap(x_44, x_45, x_53, x_57);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 5, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set(x_61, 1, x_55);
lean_ctor_set(x_61, 2, x_56);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_58);
x_62 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_47, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_66, 0, x_44);
lean_ctor_set(x_66, 1, x_45);
lean_ctor_set(x_66, 2, x_53);
lean_ctor_set(x_66, 3, x_63);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
case 4:
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_1);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_1, 0);
x_70 = lean_ctor_get(x_1, 3);
x_71 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_70, x_2);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_69);
lean_ctor_set(x_1, 3, x_73);
x_75 = lean_box(0);
x_76 = l_RBNode_insert___at_Lean_IR_mkLiveVarSet___spec__1(x_74, x_69, x_75);
lean_ctor_set(x_71, 1, x_76);
lean_ctor_set(x_71, 0, x_1);
return x_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_71, 0);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_71);
lean_inc(x_69);
lean_ctor_set(x_1, 3, x_77);
x_79 = lean_box(0);
x_80 = l_RBNode_insert___at_Lean_IR_mkLiveVarSet___spec__1(x_78, x_69, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_82 = lean_ctor_get(x_1, 0);
x_83 = lean_ctor_get(x_1, 1);
x_84 = lean_ctor_get(x_1, 2);
x_85 = lean_ctor_get(x_1, 3);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_1);
x_86 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_85, x_2);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
lean_inc(x_82);
x_90 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_90, 0, x_82);
lean_ctor_set(x_90, 1, x_83);
lean_ctor_set(x_90, 2, x_84);
lean_ctor_set(x_90, 3, x_87);
x_91 = lean_box(0);
x_92 = l_RBNode_insert___at_Lean_IR_mkLiveVarSet___spec__1(x_88, x_82, x_91);
if (lean_is_scalar(x_89)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_89;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
case 5:
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_1);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = lean_ctor_get(x_1, 0);
x_96 = lean_ctor_get(x_1, 5);
x_97 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_96, x_2);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_95);
lean_ctor_set(x_1, 5, x_99);
x_101 = lean_box(0);
x_102 = l_RBNode_insert___at_Lean_IR_mkLiveVarSet___spec__1(x_100, x_95, x_101);
lean_ctor_set(x_97, 1, x_102);
lean_ctor_set(x_97, 0, x_1);
return x_97;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_97, 0);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_97);
lean_inc(x_95);
lean_ctor_set(x_1, 5, x_103);
x_105 = lean_box(0);
x_106 = l_RBNode_insert___at_Lean_IR_mkLiveVarSet___spec__1(x_104, x_95, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_1);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_108 = lean_ctor_get(x_1, 0);
x_109 = lean_ctor_get(x_1, 1);
x_110 = lean_ctor_get(x_1, 2);
x_111 = lean_ctor_get(x_1, 3);
x_112 = lean_ctor_get(x_1, 4);
x_113 = lean_ctor_get(x_1, 5);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_1);
x_114 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_113, x_2);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
lean_inc(x_108);
x_118 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_118, 0, x_108);
lean_ctor_set(x_118, 1, x_109);
lean_ctor_set(x_118, 2, x_110);
lean_ctor_set(x_118, 3, x_111);
lean_ctor_set(x_118, 4, x_112);
lean_ctor_set(x_118, 5, x_115);
x_119 = lean_box(0);
x_120 = l_RBNode_insert___at_Lean_IR_mkLiveVarSet___spec__1(x_116, x_108, x_119);
if (lean_is_scalar(x_117)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_117;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
case 9:
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_1);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_1, 1);
x_124 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_123, x_2);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_124, 0);
lean_ctor_set(x_1, 1, x_126);
lean_ctor_set(x_124, 0, x_1);
return x_124;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_124, 0);
x_128 = lean_ctor_get(x_124, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_124);
lean_ctor_set(x_1, 1, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_1);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_130 = lean_ctor_get(x_1, 0);
x_131 = lean_ctor_get(x_1, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_1);
x_132 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_131, x_2);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
x_136 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_136, 0, x_130);
lean_ctor_set(x_136, 1, x_133);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
return x_137;
}
}
case 10:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_138 = lean_ctor_get(x_1, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_1, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_1, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_1, 3);
lean_inc(x_141);
x_142 = lean_ctor_get(x_2, 3);
lean_inc(x_142);
x_143 = lean_box(0);
lean_inc(x_1);
x_144 = l_Lean_IR_LiveVars_collectFnBody___main(x_1, x_142, x_143);
x_145 = !lean_is_exclusive(x_1);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_146 = lean_ctor_get(x_1, 3);
lean_dec(x_146);
x_147 = lean_ctor_get(x_1, 2);
lean_dec(x_147);
x_148 = lean_ctor_get(x_1, 1);
lean_dec(x_148);
x_149 = lean_ctor_get(x_1, 0);
lean_dec(x_149);
x_150 = lean_unsigned_to_nat(0u);
lean_inc(x_139);
x_151 = l_Array_umapMAux___main___at_Lean_IR_ExplicitRC_visitFnBody___main___spec__1(x_2, x_139, x_144, x_150, x_141);
lean_ctor_set(x_1, 3, x_151);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_1);
lean_ctor_set(x_152, 1, x_144);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_1);
x_153 = lean_unsigned_to_nat(0u);
lean_inc(x_139);
x_154 = l_Array_umapMAux___main___at_Lean_IR_ExplicitRC_visitFnBody___main___spec__1(x_2, x_139, x_144, x_153, x_141);
x_155 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_155, 0, x_138);
lean_ctor_set(x_155, 1, x_139);
lean_ctor_set(x_155, 2, x_140);
lean_ctor_set(x_155, 3, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_144);
return x_156;
}
}
case 11:
{
lean_object* x_157; 
x_157 = lean_ctor_get(x_1, 0);
lean_inc(x_157);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; uint8_t x_173; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec(x_157);
x_159 = l_Lean_IR_ExplicitRC_getVarInfo(x_2, x_158);
lean_dec(x_2);
x_173 = lean_ctor_get_uint8(x_159, 0);
if (x_173 == 0)
{
uint8_t x_174; 
x_174 = 0;
x_160 = x_174;
goto block_172;
}
else
{
uint8_t x_175; 
x_175 = lean_ctor_get_uint8(x_159, 2);
if (x_175 == 0)
{
x_160 = x_173;
goto block_172;
}
else
{
uint8_t x_176; 
x_176 = 0;
x_160 = x_176;
goto block_172;
}
}
block_172:
{
uint8_t x_161; uint8_t x_162; 
x_161 = 1;
x_162 = l_Bool_DecidableEq(x_160, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_159);
x_163 = l_Lean_IR_mkLiveVarSet(x_158);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_1);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
else
{
lean_object* x_165; uint8_t x_166; 
lean_inc(x_158);
x_165 = l_Lean_IR_mkLiveVarSet(x_158);
x_166 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_166 == 0)
{
uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get_uint8(x_159, 1);
lean_dec(x_159);
x_168 = lean_unsigned_to_nat(1u);
x_169 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_169, 0, x_158);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_169, 2, x_1);
lean_ctor_set_uint8(x_169, sizeof(void*)*3, x_161);
lean_ctor_set_uint8(x_169, sizeof(void*)*3 + 1, x_167);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_165);
return x_170;
}
else
{
lean_object* x_171; 
lean_dec(x_159);
lean_dec(x_158);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_1);
lean_ctor_set(x_171, 1, x_165);
return x_171;
}
}
}
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_2);
x_177 = lean_box(0);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_1);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
case 12:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_179 = lean_ctor_get(x_1, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_1, 1);
lean_inc(x_180);
x_181 = l_Lean_IR_ExplicitRC_getJPLiveVars(x_2, x_179);
x_182 = l_Lean_IR_ExplicitRC_getJPParams(x_2, x_179);
lean_dec(x_179);
x_183 = l___private_Init_Lean_Compiler_IR_RC_7__addIncBeforeAux___at___private_Init_Lean_Compiler_IR_RC_8__addIncBefore___spec__1(x_182, x_2, x_180, x_1, x_181);
lean_dec(x_181);
lean_dec(x_180);
x_184 = lean_ctor_get(x_2, 3);
lean_inc(x_184);
lean_dec(x_2);
x_185 = lean_box(0);
lean_inc(x_183);
x_186 = l_Lean_IR_LiveVars_collectFnBody___main(x_183, x_184, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_183);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
default: 
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_2);
x_188 = lean_box(0);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_1);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExplicitRC_visitFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at_Lean_IR_ExplicitRC_visitFnBody___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_IR_ExplicitRC_visitFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_ExplicitRC_visitDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_7);
lean_ctor_set(x_8, 4, x_7);
x_9 = l_Lean_IR_ExplicitRC_updateVarInfoWithParams(x_8, x_5);
lean_inc(x_9);
x_10 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_6, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams___spec__1(x_9, x_5, x_12, x_5, x_13, x_11);
lean_dec(x_12);
lean_dec(x_9);
lean_ctor_set(x_3, 3, x_14);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_ctor_get(x_3, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_19);
lean_ctor_set(x_20, 4, x_19);
x_21 = l_Lean_IR_ExplicitRC_updateVarInfoWithParams(x_20, x_16);
lean_inc(x_21);
x_22 = l_Lean_IR_ExplicitRC_visitFnBody___main(x_18, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_iterateMAux___main___at___private_Init_Lean_Compiler_IR_RC_11__addDecForDeadParams___spec__1(x_21, x_16, x_24, x_16, x_25, x_23);
lean_dec(x_24);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_27, 2, x_17);
lean_ctor_set(x_27, 3, x_26);
return x_27;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_explicitRC___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Array_empty___closed__1;
x_8 = x_4;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_array_fget(x_4, x_3);
x_10 = lean_box(0);
lean_inc(x_9);
x_11 = x_10;
x_12 = lean_array_fset(x_4, x_3, x_11);
lean_inc(x_9);
lean_inc(x_1);
lean_inc(x_2);
x_13 = l_Lean_IR_ExplicitRC_visitDecl(x_2, x_1, x_9);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_3, x_14);
x_16 = x_13;
x_17 = lean_array_fset(x_12, x_3, x_16);
lean_dec(x_3);
x_3 = x_15;
x_4 = x_17;
goto _start;
}
}
}
lean_object* l_Lean_IR_explicitRC(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_getEnv___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_8 = l_Array_umapMAux___main___at_Lean_IR_explicitRC___spec__1(x_1, x_6, x_7, x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_12 = l_Array_umapMAux___main___at_Lean_IR_explicitRC___spec__1(x_1, x_9, x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
lean_object* l_Lean_IR_explicitRC___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_explicitRC(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Lean_Runtime(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_CompilerM(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_LiveVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_RC(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Runtime(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_CompilerM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_LiveVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ExplicitRC_getVarInfo___closed__1 = _init_l_Lean_IR_ExplicitRC_getVarInfo___closed__1();
lean_mark_persistent(l_Lean_IR_ExplicitRC_getVarInfo___closed__1);
l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___closed__1 = _init_l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___closed__1();
lean_mark_persistent(l___private_Init_Lean_Compiler_IR_RC_6__getNumConsumptions___at___private_Init_Lean_Compiler_IR_RC_10__addIncBeforeConsumeAll___spec__2___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
