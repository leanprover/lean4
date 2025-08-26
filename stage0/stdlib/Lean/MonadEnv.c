// Lean compiler output
// Module: Lean.MonadEnv
// Imports: Lean.Environment Lean.Exception Lean.Declaration Lean.Log Lean.AuxRecursor Lean.Compiler.Old
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoInduct___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_getConstInfoDefn___redArg___lam__0___closed__1;
static lean_object* l_Lean_getConstInfoRec___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstant___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_setEnv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoRec___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_isInductive___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isInductive_x3f___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoDefn___redArg___lam__0___closed__2;
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStructureLike___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withEnv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_List_allM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isInductive_x3f___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductiveCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
static lean_object* l_Lean_getConstInfoDefn___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConst___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoDefn___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_matchConstStructureLike___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstRec___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
static lean_object* l_Lean_isInductive_x3f___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isInductive_x3f___redArg___lam__0___closed__0;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStructureLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRecCore___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoInduct___redArg___lam__0___closed__0;
static lean_object* l_Lean_getConstInfoCtor___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__4(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_evalConst___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_matchConstStructureLike___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_setEnv___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_setEnv___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_setEnv___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_10 = l_Lean_setEnv___redArg(x_2, x_3);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_5);
x_12 = l_Lean_setEnv___redArg(x_2, x_8);
x_13 = lean_alloc_closure((void*)(l_Lean_withEnv___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_13);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_7, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_withEnv___redArg___lam__0___boxed), 1, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_withEnv___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_5);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_withEnv___redArg___lam__3), 8, 7);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_7);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_2);
lean_closure_set(x_12, 6, x_10);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_withEnv___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_withEnv___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_withEnv___redArg___lam__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_withEnv___redArg___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_isInductiveCore(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = l_Lean_Environment_findAsync_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
lean_dec(x_5);
if (x_6 == 5)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductiveCore___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isInductiveCore(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_isInductiveCore(x_3, x_1);
x_5 = lean_box(x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_isInductive___redArg___lam__0), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isInductive___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_isRecCore(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 0;
x_4 = l_Lean_Environment_findAsync_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
lean_dec(x_5);
if (x_6 == 7)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isRecCore___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isRecCore(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_isRecCore(x_3, x_1);
x_5 = lean_box(x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_isRec___redArg___lam__0), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isRec___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Environment_unlockAsync(x_5);
x_7 = l_Lean_withEnv___redArg(x_1, x_2, x_3, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv___redArg___lam__0), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_4);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv___redArg___lam__0), 5, 4);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__1), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec_ref(x_1);
lean_inc(x_2);
x_11 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_3, x_4);
x_12 = l_Lean_setEnv___redArg(x_5, x_9);
x_13 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__4___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_13);
x_15 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_7, x_14);
x_16 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_15, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__0___boxed), 1, 0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__2), 4, 3);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__3), 2, 1);
lean_closure_set(x_12, 0, x_9);
lean_inc(x_6);
x_13 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__5), 9, 8);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_4);
lean_closure_set(x_13, 3, x_11);
lean_closure_set(x_13, 4, x_2);
lean_closure_set(x_13, 5, x_3);
lean_closure_set(x_13, 6, x_10);
lean_closure_set(x_13, 7, x_12);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec_ref(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__0___boxed), 1, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__2), 4, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_8);
lean_closure_set(x_13, 2, x_9);
x_14 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__3), 2, 1);
lean_closure_set(x_14, 0, x_11);
lean_inc(x_8);
x_15 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___redArg___lam__5), 9, 8);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_8);
lean_closure_set(x_15, 2, x_6);
lean_closure_set(x_15, 3, x_13);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_4);
lean_closure_set(x_15, 6, x_12);
lean_closure_set(x_15, 7, x_14);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_withoutModifyingEnv_x27___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_withoutModifyingEnv_x27___redArg___lam__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_matchConst___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Lean_Environment_find_x3f(x_5, x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_apply_2(x_3, x_10, x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConst___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_matchConst___redArg___lam__0), 5, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_8);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec_ref(x_5);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_matchConst___redArg___lam__0), 5, 4);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_7);
lean_closure_set(x_12, 3, x_10);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_14 = lean_box(0);
x_15 = lean_apply_1(x_6, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Lean_Environment_find_x3f(x_5, x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec_ref(x_7);
if (lean_obj_tag(x_10) == 5)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_10);
x_12 = lean_apply_2(x_3, x_11, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_2, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_matchConstInduct___redArg___lam__0), 5, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_8);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstInduct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec_ref(x_5);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_matchConstInduct___redArg___lam__0), 5, 4);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_7);
lean_closure_set(x_12, 3, x_10);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_14 = lean_box(0);
x_15 = lean_apply_1(x_6, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Lean_Environment_find_x3f(x_5, x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec_ref(x_7);
if (lean_obj_tag(x_10) == 6)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_10);
x_12 = lean_apply_2(x_3, x_11, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_2, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_matchConstCtor___redArg___lam__0), 5, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_8);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec_ref(x_5);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_matchConstCtor___redArg___lam__0), 5, 4);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_7);
lean_closure_set(x_12, 3, x_10);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_14 = lean_box(0);
x_15 = lean_apply_1(x_6, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstRec___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Lean_Environment_find_x3f(x_5, x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_2, x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec_ref(x_7);
if (lean_obj_tag(x_10) == 7)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_10);
x_12 = lean_apply_2(x_3, x_11, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_2, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstRec___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_matchConstRec___redArg___lam__0), 5, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_8);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec_ref(x_5);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_matchConstRec___redArg___lam__0), 5, 4);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_7);
lean_closure_set(x_12, 3, x_10);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_14 = lean_box(0);
x_15 = lean_apply_1(x_6, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Environment_contains(x_4, x_1, x_2);
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_box(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_hasConst___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_8);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_hasConst___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_hasConst___redArg___lam__0(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l_Lean_hasConst___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
x_7 = l_Lean_hasConst(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
lean_inc(x_1);
x_8 = l_Lean_Environment_find_x3f(x_6, x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = l_Lean_throwUnknownConstant___redArg(x_2, x_3, x_4, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_apply_2(x_5, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_getConstInfo___redArg___lam__0), 6, 5);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_3);
lean_closure_set(x_9, 4, x_8);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getConstInfo___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
lean_inc(x_1);
x_8 = l_Lean_Environment_findConstVal_x3f(x_6, x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = l_Lean_throwUnknownConstant___redArg(x_2, x_3, x_4, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_apply_2(x_5, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_getConstVal___redArg___lam__0), 6, 5);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_3);
lean_closure_set(x_9, 4, x_8);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getConstVal___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Environment_findAsync_x3f(x_7, x_1, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = l_Lean_throwUnknownConstant___redArg(x_3, x_4, x_5, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_apply_2(x_6, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_box(x_5);
x_11 = lean_alloc_closure((void*)(l_Lean_getAsyncConstInfo___redArg___lam__0___boxed), 7, 6);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_1);
lean_closure_set(x_11, 3, x_2);
lean_closure_set(x_11, 4, x_3);
lean_closure_set(x_11, 5, x_9);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getAsyncConstInfo___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_getAsyncConstInfo___redArg___lam__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
x_7 = l_Lean_getAsyncConstInfo___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
x_8 = l_Lean_getAsyncConstInfo(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_isInductive_x3f___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.MonadEnv", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_isInductive_x3f___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.isInductive\?", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_isInductive_x3f___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_isInductive_x3f___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_isInductive_x3f___redArg___lam__0___closed__2;
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(106u);
x_4 = l_Lean_isInductive_x3f___redArg___lam__0___closed__1;
x_5 = l_Lean_isInductive_x3f___redArg___lam__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
x_9 = l_Lean_Environment_findAsync_x3f(x_4, x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_3);
goto block_7;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
if (x_12 == 5)
{
lean_object* x_13; 
x_13 = l_Lean_AsyncConstantInfo_toConstantInfo(x_11);
if (lean_obj_tag(x_13) == 5)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec_ref(x_13);
lean_ctor_set(x_9, 0, x_14);
x_15 = lean_apply_2(x_1, lean_box(0), x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_13);
lean_free_object(x_9);
lean_dec(x_1);
x_16 = l_Lean_isInductive_x3f___redArg___lam__0___closed__3;
x_17 = l_panic___redArg(x_3, x_16);
return x_17;
}
}
else
{
lean_free_object(x_9);
lean_dec(x_11);
lean_dec(x_3);
goto block_7;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
if (x_19 == 5)
{
lean_object* x_20; 
x_20 = l_Lean_AsyncConstantInfo_toConstantInfo(x_18);
if (lean_obj_tag(x_20) == 5)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_apply_2(x_1, lean_box(0), x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_20);
lean_dec(x_1);
x_24 = l_Lean_isInductive_x3f___redArg___lam__0___closed__3;
x_25 = l_panic___redArg(x_3, x_24);
return x_25;
}
}
else
{
lean_dec(x_18);
lean_dec(x_3);
goto block_7;
}
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l_instInhabitedOfMonad___redArg(x_1, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_isInductive_x3f___redArg___lam__0), 4, 3);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isInductive_x3f___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkLevelParam), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0;
x_6 = lean_box(0);
x_7 = l_List_mapTR_loop___redArg(x_5, x_4, x_6);
x_8 = l_Lean_mkConst(x_1, x_7);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_inc(x_4);
x_8 = l_Lean_getConstVal___redArg(x_1, x_2, x_3, x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_mkConstWithLevelParams___redArg___lam__0), 3, 2);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkConstWithLevelParams___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoDefn___redArg___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is not a definition", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoDefn___redArg___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_8 = l_Lean_getConstInfoDefn___redArg___lam__0___closed__1;
x_9 = 0;
x_10 = l_Lean_MessageData_ofConstName(x_2, x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_getConstInfoDefn___redArg___lam__0___closed__3;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___redArg(x_3, x_4, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_8 = l_Lean_getConstInfo___redArg(x_1, x_2, x_3, x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_getConstInfoDefn___redArg___lam__0), 5, 4);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_3);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getConstInfoDefn___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is not a inductive type", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoInduct___redArg___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_8 = l_Lean_getConstInfoDefn___redArg___lam__0___closed__1;
x_9 = 0;
x_10 = l_Lean_MessageData_ofConstName(x_2, x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_getConstInfoInduct___redArg___lam__0___closed__1;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___redArg(x_3, x_4, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_8 = l_Lean_getConstInfo___redArg(x_1, x_2, x_3, x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_getConstInfoInduct___redArg___lam__0), 5, 4);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_3);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getConstInfoInduct___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is not a constructor", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoCtor___redArg___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 6)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_8 = l_Lean_getConstInfoDefn___redArg___lam__0___closed__1;
x_9 = 0;
x_10 = l_Lean_MessageData_ofConstName(x_2, x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_getConstInfoCtor___redArg___lam__0___closed__1;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___redArg(x_3, x_4, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_8 = l_Lean_getConstInfo___redArg(x_1, x_2, x_3, x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_getConstInfoCtor___redArg___lam__0), 5, 4);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_3);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getConstInfoCtor___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is not a recursor", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoRec___redArg___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 7)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_5);
lean_dec(x_1);
x_8 = l_Lean_getConstInfoDefn___redArg___lam__0___closed__1;
x_9 = 0;
x_10 = l_Lean_MessageData_ofConstName(x_2, x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_getConstInfoRec___redArg___lam__0___closed__1;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___redArg(x_3, x_4, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_8 = l_Lean_getConstInfo___redArg(x_1, x_2, x_3, x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_getConstInfoRec___redArg___lam__0), 5, 4);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_3);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getConstInfoRec___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 6)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_apply_3(x_1, x_2, x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_4, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
x_14 = l_Lean_Environment_find_x3f(x_9, x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec_ref(x_14);
if (lean_obj_tag(x_17) == 5)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 4);
if (lean_obj_tag(x_19) == 0)
{
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_12;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 1);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__0), 5, 4);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_18);
lean_closure_set(x_22, 2, x_4);
lean_closure_set(x_22, 3, x_2);
x_23 = l_Lean_getConstInfo___redArg(x_5, x_6, x_7, x_21);
x_24 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_23, x_22);
return x_24;
}
else
{
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_12;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = lean_apply_1(x_2, x_25);
return x_26;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec_ref(x_4);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__1), 9, 8);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_6);
lean_closure_set(x_11, 3, x_9);
lean_closure_set(x_11, 4, x_1);
lean_closure_set(x_11, 5, x_2);
lean_closure_set(x_11, 6, x_3);
lean_closure_set(x_11, 7, x_7);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_5, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec_ref(x_6);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_inc(x_9);
x_13 = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__1), 9, 8);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_7);
lean_closure_set(x_13, 2, x_8);
lean_closure_set(x_13, 3, x_11);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_4);
lean_closure_set(x_13, 6, x_5);
lean_closure_set(x_13, 7, x_9);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_7, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructureLike___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
x_17 = l_Lean_Environment_find_x3f(x_9, x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = lean_apply_1(x_2, x_18);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec_ref(x_17);
if (lean_obj_tag(x_20) == 5)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 4);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_21, sizeof(void*)*6);
lean_inc(x_2);
x_25 = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__0), 5, 4);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_21);
lean_closure_set(x_25, 2, x_4);
lean_closure_set(x_25, 3, x_2);
if (x_24 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_22, x_31);
lean_dec(x_22);
if (x_32 == 0)
{
lean_dec_ref(x_25);
lean_dec(x_23);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
goto block_15;
}
else
{
goto block_30;
}
}
else
{
lean_dec(x_22);
goto block_30;
}
block_30:
{
if (x_24 == 0)
{
if (lean_obj_tag(x_23) == 0)
{
lean_dec_ref(x_25);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
goto block_12;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec_ref(x_23);
x_28 = l_Lean_getConstInfo___redArg(x_5, x_6, x_7, x_27);
x_29 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_28, x_25);
return x_29;
}
else
{
lean_dec_ref(x_25);
lean_dec_ref(x_23);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
goto block_12;
}
}
}
else
{
lean_dec_ref(x_25);
lean_dec(x_23);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
goto block_15;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_box(0);
x_34 = lean_apply_1(x_2, x_33);
return x_34;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_apply_1(x_2, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructureLike___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec_ref(x_4);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_matchConstStructureLike___redArg___lam__1), 9, 8);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_6);
lean_closure_set(x_11, 3, x_9);
lean_closure_set(x_11, 4, x_1);
lean_closure_set(x_11, 5, x_2);
lean_closure_set(x_11, 6, x_3);
lean_closure_set(x_11, 7, x_7);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_5, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructureLike___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
x_17 = l_Lean_Environment_find_x3f(x_9, x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = lean_apply_1(x_2, x_18);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec_ref(x_17);
if (lean_obj_tag(x_20) == 5)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 2);
x_24 = lean_ctor_get(x_21, 4);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_23, x_25);
if (x_26 == 0)
{
lean_dec_ref(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_12;
}
else
{
if (lean_obj_tag(x_24) == 0)
{
lean_dec_ref(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_15;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 1);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_alloc_closure((void*)(l_Lean_matchConstStructure___redArg___lam__0), 5, 4);
lean_closure_set(x_29, 0, x_3);
lean_closure_set(x_29, 1, x_21);
lean_closure_set(x_29, 2, x_4);
lean_closure_set(x_29, 3, x_2);
x_30 = l_Lean_getConstInfo___redArg(x_5, x_6, x_7, x_28);
x_31 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_30, x_29);
return x_31;
}
else
{
lean_dec_ref(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_15;
}
}
}
}
else
{
lean_dec_ref(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_12;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_box(0);
x_33 = lean_apply_1(x_2, x_32);
return x_33;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_apply_1(x_2, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStructureLike(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec_ref(x_6);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_inc(x_9);
x_13 = lean_alloc_closure((void*)(l_Lean_matchConstStructureLike___lam__1), 9, 8);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_7);
lean_closure_set(x_13, 2, x_8);
lean_closure_set(x_13, 3, x_11);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_4);
lean_closure_set(x_13, 6, x_5);
lean_closure_set(x_13, 7, x_9);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_15 = lean_box(0);
x_16 = lean_apply_1(x_7, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Environment_evalConst___redArg(x_1, x_7, x_2, x_3);
x_9 = l_Lean_ofExcept___redArg(x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__0___boxed), 7, 6);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_5);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_evalConst___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_stringToMessageData___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = l_Lean_evalConst___redArg___closed__0;
x_10 = lean_box(x_6);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_evalConst___redArg___lam__1___boxed), 8, 7);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_1);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_9);
lean_closure_set(x_11, 5, x_7);
lean_closure_set(x_11, 6, x_4);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConst___redArg(x_2, x_3, x_4, x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
x_9 = l_Lean_evalConst___redArg___lam__0(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_evalConst___redArg___lam__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
x_8 = l_Lean_evalConst___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
x_10 = l_Lean_evalConst(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Environment_evalConstCheck___redArg(x_1, x_7, x_2, x_3);
x_9 = l_Lean_ofExcept___redArg(x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_evalConstCheck___redArg___lam__0___boxed), 7, 6);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_3);
lean_closure_set(x_9, 4, x_4);
lean_closure_set(x_9, 5, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = l_Lean_evalConst___redArg___closed__0;
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_evalConstCheck___redArg___lam__1), 8, 7);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_6);
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_9);
lean_closure_set(x_10, 5, x_7);
lean_closure_set(x_10, 6, x_4);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConstCheck___redArg(x_2, x_3, x_4, x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_evalConstCheck___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Environment_allImportedModuleNames(x_4);
x_6 = lean_array_get(x_1, x_5, x_2);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Environment_getModuleIdxFor_x3f(x_6, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_2);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
lean_inc(x_7);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___redArg___lam__1___boxed), 6, 5);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_4);
lean_closure_set(x_8, 3, x_5);
lean_closure_set(x_8, 4, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_box(0);
lean_inc(x_7);
lean_inc(x_8);
lean_inc(x_4);
lean_inc_ref(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___redArg___lam__2), 6, 5);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_8);
lean_closure_set(x_11, 3, x_10);
lean_closure_set(x_11, 4, x_7);
x_12 = l_Lean_getConstInfo___redArg(x_1, x_2, x_3, x_4);
x_13 = lean_box(0);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_12);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_14, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_findModuleOf_x3f___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_findModuleOf_x3f___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_findModuleOf_x3f___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 6)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_5, 4);
x_7 = lean_nat_dec_eq(x_6, x_1);
x_8 = lean_box(x_7);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(x_3);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_getConstInfo___redArg(x_1, x_2, x_3, x_6);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 4);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
x_13 = lean_ctor_get_uint8(x_7, sizeof(void*)*6 + 1);
x_14 = lean_ctor_get(x_8, 2);
x_15 = l_Lean_Expr_isProp(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_InductiveVal_numTypeFormers(x_7);
lean_dec_ref(x_7);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_19 = lean_box(x_18);
x_20 = lean_apply_2(x_1, lean_box(0), x_19);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_10, x_21);
lean_dec(x_10);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_23 = lean_box(x_22);
x_24 = lean_apply_2(x_1, lean_box(0), x_23);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_eq(x_9, x_21);
lean_dec(x_9);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_26 = lean_box(x_25);
x_27 = lean_apply_2(x_1, lean_box(0), x_26);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = l_List_isEmpty___redArg(x_11);
if (x_28 == 0)
{
if (x_12 == 0)
{
if (x_13 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_box(x_13);
x_30 = lean_alloc_closure((void*)(l_Lean_isEnumType___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_30, 0, x_21);
lean_closure_set(x_30, 1, x_1);
lean_closure_set(x_30, 2, x_29);
lean_inc_ref(x_2);
x_31 = lean_alloc_closure((void*)(l_Lean_isEnumType___redArg___lam__1), 6, 5);
lean_closure_set(x_31, 0, x_2);
lean_closure_set(x_31, 1, x_3);
lean_closure_set(x_31, 2, x_4);
lean_closure_set(x_31, 3, x_5);
lean_closure_set(x_31, 4, x_30);
x_32 = l_List_allM___redArg(x_2, x_31, x_11);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_33 = lean_box(x_12);
x_34 = lean_apply_2(x_1, lean_box(0), x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_35 = lean_box(x_28);
x_36 = lean_apply_2(x_1, lean_box(0), x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_37 = lean_box(x_15);
x_38 = lean_apply_2(x_1, lean_box(0), x_37);
return x_38;
}
}
}
}
}
else
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_39 = 0;
x_40 = lean_box(x_39);
x_41 = lean_apply_2(x_1, lean_box(0), x_40);
return x_41;
}
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_42 = 0;
x_43 = lean_box(x_42);
x_44 = lean_apply_2(x_1, lean_box(0), x_43);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_8 = l_Lean_getConstInfo___redArg(x_1, x_2, x_3, x_4);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_isEnumType___redArg___lam__2), 6, 5);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_3);
lean_closure_set(x_9, 4, x_6);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_isEnumType___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_Lean_isEnumType___redArg___lam__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Exception(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Declaration(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AuxRecursor(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Old(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_MonadEnv(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AuxRecursor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Old(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_isInductive_x3f___redArg___lam__0___closed__0 = _init_l_Lean_isInductive_x3f___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_isInductive_x3f___redArg___lam__0___closed__0);
l_Lean_isInductive_x3f___redArg___lam__0___closed__1 = _init_l_Lean_isInductive_x3f___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_isInductive_x3f___redArg___lam__0___closed__1);
l_Lean_isInductive_x3f___redArg___lam__0___closed__2 = _init_l_Lean_isInductive_x3f___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_isInductive_x3f___redArg___lam__0___closed__2);
l_Lean_isInductive_x3f___redArg___lam__0___closed__3 = _init_l_Lean_isInductive_x3f___redArg___lam__0___closed__3();
lean_mark_persistent(l_Lean_isInductive_x3f___redArg___lam__0___closed__3);
l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0 = _init_l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_mkConstWithLevelParams___redArg___lam__0___closed__0);
l_Lean_getConstInfoDefn___redArg___lam__0___closed__0 = _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_getConstInfoDefn___redArg___lam__0___closed__0);
l_Lean_getConstInfoDefn___redArg___lam__0___closed__1 = _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_getConstInfoDefn___redArg___lam__0___closed__1);
l_Lean_getConstInfoDefn___redArg___lam__0___closed__2 = _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_getConstInfoDefn___redArg___lam__0___closed__2);
l_Lean_getConstInfoDefn___redArg___lam__0___closed__3 = _init_l_Lean_getConstInfoDefn___redArg___lam__0___closed__3();
lean_mark_persistent(l_Lean_getConstInfoDefn___redArg___lam__0___closed__3);
l_Lean_getConstInfoInduct___redArg___lam__0___closed__0 = _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_getConstInfoInduct___redArg___lam__0___closed__0);
l_Lean_getConstInfoInduct___redArg___lam__0___closed__1 = _init_l_Lean_getConstInfoInduct___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_getConstInfoInduct___redArg___lam__0___closed__1);
l_Lean_getConstInfoCtor___redArg___lam__0___closed__0 = _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_getConstInfoCtor___redArg___lam__0___closed__0);
l_Lean_getConstInfoCtor___redArg___lam__0___closed__1 = _init_l_Lean_getConstInfoCtor___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_getConstInfoCtor___redArg___lam__0___closed__1);
l_Lean_getConstInfoRec___redArg___lam__0___closed__0 = _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_getConstInfoRec___redArg___lam__0___closed__0);
l_Lean_getConstInfoRec___redArg___lam__0___closed__1 = _init_l_Lean_getConstInfoRec___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_getConstInfoRec___redArg___lam__0___closed__1);
l_Lean_evalConst___redArg___closed__0 = _init_l_Lean_evalConst___redArg___closed__0();
lean_mark_persistent(l_Lean_evalConst___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
