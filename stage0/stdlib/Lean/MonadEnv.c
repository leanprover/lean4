// Lean compiler output
// Module: Lean.MonadEnv
// Imports: Init Lean.Environment Lean.Exception Lean.Declaration Lean.Log Lean.Util.FindExpr Lean.AuxRecursor Lean.Compiler.Util
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
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
LEAN_EXPORT uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl___rarg___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2(lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__30;
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_evalConst(lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3;
static lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_hasConst___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__5;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_evalConst___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst(lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__18;
static lean_object* l_Lean_getConstInfoInduct___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f(lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15;
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl___rarg___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__6;
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported(lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__29;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compile_decls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConst___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstRec___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType(lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__25;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__20;
LEAN_EXPORT lean_object* l_Lean_setEnv(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addAndCompile___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__10;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__32;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl___rarg___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_isEnumType___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___rarg___lambda__3(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__24;
LEAN_EXPORT lean_object* l_Lean_matchConstStruct___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addAndCompile___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStruct___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__7;
LEAN_EXPORT lean_object* l_Lean_addAndCompile___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoDefn___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_withEnv___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__16;
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__11;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStruct___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConst(lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn(lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__31;
LEAN_EXPORT lean_object* l_Lean_matchConstInduct(lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__26;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__1;
static lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_getConstInfo(lean_object*);
static lean_object* l_Lean_withEnv___rarg___lambda__2___closed__1;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__19;
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_evalConst___spec__1(lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_evalConstCheck(lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_compileDecls___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__12;
LEAN_EXPORT lean_object* l_Lean_mkAuxName___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxName___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__4;
static lean_object* l_Lean_getConstInfoDefn___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_matchConstRec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__2;
lean_object* l_Lean_throwKernelException___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__1;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__2;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_evalConstCheck___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__22;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__8;
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___rarg___lambda__1___closed__2;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__33;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__13;
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__21;
LEAN_EXPORT lean_object* l_Lean_isRecCore___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__23;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_mkAuxNameAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls(lean_object*);
static lean_object* l_Lean_getConstInfoRec___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_evalConstCheck___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStruct(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoRec___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_compileDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_log___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams(lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_matchConst___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
uint8_t l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__17;
LEAN_EXPORT lean_object* l_Lean_withEnv___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__27;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstCtor(lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__28;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__14;
LEAN_EXPORT lean_object* l_Lean_withEnv___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__4;
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecls___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoInduct___rarg___lambda__1___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_setEnv___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_setEnv___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_setEnv___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_withEnv___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_withEnv___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_2);
x_10 = l_Lean_setEnv___rarg(x_2, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_setEnv___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_11);
x_13 = l_Lean_setEnv___rarg(x_2, x_7);
x_14 = lean_alloc_closure((void*)(l_Lean_setEnv___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_14);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = l_Lean_withEnv___rarg___lambda__2___closed__1;
x_18 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_17, x_15);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_withEnv___rarg___lambda__2), 7, 6);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_4);
lean_closure_set(x_8, 3, x_5);
lean_closure_set(x_8, 4, x_6);
lean_closure_set(x_8, 5, x_2);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_withEnv___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_withEnv___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_environment_find(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 5)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_apply_2(x_12, lean_box(0), x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_apply_2(x_17, lean_box(0), x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_isInductive___rarg___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_isInductive___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_isRecCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 7)
{
uint8_t x_6; 
lean_dec(x_5);
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_isRec___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_isRecCore(x_3, x_2);
x_7 = lean_box(x_6);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_isRec___rarg___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_isRec___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_setEnv___rarg(x_2, x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_setEnv___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_9);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_withEnv___rarg___lambda__2___closed__1;
x_13 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv___rarg___lambda__1), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_apply_2(x_4, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___rarg___lambda__1), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___rarg___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___rarg___lambda__2), 4, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_inc(x_2);
x_11 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_4, x_10);
x_12 = l_Lean_setEnv___rarg(x_5, x_7);
x_13 = lean_alloc_closure((void*)(l_Lean_setEnv___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_13);
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_Lean_withEnv___rarg___lambda__2___closed__1;
x_17 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_16, x_14);
x_18 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___rarg___lambda__3), 2, 1);
lean_closure_set(x_18, 0, x_8);
x_19 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___rarg___lambda__4), 7, 6);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_5);
lean_closure_set(x_8, 4, x_2);
lean_closure_set(x_8, 5, x_3);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv_x27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv_x27___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_matchConst___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_environment_find(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_2(x_3, x_9, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConst___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_matchConst___rarg___lambda__1), 5, 4);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_7);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_matchConst___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_environment_find(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 5)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_3, x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_2, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_matchConstInduct___rarg___lambda__1), 5, 4);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_7);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstInduct(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_matchConstInduct___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_environment_find(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 6)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_3, x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_2, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_matchConstCtor___rarg___lambda__1), 5, 4);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_7);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstCtor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_matchConstCtor___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstRec___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_environment_find(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 7)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_3, x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_2, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_matchConstRec___rarg___lambda__1), 5, 4);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_7);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstRec(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_matchConstRec___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Environment_contains(x_3, x_2);
x_7 = lean_box(x_6);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_hasConst___rarg___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_hasConst___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_mkAuxNameAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_name_append_index_after(x_2, x_3);
lean_inc(x_4);
lean_inc(x_1);
x_5 = l_Lean_Environment_contains(x_1, x_4);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_3);
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxName___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l___private_Lean_MonadEnv_0__Lean_mkAuxNameAux(x_4, x_2, x_3);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_mkAuxName___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_4);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkAuxName___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___rarg___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = lean_environment_find(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_1, x_6);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_getConstInfo___rarg___lambda__1___closed__2;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_getConstInfo___rarg___lambda__1___closed__4;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___rarg(x_2, x_3, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_getConstInfo___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getConstInfo___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Level_param___override(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Level_param___override(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_ConstantInfo_levelParams(x_3);
x_7 = lean_box(0);
x_8 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_6, x_7);
x_9 = l_Lean_Expr_const___override(x_2, x_8);
x_10 = lean_apply_2(x_5, lean_box(0), x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_6 = l_Lean_getConstInfo___rarg(x_1, x_2, x_3, x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_mkConstWithLevelParams___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkConstWithLevelParams___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkConstWithLevelParams___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is not a definition", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoDefn___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_const___override(x_1, x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_getConstInfo___rarg___lambda__1___closed__4;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_getConstInfoDefn___rarg___lambda__1___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___rarg(x_2, x_3, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Lean_getConstInfo___rarg(x_1, x_2, x_3, x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_getConstInfoDefn___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getConstInfoDefn___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is not a inductive type", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoInduct___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_const___override(x_1, x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_getConstInfo___rarg___lambda__1___closed__4;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_getConstInfoInduct___rarg___lambda__1___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___rarg(x_2, x_3, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Lean_getConstInfo___rarg(x_1, x_2, x_3, x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_getConstInfoInduct___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getConstInfoInduct___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is not a constructor", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoCtor___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 6)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_const___override(x_1, x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_getConstInfo___rarg___lambda__1___closed__4;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_getConstInfoCtor___rarg___lambda__1___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___rarg(x_2, x_3, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Lean_getConstInfo___rarg(x_1, x_2, x_3, x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_getConstInfoCtor___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getConstInfoCtor___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is not a recursor", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoRec___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_const___override(x_1, x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_getConstInfo___rarg___lambda__1___closed__4;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_getConstInfoRec___rarg___lambda__1___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___rarg(x_2, x_3, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_Lean_getConstInfo___rarg(x_1, x_2, x_3, x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_getConstInfoRec___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getConstInfoRec___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStruct___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 6)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_apply_3(x_2, x_3, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStruct___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_environment_find(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_2, x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 5)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_box(0);
x_20 = lean_apply_1(x_2, x_19);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_14, 4);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_apply_1(x_2, x_22);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_getConstInfo___rarg(x_3, x_4, x_5, x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_matchConstStruct___rarg___lambda__1), 5, 4);
lean_closure_set(x_27, 0, x_2);
lean_closure_set(x_27, 1, x_6);
lean_closure_set(x_27, 2, x_14);
lean_closure_set(x_27, 3, x_7);
x_28 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_26, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_box(0);
x_30 = lean_apply_1(x_2, x_29);
return x_30;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_box(0);
x_32 = lean_apply_1(x_2, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_box(0);
x_34 = lean_apply_1(x_2, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStruct___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_matchConstStruct___rarg___lambda__2), 9, 8);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_1);
lean_closure_set(x_11, 3, x_2);
lean_closure_set(x_11, 4, x_3);
lean_closure_set(x_11, 5, x_6);
lean_closure_set(x_11, 6, x_8);
lean_closure_set(x_11, 7, x_9);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_5, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_matchConstStruct(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_matchConstStruct___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_add_decl(x_6, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_throwKernelException___rarg(x_2, x_3, x_4, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_setEnv___rarg(x_5, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_addDecl___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_4);
lean_closure_set(x_9, 3, x_5);
lean_closure_set(x_9, 4, x_1);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_addDecl___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declaration uses 'sorry'", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_addDecl___rarg___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDecl___rarg___lambda__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addDecl___rarg___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDecl___rarg___lambda__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_addDecl___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
lean_closure_set(x_10, 5, x_6);
if (x_9 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = 0;
x_12 = l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
x_17 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_16, x_10);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lean_addDecl___rarg___lambda__3___closed__3;
x_19 = 1;
x_20 = l_Lean_log___rarg(x_3, x_7, x_8, x_18, x_19);
x_21 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_20, x_10);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
x_26 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_25, x_10);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 3);
lean_inc(x_9);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_addDecl___rarg___lambda__3___boxed), 9, 8);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_8);
lean_closure_set(x_10, 6, x_5);
lean_closure_set(x_10, 7, x_6);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_addDecl___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addDecl___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addDecl___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = l_Lean_addDecl___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
return x_11;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Empty", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rec", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__2;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("False", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__6;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ndrec", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("recOn", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("casesOn", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__6;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__2;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("And", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__19;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__20;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__20;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__23;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__24;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__25;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__26;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__12;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__27;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__14;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__28;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__16;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__29;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__17;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__30;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__18;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__31;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__21;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__32;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__22;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__33;
return x_1;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_is_aux_recursor(x_1, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_inc(x_3);
x_5 = l_Lean_isRecCore(x_1, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_8 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_7, x_3);
lean_dec(x_3);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
else
{
uint8_t x_11; 
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_isCasesOnRecursor(x_1, x_3);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_12 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_13 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_12, x_3);
lean_dec(x_3);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_inc(x_3);
x_16 = l_Lean_isRecCore(x_1, x_3);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = 0;
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
x_19 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_18, x_3);
lean_dec(x_3);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 1;
return x_20;
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = 0;
return x_22;
}
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("code generator does not support recursor '", 42);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' yet, consider using 'match ... with' and/or structural recursion", 66);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___rarg(x_3, x_4, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_4);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = lean_apply_2(x_21, lean_box(0), x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_3);
lean_inc(x_14);
x_15 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_14, x_13);
lean_inc(x_2);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_16, 0, x_9);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_1);
lean_closure_set(x_16, 3, x_2);
lean_inc(x_2);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__3), 5, 4);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
lean_inc(x_11);
x_22 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_21, x_16);
x_23 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_22, x_17);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
if (lean_obj_tag(x_24) == 4)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___rarg(x_1, x_2, x_30);
lean_inc(x_11);
x_32 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_31, x_16);
x_33 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_32, x_17);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_24);
lean_dec(x_2);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = lean_apply_2(x_35, lean_box(0), x_36);
lean_inc(x_11);
x_38 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_37, x_16);
x_39 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_38, x_17);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
lean_inc(x_3);
x_13 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_3, x_12);
lean_inc(x_2);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg___lambda__1), 5, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_16, lean_box(0), x_17);
x_19 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_18, x_14);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
if (lean_obj_tag(x_20) == 4)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___rarg(x_1, x_2, x_26);
x_28 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_27, x_14);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = lean_apply_2(x_30, lean_box(0), x_31);
x_33 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_32, x_14);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_7, lean_box(0), x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_13, 0, x_3);
lean_inc(x_13);
x_14 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_13, x_12);
lean_inc(x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___lambda__1), 5, 4);
lean_closure_set(x_15, 0, x_9);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_13);
lean_inc(x_2);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___lambda__2), 5, 4);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_18, lean_box(0), x_19);
lean_inc(x_11);
x_21 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_20, x_15);
x_22 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_21, x_16);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
if (lean_obj_tag(x_23) == 4)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___rarg(x_1, x_2, x_29);
lean_inc(x_11);
x_31 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_30, x_15);
x_32 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_31, x_16);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = lean_apply_2(x_34, lean_box(0), x_35);
lean_inc(x_11);
x_37 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_36, x_15);
x_38 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_37, x_16);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___rarg(x_3, x_4, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_4);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_20, lean_box(0), x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_9, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___rarg(x_1, x_2, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = lean_apply_2(x_24, lean_box(0), x_25);
return x_26;
}
}
}
case 4:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_apply_2(x_28, lean_box(0), x_5);
return x_29;
}
case 5:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_4, 0);
lean_inc(x_30);
lean_dec(x_4);
x_31 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg(x_1, x_2, x_3, x_5, x_30);
return x_31;
}
case 6:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_4, 2);
lean_inc(x_32);
lean_dec(x_4);
x_33 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg(x_1, x_2, x_3, x_5, x_32);
return x_33;
}
default: 
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
lean_dec(x_4);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 2);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_39, 0, x_3);
lean_inc(x_39);
x_40 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_39, x_37);
lean_inc(x_2);
lean_inc(x_1);
x_41 = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_41, 0, x_39);
lean_closure_set(x_41, 1, x_36);
lean_closure_set(x_41, 2, x_1);
lean_closure_set(x_41, 3, x_2);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = lean_apply_2(x_43, lean_box(0), x_44);
x_46 = lean_apply_4(x_38, lean_box(0), lean_box(0), x_45, x_41);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
if (lean_obj_tag(x_47) == 4)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_throwError___rarg(x_1, x_2, x_53);
x_55 = lean_apply_4(x_38, lean_box(0), lean_box(0), x_54, x_41);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_47);
lean_dec(x_2);
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
lean_dec(x_1);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_box(0);
x_59 = lean_apply_2(x_57, lean_box(0), x_58);
x_60 = lean_apply_4(x_38, lean_box(0), lean_box(0), x_59, x_41);
return x_60;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg(x_1, x_2, x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_closure((void*)(l___private_Lean_MonadEnv_0__Lean_checkUnsupported___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_4);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_MonadEnv_0__Lean_checkUnsupported___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_throwError___rarg(x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
x_9 = l_Lean_Environment_compileDecl(x_1, x_8, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 11)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l___private_Lean_MonadEnv_0__Lean_checkUnsupported___rarg(x_3, x_6, x_4, x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_compileDecl___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_4);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_15 = l_Lean_throwKernelException___rarg(x_3, x_4, x_5, x_10);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = l_Lean_setEnv___rarg(x_6, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_compileDecl___rarg___lambda__2___boxed), 8, 7);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_5);
lean_closure_set(x_8, 6, x_6);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_4, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_compileDecl___rarg___lambda__3), 7, 6);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_2);
lean_closure_set(x_8, 5, x_6);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_compileDecl___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_compileDecl___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_compileDecl___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_compile_decls(x_1, x_7, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 11)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_throwError___rarg(x_3, x_4, x_12);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_throwKernelException___rarg(x_3, x_4, x_5, x_9);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = l_Lean_setEnv___rarg(x_6, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_compileDecls___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_4, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_compileDecls___rarg___lambda__2), 7, 6);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_2);
lean_closure_set(x_8, 5, x_6);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_compileDecls___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_compileDecls___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_compileDecls___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_compileDecl___rarg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_addDecl___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_addAndCompile___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_7);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_addAndCompile___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addAndCompile___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_evalConst___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_throwError___rarg(x_1, x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_evalConst___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ofExcept___at_Lean_evalConst___spec__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_eval_const(x_1, x_5, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_ofExcept___at_Lean_evalConst___spec__1___rarg(x_3, x_4, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_evalConst___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_evalConst___rarg___lambda__2), 6, 5);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_7);
lean_closure_set(x_9, 4, x_4);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_evalConst___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_evalConst___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_evalConstCheck___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_throwError___rarg(x_1, x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_evalConstCheck___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ofExcept___at_Lean_evalConstCheck___spec__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Environment_evalConstCheck___rarg(x_1, x_6, x_2, x_3);
x_8 = l_Lean_ofExcept___at_Lean_evalConstCheck___spec__1___rarg(x_4, x_5, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_evalConstCheck___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_evalConstCheck___rarg___lambda__2), 7, 6);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_8);
lean_closure_set(x_10, 5, x_4);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_evalConstCheck___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_evalConstCheck___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__1;
x_2 = l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(70u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Environment_allImportedModuleNames(x_3);
x_6 = lean_array_get_size(x_5);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_8 = l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__4;
x_9 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_apply_2(x_4, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_fget(x_5, x_2);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_apply_2(x_4, lean_box(0), x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Environment_getModuleIdxFor_x3f(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___rarg___lambda__2), 5, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_6);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_2);
x_8 = l_Lean_getConstInfo___rarg(x_1, x_2, x_3, x_4);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_8);
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___rarg___lambda__3___boxed), 5, 4);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_4);
lean_closure_set(x_12, 2, x_6);
lean_closure_set(x_12, 3, x_5);
x_13 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_findModuleOf_x3f___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_findModuleOf_x3f___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_findModuleOf_x3f___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
x_9 = lean_box(x_8);
x_10 = lean_apply_2(x_5, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_apply_2(x_12, lean_box(0), x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_List_allM___at_Lean_isEnumType___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_apply_2(x_7, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_getConstInfo___rarg(x_1, x_2, x_3, x_11);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_4);
x_16 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_14, x_15);
x_17 = lean_alloc_closure((void*)(l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_4);
lean_closure_set(x_17, 4, x_12);
x_18 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_allM___at_Lean_isEnumType___spec__1___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Expr_isProp(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_6, 3);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthTRAux___rarg(x_10, x_11);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_apply_2(x_16, lean_box(0), x_18);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_6, 2);
lean_inc(x_20);
x_21 = lean_nat_dec_eq(x_20, x_11);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_apply_2(x_23, lean_box(0), x_25);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
x_28 = lean_nat_dec_eq(x_27, x_11);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_apply_2(x_30, lean_box(0), x_32);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_6, 4);
lean_inc(x_34);
x_35 = l_List_isEmpty___rarg(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_6, sizeof(void*)*5);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 3);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 1);
lean_dec(x_6);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = l_List_allM___at_Lean_isEnumType___spec__1___rarg(x_1, x_2, x_3, x_4, x_34);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_34);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = 0;
x_43 = lean_box(x_42);
x_44 = lean_apply_2(x_41, lean_box(0), x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = 0;
x_48 = lean_box(x_47);
x_49 = lean_apply_2(x_46, lean_box(0), x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
lean_dec(x_1);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_apply_2(x_51, lean_box(0), x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = 0;
x_58 = lean_box(x_57);
x_59 = lean_apply_2(x_56, lean_box(0), x_58);
return x_59;
}
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
lean_dec(x_1);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = 0;
x_63 = lean_box(x_62);
x_64 = lean_apply_2(x_61, lean_box(0), x_63);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
lean_dec(x_1);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = 0;
x_68 = lean_box(x_67);
x_69 = lean_apply_2(x_66, lean_box(0), x_68);
return x_69;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_getConstInfo___rarg(x_1, x_2, x_3, x_4);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_isEnumType___rarg___lambda__1), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_5);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_isEnumType___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Exception(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Declaration(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FindExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AuxRecursor(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_MonadEnv(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
res = initialize_Lean_Util_FindExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AuxRecursor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_withEnv___rarg___lambda__2___closed__1 = _init_l_Lean_withEnv___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_withEnv___rarg___lambda__2___closed__1);
l_Lean_getConstInfo___rarg___lambda__1___closed__1 = _init_l_Lean_getConstInfo___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___rarg___lambda__1___closed__1);
l_Lean_getConstInfo___rarg___lambda__1___closed__2 = _init_l_Lean_getConstInfo___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___rarg___lambda__1___closed__2);
l_Lean_getConstInfo___rarg___lambda__1___closed__3 = _init_l_Lean_getConstInfo___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___rarg___lambda__1___closed__3);
l_Lean_getConstInfo___rarg___lambda__1___closed__4 = _init_l_Lean_getConstInfo___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___rarg___lambda__1___closed__4);
l_Lean_getConstInfoDefn___rarg___lambda__1___closed__1 = _init_l_Lean_getConstInfoDefn___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfoDefn___rarg___lambda__1___closed__1);
l_Lean_getConstInfoDefn___rarg___lambda__1___closed__2 = _init_l_Lean_getConstInfoDefn___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfoDefn___rarg___lambda__1___closed__2);
l_Lean_getConstInfoInduct___rarg___lambda__1___closed__1 = _init_l_Lean_getConstInfoInduct___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfoInduct___rarg___lambda__1___closed__1);
l_Lean_getConstInfoInduct___rarg___lambda__1___closed__2 = _init_l_Lean_getConstInfoInduct___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfoInduct___rarg___lambda__1___closed__2);
l_Lean_getConstInfoCtor___rarg___lambda__1___closed__1 = _init_l_Lean_getConstInfoCtor___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfoCtor___rarg___lambda__1___closed__1);
l_Lean_getConstInfoCtor___rarg___lambda__1___closed__2 = _init_l_Lean_getConstInfoCtor___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfoCtor___rarg___lambda__1___closed__2);
l_Lean_getConstInfoRec___rarg___lambda__1___closed__1 = _init_l_Lean_getConstInfoRec___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfoRec___rarg___lambda__1___closed__1);
l_Lean_getConstInfoRec___rarg___lambda__1___closed__2 = _init_l_Lean_getConstInfoRec___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfoRec___rarg___lambda__1___closed__2);
l_Lean_addDecl___rarg___lambda__3___closed__1 = _init_l_Lean_addDecl___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_addDecl___rarg___lambda__3___closed__1);
l_Lean_addDecl___rarg___lambda__3___closed__2 = _init_l_Lean_addDecl___rarg___lambda__3___closed__2();
lean_mark_persistent(l_Lean_addDecl___rarg___lambda__3___closed__2);
l_Lean_addDecl___rarg___lambda__3___closed__3 = _init_l_Lean_addDecl___rarg___lambda__3___closed__3();
lean_mark_persistent(l_Lean_addDecl___rarg___lambda__3___closed__3);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__1 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__1();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__1);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__2 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__2();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__2);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__4 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__4();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__4);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__5 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__5();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__5);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__6 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__6();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__6);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__7 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__7();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__7);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__8 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__8();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__8);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__10 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__10();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__10);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__11 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__11();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__11);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__12 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__12();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__12);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__13 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__13();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__13);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__14 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__14();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__14);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__16 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__16();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__16);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__17 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__17();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__17);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__18 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__18();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__18);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__19 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__19();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__19);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__20 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__20();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__20);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__21 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__21();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__21);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__22 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__22();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__22);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__23 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__23();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__23);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__24 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__24();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__24);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__25 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__25();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__25);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__26 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__26();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__26);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__27 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__27();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__27);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__28 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__28();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__28);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__29 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__29();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__29);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__30 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__30();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__30);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__31 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__31();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__31);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__32 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__32();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__32);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__33 = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__33();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__33);
l___private_Lean_MonadEnv_0__Lean_supportedRecursors = _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors();
lean_mark_persistent(l___private_Lean_MonadEnv_0__Lean_supportedRecursors);
l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__1 = _init_l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__1();
lean_mark_persistent(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__1);
l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2 = _init_l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2();
lean_mark_persistent(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2);
l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__3 = _init_l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__3();
lean_mark_persistent(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__3);
l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4 = _init_l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4();
lean_mark_persistent(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4);
l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__1 = _init_l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__1);
l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__2 = _init_l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__2);
l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__3 = _init_l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__3);
l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__4 = _init_l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_findModuleOf_x3f___rarg___lambda__1___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
