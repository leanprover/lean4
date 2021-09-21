// Lean compiler output
// Module: Lean.MonadEnv
// Imports: Init Lean.Environment Lean.Exception Lean.Declaration Lean.Util.FindExpr Lean.AuxRecursor
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
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2(lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__30;
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_evalConst(lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3;
static lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_hasConst___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___rarg(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__5;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_evalConst___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst(lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__18;
static lean_object* l_Lean_getConstInfoInduct___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f(lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15;
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__6;
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__29;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConst___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_addAndCompile___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__10;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__32;
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_withoutModifyingEnv___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__24;
LEAN_EXPORT lean_object* l_Lean_matchConstStruct___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addAndCompile___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStruct___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__7;
LEAN_EXPORT lean_object* l_Lean_addAndCompile___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___rarg___lambda__1___boxed(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__16;
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__11;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStruct___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConst(lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__31;
LEAN_EXPORT lean_object* l_Lean_matchConstInduct(lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__26;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isInductivePredicate_visit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo(lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__19;
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_evalConst___spec__1(lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck(lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_isInductive___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1(lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__12;
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxName___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductivePredicate___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_mkAuxName___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___rarg___lambda__1(lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__22;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__8;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___rarg___lambda__1___closed__2;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__33;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__13;
LEAN_EXPORT lean_object* l_Lean_isInductivePredicate_visit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstInduct___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__21;
LEAN_EXPORT lean_object* l_Lean_isRecCore___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__23;
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_mkAuxNameAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoRec___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_evalConstCheck___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductivePredicate___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstStruct(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoRec___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_compile_decl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams(lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_matchConst___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at_Lean_isEnumType___spec__1___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__17;
uint8_t lean_level_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_checkUnsupported___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__27;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_matchConstCtor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductivePredicate(lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors;
LEAN_EXPORT lean_object* l_Lean_matchConstCtor___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__28;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__14;
static lean_object* l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__4;
LEAN_EXPORT lean_object* l_Lean_compileDecl___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoInduct___rarg___lambda__1___closed__1;
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
LEAN_EXPORT uint8_t l_Lean_isInductivePredicate_visit(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_levelZero;
x_4 = lean_level_eq(x_2, x_3);
return x_4;
}
case 7:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 2);
x_1 = x_5;
goto _start;
}
default: 
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductivePredicate_visit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_isInductivePredicate_visit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductivePredicate___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_isInductivePredicate_visit(x_13);
lean_dec(x_13);
x_17 = lean_box(x_16);
x_18 = lean_apply_2(x_15, lean_box(0), x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_apply_2(x_20, lean_box(0), x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductivePredicate___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_isInductivePredicate___rarg___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductivePredicate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_isInductivePredicate___rarg), 3, 0);
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
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_withoutModifyingEnv___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l_Lean_withoutModifyingEnv___rarg___lambda__2___closed__1;
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
x_8 = lean_alloc_closure((void*)(l_Lean_withoutModifyingEnv___rarg___lambda__2), 5, 4);
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
LEAN_EXPORT lean_object* l_Lean_withoutModifyingEnv___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_withoutModifyingEnv___rarg___lambda__1(x_1);
lean_dec(x_1);
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
x_1 = lean_mk_string("unknown constant '");
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
x_1 = lean_mk_string("'");
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
x_7 = l_Lean_mkConst(x_1, x_6);
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
x_7 = l_Lean_mkLevelParam(x_5);
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
x_11 = l_Lean_mkLevelParam(x_9);
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
x_9 = l_Lean_mkConst(x_2, x_8);
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
static lean_object* _init_l_Lean_getConstInfoInduct___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a inductive type");
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
x_10 = l_Lean_mkConst(x_1, x_9);
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
x_1 = lean_mk_string("' is not a constructor");
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
x_10 = l_Lean_mkConst(x_1, x_9);
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
x_1 = lean_mk_string("' is not a recursor");
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
x_10 = l_Lean_mkConst(x_1, x_9);
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
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 4);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_apply_1(x_2, x_17);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Lean_getConstInfo___rarg(x_3, x_4, x_5, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_matchConstStruct___rarg___lambda__1), 5, 4);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_6);
lean_closure_set(x_22, 2, x_14);
lean_closure_set(x_22, 3, x_7);
x_23 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = lean_apply_1(x_2, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_box(0);
x_27 = lean_apply_1(x_2, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_box(0);
x_29 = lean_apply_1(x_2, x_28);
return x_29;
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
LEAN_EXPORT lean_object* l_Lean_addDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_addDecl___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_2);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_addDecl___rarg), 5, 0);
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
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Empty");
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rec");
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__2;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("False");
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__6;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ndrec");
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("recOn");
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("casesOn");
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__9;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__6;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__2;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("And");
return x_1;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__20;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__20;
x_2 = l___private_Lean_MonadEnv_0__Lean_supportedRecursors___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
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
x_1 = lean_mk_string("code generator does not support recursor '");
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
x_1 = lean_mk_string("' yet, consider using 'match ... with' and/or structural recursion");
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
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Expr_FindImpl_initCache;
x_9 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_2, x_3, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
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
x_22 = l_Lean_throwError___rarg(x_4, x_5, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_5);
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
lean_dec(x_4);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = lean_apply_2(x_24, lean_box(0), x_25);
return x_26;
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
static lean_object* _init_l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 8192;
x_2 = lean_box_usize(x_1);
return x_2;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
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
x_15 = 8192;
x_16 = l_Lean_Expr_FindImpl_initCache;
lean_inc(x_14);
x_17 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_14, x_15, x_13, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___boxed__const__1;
lean_inc(x_2);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_20, 0, x_9);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_19);
lean_closure_set(x_20, 3, x_1);
lean_closure_set(x_20, 4, x_2);
lean_inc(x_2);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__3), 5, 4);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
lean_inc(x_11);
x_26 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_25, x_20);
x_27 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_26, x_21);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
if (lean_obj_tag(x_28) == 4)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___rarg(x_1, x_2, x_34);
lean_inc(x_11);
x_36 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_35, x_20);
x_37 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_36, x_21);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_28);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = lean_apply_2(x_39, lean_box(0), x_40);
lean_inc(x_11);
x_42 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_41, x_20);
x_43 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_42, x_21);
return x_43;
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
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg(x_1, x_2, x_3, x_4, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Expr_FindImpl_initCache;
lean_inc(x_3);
x_15 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_3, x_4, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box_usize(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_17);
lean_closure_set(x_18, 4, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_20, lean_box(0), x_21);
x_23 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_22, x_18);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
if (lean_obj_tag(x_24) == 4)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_32 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_31, x_18);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_24);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = lean_apply_2(x_34, lean_box(0), x_35);
x_37 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_36, x_18);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
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
static lean_object* _init_l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 8192;
x_2 = lean_box_usize(x_1);
return x_2;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
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
x_14 = 8192;
x_15 = l_Lean_Expr_FindImpl_initCache;
lean_inc(x_13);
x_16 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_13, x_14, x_12, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___boxed__const__1;
lean_inc(x_2);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_19, 0, x_9);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_13);
lean_closure_set(x_19, 4, x_18);
lean_inc(x_2);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___lambda__2), 5, 4);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = lean_apply_2(x_22, lean_box(0), x_23);
lean_inc(x_11);
x_25 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_24, x_19);
x_26 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_25, x_20);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
if (lean_obj_tag(x_27) == 4)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___rarg(x_1, x_2, x_33);
lean_inc(x_11);
x_35 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_34, x_19);
x_36 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_35, x_20);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_27);
lean_dec(x_2);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = lean_apply_2(x_38, lean_box(0), x_39);
lean_inc(x_11);
x_41 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_40, x_19);
x_42 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_41, x_20);
return x_42;
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
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Expr_FindImpl_initCache;
x_8 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_1, x_2, x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___rarg(x_4, x_5, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
lean_dec(x_5);
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 8192;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
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
x_10 = 8192;
x_11 = l_Lean_Expr_FindImpl_initCache;
x_12 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_9, x_10, x_8, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_15, lean_box(0), x_16);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___rarg(x_1, x_2, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = lean_apply_2(x_27, lean_box(0), x_28);
return x_29;
}
}
}
case 4:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_apply_2(x_31, lean_box(0), x_5);
return x_32;
}
case 5:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
lean_dec(x_4);
x_34 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg(x_1, x_2, x_3, x_5, x_33);
return x_34;
}
case 6:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
lean_dec(x_4);
x_36 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg(x_1, x_2, x_3, x_5, x_35);
return x_36;
}
default: 
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_5);
x_37 = lean_ctor_get(x_4, 0);
lean_inc(x_37);
lean_dec(x_4);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 2);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_alloc_closure((void*)(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_42, 0, x_3);
x_43 = 8192;
x_44 = l_Lean_Expr_FindImpl_initCache;
lean_inc(x_42);
x_45 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_42, x_43, x_40, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___boxed__const__1;
lean_inc(x_2);
lean_inc(x_1);
x_48 = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_48, 0, x_42);
lean_closure_set(x_48, 1, x_47);
lean_closure_set(x_48, 2, x_39);
lean_closure_set(x_48, 3, x_1);
lean_closure_set(x_48, 4, x_2);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_2);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_box(0);
x_52 = lean_apply_2(x_50, lean_box(0), x_51);
x_53 = lean_apply_4(x_41, lean_box(0), lean_box(0), x_52, x_48);
return x_53;
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
lean_dec(x_46);
if (lean_obj_tag(x_54) == 4)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__2;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___closed__4;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_throwError___rarg(x_1, x_2, x_60);
x_62 = lean_apply_4(x_41, lean_box(0), lean_box(0), x_61, x_48);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_54);
lean_dec(x_2);
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_box(0);
x_66 = lean_apply_2(x_64, lean_box(0), x_65);
x_67 = lean_apply_4(x_41, lean_box(0), lean_box(0), x_66, x_48);
return x_67;
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
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___lambda__2(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg___lambda__1(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__3___rarg(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___lambda__1(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___lambda__1(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_8;
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
x_9 = lean_compile_decl(x_1, x_8, x_2);
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
LEAN_EXPORT lean_object* l_Lean_addAndCompile___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_compileDecl___rarg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_addDecl___rarg(x_1, x_2, x_3, x_4, x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_addAndCompile___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_addAndCompile___rarg), 5, 0);
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
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Environment_allImportedModuleNames(x_3);
x_6 = l_Lean_instInhabitedName;
x_7 = lean_array_get(x_6, x_5, x_2);
lean_dec(x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_List_lengthTRAux___rarg(x_7, x_8);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_apply_2(x_13, lean_box(0), x_15);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_6, 2);
lean_inc(x_17);
x_18 = lean_nat_dec_eq(x_17, x_8);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_apply_2(x_20, lean_box(0), x_22);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
x_25 = lean_nat_dec_eq(x_24, x_8);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_apply_2(x_27, lean_box(0), x_29);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_6, 4);
lean_inc(x_31);
x_32 = l_List_isEmpty___rarg(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = lean_ctor_get_uint8(x_6, sizeof(void*)*5);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 3);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 1);
lean_dec(x_6);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_List_allM___at_Lean_isEnumType___spec__1___rarg(x_1, x_2, x_3, x_4, x_31);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = 0;
x_40 = lean_box(x_39);
x_41 = lean_apply_2(x_38, lean_box(0), x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = 0;
x_45 = lean_box(x_44);
x_46 = lean_apply_2(x_43, lean_box(0), x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = 0;
x_50 = lean_box(x_49);
x_51 = lean_apply_2(x_48, lean_box(0), x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
lean_dec(x_1);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = 0;
x_55 = lean_box(x_54);
x_56 = lean_apply_2(x_53, lean_box(0), x_55);
return x_56;
}
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
lean_dec(x_1);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = 0;
x_60 = lean_box(x_59);
x_61 = lean_apply_2(x_58, lean_box(0), x_60);
return x_61;
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Exception(lean_object*);
lean_object* initialize_Lean_Declaration(lean_object*);
lean_object* initialize_Lean_Util_FindExpr(lean_object*);
lean_object* initialize_Lean_AuxRecursor(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_MonadEnv(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AuxRecursor(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_withoutModifyingEnv___rarg___lambda__2___closed__1 = _init_l_Lean_withoutModifyingEnv___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_withoutModifyingEnv___rarg___lambda__2___closed__1);
l_Lean_getConstInfo___rarg___lambda__1___closed__1 = _init_l_Lean_getConstInfo___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___rarg___lambda__1___closed__1);
l_Lean_getConstInfo___rarg___lambda__1___closed__2 = _init_l_Lean_getConstInfo___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___rarg___lambda__1___closed__2);
l_Lean_getConstInfo___rarg___lambda__1___closed__3 = _init_l_Lean_getConstInfo___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___rarg___lambda__1___closed__3);
l_Lean_getConstInfo___rarg___lambda__1___closed__4 = _init_l_Lean_getConstInfo___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___rarg___lambda__1___closed__4);
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
l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___boxed__const__1 = _init_l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___boxed__const__1();
lean_mark_persistent(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__2___rarg___boxed__const__1);
l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___boxed__const__1 = _init_l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___boxed__const__1();
lean_mark_persistent(l_List_foldlM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__4___rarg___boxed__const__1);
l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___boxed__const__1 = _init_l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___boxed__const__1();
lean_mark_persistent(l_Lean_Declaration_foldExprM___at___private_Lean_MonadEnv_0__Lean_checkUnsupported___spec__1___rarg___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
