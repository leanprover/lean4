// Lean compiler output
// Module: Lean.Elab.PreDefinition.Basic
// Imports: Init Lean.Compiler.NoncomputableAttr Lean.Util.CollectLevelParams Lean.Meta.AbstractNestedProofs Lean.Elab.RecAppSyntax Lean.Elab.DefView
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_Elab_ensureNoRecFn___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_instInhabitedPreDefinition;
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_fixLevelParams___spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__6(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_addNonRec(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__15;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__21;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_fixLevelParams___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_noncomputableExt;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__12;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___closed__1;
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
lean_object* l_Lean_instBEqLocalInstance___boxed(lean_object*, lean_object*);
lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__6;
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__18;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__1(lean_object*, lean_object*, size_t, size_t);
extern lean_object* l_Lean_Expr_instBEqExpr;
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__10(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isExample(uint8_t);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__16;
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__14;
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableArray___rarg___boxed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_fixLevelParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyAttributesOf(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__20;
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__4;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__9;
lean_object* l_Lean_getMaxHeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_levelMVarToParamPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompileUnsafe___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___closed__1;
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_applyAttributesOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__8;
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__19;
LEAN_EXPORT lean_object* l_Lean_Elab_instantiateMVarsAtPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
LEAN_EXPORT lean_object* l_Lean_Elab_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_substitute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_fixLevelParams___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ensureNoRecFn___lambda__1___closed__3;
lean_object* l_Lean_instHashableLocalInstance___boxed(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__11;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_addAndCompileUnsafe___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_addAndCompileUnsafe___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__3(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__1;
size_t lean_usize_mod(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_ensureNoRecFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompileUnsafe___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_addAndCompileUnsafe___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__7;
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__2;
lean_object* l_Lean_Meta_forEachExpr___at_Lean_Meta_setMVarUserNamesAt___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_Cache_new(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_instInhabitedPreDefinition___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___closed__1;
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_ensureNoRecFn___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___lambda__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addAndCompileUnsafe___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_ensureNoRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_save___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__17;
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_ensureNoRecFn___lambda__1___closed__2;
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_expandDeclId___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instBEqArray___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdataExpr_x21(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2;
static lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_Cache_store(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ensureNoRecFn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addAndCompileUnsafe___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__13;
static lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 0;
x_4 = 0;
x_5 = l_Lean_Elab_instInhabitedPreDefinition___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = 0;
x_4 = l_Lean_Elab_instInhabitedPreDefinition___closed__2;
x_5 = lean_box(0);
x_6 = l_Lean_Elab_instInhabitedPreDefinition___closed__3;
x_7 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set(x_7, 4, x_6);
lean_ctor_set(x_7, 5, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*6, x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_instInhabitedPreDefinition() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_instInhabitedPreDefinition___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_13, 4);
x_18 = lean_ctor_get(x_13, 5);
x_19 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_ctor_set(x_13, 5, x_23);
lean_ctor_set(x_13, 4, x_20);
x_25 = 1;
x_26 = lean_usize_add(x_2, x_25);
x_27 = lean_array_uset(x_15, x_2, x_13);
x_2 = x_26;
x_3 = x_27;
x_10 = x_24;
goto _start;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get_uint8(x_13, sizeof(void*)*6);
x_31 = lean_ctor_get(x_13, 1);
x_32 = lean_ctor_get(x_13, 2);
x_33 = lean_ctor_get(x_13, 3);
x_34 = lean_ctor_get(x_13, 4);
x_35 = lean_ctor_get(x_13, 5);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_29);
lean_dec(x_13);
x_36 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_34, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_31);
lean_ctor_set(x_42, 2, x_32);
lean_ctor_set(x_42, 3, x_33);
lean_ctor_set(x_42, 4, x_37);
lean_ctor_set(x_42, 5, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*6, x_30);
x_43 = 1;
x_44 = lean_usize_add(x_2, x_43);
x_45 = lean_array_uset(x_15, x_2, x_42);
x_2 = x_44;
x_3 = x_45;
x_10 = x_41;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_instantiateMVarsAtPreDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1(x_10, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_instantiateMVarsAtPreDecls___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_13, 4);
x_18 = lean_ctor_get(x_13, 5);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___closed__1;
x_20 = l_Lean_Elab_Term_levelMVarToParam(x_17, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Term_levelMVarToParam(x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set(x_13, 5, x_24);
lean_ctor_set(x_13, 4, x_21);
x_26 = 1;
x_27 = lean_usize_add(x_2, x_26);
x_28 = lean_array_uset(x_15, x_2, x_13);
x_2 = x_27;
x_3 = x_28;
x_10 = x_25;
goto _start;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get_uint8(x_13, sizeof(void*)*6);
x_32 = lean_ctor_get(x_13, 1);
x_33 = lean_ctor_get(x_13, 2);
x_34 = lean_ctor_get(x_13, 3);
x_35 = lean_ctor_get(x_13, 4);
x_36 = lean_ctor_get(x_13, 5);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_30);
lean_dec(x_13);
x_37 = l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___closed__1;
x_38 = l_Lean_Elab_Term_levelMVarToParam(x_35, x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_Term_levelMVarToParam(x_36, x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_44, 0, x_30);
lean_ctor_set(x_44, 1, x_32);
lean_ctor_set(x_44, 2, x_33);
lean_ctor_set(x_44, 3, x_34);
lean_ctor_set(x_44, 4, x_39);
lean_ctor_set(x_44, 5, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_31);
x_45 = 1;
x_46 = lean_usize_add(x_2, x_45);
x_47 = lean_array_uset(x_15, x_2, x_44);
x_2 = x_46;
x_3 = x_47;
x_10 = x_43;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_levelMVarToParamPreDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1(x_10, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
x_16 = l_Lean_CollectLevelParams_main(x_15, x_4);
x_17 = lean_ctor_get(x_14, 5);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_CollectLevelParams_main(x_17, x_16);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_4 = x_18;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1;
x_2 = l_Lean_Elab_instInhabitedPreDefinition___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2;
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1(x_1, x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_sortDeclLevelParams(x_2, x_3, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_4);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_ctor_get(x_26, 2);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_sortDeclLevelParams(x_2, x_3, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_fixLevelParams___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
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
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_236; size_t x_237; size_t x_238; size_t x_239; lean_object* x_240; size_t x_241; uint8_t x_242; 
x_236 = lean_ctor_get(x_4, 0);
lean_inc(x_236);
x_237 = lean_ptr_addr(x_3);
x_238 = lean_ctor_get_usize(x_4, 1);
x_239 = lean_usize_mod(x_237, x_238);
x_240 = lean_array_uget(x_236, x_239);
x_241 = lean_ptr_addr(x_240);
lean_dec(x_240);
x_242 = lean_usize_dec_eq(x_237, x_241);
if (x_242 == 0)
{
lean_dec(x_236);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_243 = lean_ctor_get(x_3, 0);
lean_inc(x_243);
x_244 = lean_array_get_size(x_1);
x_245 = lean_unsigned_to_nat(0u);
x_246 = lean_nat_dec_lt(x_245, x_244);
if (x_246 == 0)
{
lean_object* x_247; 
lean_dec(x_244);
lean_dec(x_243);
x_247 = lean_box(0);
x_5 = x_247;
goto block_235;
}
else
{
size_t x_248; size_t x_249; uint8_t x_250; 
x_248 = 0;
x_249 = lean_usize_of_nat(x_244);
lean_dec(x_244);
x_250 = l_Array_anyMUnsafe_any___at_Lean_Elab_fixLevelParams___spec__1(x_243, x_1, x_248, x_249);
if (x_250 == 0)
{
lean_object* x_251; 
lean_dec(x_243);
x_251 = lean_box(0);
x_5 = x_251;
goto block_235;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = l_Lean_Expr_const___override(x_243, x_2);
lean_inc(x_252);
x_253 = l_Lean_Expr_ReplaceImpl_Cache_store(x_4, x_3, x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
else
{
lean_object* x_255; 
x_255 = lean_box(0);
x_5 = x_255;
goto block_235;
}
}
else
{
size_t x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_3);
lean_dec(x_2);
x_256 = lean_usize_add(x_239, x_238);
x_257 = lean_array_uget(x_236, x_256);
lean_dec(x_236);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_4);
return x_258;
}
block_235:
{
lean_dec(x_5);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_8 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_6, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_7);
x_11 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_7, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_16 = lean_ptr_addr(x_9);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_Lean_Expr_app___override(x_9, x_13);
lean_inc(x_18);
x_19 = l_Lean_Expr_ReplaceImpl_Cache_store(x_14, x_3, x_18);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_21 = lean_ptr_addr(x_13);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Expr_app___override(x_9, x_13);
lean_inc(x_23);
x_24 = l_Lean_Expr_ReplaceImpl_Cache_store(x_14, x_3, x_23);
lean_ctor_set(x_11, 1, x_24);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
else
{
lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_9);
lean_inc_n(x_3, 2);
x_25 = l_Lean_Expr_ReplaceImpl_Cache_store(x_14, x_3, x_3);
lean_ctor_set(x_11, 1, x_25);
lean_ctor_set(x_11, 0, x_3);
return x_11;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_29 = lean_ptr_addr(x_9);
x_30 = lean_usize_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_7);
x_31 = l_Lean_Expr_app___override(x_9, x_26);
lean_inc(x_31);
x_32 = l_Lean_Expr_ReplaceImpl_Cache_store(x_27, x_3, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
size_t x_34; size_t x_35; uint8_t x_36; 
x_34 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_35 = lean_ptr_addr(x_26);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_Lean_Expr_app___override(x_9, x_26);
lean_inc(x_37);
x_38 = l_Lean_Expr_ReplaceImpl_Cache_store(x_27, x_3, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_26);
lean_dec(x_9);
lean_inc_n(x_3, 2);
x_40 = l_Lean_Expr_ReplaceImpl_Cache_store(x_27, x_3, x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_3);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
case 6:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 2);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_43);
lean_inc(x_2);
x_46 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_43, x_4);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_44);
x_49 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_44, x_48);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_53 = l_Lean_Expr_lam___override(x_42, x_43, x_44, x_45);
x_54 = lean_ptr_addr(x_43);
lean_dec(x_43);
x_55 = lean_ptr_addr(x_47);
x_56 = lean_usize_dec_eq(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_53);
lean_dec(x_44);
x_57 = l_Lean_Expr_lam___override(x_42, x_47, x_51, x_45);
lean_inc(x_57);
x_58 = l_Lean_Expr_ReplaceImpl_Cache_store(x_52, x_3, x_57);
lean_ctor_set(x_49, 1, x_58);
lean_ctor_set(x_49, 0, x_57);
return x_49;
}
else
{
size_t x_59; size_t x_60; uint8_t x_61; 
x_59 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_60 = lean_ptr_addr(x_51);
x_61 = lean_usize_dec_eq(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_53);
x_62 = l_Lean_Expr_lam___override(x_42, x_47, x_51, x_45);
lean_inc(x_62);
x_63 = l_Lean_Expr_ReplaceImpl_Cache_store(x_52, x_3, x_62);
lean_ctor_set(x_49, 1, x_63);
lean_ctor_set(x_49, 0, x_62);
return x_49;
}
else
{
uint8_t x_64; 
x_64 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_45, x_45);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_53);
x_65 = l_Lean_Expr_lam___override(x_42, x_47, x_51, x_45);
lean_inc(x_65);
x_66 = l_Lean_Expr_ReplaceImpl_Cache_store(x_52, x_3, x_65);
lean_ctor_set(x_49, 1, x_66);
lean_ctor_set(x_49, 0, x_65);
return x_49;
}
else
{
lean_object* x_67; 
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_42);
lean_inc(x_53);
x_67 = l_Lean_Expr_ReplaceImpl_Cache_store(x_52, x_3, x_53);
lean_ctor_set(x_49, 1, x_67);
lean_ctor_set(x_49, 0, x_53);
return x_49;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_49, 0);
x_69 = lean_ctor_get(x_49, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_49);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_70 = l_Lean_Expr_lam___override(x_42, x_43, x_44, x_45);
x_71 = lean_ptr_addr(x_43);
lean_dec(x_43);
x_72 = lean_ptr_addr(x_47);
x_73 = lean_usize_dec_eq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_70);
lean_dec(x_44);
x_74 = l_Lean_Expr_lam___override(x_42, x_47, x_68, x_45);
lean_inc(x_74);
x_75 = l_Lean_Expr_ReplaceImpl_Cache_store(x_69, x_3, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
else
{
size_t x_77; size_t x_78; uint8_t x_79; 
x_77 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_78 = lean_ptr_addr(x_68);
x_79 = lean_usize_dec_eq(x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_70);
x_80 = l_Lean_Expr_lam___override(x_42, x_47, x_68, x_45);
lean_inc(x_80);
x_81 = l_Lean_Expr_ReplaceImpl_Cache_store(x_69, x_3, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
else
{
uint8_t x_83; 
x_83 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_45, x_45);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_70);
x_84 = l_Lean_Expr_lam___override(x_42, x_47, x_68, x_45);
lean_inc(x_84);
x_85 = l_Lean_Expr_ReplaceImpl_Cache_store(x_69, x_3, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_68);
lean_dec(x_47);
lean_dec(x_42);
lean_inc(x_70);
x_87 = l_Lean_Expr_ReplaceImpl_Cache_store(x_69, x_3, x_70);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_70);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
case 7:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_89 = lean_ctor_get(x_3, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_3, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_3, 2);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_90);
lean_inc(x_2);
x_93 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_90, x_4);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_91);
x_96 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_91, x_95);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; size_t x_101; size_t x_102; uint8_t x_103; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
x_100 = l_Lean_Expr_forallE___override(x_89, x_90, x_91, x_92);
x_101 = lean_ptr_addr(x_90);
lean_dec(x_90);
x_102 = lean_ptr_addr(x_94);
x_103 = lean_usize_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_100);
lean_dec(x_91);
x_104 = l_Lean_Expr_forallE___override(x_89, x_94, x_98, x_92);
lean_inc(x_104);
x_105 = l_Lean_Expr_ReplaceImpl_Cache_store(x_99, x_3, x_104);
lean_ctor_set(x_96, 1, x_105);
lean_ctor_set(x_96, 0, x_104);
return x_96;
}
else
{
size_t x_106; size_t x_107; uint8_t x_108; 
x_106 = lean_ptr_addr(x_91);
lean_dec(x_91);
x_107 = lean_ptr_addr(x_98);
x_108 = lean_usize_dec_eq(x_106, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_100);
x_109 = l_Lean_Expr_forallE___override(x_89, x_94, x_98, x_92);
lean_inc(x_109);
x_110 = l_Lean_Expr_ReplaceImpl_Cache_store(x_99, x_3, x_109);
lean_ctor_set(x_96, 1, x_110);
lean_ctor_set(x_96, 0, x_109);
return x_96;
}
else
{
uint8_t x_111; 
x_111 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_92, x_92);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_100);
x_112 = l_Lean_Expr_forallE___override(x_89, x_94, x_98, x_92);
lean_inc(x_112);
x_113 = l_Lean_Expr_ReplaceImpl_Cache_store(x_99, x_3, x_112);
lean_ctor_set(x_96, 1, x_113);
lean_ctor_set(x_96, 0, x_112);
return x_96;
}
else
{
lean_object* x_114; 
lean_dec(x_98);
lean_dec(x_94);
lean_dec(x_89);
lean_inc(x_100);
x_114 = l_Lean_Expr_ReplaceImpl_Cache_store(x_99, x_3, x_100);
lean_ctor_set(x_96, 1, x_114);
lean_ctor_set(x_96, 0, x_100);
return x_96;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; size_t x_118; size_t x_119; uint8_t x_120; 
x_115 = lean_ctor_get(x_96, 0);
x_116 = lean_ctor_get(x_96, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_96);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
x_117 = l_Lean_Expr_forallE___override(x_89, x_90, x_91, x_92);
x_118 = lean_ptr_addr(x_90);
lean_dec(x_90);
x_119 = lean_ptr_addr(x_94);
x_120 = lean_usize_dec_eq(x_118, x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_117);
lean_dec(x_91);
x_121 = l_Lean_Expr_forallE___override(x_89, x_94, x_115, x_92);
lean_inc(x_121);
x_122 = l_Lean_Expr_ReplaceImpl_Cache_store(x_116, x_3, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
else
{
size_t x_124; size_t x_125; uint8_t x_126; 
x_124 = lean_ptr_addr(x_91);
lean_dec(x_91);
x_125 = lean_ptr_addr(x_115);
x_126 = lean_usize_dec_eq(x_124, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_117);
x_127 = l_Lean_Expr_forallE___override(x_89, x_94, x_115, x_92);
lean_inc(x_127);
x_128 = l_Lean_Expr_ReplaceImpl_Cache_store(x_116, x_3, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
else
{
uint8_t x_130; 
x_130 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_92, x_92);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_117);
x_131 = l_Lean_Expr_forallE___override(x_89, x_94, x_115, x_92);
lean_inc(x_131);
x_132 = l_Lean_Expr_ReplaceImpl_Cache_store(x_116, x_3, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_115);
lean_dec(x_94);
lean_dec(x_89);
lean_inc(x_117);
x_134 = l_Lean_Expr_ReplaceImpl_Cache_store(x_116, x_3, x_117);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_117);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
}
case 8:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_136 = lean_ctor_get(x_3, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_3, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_3, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_3, 3);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 8);
lean_inc(x_137);
lean_inc(x_2);
x_141 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_137, x_4);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_138);
lean_inc(x_2);
x_144 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_138, x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_139);
x_147 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_139, x_146);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; size_t x_151; size_t x_152; uint8_t x_153; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = lean_ctor_get(x_147, 1);
x_151 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_152 = lean_ptr_addr(x_142);
x_153 = lean_usize_dec_eq(x_151, x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_139);
lean_dec(x_138);
x_154 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_149, x_140);
lean_inc(x_154);
x_155 = l_Lean_Expr_ReplaceImpl_Cache_store(x_150, x_3, x_154);
lean_ctor_set(x_147, 1, x_155);
lean_ctor_set(x_147, 0, x_154);
return x_147;
}
else
{
size_t x_156; size_t x_157; uint8_t x_158; 
x_156 = lean_ptr_addr(x_138);
lean_dec(x_138);
x_157 = lean_ptr_addr(x_145);
x_158 = lean_usize_dec_eq(x_156, x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_139);
x_159 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_149, x_140);
lean_inc(x_159);
x_160 = l_Lean_Expr_ReplaceImpl_Cache_store(x_150, x_3, x_159);
lean_ctor_set(x_147, 1, x_160);
lean_ctor_set(x_147, 0, x_159);
return x_147;
}
else
{
size_t x_161; size_t x_162; uint8_t x_163; 
x_161 = lean_ptr_addr(x_139);
lean_dec(x_139);
x_162 = lean_ptr_addr(x_149);
x_163 = lean_usize_dec_eq(x_161, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_149, x_140);
lean_inc(x_164);
x_165 = l_Lean_Expr_ReplaceImpl_Cache_store(x_150, x_3, x_164);
lean_ctor_set(x_147, 1, x_165);
lean_ctor_set(x_147, 0, x_164);
return x_147;
}
else
{
lean_object* x_166; 
lean_dec(x_149);
lean_dec(x_145);
lean_dec(x_142);
lean_dec(x_136);
lean_inc_n(x_3, 2);
x_166 = l_Lean_Expr_ReplaceImpl_Cache_store(x_150, x_3, x_3);
lean_ctor_set(x_147, 1, x_166);
lean_ctor_set(x_147, 0, x_3);
return x_147;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; size_t x_169; size_t x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_147, 0);
x_168 = lean_ctor_get(x_147, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_147);
x_169 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_170 = lean_ptr_addr(x_142);
x_171 = lean_usize_dec_eq(x_169, x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
x_172 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_167, x_140);
lean_inc(x_172);
x_173 = l_Lean_Expr_ReplaceImpl_Cache_store(x_168, x_3, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
else
{
size_t x_175; size_t x_176; uint8_t x_177; 
x_175 = lean_ptr_addr(x_138);
lean_dec(x_138);
x_176 = lean_ptr_addr(x_145);
x_177 = lean_usize_dec_eq(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_139);
x_178 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_167, x_140);
lean_inc(x_178);
x_179 = l_Lean_Expr_ReplaceImpl_Cache_store(x_168, x_3, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
else
{
size_t x_181; size_t x_182; uint8_t x_183; 
x_181 = lean_ptr_addr(x_139);
lean_dec(x_139);
x_182 = lean_ptr_addr(x_167);
x_183 = lean_usize_dec_eq(x_181, x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_167, x_140);
lean_inc(x_184);
x_185 = l_Lean_Expr_ReplaceImpl_Cache_store(x_168, x_3, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_167);
lean_dec(x_145);
lean_dec(x_142);
lean_dec(x_136);
lean_inc_n(x_3, 2);
x_187 = l_Lean_Expr_ReplaceImpl_Cache_store(x_168, x_3, x_3);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_3);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
}
}
case 10:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_189 = lean_ctor_get(x_3, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_3, 1);
lean_inc(x_190);
lean_inc(x_190);
x_191 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_190, x_4);
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; size_t x_195; size_t x_196; uint8_t x_197; 
x_193 = lean_ctor_get(x_191, 0);
x_194 = lean_ctor_get(x_191, 1);
x_195 = lean_ptr_addr(x_190);
lean_dec(x_190);
x_196 = lean_ptr_addr(x_193);
x_197 = lean_usize_dec_eq(x_195, x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
x_198 = l_Lean_Expr_mdata___override(x_189, x_193);
lean_inc(x_198);
x_199 = l_Lean_Expr_ReplaceImpl_Cache_store(x_194, x_3, x_198);
lean_ctor_set(x_191, 1, x_199);
lean_ctor_set(x_191, 0, x_198);
return x_191;
}
else
{
lean_object* x_200; 
lean_dec(x_193);
lean_dec(x_189);
lean_inc_n(x_3, 2);
x_200 = l_Lean_Expr_ReplaceImpl_Cache_store(x_194, x_3, x_3);
lean_ctor_set(x_191, 1, x_200);
lean_ctor_set(x_191, 0, x_3);
return x_191;
}
}
else
{
lean_object* x_201; lean_object* x_202; size_t x_203; size_t x_204; uint8_t x_205; 
x_201 = lean_ctor_get(x_191, 0);
x_202 = lean_ctor_get(x_191, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_191);
x_203 = lean_ptr_addr(x_190);
lean_dec(x_190);
x_204 = lean_ptr_addr(x_201);
x_205 = lean_usize_dec_eq(x_203, x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = l_Lean_Expr_mdata___override(x_189, x_201);
lean_inc(x_206);
x_207 = l_Lean_Expr_ReplaceImpl_Cache_store(x_202, x_3, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_201);
lean_dec(x_189);
lean_inc_n(x_3, 2);
x_209 = l_Lean_Expr_ReplaceImpl_Cache_store(x_202, x_3, x_3);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_3);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
case 11:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_211 = lean_ctor_get(x_3, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_3, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_3, 2);
lean_inc(x_213);
lean_inc(x_213);
x_214 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_213, x_4);
x_215 = !lean_is_exclusive(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; size_t x_218; size_t x_219; uint8_t x_220; 
x_216 = lean_ctor_get(x_214, 0);
x_217 = lean_ctor_get(x_214, 1);
x_218 = lean_ptr_addr(x_213);
lean_dec(x_213);
x_219 = lean_ptr_addr(x_216);
x_220 = lean_usize_dec_eq(x_218, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = l_Lean_Expr_proj___override(x_211, x_212, x_216);
lean_inc(x_221);
x_222 = l_Lean_Expr_ReplaceImpl_Cache_store(x_217, x_3, x_221);
lean_ctor_set(x_214, 1, x_222);
lean_ctor_set(x_214, 0, x_221);
return x_214;
}
else
{
lean_object* x_223; 
lean_dec(x_216);
lean_dec(x_212);
lean_dec(x_211);
lean_inc_n(x_3, 2);
x_223 = l_Lean_Expr_ReplaceImpl_Cache_store(x_217, x_3, x_3);
lean_ctor_set(x_214, 1, x_223);
lean_ctor_set(x_214, 0, x_3);
return x_214;
}
}
else
{
lean_object* x_224; lean_object* x_225; size_t x_226; size_t x_227; uint8_t x_228; 
x_224 = lean_ctor_get(x_214, 0);
x_225 = lean_ctor_get(x_214, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_214);
x_226 = lean_ptr_addr(x_213);
lean_dec(x_213);
x_227 = lean_ptr_addr(x_224);
x_228 = lean_usize_dec_eq(x_226, x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = l_Lean_Expr_proj___override(x_211, x_212, x_224);
lean_inc(x_229);
x_230 = l_Lean_Expr_ReplaceImpl_Cache_store(x_225, x_3, x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_224);
lean_dec(x_212);
lean_dec(x_211);
lean_inc_n(x_3, 2);
x_232 = l_Lean_Expr_ReplaceImpl_Cache_store(x_225, x_3, x_3);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_3);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
default: 
{
lean_object* x_234; 
lean_dec(x_2);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_3);
lean_ctor_set(x_234, 1, x_4);
return x_234;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_236; size_t x_237; size_t x_238; size_t x_239; lean_object* x_240; size_t x_241; uint8_t x_242; 
x_236 = lean_ctor_get(x_4, 0);
lean_inc(x_236);
x_237 = lean_ptr_addr(x_3);
x_238 = lean_ctor_get_usize(x_4, 1);
x_239 = lean_usize_mod(x_237, x_238);
x_240 = lean_array_uget(x_236, x_239);
x_241 = lean_ptr_addr(x_240);
lean_dec(x_240);
x_242 = lean_usize_dec_eq(x_237, x_241);
if (x_242 == 0)
{
lean_dec(x_236);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_243 = lean_ctor_get(x_3, 0);
lean_inc(x_243);
x_244 = lean_array_get_size(x_1);
x_245 = lean_unsigned_to_nat(0u);
x_246 = lean_nat_dec_lt(x_245, x_244);
if (x_246 == 0)
{
lean_object* x_247; 
lean_dec(x_244);
lean_dec(x_243);
x_247 = lean_box(0);
x_5 = x_247;
goto block_235;
}
else
{
size_t x_248; size_t x_249; uint8_t x_250; 
x_248 = 0;
x_249 = lean_usize_of_nat(x_244);
lean_dec(x_244);
x_250 = l_Array_anyMUnsafe_any___at_Lean_Elab_fixLevelParams___spec__1(x_243, x_1, x_248, x_249);
if (x_250 == 0)
{
lean_object* x_251; 
lean_dec(x_243);
x_251 = lean_box(0);
x_5 = x_251;
goto block_235;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = l_Lean_Expr_const___override(x_243, x_2);
lean_inc(x_252);
x_253 = l_Lean_Expr_ReplaceImpl_Cache_store(x_4, x_3, x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
else
{
lean_object* x_255; 
x_255 = lean_box(0);
x_5 = x_255;
goto block_235;
}
}
else
{
size_t x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_3);
lean_dec(x_2);
x_256 = lean_usize_add(x_239, x_238);
x_257 = lean_array_uget(x_236, x_256);
lean_dec(x_236);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_4);
return x_258;
}
block_235:
{
lean_dec(x_5);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_8 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_6, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_7);
x_11 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_7, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_16 = lean_ptr_addr(x_9);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_Lean_Expr_app___override(x_9, x_13);
lean_inc(x_18);
x_19 = l_Lean_Expr_ReplaceImpl_Cache_store(x_14, x_3, x_18);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_21 = lean_ptr_addr(x_13);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Expr_app___override(x_9, x_13);
lean_inc(x_23);
x_24 = l_Lean_Expr_ReplaceImpl_Cache_store(x_14, x_3, x_23);
lean_ctor_set(x_11, 1, x_24);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
else
{
lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_9);
lean_inc_n(x_3, 2);
x_25 = l_Lean_Expr_ReplaceImpl_Cache_store(x_14, x_3, x_3);
lean_ctor_set(x_11, 1, x_25);
lean_ctor_set(x_11, 0, x_3);
return x_11;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_29 = lean_ptr_addr(x_9);
x_30 = lean_usize_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_7);
x_31 = l_Lean_Expr_app___override(x_9, x_26);
lean_inc(x_31);
x_32 = l_Lean_Expr_ReplaceImpl_Cache_store(x_27, x_3, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
size_t x_34; size_t x_35; uint8_t x_36; 
x_34 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_35 = lean_ptr_addr(x_26);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_Lean_Expr_app___override(x_9, x_26);
lean_inc(x_37);
x_38 = l_Lean_Expr_ReplaceImpl_Cache_store(x_27, x_3, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_26);
lean_dec(x_9);
lean_inc_n(x_3, 2);
x_40 = l_Lean_Expr_ReplaceImpl_Cache_store(x_27, x_3, x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_3);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
case 6:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 2);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_43);
lean_inc(x_2);
x_46 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_43, x_4);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_44);
x_49 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_44, x_48);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_53 = l_Lean_Expr_lam___override(x_42, x_43, x_44, x_45);
x_54 = lean_ptr_addr(x_43);
lean_dec(x_43);
x_55 = lean_ptr_addr(x_47);
x_56 = lean_usize_dec_eq(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_53);
lean_dec(x_44);
x_57 = l_Lean_Expr_lam___override(x_42, x_47, x_51, x_45);
lean_inc(x_57);
x_58 = l_Lean_Expr_ReplaceImpl_Cache_store(x_52, x_3, x_57);
lean_ctor_set(x_49, 1, x_58);
lean_ctor_set(x_49, 0, x_57);
return x_49;
}
else
{
size_t x_59; size_t x_60; uint8_t x_61; 
x_59 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_60 = lean_ptr_addr(x_51);
x_61 = lean_usize_dec_eq(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_53);
x_62 = l_Lean_Expr_lam___override(x_42, x_47, x_51, x_45);
lean_inc(x_62);
x_63 = l_Lean_Expr_ReplaceImpl_Cache_store(x_52, x_3, x_62);
lean_ctor_set(x_49, 1, x_63);
lean_ctor_set(x_49, 0, x_62);
return x_49;
}
else
{
uint8_t x_64; 
x_64 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_45, x_45);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_53);
x_65 = l_Lean_Expr_lam___override(x_42, x_47, x_51, x_45);
lean_inc(x_65);
x_66 = l_Lean_Expr_ReplaceImpl_Cache_store(x_52, x_3, x_65);
lean_ctor_set(x_49, 1, x_66);
lean_ctor_set(x_49, 0, x_65);
return x_49;
}
else
{
lean_object* x_67; 
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_42);
lean_inc(x_53);
x_67 = l_Lean_Expr_ReplaceImpl_Cache_store(x_52, x_3, x_53);
lean_ctor_set(x_49, 1, x_67);
lean_ctor_set(x_49, 0, x_53);
return x_49;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_49, 0);
x_69 = lean_ctor_get(x_49, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_49);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_70 = l_Lean_Expr_lam___override(x_42, x_43, x_44, x_45);
x_71 = lean_ptr_addr(x_43);
lean_dec(x_43);
x_72 = lean_ptr_addr(x_47);
x_73 = lean_usize_dec_eq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_70);
lean_dec(x_44);
x_74 = l_Lean_Expr_lam___override(x_42, x_47, x_68, x_45);
lean_inc(x_74);
x_75 = l_Lean_Expr_ReplaceImpl_Cache_store(x_69, x_3, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
else
{
size_t x_77; size_t x_78; uint8_t x_79; 
x_77 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_78 = lean_ptr_addr(x_68);
x_79 = lean_usize_dec_eq(x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_70);
x_80 = l_Lean_Expr_lam___override(x_42, x_47, x_68, x_45);
lean_inc(x_80);
x_81 = l_Lean_Expr_ReplaceImpl_Cache_store(x_69, x_3, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
else
{
uint8_t x_83; 
x_83 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_45, x_45);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_70);
x_84 = l_Lean_Expr_lam___override(x_42, x_47, x_68, x_45);
lean_inc(x_84);
x_85 = l_Lean_Expr_ReplaceImpl_Cache_store(x_69, x_3, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_68);
lean_dec(x_47);
lean_dec(x_42);
lean_inc(x_70);
x_87 = l_Lean_Expr_ReplaceImpl_Cache_store(x_69, x_3, x_70);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_70);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
case 7:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_89 = lean_ctor_get(x_3, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_3, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_3, 2);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_90);
lean_inc(x_2);
x_93 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_90, x_4);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_91);
x_96 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_91, x_95);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; size_t x_101; size_t x_102; uint8_t x_103; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
x_100 = l_Lean_Expr_forallE___override(x_89, x_90, x_91, x_92);
x_101 = lean_ptr_addr(x_90);
lean_dec(x_90);
x_102 = lean_ptr_addr(x_94);
x_103 = lean_usize_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_100);
lean_dec(x_91);
x_104 = l_Lean_Expr_forallE___override(x_89, x_94, x_98, x_92);
lean_inc(x_104);
x_105 = l_Lean_Expr_ReplaceImpl_Cache_store(x_99, x_3, x_104);
lean_ctor_set(x_96, 1, x_105);
lean_ctor_set(x_96, 0, x_104);
return x_96;
}
else
{
size_t x_106; size_t x_107; uint8_t x_108; 
x_106 = lean_ptr_addr(x_91);
lean_dec(x_91);
x_107 = lean_ptr_addr(x_98);
x_108 = lean_usize_dec_eq(x_106, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_100);
x_109 = l_Lean_Expr_forallE___override(x_89, x_94, x_98, x_92);
lean_inc(x_109);
x_110 = l_Lean_Expr_ReplaceImpl_Cache_store(x_99, x_3, x_109);
lean_ctor_set(x_96, 1, x_110);
lean_ctor_set(x_96, 0, x_109);
return x_96;
}
else
{
uint8_t x_111; 
x_111 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_92, x_92);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_100);
x_112 = l_Lean_Expr_forallE___override(x_89, x_94, x_98, x_92);
lean_inc(x_112);
x_113 = l_Lean_Expr_ReplaceImpl_Cache_store(x_99, x_3, x_112);
lean_ctor_set(x_96, 1, x_113);
lean_ctor_set(x_96, 0, x_112);
return x_96;
}
else
{
lean_object* x_114; 
lean_dec(x_98);
lean_dec(x_94);
lean_dec(x_89);
lean_inc(x_100);
x_114 = l_Lean_Expr_ReplaceImpl_Cache_store(x_99, x_3, x_100);
lean_ctor_set(x_96, 1, x_114);
lean_ctor_set(x_96, 0, x_100);
return x_96;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; size_t x_118; size_t x_119; uint8_t x_120; 
x_115 = lean_ctor_get(x_96, 0);
x_116 = lean_ctor_get(x_96, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_96);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
x_117 = l_Lean_Expr_forallE___override(x_89, x_90, x_91, x_92);
x_118 = lean_ptr_addr(x_90);
lean_dec(x_90);
x_119 = lean_ptr_addr(x_94);
x_120 = lean_usize_dec_eq(x_118, x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_117);
lean_dec(x_91);
x_121 = l_Lean_Expr_forallE___override(x_89, x_94, x_115, x_92);
lean_inc(x_121);
x_122 = l_Lean_Expr_ReplaceImpl_Cache_store(x_116, x_3, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
else
{
size_t x_124; size_t x_125; uint8_t x_126; 
x_124 = lean_ptr_addr(x_91);
lean_dec(x_91);
x_125 = lean_ptr_addr(x_115);
x_126 = lean_usize_dec_eq(x_124, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_117);
x_127 = l_Lean_Expr_forallE___override(x_89, x_94, x_115, x_92);
lean_inc(x_127);
x_128 = l_Lean_Expr_ReplaceImpl_Cache_store(x_116, x_3, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
else
{
uint8_t x_130; 
x_130 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_92, x_92);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_117);
x_131 = l_Lean_Expr_forallE___override(x_89, x_94, x_115, x_92);
lean_inc(x_131);
x_132 = l_Lean_Expr_ReplaceImpl_Cache_store(x_116, x_3, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_115);
lean_dec(x_94);
lean_dec(x_89);
lean_inc(x_117);
x_134 = l_Lean_Expr_ReplaceImpl_Cache_store(x_116, x_3, x_117);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_117);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
}
case 8:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_136 = lean_ctor_get(x_3, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_3, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_3, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_3, 3);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 8);
lean_inc(x_137);
lean_inc(x_2);
x_141 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_137, x_4);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_138);
lean_inc(x_2);
x_144 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_138, x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_139);
x_147 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_139, x_146);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; size_t x_151; size_t x_152; uint8_t x_153; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = lean_ctor_get(x_147, 1);
x_151 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_152 = lean_ptr_addr(x_142);
x_153 = lean_usize_dec_eq(x_151, x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_139);
lean_dec(x_138);
x_154 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_149, x_140);
lean_inc(x_154);
x_155 = l_Lean_Expr_ReplaceImpl_Cache_store(x_150, x_3, x_154);
lean_ctor_set(x_147, 1, x_155);
lean_ctor_set(x_147, 0, x_154);
return x_147;
}
else
{
size_t x_156; size_t x_157; uint8_t x_158; 
x_156 = lean_ptr_addr(x_138);
lean_dec(x_138);
x_157 = lean_ptr_addr(x_145);
x_158 = lean_usize_dec_eq(x_156, x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_139);
x_159 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_149, x_140);
lean_inc(x_159);
x_160 = l_Lean_Expr_ReplaceImpl_Cache_store(x_150, x_3, x_159);
lean_ctor_set(x_147, 1, x_160);
lean_ctor_set(x_147, 0, x_159);
return x_147;
}
else
{
size_t x_161; size_t x_162; uint8_t x_163; 
x_161 = lean_ptr_addr(x_139);
lean_dec(x_139);
x_162 = lean_ptr_addr(x_149);
x_163 = lean_usize_dec_eq(x_161, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_149, x_140);
lean_inc(x_164);
x_165 = l_Lean_Expr_ReplaceImpl_Cache_store(x_150, x_3, x_164);
lean_ctor_set(x_147, 1, x_165);
lean_ctor_set(x_147, 0, x_164);
return x_147;
}
else
{
lean_object* x_166; 
lean_dec(x_149);
lean_dec(x_145);
lean_dec(x_142);
lean_dec(x_136);
lean_inc_n(x_3, 2);
x_166 = l_Lean_Expr_ReplaceImpl_Cache_store(x_150, x_3, x_3);
lean_ctor_set(x_147, 1, x_166);
lean_ctor_set(x_147, 0, x_3);
return x_147;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; size_t x_169; size_t x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_147, 0);
x_168 = lean_ctor_get(x_147, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_147);
x_169 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_170 = lean_ptr_addr(x_142);
x_171 = lean_usize_dec_eq(x_169, x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
x_172 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_167, x_140);
lean_inc(x_172);
x_173 = l_Lean_Expr_ReplaceImpl_Cache_store(x_168, x_3, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
else
{
size_t x_175; size_t x_176; uint8_t x_177; 
x_175 = lean_ptr_addr(x_138);
lean_dec(x_138);
x_176 = lean_ptr_addr(x_145);
x_177 = lean_usize_dec_eq(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_139);
x_178 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_167, x_140);
lean_inc(x_178);
x_179 = l_Lean_Expr_ReplaceImpl_Cache_store(x_168, x_3, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
else
{
size_t x_181; size_t x_182; uint8_t x_183; 
x_181 = lean_ptr_addr(x_139);
lean_dec(x_139);
x_182 = lean_ptr_addr(x_167);
x_183 = lean_usize_dec_eq(x_181, x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_167, x_140);
lean_inc(x_184);
x_185 = l_Lean_Expr_ReplaceImpl_Cache_store(x_168, x_3, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_167);
lean_dec(x_145);
lean_dec(x_142);
lean_dec(x_136);
lean_inc_n(x_3, 2);
x_187 = l_Lean_Expr_ReplaceImpl_Cache_store(x_168, x_3, x_3);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_3);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
}
}
case 10:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_189 = lean_ctor_get(x_3, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_3, 1);
lean_inc(x_190);
lean_inc(x_190);
x_191 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_190, x_4);
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; size_t x_195; size_t x_196; uint8_t x_197; 
x_193 = lean_ctor_get(x_191, 0);
x_194 = lean_ctor_get(x_191, 1);
x_195 = lean_ptr_addr(x_190);
lean_dec(x_190);
x_196 = lean_ptr_addr(x_193);
x_197 = lean_usize_dec_eq(x_195, x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
x_198 = l_Lean_Expr_mdata___override(x_189, x_193);
lean_inc(x_198);
x_199 = l_Lean_Expr_ReplaceImpl_Cache_store(x_194, x_3, x_198);
lean_ctor_set(x_191, 1, x_199);
lean_ctor_set(x_191, 0, x_198);
return x_191;
}
else
{
lean_object* x_200; 
lean_dec(x_193);
lean_dec(x_189);
lean_inc_n(x_3, 2);
x_200 = l_Lean_Expr_ReplaceImpl_Cache_store(x_194, x_3, x_3);
lean_ctor_set(x_191, 1, x_200);
lean_ctor_set(x_191, 0, x_3);
return x_191;
}
}
else
{
lean_object* x_201; lean_object* x_202; size_t x_203; size_t x_204; uint8_t x_205; 
x_201 = lean_ctor_get(x_191, 0);
x_202 = lean_ctor_get(x_191, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_191);
x_203 = lean_ptr_addr(x_190);
lean_dec(x_190);
x_204 = lean_ptr_addr(x_201);
x_205 = lean_usize_dec_eq(x_203, x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = l_Lean_Expr_mdata___override(x_189, x_201);
lean_inc(x_206);
x_207 = l_Lean_Expr_ReplaceImpl_Cache_store(x_202, x_3, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_201);
lean_dec(x_189);
lean_inc_n(x_3, 2);
x_209 = l_Lean_Expr_ReplaceImpl_Cache_store(x_202, x_3, x_3);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_3);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
case 11:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_211 = lean_ctor_get(x_3, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_3, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_3, 2);
lean_inc(x_213);
lean_inc(x_213);
x_214 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_213, x_4);
x_215 = !lean_is_exclusive(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; size_t x_218; size_t x_219; uint8_t x_220; 
x_216 = lean_ctor_get(x_214, 0);
x_217 = lean_ctor_get(x_214, 1);
x_218 = lean_ptr_addr(x_213);
lean_dec(x_213);
x_219 = lean_ptr_addr(x_216);
x_220 = lean_usize_dec_eq(x_218, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = l_Lean_Expr_proj___override(x_211, x_212, x_216);
lean_inc(x_221);
x_222 = l_Lean_Expr_ReplaceImpl_Cache_store(x_217, x_3, x_221);
lean_ctor_set(x_214, 1, x_222);
lean_ctor_set(x_214, 0, x_221);
return x_214;
}
else
{
lean_object* x_223; 
lean_dec(x_216);
lean_dec(x_212);
lean_dec(x_211);
lean_inc_n(x_3, 2);
x_223 = l_Lean_Expr_ReplaceImpl_Cache_store(x_217, x_3, x_3);
lean_ctor_set(x_214, 1, x_223);
lean_ctor_set(x_214, 0, x_3);
return x_214;
}
}
else
{
lean_object* x_224; lean_object* x_225; size_t x_226; size_t x_227; uint8_t x_228; 
x_224 = lean_ctor_get(x_214, 0);
x_225 = lean_ctor_get(x_214, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_214);
x_226 = lean_ptr_addr(x_213);
lean_dec(x_213);
x_227 = lean_ptr_addr(x_224);
x_228 = lean_usize_dec_eq(x_226, x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = l_Lean_Expr_proj___override(x_211, x_212, x_224);
lean_inc(x_229);
x_230 = l_Lean_Expr_ReplaceImpl_Cache_store(x_225, x_3, x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_224);
lean_dec(x_212);
lean_dec(x_211);
lean_inc_n(x_3, 2);
x_232 = l_Lean_Expr_ReplaceImpl_Cache_store(x_225, x_3, x_3);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_3);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
default: 
{
lean_object* x_234; 
lean_dec(x_2);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_3);
lean_ctor_set(x_234, 1, x_4);
return x_234;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_fixLevelParams___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_6, x_5, x_9);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_8, 4);
x_13 = lean_ctor_get(x_8, 5);
x_14 = lean_ctor_get(x_8, 1);
lean_dec(x_14);
x_15 = l_Lean_Expr_ReplaceImpl_Cache_new(x_12);
lean_inc(x_3);
x_16 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_3, x_12, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Expr_ReplaceImpl_Cache_new(x_13);
lean_inc(x_3);
x_19 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_3, x_13, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_2);
lean_ctor_set(x_8, 5, x_20);
lean_ctor_set(x_8, 4, x_17);
lean_ctor_set(x_8, 1, x_2);
x_21 = 1;
x_22 = lean_usize_add(x_5, x_21);
x_23 = lean_array_uset(x_10, x_5, x_8);
x_5 = x_22;
x_6 = x_23;
goto _start;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get_uint8(x_8, sizeof(void*)*6);
x_27 = lean_ctor_get(x_8, 2);
x_28 = lean_ctor_get(x_8, 3);
x_29 = lean_ctor_get(x_8, 4);
x_30 = lean_ctor_get(x_8, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_25);
lean_dec(x_8);
x_31 = l_Lean_Expr_ReplaceImpl_Cache_new(x_29);
lean_inc(x_3);
x_32 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_3, x_29, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Expr_ReplaceImpl_Cache_new(x_30);
lean_inc(x_3);
x_35 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_3, x_30, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_2);
x_37 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_2);
lean_ctor_set(x_37, 2, x_27);
lean_ctor_set(x_37, 3, x_28);
lean_ctor_set(x_37, 4, x_33);
lean_ctor_set(x_37, 5, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_26);
x_38 = 1;
x_39 = lean_usize_add(x_5, x_38);
x_40 = lean_array_uset(x_10, x_5, x_37);
x_5 = x_39;
x_6 = x_40;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
lean_inc(x_13);
x_15 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_13, x_14);
x_16 = lean_array_get_size(x_1);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
lean_inc(x_1);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_fixLevelParams___spec__4(x_1, x_13, x_15, x_17, x_18, x_1);
lean_dec(x_1);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_box(0);
lean_inc(x_20);
x_23 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_20, x_22);
x_24 = lean_array_get_size(x_1);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
lean_inc(x_1);
x_27 = l_Array_mapMUnsafe_map___at_Lean_Elab_fixLevelParams___spec__4(x_1, x_20, x_23, x_25, x_26, x_1);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_fixLevelParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_fixLevelParams___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_fixLevelParams___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_fixLevelParams___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_fixLevelParams___spec__4(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_fixLevelParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_fixLevelParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Elab_Term_applyAttributesAt(x_16, x_18, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 1;
x_22 = lean_usize_add(x_4, x_21);
x_23 = lean_box(0);
x_4 = x_22;
x_5 = x_23;
x_12 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyAttributesOf(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = lean_box(0);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1(x_2, x_1, x_11, x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_applyAttributesOf___spec__1(x_13, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_applyAttributesOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_applyAttributesOf(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_abstractNestedProofs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 5);
lean_inc(x_13);
x_14 = l_Lean_Elab_DefKind_isTheorem(x_8);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Elab_DefKind_isExample(x_8);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_1, 5);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 4);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
lean_inc(x_11);
x_23 = l_Lean_Meta_abstractNestedProofs(x_11, x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_1, 5, x_25);
lean_ctor_set(x_23, 0, x_1);
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
lean_ctor_set(x_1, 5, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_1);
lean_inc(x_11);
x_33 = l_Lean_Meta_abstractNestedProofs(x_11, x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_9);
lean_ctor_set(x_37, 2, x_10);
lean_ctor_set(x_37, 3, x_11);
lean_ctor_set(x_37, 4, x_12);
lean_ctor_set(x_37, 5, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_8);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_41 = x_33;
} else {
 lean_dec_ref(x_33);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_6);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_6);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*2 + 3);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 5);
x_18 = l_Lean_replaceRef(x_7, x_17);
lean_dec(x_17);
lean_ctor_set(x_4, 5, x_18);
x_19 = l_Lean_addDecl(x_15, x_4, x_5, x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_4, 2);
x_23 = lean_ctor_get(x_4, 3);
x_24 = lean_ctor_get(x_4, 4);
x_25 = lean_ctor_get(x_4, 5);
x_26 = lean_ctor_get(x_4, 6);
x_27 = lean_ctor_get(x_4, 7);
x_28 = lean_ctor_get(x_4, 8);
x_29 = lean_ctor_get(x_4, 9);
x_30 = lean_ctor_get(x_4, 10);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_31 = l_Lean_replaceRef(x_7, x_25);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_23);
lean_ctor_set(x_32, 4, x_24);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set(x_32, 6, x_26);
lean_ctor_set(x_32, 7, x_27);
lean_ctor_set(x_32, 8, x_28);
lean_ctor_set(x_32, 9, x_29);
lean_ctor_set(x_32, 10, x_30);
x_33 = l_Lean_addDecl(x_15, x_32, x_5, x_6);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAsAxiom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_addAsAxiom(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_3 = l_Lean_Elab_DefKind_isTheorem(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 1);
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
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
x_9 = l_Lean_compileDecl(x_1, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___closed__1;
x_13 = lean_apply_8(x_12, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 4);
lean_dec(x_2);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
lean_dec(x_20);
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_dec(x_9);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
lean_inc(x_1);
x_17 = l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__3(x_1, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_16, x_3, x_18);
x_3 = x_21;
x_4 = x_22;
x_11 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = l_Lean_Elab_InfoTree_substitute(x_14, x_17);
x_19 = l_Lean_Elab_ContextInfo_save___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_18);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_16, x_3, x_22);
x_3 = x_24;
x_4 = x_25;
x_11 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__4(x_1, x_13, x_14, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_2, 0, x_17);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_2, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_array_get_size(x_21);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = 0;
x_25 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__4(x_1, x_23, x_24, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_array_get_size(x_32);
x_34 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_35 = 0;
x_36 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__5(x_1, x_34, x_35, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_ctor_set(x_2, 0, x_38);
lean_ctor_set(x_36, 0, x_2);
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
lean_ctor_set(x_2, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
lean_dec(x_2);
x_43 = lean_array_get_size(x_42);
x_44 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_45 = 0;
x_46 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__5(x_1, x_44, x_45, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_47);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = l_Lean_Elab_InfoTree_substitute(x_14, x_17);
x_19 = l_Lean_Elab_ContextInfo_save___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_18);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_16, x_3, x_22);
x_3 = x_24;
x_4 = x_25;
x_11 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_13 = l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__3(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_12);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__6(x_1, x_17, x_18, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_14);
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_2, 1, x_22);
lean_ctor_set(x_2, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get_usize(x_2, 4);
x_29 = lean_ctor_get(x_2, 3);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_1);
x_30 = l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__3(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_get_size(x_26);
x_34 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_35 = 0;
x_36 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__6(x_1, x_34, x_35, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_27);
lean_ctor_set(x_40, 3, x_29);
lean_ctor_set_usize(x_40, 4, x_28);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
lean_inc(x_1);
x_17 = l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__8(x_1, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_16, x_3, x_18);
x_3 = x_21;
x_4 = x_22;
x_11 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = l_Lean_Elab_InfoTree_substitute(x_14, x_17);
x_19 = l_Lean_Elab_ContextInfo_save___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_18);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_16, x_3, x_22);
x_3 = x_24;
x_4 = x_25;
x_11 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__9(x_1, x_13, x_14, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_2, 0, x_17);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_2, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_array_get_size(x_21);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = 0;
x_25 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__9(x_1, x_23, x_24, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_array_get_size(x_32);
x_34 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_35 = 0;
x_36 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__10(x_1, x_34, x_35, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_ctor_set(x_2, 0, x_38);
lean_ctor_set(x_36, 0, x_2);
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
lean_ctor_set(x_2, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_2, 0);
lean_inc(x_42);
lean_dec(x_2);
x_43 = lean_array_get_size(x_42);
x_44 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_45 = 0;
x_46 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__10(x_1, x_44, x_45, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_47);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = l_Lean_Elab_InfoTree_substitute(x_14, x_17);
x_19 = l_Lean_Elab_ContextInfo_save___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_18);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_16, x_3, x_22);
x_3 = x_24;
x_4 = x_25;
x_11 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_13 = l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__8(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_12);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__11(x_1, x_17, x_18, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_14);
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_2, 1, x_22);
lean_ctor_set(x_2, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get_usize(x_2, 4);
x_29 = lean_ctor_get(x_2, 3);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_1);
x_30 = l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__8(x_1, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_get_size(x_26);
x_34 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_35 = 0;
x_36 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__11(x_1, x_34, x_35, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_27);
lean_ctor_set(x_40, 3, x_29);
lean_ctor_set_usize(x_40, 4, x_28);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withSaveInfoContext___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 6);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_Lean_Elab_getResetInfoTrees___at_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___spec__2___rarg(x_7, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_7, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 6);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = l_Lean_PersistentArray_mapM___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__2(x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_take(x_7, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 6);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_31, 6);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_32, 1);
lean_dec(x_37);
x_38 = l_Lean_PersistentArray_append___rarg(x_17, x_28);
lean_ctor_set(x_32, 1, x_38);
x_39 = lean_st_ref_set(x_7, x_31, x_33);
lean_dec(x_7);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_20);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_20);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get_uint8(x_32, sizeof(void*)*2);
x_45 = lean_ctor_get(x_32, 0);
lean_inc(x_45);
lean_dec(x_32);
x_46 = l_Lean_PersistentArray_append___rarg(x_17, x_28);
x_47 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_44);
lean_ctor_set(x_31, 6, x_47);
x_48 = lean_st_ref_set(x_7, x_31, x_33);
lean_dec(x_7);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_20);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_52 = lean_ctor_get(x_31, 0);
x_53 = lean_ctor_get(x_31, 1);
x_54 = lean_ctor_get(x_31, 2);
x_55 = lean_ctor_get(x_31, 3);
x_56 = lean_ctor_get(x_31, 4);
x_57 = lean_ctor_get(x_31, 5);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_31);
x_58 = lean_ctor_get_uint8(x_32, sizeof(void*)*2);
x_59 = lean_ctor_get(x_32, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_60 = x_32;
} else {
 lean_dec_ref(x_32);
 x_60 = lean_box(0);
}
x_61 = l_Lean_PersistentArray_append___rarg(x_17, x_28);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 1);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_58);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_52);
lean_ctor_set(x_63, 1, x_53);
lean_ctor_set(x_63, 2, x_54);
lean_ctor_set(x_63, 3, x_55);
lean_ctor_set(x_63, 4, x_56);
lean_ctor_set(x_63, 5, x_57);
lean_ctor_set(x_63, 6, x_62);
x_64 = lean_st_ref_set(x_7, x_63, x_33);
lean_dec(x_7);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_20);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_68 = lean_ctor_get(x_19, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_19, 1);
lean_inc(x_69);
lean_dec(x_19);
x_70 = lean_st_ref_get(x_7, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 6);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
x_75 = l_Lean_PersistentArray_mapM___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__7(x_73, x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_72);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_st_ref_take(x_7, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 6);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = !lean_is_exclusive(x_79);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_79, 6);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_80);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_80, 1);
lean_dec(x_85);
x_86 = l_Lean_PersistentArray_append___rarg(x_17, x_76);
lean_ctor_set(x_80, 1, x_86);
x_87 = lean_st_ref_set(x_7, x_79, x_81);
lean_dec(x_7);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
lean_ctor_set_tag(x_87, 1);
lean_ctor_set(x_87, 0, x_68);
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_68);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
else
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get_uint8(x_80, sizeof(void*)*2);
x_93 = lean_ctor_get(x_80, 0);
lean_inc(x_93);
lean_dec(x_80);
x_94 = l_Lean_PersistentArray_append___rarg(x_17, x_76);
x_95 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set_uint8(x_95, sizeof(void*)*2, x_92);
lean_ctor_set(x_79, 6, x_95);
x_96 = lean_st_ref_set(x_7, x_79, x_81);
lean_dec(x_7);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
 lean_ctor_set_tag(x_99, 1);
}
lean_ctor_set(x_99, 0, x_68);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_100 = lean_ctor_get(x_79, 0);
x_101 = lean_ctor_get(x_79, 1);
x_102 = lean_ctor_get(x_79, 2);
x_103 = lean_ctor_get(x_79, 3);
x_104 = lean_ctor_get(x_79, 4);
x_105 = lean_ctor_get(x_79, 5);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_79);
x_106 = lean_ctor_get_uint8(x_80, sizeof(void*)*2);
x_107 = lean_ctor_get(x_80, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_108 = x_80;
} else {
 lean_dec_ref(x_80);
 x_108 = lean_box(0);
}
x_109 = l_Lean_PersistentArray_append___rarg(x_17, x_76);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 1);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_106);
x_111 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_111, 0, x_100);
lean_ctor_set(x_111, 1, x_101);
lean_ctor_set(x_111, 2, x_102);
lean_ctor_set(x_111, 3, x_103);
lean_ctor_set(x_111, 4, x_104);
lean_ctor_set(x_111, 5, x_105);
lean_ctor_set(x_111, 6, x_110);
x_112 = lean_st_ref_set(x_7, x_111, x_81);
lean_dec(x_7);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
 lean_ctor_set_tag(x_115, 1);
}
lean_ctor_set(x_115, 0, x_68);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_3);
x_10 = l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_expandDeclId___spec__7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = 1;
x_17 = l_Lean_Elab_Term_addTermInfo_x27(x_13, x_11, x_14, x_14, x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
uint8_t x_13; lean_object* x_14; 
x_13 = 1;
x_14 = l_Lean_Elab_applyAttributesOf(x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__3(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_dec(x_6);
if (x_3 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__2(x_1, x_2, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(x_4);
lean_dec(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__2(x_1, x_2, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
else
{
lean_object* x_19; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl(x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__2(x_1, x_2, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_noncomputableExt;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__5;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqLocalInstance___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__10;
x_2 = lean_alloc_closure((void*)(l_Array_instBEqArray___rarg___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__11;
x_2 = l_Lean_Expr_instBEqExpr;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instHashableLocalInstance___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__13;
x_2 = lean_alloc_closure((void*)(l_instHashableArray___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__14;
x_2 = l_Lean_Expr_instHashableExpr;
x_3 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__19;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__7;
x_2 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__9;
x_3 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__16;
x_4 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__20;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_12 = l_Lean_addDecl(x_4, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_inc(x_1);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__1), 9, 2);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Elab_withSaveInfoContext___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__1(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__1;
lean_inc(x_1);
x_19 = lean_array_push(x_18, x_1);
x_20 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_Elab_applyAttributesOf(x_19, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*2 + 1);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__3(x_2, x_19, x_3, x_1, x_4, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
lean_dec(x_19);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_st_ref_take(x_10, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 4);
lean_dec(x_33);
x_34 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__2;
x_35 = l_Lean_TagDeclarationExtension_tag(x_34, x_32, x_14);
x_36 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__6;
lean_ctor_set(x_29, 4, x_36);
lean_ctor_set(x_29, 0, x_35);
x_37 = lean_st_ref_set(x_10, x_29, x_30);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_take(x_8, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_40, 1);
lean_dec(x_43);
x_44 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__21;
lean_ctor_set(x_40, 1, x_44);
x_45 = lean_st_ref_set(x_8, x_40, x_41);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
x_48 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__3(x_2, x_19, x_3, x_1, x_4, x_47, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
lean_dec(x_19);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 2);
x_51 = lean_ctor_get(x_40, 3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
x_52 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__21;
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_51);
x_54 = lean_st_ref_set(x_8, x_53, x_41);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_box(0);
x_57 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__3(x_2, x_19, x_3, x_1, x_4, x_56, x_5, x_6, x_7, x_8, x_9, x_10, x_55);
lean_dec(x_19);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_58 = lean_ctor_get(x_29, 0);
x_59 = lean_ctor_get(x_29, 1);
x_60 = lean_ctor_get(x_29, 2);
x_61 = lean_ctor_get(x_29, 3);
x_62 = lean_ctor_get(x_29, 5);
x_63 = lean_ctor_get(x_29, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_29);
x_64 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__2;
x_65 = l_Lean_TagDeclarationExtension_tag(x_64, x_58, x_14);
x_66 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__6;
x_67 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_60);
lean_ctor_set(x_67, 3, x_61);
lean_ctor_set(x_67, 4, x_66);
lean_ctor_set(x_67, 5, x_62);
lean_ctor_set(x_67, 6, x_63);
x_68 = lean_st_ref_set(x_10, x_67, x_30);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_st_ref_take(x_8, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 3);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
 x_76 = lean_box(0);
}
x_77 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__21;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 4, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_74);
lean_ctor_set(x_78, 3, x_75);
x_79 = lean_st_ref_set(x_8, x_78, x_72);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_box(0);
x_82 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__3(x_2, x_19, x_3, x_1, x_4, x_81, x_5, x_6, x_7, x_8, x_9, x_10, x_80);
lean_dec(x_19);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_21);
if (x_83 == 0)
{
return x_21;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_21, 0);
x_85 = lean_ctor_get(x_21, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_21);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_16);
if (x_87 == 0)
{
return x_16;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_16, 0);
x_89 = lean_ctor_get(x_16, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_16);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_12);
if (x_91 == 0)
{
return x_12;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_12, 0);
x_93 = lean_ctor_get(x_12, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_12);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 5);
x_15 = l_Lean_replaceRef(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
lean_ctor_set(x_9, 5, x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_Elab_abstractNestedProofs(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*6);
x_19 = lean_box(x_18);
switch (lean_obj_tag(x_19)) {
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_17, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 4);
lean_inc(x_23);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_ctor_get(x_17, 5);
lean_inc(x_25);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_3);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(x_17, x_4, x_2, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
return x_28;
}
case 3:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_dec(x_16);
x_30 = lean_ctor_get(x_17, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_17, 4);
lean_inc(x_32);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_ctor_get(x_17, 5);
lean_inc(x_34);
x_35 = lean_ctor_get(x_17, 2);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_35, sizeof(void*)*2 + 3);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_3);
lean_ctor_set_uint8(x_37, sizeof(void*)*3, x_36);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(x_17, x_4, x_2, x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
return x_39;
}
case 4:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_dec(x_16);
x_41 = lean_ctor_get(x_17, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_17, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_17, 4);
lean_inc(x_43);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_ctor_get(x_17, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*2 + 3);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_17, 5);
lean_inc(x_47);
x_48 = lean_box(1);
x_49 = 1;
x_50 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set(x_50, 3, x_3);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(x_17, x_4, x_2, x_51, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_17, 5);
lean_inc(x_53);
x_54 = lean_box(1);
x_55 = 0;
x_56 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_54);
lean_ctor_set(x_56, 3, x_3);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(x_17, x_4, x_2, x_57, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
return x_58;
}
}
default: 
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint32_t x_70; uint32_t x_71; uint32_t x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_19);
x_59 = lean_ctor_get(x_16, 1);
lean_inc(x_59);
lean_dec(x_16);
x_60 = lean_st_ref_get(x_10, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_17, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_17, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_17, 4);
lean_inc(x_66);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_ctor_get(x_17, 5);
lean_inc(x_68);
lean_inc(x_68);
x_69 = l_Lean_getMaxHeight(x_63, x_68);
x_70 = lean_unbox_uint32(x_69);
lean_dec(x_69);
x_71 = 1;
x_72 = lean_uint32_add(x_70, x_71);
x_73 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_73, 0, x_72);
x_74 = lean_ctor_get(x_17, 2);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_74, sizeof(void*)*2 + 3);
lean_dec(x_74);
if (x_75 == 0)
{
uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = 1;
x_77 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 2, x_73);
lean_ctor_set(x_77, 3, x_3);
lean_ctor_set_uint8(x_77, sizeof(void*)*4, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(x_17, x_4, x_2, x_78, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
return x_79;
}
else
{
uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = 0;
x_81 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_81, 0, x_67);
lean_ctor_set(x_81, 1, x_68);
lean_ctor_set(x_81, 2, x_73);
lean_ctor_set(x_81, 3, x_3);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_80);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(x_17, x_4, x_2, x_82, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
return x_83;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_16);
if (x_84 == 0)
{
return x_16;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_16, 0);
x_86 = lean_ctor_get(x_16, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_16);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_88 = lean_ctor_get(x_9, 0);
x_89 = lean_ctor_get(x_9, 1);
x_90 = lean_ctor_get(x_9, 2);
x_91 = lean_ctor_get(x_9, 3);
x_92 = lean_ctor_get(x_9, 4);
x_93 = lean_ctor_get(x_9, 5);
x_94 = lean_ctor_get(x_9, 6);
x_95 = lean_ctor_get(x_9, 7);
x_96 = lean_ctor_get(x_9, 8);
x_97 = lean_ctor_get(x_9, 9);
x_98 = lean_ctor_get(x_9, 10);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_9);
x_99 = l_Lean_replaceRef(x_12, x_93);
lean_dec(x_93);
lean_dec(x_12);
x_100 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_100, 0, x_88);
lean_ctor_set(x_100, 1, x_89);
lean_ctor_set(x_100, 2, x_90);
lean_ctor_set(x_100, 3, x_91);
lean_ctor_set(x_100, 4, x_92);
lean_ctor_set(x_100, 5, x_99);
lean_ctor_set(x_100, 6, x_94);
lean_ctor_set(x_100, 7, x_95);
lean_ctor_set(x_100, 8, x_96);
lean_ctor_set(x_100, 9, x_97);
lean_ctor_set(x_100, 10, x_98);
lean_inc(x_10);
lean_inc(x_100);
lean_inc(x_8);
lean_inc(x_7);
x_101 = l_Lean_Elab_abstractNestedProofs(x_1, x_7, x_8, x_100, x_10, x_11);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get_uint8(x_102, sizeof(void*)*6);
x_104 = lean_box(x_103);
switch (lean_obj_tag(x_104)) {
case 1:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_dec(x_101);
x_106 = lean_ctor_get(x_102, 3);
lean_inc(x_106);
x_107 = lean_ctor_get(x_102, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_102, 4);
lean_inc(x_108);
x_109 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_109, 2, x_108);
x_110 = lean_ctor_get(x_102, 5);
lean_inc(x_110);
x_111 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_3);
x_112 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(x_102, x_4, x_2, x_112, x_5, x_6, x_7, x_8, x_100, x_10, x_105);
return x_113;
}
case 3:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_114 = lean_ctor_get(x_101, 1);
lean_inc(x_114);
lean_dec(x_101);
x_115 = lean_ctor_get(x_102, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_102, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_102, 4);
lean_inc(x_117);
x_118 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
lean_ctor_set(x_118, 2, x_117);
x_119 = lean_ctor_get(x_102, 5);
lean_inc(x_119);
x_120 = lean_ctor_get(x_102, 2);
lean_inc(x_120);
x_121 = lean_ctor_get_uint8(x_120, sizeof(void*)*2 + 3);
lean_dec(x_120);
x_122 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_119);
lean_ctor_set(x_122, 2, x_3);
lean_ctor_set_uint8(x_122, sizeof(void*)*3, x_121);
x_123 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(x_102, x_4, x_2, x_123, x_5, x_6, x_7, x_8, x_100, x_10, x_114);
return x_124;
}
case 4:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_125 = lean_ctor_get(x_101, 1);
lean_inc(x_125);
lean_dec(x_101);
x_126 = lean_ctor_get(x_102, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_102, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_102, 4);
lean_inc(x_128);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
lean_ctor_set(x_129, 2, x_128);
x_130 = lean_ctor_get(x_102, 2);
lean_inc(x_130);
x_131 = lean_ctor_get_uint8(x_130, sizeof(void*)*2 + 3);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_132 = lean_ctor_get(x_102, 5);
lean_inc(x_132);
x_133 = lean_box(1);
x_134 = 1;
x_135 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_135, 0, x_129);
lean_ctor_set(x_135, 1, x_132);
lean_ctor_set(x_135, 2, x_133);
lean_ctor_set(x_135, 3, x_3);
lean_ctor_set_uint8(x_135, sizeof(void*)*4, x_134);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(x_102, x_4, x_2, x_136, x_5, x_6, x_7, x_8, x_100, x_10, x_125);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_138 = lean_ctor_get(x_102, 5);
lean_inc(x_138);
x_139 = lean_box(1);
x_140 = 0;
x_141 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_141, 0, x_129);
lean_ctor_set(x_141, 1, x_138);
lean_ctor_set(x_141, 2, x_139);
lean_ctor_set(x_141, 3, x_3);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_140);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(x_102, x_4, x_2, x_142, x_5, x_6, x_7, x_8, x_100, x_10, x_125);
return x_143;
}
}
default: 
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint32_t x_155; uint32_t x_156; uint32_t x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
lean_dec(x_104);
x_144 = lean_ctor_get(x_101, 1);
lean_inc(x_144);
lean_dec(x_101);
x_145 = lean_st_ref_get(x_10, x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_102, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_102, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_102, 4);
lean_inc(x_151);
x_152 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
lean_ctor_set(x_152, 2, x_151);
x_153 = lean_ctor_get(x_102, 5);
lean_inc(x_153);
lean_inc(x_153);
x_154 = l_Lean_getMaxHeight(x_148, x_153);
x_155 = lean_unbox_uint32(x_154);
lean_dec(x_154);
x_156 = 1;
x_157 = lean_uint32_add(x_155, x_156);
x_158 = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(x_158, 0, x_157);
x_159 = lean_ctor_get(x_102, 2);
lean_inc(x_159);
x_160 = lean_ctor_get_uint8(x_159, sizeof(void*)*2 + 3);
lean_dec(x_159);
if (x_160 == 0)
{
uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = 1;
x_162 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_162, 0, x_152);
lean_ctor_set(x_162, 1, x_153);
lean_ctor_set(x_162, 2, x_158);
lean_ctor_set(x_162, 3, x_3);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_161);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(x_102, x_4, x_2, x_163, x_5, x_6, x_7, x_8, x_100, x_10, x_147);
return x_164;
}
else
{
uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = 0;
x_166 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_166, 0, x_152);
lean_ctor_set(x_166, 1, x_153);
lean_ctor_set(x_166, 2, x_158);
lean_ctor_set(x_166, 3, x_3);
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_165);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_168 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(x_102, x_4, x_2, x_167, x_5, x_6, x_7, x_8, x_100, x_10, x_147);
return x_168;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_100);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_169 = lean_ctor_get(x_101, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_101, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_171 = x_101;
} else {
 lean_dec_ref(x_101);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__5(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__6(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_mapM___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__9(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__10(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_mapMAux___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__11(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_mapM___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__3(x_14, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_1, x_12, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileNonRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
x_11 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_1, x_10, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addNonRec(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_1, x_11, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addNonRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Elab_addNonRec(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getRecAppSyntax_x3f(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = l_Lean_Expr_mdataExpr_x21(x_1);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
static lean_object* _init_l_Lean_Elab_eraseRecAppSyntaxExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_eraseRecAppSyntaxExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__2___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Elab_eraseRecAppSyntaxExpr___closed__1;
x_6 = l_Lean_Elab_eraseRecAppSyntaxExpr___closed__2;
x_7 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_1, x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_eraseRecAppSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get(x_1, 5);
x_12 = l_Lean_Elab_eraseRecAppSyntaxExpr___closed__1;
x_13 = l_Lean_Elab_eraseRecAppSyntaxExpr___closed__2;
x_14 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_11, x_12, x_13, x_2, x_3, x_4);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_1, 5, x_16);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_1, 5, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_free_object(x_1);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get(x_1, 3);
x_29 = lean_ctor_get(x_1, 4);
x_30 = lean_ctor_get(x_1, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_24);
lean_dec(x_1);
x_31 = l_Lean_Elab_eraseRecAppSyntaxExpr___closed__1;
x_32 = l_Lean_Elab_eraseRecAppSyntaxExpr___closed__2;
x_33 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_30, x_31, x_32, x_2, x_3, x_4);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_26);
lean_ctor_set(x_37, 2, x_27);
lean_ctor_set(x_37, 3, x_28);
lean_ctor_set(x_37, 4, x_29);
lean_ctor_set(x_37, 5, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_25);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_41 = x_33;
} else {
 lean_dec_ref(x_33);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompileUnsafe___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
lean_inc(x_9);
lean_inc(x_8);
x_16 = l_Lean_Elab_eraseRecAppSyntax(x_13, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_15, x_2, x_17);
x_2 = x_20;
x_3 = x_21;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_addAndCompileUnsafe___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_ctor_get(x_5, 3);
lean_inc(x_7);
lean_dec(x_5);
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
x_11 = lean_ctor_get(x_9, 3);
lean_inc(x_11);
lean_dec(x_9);
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_addAndCompileUnsafe___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = l_List_reverse___rarg(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 4);
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_ctor_get(x_15, 5);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
lean_inc(x_2);
x_23 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_2);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_1);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_23);
{
lean_object* _tmp_2 = x_16;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_27 = lean_ctor_get(x_25, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 4);
lean_inc(x_29);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_ctor_get(x_25, 5);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_box(0);
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_2);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_1);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
x_3 = x_26;
x_4 = x_34;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addAndCompileUnsafe___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
lean_inc(x_5);
x_16 = l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_expandDeclId___spec__7(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_box(0);
x_22 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l_Lean_Elab_Term_addTermInfo_x27(x_19, x_17, x_20, x_20, x_21, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_box(0);
x_3 = x_26;
x_4 = x_27;
x_11 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___lambda__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_addAndCompileUnsafe___spec__4(x_1, x_2, x_3, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Elab_addAndCompileUnsafe___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompileUnsafe___spec__1(x_11, x_12, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
lean_inc(x_14);
x_19 = lean_array_to_list(lean_box(0), x_14);
x_20 = lean_box(0);
lean_inc(x_19);
x_21 = l_List_mapTR_loop___at_Lean_Elab_addAndCompileUnsafe___spec__2(x_19, x_20);
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_7, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 4);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 5);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 6);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 7);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 8);
lean_inc(x_30);
x_31 = lean_ctor_get(x_7, 9);
lean_inc(x_31);
x_32 = lean_ctor_get(x_7, 10);
lean_inc(x_32);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 lean_ctor_release(x_7, 6);
 lean_ctor_release(x_7, 7);
 lean_ctor_release(x_7, 8);
 lean_ctor_release(x_7, 9);
 lean_ctor_release(x_7, 10);
 x_33 = x_7;
} else {
 lean_dec_ref(x_7);
 x_33 = lean_box(0);
}
if (x_18 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = l_Lean_Elab_instInhabitedPreDefinition;
x_85 = l___private_Init_Util_0__outOfBounds___rarg(x_84);
x_34 = x_85;
goto block_83;
}
else
{
lean_object* x_86; 
x_86 = lean_array_fget(x_14, x_17);
x_34 = x_86;
goto block_83;
}
block_83:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_replaceRef(x_35, x_27);
lean_dec(x_27);
lean_dec(x_35);
if (lean_is_scalar(x_33)) {
 x_37 = lean_alloc_ctor(0, 11, 0);
} else {
 x_37 = x_33;
}
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_23);
lean_ctor_set(x_37, 2, x_24);
lean_ctor_set(x_37, 3, x_25);
lean_ctor_set(x_37, 4, x_26);
lean_ctor_set(x_37, 5, x_36);
lean_ctor_set(x_37, 6, x_28);
lean_ctor_set(x_37, 7, x_29);
lean_ctor_set(x_37, 8, x_30);
lean_ctor_set(x_37, 9, x_31);
lean_ctor_set(x_37, 10, x_32);
x_38 = l_List_mapM_loop___at_Lean_Elab_addAndCompileUnsafe___spec__3(x_2, x_21, x_19, x_20, x_3, x_4, x_5, x_6, x_37, x_8, x_15);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_41, 0, x_39);
lean_inc(x_8);
lean_inc(x_37);
lean_inc(x_41);
x_42 = l_Lean_addDecl(x_41, x_37, x_8, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_45 = lean_box_usize(x_44);
x_46 = l_Lean_Elab_addAndCompileUnsafe___boxed__const__1;
lean_inc(x_14);
x_47 = lean_alloc_closure((void*)(l_Lean_Elab_addAndCompileUnsafe___lambda__1___boxed), 10, 3);
lean_closure_set(x_47, 0, x_14);
lean_closure_set(x_47, 1, x_45);
lean_closure_set(x_47, 2, x_46);
lean_inc(x_8);
lean_inc(x_37);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_48 = l_Lean_Elab_withSaveInfoContext___at___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___spec__1(x_47, x_3, x_4, x_5, x_6, x_37, x_8, x_43);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = 0;
lean_inc(x_8);
lean_inc(x_37);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Elab_applyAttributesOf(x_14, x_50, x_3, x_4, x_5, x_6, x_37, x_8, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_8);
lean_inc(x_37);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_53 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl(x_41, x_3, x_4, x_5, x_6, x_37, x_8, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = 1;
x_56 = l_Lean_Elab_applyAttributesOf(x_14, x_55, x_3, x_4, x_5, x_6, x_37, x_8, x_54);
lean_dec(x_14);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
x_59 = lean_box(0);
lean_ctor_set(x_56, 0, x_59);
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_56);
if (x_63 == 0)
{
return x_56;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_56, 0);
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_56);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_67 = !lean_is_exclusive(x_53);
if (x_67 == 0)
{
return x_53;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_53, 0);
x_69 = lean_ctor_get(x_53, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_51);
if (x_71 == 0)
{
return x_51;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_51, 0);
x_73 = lean_ctor_get(x_51, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_51);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_48);
if (x_75 == 0)
{
return x_48;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_48, 0);
x_77 = lean_ctor_get(x_48, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_48);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_41);
lean_dec(x_37);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_79 = !lean_is_exclusive(x_42);
if (x_79 == 0)
{
return x_42;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_42, 0);
x_81 = lean_ctor_get(x_42, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_42);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_87 = !lean_is_exclusive(x_13);
if (x_87 == 0)
{
return x_13;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_13, 0);
x_89 = lean_ctor_get(x_13, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_13);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompileUnsafe___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompileUnsafe___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_Lean_Elab_addAndCompileUnsafe___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_List_mapM_loop___at_Lean_Elab_addAndCompileUnsafe___spec__3(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addAndCompileUnsafe___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_addAndCompileUnsafe___spec__4(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Lean_Elab_addAndCompileUnsafe___lambda__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompileUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_addAndCompileUnsafe(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
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
x_13 = 0;
return x_13;
}
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_unsafe_rec", 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_236; size_t x_237; size_t x_238; size_t x_239; lean_object* x_240; size_t x_241; uint8_t x_242; 
x_236 = lean_ctor_get(x_4, 0);
lean_inc(x_236);
x_237 = lean_ptr_addr(x_3);
x_238 = lean_ctor_get_usize(x_4, 1);
x_239 = lean_usize_mod(x_237, x_238);
x_240 = lean_array_uget(x_236, x_239);
x_241 = lean_ptr_addr(x_240);
lean_dec(x_240);
x_242 = lean_usize_dec_eq(x_237, x_241);
if (x_242 == 0)
{
lean_dec(x_236);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_243 = lean_ctor_get(x_3, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_3, 1);
lean_inc(x_244);
x_245 = lean_unsigned_to_nat(0u);
x_246 = lean_nat_dec_lt(x_245, x_2);
if (x_246 == 0)
{
lean_object* x_247; 
lean_dec(x_244);
lean_dec(x_243);
x_247 = lean_box(0);
x_5 = x_247;
goto block_235;
}
else
{
size_t x_248; size_t x_249; uint8_t x_250; 
x_248 = 0;
x_249 = lean_usize_of_nat(x_2);
x_250 = l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__1(x_243, x_1, x_248, x_249);
if (x_250 == 0)
{
lean_object* x_251; 
lean_dec(x_244);
lean_dec(x_243);
x_251 = lean_box(0);
x_5 = x_251;
goto block_235;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1;
x_253 = l_Lean_Name_str___override(x_243, x_252);
x_254 = l_Lean_Expr_const___override(x_253, x_244);
lean_inc(x_254);
x_255 = l_Lean_Expr_ReplaceImpl_Cache_store(x_4, x_3, x_254);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
lean_object* x_257; 
x_257 = lean_box(0);
x_5 = x_257;
goto block_235;
}
}
else
{
size_t x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_3);
x_258 = lean_usize_add(x_239, x_238);
x_259 = lean_array_uget(x_236, x_258);
lean_dec(x_236);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_4);
return x_260;
}
block_235:
{
lean_dec(x_5);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_inc(x_6);
x_8 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_6, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_7);
x_11 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_7, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_16 = lean_ptr_addr(x_9);
x_17 = lean_usize_dec_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_Lean_Expr_app___override(x_9, x_13);
lean_inc(x_18);
x_19 = l_Lean_Expr_ReplaceImpl_Cache_store(x_14, x_3, x_18);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_21 = lean_ptr_addr(x_13);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Expr_app___override(x_9, x_13);
lean_inc(x_23);
x_24 = l_Lean_Expr_ReplaceImpl_Cache_store(x_14, x_3, x_23);
lean_ctor_set(x_11, 1, x_24);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
else
{
lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_9);
lean_inc_n(x_3, 2);
x_25 = l_Lean_Expr_ReplaceImpl_Cache_store(x_14, x_3, x_3);
lean_ctor_set(x_11, 1, x_25);
lean_ctor_set(x_11, 0, x_3);
return x_11;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_29 = lean_ptr_addr(x_9);
x_30 = lean_usize_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_7);
x_31 = l_Lean_Expr_app___override(x_9, x_26);
lean_inc(x_31);
x_32 = l_Lean_Expr_ReplaceImpl_Cache_store(x_27, x_3, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
size_t x_34; size_t x_35; uint8_t x_36; 
x_34 = lean_ptr_addr(x_7);
lean_dec(x_7);
x_35 = lean_ptr_addr(x_26);
x_36 = lean_usize_dec_eq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_Lean_Expr_app___override(x_9, x_26);
lean_inc(x_37);
x_38 = l_Lean_Expr_ReplaceImpl_Cache_store(x_27, x_3, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_26);
lean_dec(x_9);
lean_inc_n(x_3, 2);
x_40 = l_Lean_Expr_ReplaceImpl_Cache_store(x_27, x_3, x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_3);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
case 6:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 2);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_43);
x_46 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_43, x_4);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_44);
x_49 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_44, x_48);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_53 = l_Lean_Expr_lam___override(x_42, x_43, x_44, x_45);
x_54 = lean_ptr_addr(x_43);
lean_dec(x_43);
x_55 = lean_ptr_addr(x_47);
x_56 = lean_usize_dec_eq(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_53);
lean_dec(x_44);
x_57 = l_Lean_Expr_lam___override(x_42, x_47, x_51, x_45);
lean_inc(x_57);
x_58 = l_Lean_Expr_ReplaceImpl_Cache_store(x_52, x_3, x_57);
lean_ctor_set(x_49, 1, x_58);
lean_ctor_set(x_49, 0, x_57);
return x_49;
}
else
{
size_t x_59; size_t x_60; uint8_t x_61; 
x_59 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_60 = lean_ptr_addr(x_51);
x_61 = lean_usize_dec_eq(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_53);
x_62 = l_Lean_Expr_lam___override(x_42, x_47, x_51, x_45);
lean_inc(x_62);
x_63 = l_Lean_Expr_ReplaceImpl_Cache_store(x_52, x_3, x_62);
lean_ctor_set(x_49, 1, x_63);
lean_ctor_set(x_49, 0, x_62);
return x_49;
}
else
{
uint8_t x_64; 
x_64 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_45, x_45);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_53);
x_65 = l_Lean_Expr_lam___override(x_42, x_47, x_51, x_45);
lean_inc(x_65);
x_66 = l_Lean_Expr_ReplaceImpl_Cache_store(x_52, x_3, x_65);
lean_ctor_set(x_49, 1, x_66);
lean_ctor_set(x_49, 0, x_65);
return x_49;
}
else
{
lean_object* x_67; 
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_42);
lean_inc(x_53);
x_67 = l_Lean_Expr_ReplaceImpl_Cache_store(x_52, x_3, x_53);
lean_ctor_set(x_49, 1, x_67);
lean_ctor_set(x_49, 0, x_53);
return x_49;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_49, 0);
x_69 = lean_ctor_get(x_49, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_49);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_70 = l_Lean_Expr_lam___override(x_42, x_43, x_44, x_45);
x_71 = lean_ptr_addr(x_43);
lean_dec(x_43);
x_72 = lean_ptr_addr(x_47);
x_73 = lean_usize_dec_eq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_70);
lean_dec(x_44);
x_74 = l_Lean_Expr_lam___override(x_42, x_47, x_68, x_45);
lean_inc(x_74);
x_75 = l_Lean_Expr_ReplaceImpl_Cache_store(x_69, x_3, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
else
{
size_t x_77; size_t x_78; uint8_t x_79; 
x_77 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_78 = lean_ptr_addr(x_68);
x_79 = lean_usize_dec_eq(x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_70);
x_80 = l_Lean_Expr_lam___override(x_42, x_47, x_68, x_45);
lean_inc(x_80);
x_81 = l_Lean_Expr_ReplaceImpl_Cache_store(x_69, x_3, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
else
{
uint8_t x_83; 
x_83 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_45, x_45);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_70);
x_84 = l_Lean_Expr_lam___override(x_42, x_47, x_68, x_45);
lean_inc(x_84);
x_85 = l_Lean_Expr_ReplaceImpl_Cache_store(x_69, x_3, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_68);
lean_dec(x_47);
lean_dec(x_42);
lean_inc(x_70);
x_87 = l_Lean_Expr_ReplaceImpl_Cache_store(x_69, x_3, x_70);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_70);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
case 7:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_89 = lean_ctor_get(x_3, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_3, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_3, 2);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_inc(x_90);
x_93 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_90, x_4);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_91);
x_96 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_91, x_95);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; size_t x_101; size_t x_102; uint8_t x_103; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
x_100 = l_Lean_Expr_forallE___override(x_89, x_90, x_91, x_92);
x_101 = lean_ptr_addr(x_90);
lean_dec(x_90);
x_102 = lean_ptr_addr(x_94);
x_103 = lean_usize_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_100);
lean_dec(x_91);
x_104 = l_Lean_Expr_forallE___override(x_89, x_94, x_98, x_92);
lean_inc(x_104);
x_105 = l_Lean_Expr_ReplaceImpl_Cache_store(x_99, x_3, x_104);
lean_ctor_set(x_96, 1, x_105);
lean_ctor_set(x_96, 0, x_104);
return x_96;
}
else
{
size_t x_106; size_t x_107; uint8_t x_108; 
x_106 = lean_ptr_addr(x_91);
lean_dec(x_91);
x_107 = lean_ptr_addr(x_98);
x_108 = lean_usize_dec_eq(x_106, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_100);
x_109 = l_Lean_Expr_forallE___override(x_89, x_94, x_98, x_92);
lean_inc(x_109);
x_110 = l_Lean_Expr_ReplaceImpl_Cache_store(x_99, x_3, x_109);
lean_ctor_set(x_96, 1, x_110);
lean_ctor_set(x_96, 0, x_109);
return x_96;
}
else
{
uint8_t x_111; 
x_111 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_92, x_92);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_100);
x_112 = l_Lean_Expr_forallE___override(x_89, x_94, x_98, x_92);
lean_inc(x_112);
x_113 = l_Lean_Expr_ReplaceImpl_Cache_store(x_99, x_3, x_112);
lean_ctor_set(x_96, 1, x_113);
lean_ctor_set(x_96, 0, x_112);
return x_96;
}
else
{
lean_object* x_114; 
lean_dec(x_98);
lean_dec(x_94);
lean_dec(x_89);
lean_inc(x_100);
x_114 = l_Lean_Expr_ReplaceImpl_Cache_store(x_99, x_3, x_100);
lean_ctor_set(x_96, 1, x_114);
lean_ctor_set(x_96, 0, x_100);
return x_96;
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; size_t x_118; size_t x_119; uint8_t x_120; 
x_115 = lean_ctor_get(x_96, 0);
x_116 = lean_ctor_get(x_96, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_96);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
x_117 = l_Lean_Expr_forallE___override(x_89, x_90, x_91, x_92);
x_118 = lean_ptr_addr(x_90);
lean_dec(x_90);
x_119 = lean_ptr_addr(x_94);
x_120 = lean_usize_dec_eq(x_118, x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_117);
lean_dec(x_91);
x_121 = l_Lean_Expr_forallE___override(x_89, x_94, x_115, x_92);
lean_inc(x_121);
x_122 = l_Lean_Expr_ReplaceImpl_Cache_store(x_116, x_3, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
else
{
size_t x_124; size_t x_125; uint8_t x_126; 
x_124 = lean_ptr_addr(x_91);
lean_dec(x_91);
x_125 = lean_ptr_addr(x_115);
x_126 = lean_usize_dec_eq(x_124, x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_117);
x_127 = l_Lean_Expr_forallE___override(x_89, x_94, x_115, x_92);
lean_inc(x_127);
x_128 = l_Lean_Expr_ReplaceImpl_Cache_store(x_116, x_3, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
else
{
uint8_t x_130; 
x_130 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_92, x_92);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_117);
x_131 = l_Lean_Expr_forallE___override(x_89, x_94, x_115, x_92);
lean_inc(x_131);
x_132 = l_Lean_Expr_ReplaceImpl_Cache_store(x_116, x_3, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_115);
lean_dec(x_94);
lean_dec(x_89);
lean_inc(x_117);
x_134 = l_Lean_Expr_ReplaceImpl_Cache_store(x_116, x_3, x_117);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_117);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
}
case 8:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_136 = lean_ctor_get(x_3, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_3, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_3, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_3, 3);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_3, sizeof(void*)*4 + 8);
lean_inc(x_137);
x_141 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_137, x_4);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_138);
x_144 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_138, x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_139);
x_147 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_139, x_146);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; size_t x_151; size_t x_152; uint8_t x_153; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = lean_ctor_get(x_147, 1);
x_151 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_152 = lean_ptr_addr(x_142);
x_153 = lean_usize_dec_eq(x_151, x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_139);
lean_dec(x_138);
x_154 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_149, x_140);
lean_inc(x_154);
x_155 = l_Lean_Expr_ReplaceImpl_Cache_store(x_150, x_3, x_154);
lean_ctor_set(x_147, 1, x_155);
lean_ctor_set(x_147, 0, x_154);
return x_147;
}
else
{
size_t x_156; size_t x_157; uint8_t x_158; 
x_156 = lean_ptr_addr(x_138);
lean_dec(x_138);
x_157 = lean_ptr_addr(x_145);
x_158 = lean_usize_dec_eq(x_156, x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_139);
x_159 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_149, x_140);
lean_inc(x_159);
x_160 = l_Lean_Expr_ReplaceImpl_Cache_store(x_150, x_3, x_159);
lean_ctor_set(x_147, 1, x_160);
lean_ctor_set(x_147, 0, x_159);
return x_147;
}
else
{
size_t x_161; size_t x_162; uint8_t x_163; 
x_161 = lean_ptr_addr(x_139);
lean_dec(x_139);
x_162 = lean_ptr_addr(x_149);
x_163 = lean_usize_dec_eq(x_161, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_149, x_140);
lean_inc(x_164);
x_165 = l_Lean_Expr_ReplaceImpl_Cache_store(x_150, x_3, x_164);
lean_ctor_set(x_147, 1, x_165);
lean_ctor_set(x_147, 0, x_164);
return x_147;
}
else
{
lean_object* x_166; 
lean_dec(x_149);
lean_dec(x_145);
lean_dec(x_142);
lean_dec(x_136);
lean_inc_n(x_3, 2);
x_166 = l_Lean_Expr_ReplaceImpl_Cache_store(x_150, x_3, x_3);
lean_ctor_set(x_147, 1, x_166);
lean_ctor_set(x_147, 0, x_3);
return x_147;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; size_t x_169; size_t x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_147, 0);
x_168 = lean_ctor_get(x_147, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_147);
x_169 = lean_ptr_addr(x_137);
lean_dec(x_137);
x_170 = lean_ptr_addr(x_142);
x_171 = lean_usize_dec_eq(x_169, x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_139);
lean_dec(x_138);
x_172 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_167, x_140);
lean_inc(x_172);
x_173 = l_Lean_Expr_ReplaceImpl_Cache_store(x_168, x_3, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
else
{
size_t x_175; size_t x_176; uint8_t x_177; 
x_175 = lean_ptr_addr(x_138);
lean_dec(x_138);
x_176 = lean_ptr_addr(x_145);
x_177 = lean_usize_dec_eq(x_175, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_139);
x_178 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_167, x_140);
lean_inc(x_178);
x_179 = l_Lean_Expr_ReplaceImpl_Cache_store(x_168, x_3, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
else
{
size_t x_181; size_t x_182; uint8_t x_183; 
x_181 = lean_ptr_addr(x_139);
lean_dec(x_139);
x_182 = lean_ptr_addr(x_167);
x_183 = lean_usize_dec_eq(x_181, x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = l_Lean_Expr_letE___override(x_136, x_142, x_145, x_167, x_140);
lean_inc(x_184);
x_185 = l_Lean_Expr_ReplaceImpl_Cache_store(x_168, x_3, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_167);
lean_dec(x_145);
lean_dec(x_142);
lean_dec(x_136);
lean_inc_n(x_3, 2);
x_187 = l_Lean_Expr_ReplaceImpl_Cache_store(x_168, x_3, x_3);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_3);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
}
}
case 10:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_189 = lean_ctor_get(x_3, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_3, 1);
lean_inc(x_190);
lean_inc(x_190);
x_191 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_190, x_4);
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; size_t x_195; size_t x_196; uint8_t x_197; 
x_193 = lean_ctor_get(x_191, 0);
x_194 = lean_ctor_get(x_191, 1);
x_195 = lean_ptr_addr(x_190);
lean_dec(x_190);
x_196 = lean_ptr_addr(x_193);
x_197 = lean_usize_dec_eq(x_195, x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
x_198 = l_Lean_Expr_mdata___override(x_189, x_193);
lean_inc(x_198);
x_199 = l_Lean_Expr_ReplaceImpl_Cache_store(x_194, x_3, x_198);
lean_ctor_set(x_191, 1, x_199);
lean_ctor_set(x_191, 0, x_198);
return x_191;
}
else
{
lean_object* x_200; 
lean_dec(x_193);
lean_dec(x_189);
lean_inc_n(x_3, 2);
x_200 = l_Lean_Expr_ReplaceImpl_Cache_store(x_194, x_3, x_3);
lean_ctor_set(x_191, 1, x_200);
lean_ctor_set(x_191, 0, x_3);
return x_191;
}
}
else
{
lean_object* x_201; lean_object* x_202; size_t x_203; size_t x_204; uint8_t x_205; 
x_201 = lean_ctor_get(x_191, 0);
x_202 = lean_ctor_get(x_191, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_191);
x_203 = lean_ptr_addr(x_190);
lean_dec(x_190);
x_204 = lean_ptr_addr(x_201);
x_205 = lean_usize_dec_eq(x_203, x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = l_Lean_Expr_mdata___override(x_189, x_201);
lean_inc(x_206);
x_207 = l_Lean_Expr_ReplaceImpl_Cache_store(x_202, x_3, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_201);
lean_dec(x_189);
lean_inc_n(x_3, 2);
x_209 = l_Lean_Expr_ReplaceImpl_Cache_store(x_202, x_3, x_3);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_3);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
case 11:
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_211 = lean_ctor_get(x_3, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_3, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_3, 2);
lean_inc(x_213);
lean_inc(x_213);
x_214 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_213, x_4);
x_215 = !lean_is_exclusive(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; size_t x_218; size_t x_219; uint8_t x_220; 
x_216 = lean_ctor_get(x_214, 0);
x_217 = lean_ctor_get(x_214, 1);
x_218 = lean_ptr_addr(x_213);
lean_dec(x_213);
x_219 = lean_ptr_addr(x_216);
x_220 = lean_usize_dec_eq(x_218, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = l_Lean_Expr_proj___override(x_211, x_212, x_216);
lean_inc(x_221);
x_222 = l_Lean_Expr_ReplaceImpl_Cache_store(x_217, x_3, x_221);
lean_ctor_set(x_214, 1, x_222);
lean_ctor_set(x_214, 0, x_221);
return x_214;
}
else
{
lean_object* x_223; 
lean_dec(x_216);
lean_dec(x_212);
lean_dec(x_211);
lean_inc_n(x_3, 2);
x_223 = l_Lean_Expr_ReplaceImpl_Cache_store(x_217, x_3, x_3);
lean_ctor_set(x_214, 1, x_223);
lean_ctor_set(x_214, 0, x_3);
return x_214;
}
}
else
{
lean_object* x_224; lean_object* x_225; size_t x_226; size_t x_227; uint8_t x_228; 
x_224 = lean_ctor_get(x_214, 0);
x_225 = lean_ctor_get(x_214, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_214);
x_226 = lean_ptr_addr(x_213);
lean_dec(x_213);
x_227 = lean_ptr_addr(x_224);
x_228 = lean_usize_dec_eq(x_226, x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = l_Lean_Expr_proj___override(x_211, x_212, x_224);
lean_inc(x_229);
x_230 = l_Lean_Expr_ReplaceImpl_Cache_store(x_225, x_3, x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_224);
lean_dec(x_212);
lean_dec(x_211);
lean_inc_n(x_3, 2);
x_232 = l_Lean_Expr_ReplaceImpl_Cache_store(x_225, x_3, x_3);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_3);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
default: 
{
lean_object* x_234; 
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_3);
lean_ctor_set(x_234, 1, x_4);
return x_234;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 0;
x_4 = 2;
x_5 = l_Lean_Elab_instInhabitedPreDefinition___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_5, x_4, x_8);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = lean_ctor_get(x_7, 5);
x_13 = lean_ctor_get(x_7, 2);
lean_dec(x_13);
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1;
x_15 = l_Lean_Name_str___override(x_11, x_14);
x_16 = l_Lean_Expr_ReplaceImpl_Cache_new(x_12);
x_17 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_12, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___closed__1;
lean_ctor_set(x_7, 5, x_18);
lean_ctor_set(x_7, 3, x_15);
lean_ctor_set(x_7, 2, x_19);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_22 = lean_array_uset(x_9, x_4, x_7);
x_4 = x_21;
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
x_26 = lean_ctor_get(x_7, 1);
x_27 = lean_ctor_get(x_7, 3);
x_28 = lean_ctor_get(x_7, 4);
x_29 = lean_ctor_get(x_7, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_24);
lean_dec(x_7);
x_30 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1;
x_31 = l_Lean_Name_str___override(x_27, x_30);
x_32 = l_Lean_Expr_ReplaceImpl_Cache_new(x_29);
x_33 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_29, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___closed__1;
x_36 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_26);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_28);
lean_ctor_set(x_36, 5, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*6, x_25);
x_37 = 1;
x_38 = lean_usize_add(x_4, x_37);
x_39 = lean_array_uset(x_9, x_4, x_36);
x_4 = x_38;
x_5 = x_39;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_st_ref_take(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 6);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 6);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_1);
x_16 = lean_st_ref_set(x_7, x_10, x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_1);
lean_ctor_set(x_10, 6, x_25);
x_26 = lean_st_ref_set(x_7, x_10, x_12);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
x_33 = lean_ctor_get(x_10, 2);
x_34 = lean_ctor_get(x_10, 3);
x_35 = lean_ctor_get(x_10, 4);
x_36 = lean_ctor_get(x_10, 5);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_39 = x_11;
} else {
 lean_dec_ref(x_11);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 1);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_1);
x_41 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_33);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_41, 4, x_35);
lean_ctor_set(x_41, 5, x_36);
lean_ctor_set(x_41, 6, x_40);
x_42 = lean_st_ref_set(x_7, x_41, x_12);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 6);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
x_15 = l_Lean_Elab_enableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__5(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_enableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__5(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = l_Lean_Elab_enableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__5(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__6(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_shouldGenCodeFor(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_20; uint8_t x_21; 
x_9 = lean_array_get_size(x_1);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_9);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
x_10 = x_22;
goto block_19;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_9);
x_25 = l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__6(x_1, x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_box(0);
x_10 = x_26;
goto block_19;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
}
block_19:
{
size_t x_11; size_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
lean_dec(x_10);
x_11 = lean_usize_of_nat(x_9);
x_12 = 0;
lean_inc(x_1);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3(x_1, x_9, x_11, x_12, x_1);
lean_dec(x_9);
lean_dec(x_1);
x_14 = 2;
x_15 = lean_box(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_addAndCompileUnsafe___boxed), 9, 2);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_15);
x_17 = 0;
x_18 = l_Lean_Elab_withEnableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__4(x_17, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Elab_enableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__5(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Elab_withEnableInfoTree___at_Lean_Elab_addAndCompilePartialRec___spec__4(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_addAndCompilePartialRec___spec__6(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_isConstOf(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_ensureNoRecFn___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected occurrence of recursive application", 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ensureNoRecFn___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ensureNoRecFn___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_ensureNoRecFn___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_ensureNoRecFn___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_ensureNoRecFn___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ensureNoRecFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isAppOf(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_indentExpr(x_2);
x_12 = l_Lean_Elab_ensureNoRecFn___lambda__1___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_ensureNoRecFn___lambda__1___closed__4;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ensureNoRecFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_containsRecFn(x_1, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_ensureNoRecFn___lambda__1___boxed), 7, 1);
lean_closure_set(x_10, 0, x_1);
lean_inc(x_2);
x_11 = l_Lean_Meta_forEachExpr___at_Lean_Meta_setMVarUserNamesAt___spec__5(x_2, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ensureNoRecFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_ensureNoRecFn___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AbstractNestedProofs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_RecAppSyntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DefView(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_NoncomputableAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AbstractNestedProofs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_RecAppSyntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DefView(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_instInhabitedPreDefinition___closed__1 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__1();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__1);
l_Lean_Elab_instInhabitedPreDefinition___closed__2 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__2();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__2);
l_Lean_Elab_instInhabitedPreDefinition___closed__3 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__3();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__3);
l_Lean_Elab_instInhabitedPreDefinition___closed__4 = _init_l_Lean_Elab_instInhabitedPreDefinition___closed__4();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition___closed__4);
l_Lean_Elab_instInhabitedPreDefinition = _init_l_Lean_Elab_instInhabitedPreDefinition();
lean_mark_persistent(l_Lean_Elab_instInhabitedPreDefinition);
l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_levelMVarToParamPreDecls___spec__1___closed__1);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__1);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_getLevelParamsPreDecls___closed__2);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_compileDecl___closed__1);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__1);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__2);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__3);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__4);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__5);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__6);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__7 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__7);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__8);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__9 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__9);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__10 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__10);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__11 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__11);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__12 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__12);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__13 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__13();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__13);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__14 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__14();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__14);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__15 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__15();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__15);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__16 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__16();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__16);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__17 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__17();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__17);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__18 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__18();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__18);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__19 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__19();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__19);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__20 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__20();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__20);
l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__21 = _init_l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__21();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux___lambda__4___closed__21);
l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1___closed__1 = _init_l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_eraseRecAppSyntaxExpr___lambda__1___closed__1);
l_Lean_Elab_eraseRecAppSyntaxExpr___closed__1 = _init_l_Lean_Elab_eraseRecAppSyntaxExpr___closed__1();
lean_mark_persistent(l_Lean_Elab_eraseRecAppSyntaxExpr___closed__1);
l_Lean_Elab_eraseRecAppSyntaxExpr___closed__2 = _init_l_Lean_Elab_eraseRecAppSyntaxExpr___closed__2();
lean_mark_persistent(l_Lean_Elab_eraseRecAppSyntaxExpr___closed__2);
l_Lean_Elab_addAndCompileUnsafe___boxed__const__1 = _init_l_Lean_Elab_addAndCompileUnsafe___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_addAndCompileUnsafe___boxed__const__1);
l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at_Lean_Elab_addAndCompilePartialRec___spec__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompilePartialRec___spec__3___closed__1);
l_Lean_Elab_ensureNoRecFn___lambda__1___closed__1 = _init_l_Lean_Elab_ensureNoRecFn___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_ensureNoRecFn___lambda__1___closed__1);
l_Lean_Elab_ensureNoRecFn___lambda__1___closed__2 = _init_l_Lean_Elab_ensureNoRecFn___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_ensureNoRecFn___lambda__1___closed__2);
l_Lean_Elab_ensureNoRecFn___lambda__1___closed__3 = _init_l_Lean_Elab_ensureNoRecFn___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_ensureNoRecFn___lambda__1___closed__3);
l_Lean_Elab_ensureNoRecFn___lambda__1___closed__4 = _init_l_Lean_Elab_ensureNoRecFn___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_ensureNoRecFn___lambda__1___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
