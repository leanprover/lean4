// Lean compiler output
// Module: Lean.Elab.App
// Imports: Init Lean.Util.FindMVar Lean.Parser.Term Lean.Elab.Term Lean.Elab.Binders Lean.Elab.SyntheticMVars
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__3;
extern lean_object* l_Lean_instInhabitedTagAttribute___closed__1;
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__1;
lean_object* l_Lean_Elab_Term_expandArgs_match__1(lean_object*);
uint8_t l_Lean_Expr_bindingInfo_x21(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f_match__1(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_shouldPropagateExpectedTypeFor___boxed(lean_object*);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__4;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__1;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_List_tail_x21___rarg(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedNamedArg___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__6;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
extern lean_object* l_Array_split___rarg___closed__1;
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__1;
uint8_t l_Lean_Expr_isProp(lean_object*);
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1090____closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toName_match__1(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__4___boxed(lean_object**);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__1(lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_propagateExpectedTypeFor_match__1(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_Lean_Elab_Term_NamedArg_ref___default;
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabResult___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isCoeDecl___closed__37;
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2;
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__3;
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__3;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabApp_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__1___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent(lean_object*);
extern lean_object* l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
extern lean_object* l_instInhabitedNat;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess___boxed(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__2(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__2;
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__3___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__2;
lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
uint8_t l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_propagateExpectedTypeFor_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_15378____closed__9;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__1;
extern lean_object* l_Lean_Parser_Term_proj___elambda__1___closed__1;
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__2;
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_hasElabWithoutExpectedType(lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeProj(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures(lean_object*);
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19475____closed__5;
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_expandApp_match__1(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instToStringArg_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_hasElabWithoutExpectedType___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv(lean_object*);
extern lean_object* l_myMacro____x40_Init_NotationExtra___hyg_5659____closed__28;
extern lean_object* l_Lean_Json_Parser_anyCore___rarg___closed__6;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_22690____closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1;
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___boxed(lean_object**);
uint8_t l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandArgs_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_fTypeHasOptAutoParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__7;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAppArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__1;
lean_object* l_Lean_Syntax_SepArray_getElems___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
extern lean_object* l_Lean_Elab_goalsToMessageData___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__3;
lean_object* l_Lean_Elab_Term_elabPipeProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__4;
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__2(lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4;
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Term_elabExplicitUnivs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__2___boxed(lean_object**);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__1(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13856____closed__8;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3;
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
uint8_t l_Lean_Elab_Term_ElabAppArgs_State_ellipsis___default;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__2___closed__1;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instMonadControlReaderT___closed__3;
lean_object* l_Lean_Elab_logException___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__6;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__2;
lean_object* l_List_filterAux___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_propagateExpectedTypeFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__3;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2278____closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_expandCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__2(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__1(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___boxed__const__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__3(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processInstImplicitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17217____closed__3;
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__4___boxed(lean_object**);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg_match__1(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__5___boxed(lean_object**);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___boxed(lean_object**);
lean_object* l_Lean_Elab_Term_elabAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_pipeProj___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals_match__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2;
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__1;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_State_instMVars___default;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData_match__1(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern(lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1;
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice(lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_State_toSetErrorCtx___default;
extern lean_object* l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__4;
extern lean_object* l_termIfLet___x3a_x3d__Then__Else_____closed__7;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___closed__2;
lean_object* l_Lean_Elab_Term_elabIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Elab_Term_elabApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_localDeclDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_shouldPropagateExpectedTypeFor(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__1;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__1(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedArg___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__1(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_elabChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__2;
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__1(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_instToStringNamedArg(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
lean_object* l_Lean_Elab_Term_LVal_getRef(lean_object*);
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
extern lean_object* l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList(lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_expandArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isCoeDecl___closed__12;
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__5;
lean_object* l_Lean_Elab_Term_instToStringArg(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14458____closed__12;
extern lean_object* l_Option_get_x21___rarg___closed__4;
extern lean_object* l_Lean_Syntax_mkApp___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabWithoutExpectedTypeAttr;
lean_object* l_List_filterAux___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__2;
lean_object* l_Lean_getParentStructures(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess_match__1(lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_postponeExceptionId;
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandArgs_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__3(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_saveAllState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlT___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__1(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12;
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_ellipsis___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__5;
lean_object* l_Lean_Elab_Term_addTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toName_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_State_etaArgs___default;
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandArgs(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__1(lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__6;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toName___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_instToStringArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_expandArgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUnivs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_expandArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_8911_(lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4_(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_propagateExpectedTypeFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_elabAppArgs___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__4;
lean_object* l_Lean_Meta_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
extern lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__2;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedNamedArg;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3;
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__9;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__1;
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__3;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14458____closed__13;
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__1;
lean_object* l_Lean_Elab_Term_expandArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206_(uint8_t, uint8_t);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
lean_object* l_Lean_Elab_Term_registerSyntheticMVarWithCurrRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_expandArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__3___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__3(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabApp_match__1(lean_object*);
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___boxed(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__3;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Std_fmt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__2(uint8_t);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_ElabAppArgs_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_elabAppArgs___closed__1;
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabApp___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_22690____closed__3;
extern lean_object* l_prec_x28___x29___closed__3;
lean_object* l_Lean_Elab_Term_elabAppArgs___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEqAux___closed__5;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole_match__1(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_elabAppArgs___closed__3;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__6;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__3;
lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeProj___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ensureArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAppArgs___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__1(lean_object*);
extern lean_object* l_Lean_Meta_substCore___lambda__1___closed__3;
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2;
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14;
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1;
lean_object* l_Lean_Elab_Term_synthesizeCoeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1;
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___lambda__3___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__2;
lean_object* l_Lean_Meta_setPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__4(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__5;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2;
lean_object* l_Lean_Elab_Term_ensureHasTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Meta_processPostponed(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals_match__1(lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__4;
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__3___boxed(lean_object**);
extern lean_object* l_Array_findSomeM_x3f___rarg___closed__1;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1___boxed(lean_object**);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUnivs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__8;
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandArgs_match__2___rarg(lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___closed__1;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals(lean_object*, uint8_t);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toName(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__3(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedArg;
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__3___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabWithoutExpectedType");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mark that applications of the given declaration should be elaborated without the expected type");
return x_1;
}
}
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__2;
x_3 = l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__3;
x_4 = l_Lean_Meta_SynthInstance_initFn____x40_Lean_Meta_SynthInstance___hyg_69____closed__4;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
uint8_t l_Lean_Elab_Term_hasElabWithoutExpectedType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_Term_elabWithoutExpectedTypeAttr;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_hasElabWithoutExpectedType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Term_hasElabWithoutExpectedType(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_instInhabitedArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_instInhabitedArg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedArg___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_instToStringArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_instToStringArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_instToStringArg_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_instToStringArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = 0;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_formatStxAux(x_3, x_4, x_5, x_2);
x_7 = l_Std_Format_defWidth;
x_8 = lean_format_pretty(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
return x_10;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_NamedArg_ref___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_instInhabitedNamedArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Elab_Term_instInhabitedArg___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_instInhabitedNamedArg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedNamedArg___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_instToStringNamedArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_Name_toStringWithSep(x_3, x_2);
x_5 = l_prec_x28___x29___closed__3;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_termIfLet___x3a_x3d__Then__Else_____closed__7;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = 0;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_formatStxAux(x_11, x_12, x_13, x_10);
x_15 = l_Std_Format_defWidth;
x_16 = lean_format_pretty(x_14, x_15);
x_17 = lean_string_append(x_8, x_16);
lean_dec(x_16);
x_18 = l_prec_x28___x29___closed__7;
x_19 = lean_string_append(x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_expr_dbg_to_string(x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_8, x_21);
lean_dec(x_21);
x_23 = l_prec_x28___x29___closed__7;
x_24 = lean_string_append(x_22, x_23);
return x_24;
}
}
}
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwInvalidNamedArg_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid argument name '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' for function");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' for function '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_7, 3);
x_13 = l_Lean_replaceRef(x_11, x_12);
lean_dec(x_12);
lean_ctor_set(x_7, 3, x_13);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__1___rarg(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_21);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_21);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_KernelException_toMessageData___closed__3;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__2___rarg(x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
x_36 = lean_ctor_get(x_7, 2);
x_37 = lean_ctor_get(x_7, 3);
x_38 = lean_ctor_get(x_7, 4);
x_39 = lean_ctor_get(x_7, 5);
x_40 = lean_ctor_get(x_7, 6);
x_41 = lean_ctor_get(x_7, 7);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_42 = l_Lean_replaceRef(x_33, x_37);
lean_dec(x_37);
x_43 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_35);
lean_ctor_set(x_43, 2, x_36);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_43, 4, x_38);
lean_ctor_set(x_43, 5, x_39);
lean_ctor_set(x_43, 6, x_40);
lean_ctor_set(x_43, 7, x_41);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__4;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__1___rarg(x_49, x_3, x_4, x_5, x_6, x_43, x_8, x_9);
lean_dec(x_43);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_2, 0);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__6;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_inc(x_51);
x_58 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_58, 0, x_51);
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_KernelException_toMessageData___closed__3;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__2___rarg(x_61, x_3, x_4, x_5, x_6, x_43, x_8, x_9);
lean_dec(x_43);
return x_62;
}
}
}
}
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwInvalidNamedArg___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_throwInvalidNamedArg___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_3 + x_10;
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
lean_object* l_Lean_Elab_Term_addNamedArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_push(x_1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("argument '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' was already set");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Elab_Term_addNamedArg___lambda__1(x_1, x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_10, x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Term_addNamedArg___lambda__1(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_20 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addNamedArg___spec__1(x_2, x_1, x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Term_addNamedArg___lambda__1(x_1, x_2, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Elab_Term_addNamedArg___closed__2;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_Term_addNamedArg___closed__4;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_addNamedArg___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_addNamedArg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_addNamedArg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_addNamedArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ensureArgType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_11 = l_Lean_Meta_inferType(x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Term_ensureHasTypeAux(x_14, x_12, x_2, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_mkSort(x_11);
lean_inc(x_1);
x_14 = l_Lean_Meta_mkArrow(x_1, x_13, x_5, x_6, x_7, x_8, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = 0;
x_19 = lean_box(0);
lean_inc(x_5);
x_20 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_23 = l_Lean_Meta_getLevel(x_1, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Meta_isCoeDecl___closed__37;
lean_inc(x_28);
x_30 = l_Lean_mkConst(x_29, x_28);
x_31 = l_Lean_Syntax_mkApp___closed__1;
lean_inc(x_1);
x_32 = lean_array_push(x_31, x_1);
lean_inc(x_21);
x_33 = lean_array_push(x_32, x_21);
x_34 = l_Lean_mkAppN(x_30, x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = 1;
lean_inc(x_5);
x_37 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_35, x_36, x_19, x_5, x_6, x_7, x_8, x_25);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Expr_mvarId_x21(x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_41 = l_Lean_Elab_Term_synthesizeCoeInstMVarCore(x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_41, 0, x_46);
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_dec(x_41);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = l_Lean_Meta_isCoeDecl___closed__12;
x_52 = l_Lean_mkConst(x_51, x_28);
x_53 = l_Lean_Json_Parser_anyCore___rarg___closed__6;
x_54 = lean_array_push(x_53, x_1);
x_55 = lean_array_push(x_54, x_21);
x_56 = lean_array_push(x_55, x_2);
x_57 = lean_array_push(x_56, x_38);
x_58 = l_Lean_mkAppN(x_52, x_57);
lean_dec(x_57);
x_59 = l_Lean_Meta_expandCoe(x_58, x_5, x_6, x_7, x_8, x_50);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_59, 0, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_59);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_59, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set_tag(x_59, 0);
lean_ctor_set(x_59, 0, x_69);
return x_59;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_59, 1);
lean_inc(x_70);
lean_dec(x_59);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_38);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_41);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_41, 0);
lean_dec(x_74);
x_75 = lean_box(0);
lean_ctor_set_tag(x_41, 0);
lean_ctor_set(x_41, 0, x_75);
return x_41;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_41, 1);
lean_inc(x_76);
lean_dec(x_41);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_23);
if (x_79 == 0)
{
return x_23;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_23, 0);
x_81 = lean_ctor_get(x_23, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_23);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
x_15 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_14);
x_16 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
lean_inc(x_9);
x_21 = l_Lean_Elab_Term_registerSyntheticMVarWithCurrRef(x_14, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 1;
x_24 = x_3 + x_23;
x_25 = lean_box(0);
x_3 = x_24;
x_4 = x_25;
x_11 = x_22;
goto _start;
}
else
{
lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
lean_dec(x_14);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec(x_16);
x_28 = 1;
x_29 = x_3 + x_28;
x_30 = lean_box(0);
x_3 = x_29;
x_4 = x_30;
x_11 = x_27;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_1, x_10, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_synthesizeAppInstMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
static uint8_t _init_l_Lean_Elab_Term_ElabAppArgs_State_ellipsis___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_ElabAppArgs_State_etaArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_ElabAppArgs_State_toSetErrorCtx___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_ElabAppArgs_State_instMVars___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_13, 7);
x_17 = lean_array_push(x_16, x_1);
lean_ctor_set(x_13, 7, x_17);
x_18 = lean_st_ref_set(x_2, x_13, x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_25 = lean_ctor_get_uint8(x_13, sizeof(void*)*8);
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
x_28 = lean_ctor_get(x_13, 2);
x_29 = lean_ctor_get(x_13, 3);
x_30 = lean_ctor_get_uint8(x_13, sizeof(void*)*8 + 1);
x_31 = lean_ctor_get(x_13, 4);
x_32 = lean_ctor_get(x_13, 5);
x_33 = lean_ctor_get(x_13, 6);
x_34 = lean_ctor_get(x_13, 7);
x_35 = lean_ctor_get_uint8(x_13, sizeof(void*)*8 + 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_36 = lean_array_push(x_34, x_1);
x_37 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 3, x_29);
lean_ctor_set(x_37, 4, x_31);
lean_ctor_set(x_37, 5, x_32);
lean_ctor_set(x_37, 6, x_33);
lean_ctor_set(x_37, 7, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*8, x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 1, x_30);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 2, x_35);
x_38 = lean_st_ref_set(x_2, x_37, x_14);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 7);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_7, x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_1, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_18, 7);
lean_dec(x_21);
x_22 = l_Array_empty___closed__1;
lean_ctor_set(x_18, 7, x_22);
x_23 = lean_st_ref_set(x_1, x_18, x_19);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Term_synthesizeAppInstMVars(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_24);
lean_dec(x_14);
return x_25;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get_uint8(x_18, sizeof(void*)*8);
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
x_29 = lean_ctor_get(x_18, 2);
x_30 = lean_ctor_get(x_18, 3);
x_31 = lean_ctor_get_uint8(x_18, sizeof(void*)*8 + 1);
x_32 = lean_ctor_get(x_18, 4);
x_33 = lean_ctor_get(x_18, 5);
x_34 = lean_ctor_get(x_18, 6);
x_35 = lean_ctor_get_uint8(x_18, sizeof(void*)*8 + 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_36 = l_Array_empty___closed__1;
x_37 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_29);
lean_ctor_set(x_37, 3, x_30);
lean_ctor_set(x_37, 4, x_32);
lean_ctor_set(x_37, 5, x_33);
lean_ctor_set(x_37, 6, x_34);
lean_ctor_set(x_37, 7, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*8, x_26);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 1, x_31);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 2, x_35);
x_38 = lean_st_ref_set(x_1, x_37, x_19);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Elab_Term_synthesizeAppInstMVars(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_39);
lean_dec(x_14);
return x_40;
}
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Expr_getAppFn(x_1);
x_15 = l_Lean_Expr_isConst(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = l_Lean_Expr_constName_x21(x_14);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
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
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("function expected at");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nterm has type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_9 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_7, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_1, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Meta_whnfForall(x_20, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_isForall(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_25);
lean_inc(x_22);
x_26 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(x_22, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_18, 3);
lean_inc(x_29);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_2);
x_30 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1(x_25, x_29, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_indentExpr(x_25);
x_33 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_indentExpr(x_22);
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_KernelException_toMessageData___closed__15;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2(x_40, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_ctor_get(x_26, 1);
lean_inc(x_46);
lean_dec(x_26);
x_47 = lean_ctor_get(x_27, 0);
lean_inc(x_47);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_47);
x_48 = l_Lean_Meta_inferType(x_47, x_4, x_5, x_6, x_7, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_st_ref_get(x_7, x_50);
lean_dec(x_7);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_ref_take(x_1, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_54, 1);
lean_dec(x_57);
x_58 = lean_ctor_get(x_54, 0);
lean_dec(x_58);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_54, 0, x_47);
x_59 = lean_st_ref_set(x_1, x_54, x_55);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set(x_59, 0, x_12);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_12);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_64 = lean_ctor_get_uint8(x_54, sizeof(void*)*8);
x_65 = lean_ctor_get(x_54, 2);
x_66 = lean_ctor_get(x_54, 3);
x_67 = lean_ctor_get_uint8(x_54, sizeof(void*)*8 + 1);
x_68 = lean_ctor_get(x_54, 4);
x_69 = lean_ctor_get(x_54, 5);
x_70 = lean_ctor_get(x_54, 6);
x_71 = lean_ctor_get(x_54, 7);
x_72 = lean_ctor_get_uint8(x_54, sizeof(void*)*8 + 2);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_54);
x_73 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_73, 0, x_47);
lean_ctor_set(x_73, 1, x_49);
lean_ctor_set(x_73, 2, x_65);
lean_ctor_set(x_73, 3, x_66);
lean_ctor_set(x_73, 4, x_68);
lean_ctor_set(x_73, 5, x_69);
lean_ctor_set(x_73, 6, x_70);
lean_ctor_set(x_73, 7, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*8, x_64);
lean_ctor_set_uint8(x_73, sizeof(void*)*8 + 1, x_67);
lean_ctor_set_uint8(x_73, sizeof(void*)*8 + 2, x_72);
x_74 = lean_st_ref_set(x_1, x_73, x_55);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_12);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_47);
lean_dec(x_7);
x_78 = !lean_is_exclusive(x_48);
if (x_78 == 0)
{
return x_48;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_48, 0);
x_80 = lean_ctor_get(x_48, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_48);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_26);
if (x_82 == 0)
{
return x_26;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_26, 0);
x_84 = lean_ctor_get(x_26, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_26);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_st_ref_get(x_7, x_23);
lean_dec(x_7);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_st_ref_take(x_1, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = !lean_is_exclusive(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_89, 1);
lean_dec(x_92);
lean_ctor_set(x_89, 1, x_22);
x_93 = lean_st_ref_set(x_1, x_89, x_90);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_93, 0);
lean_dec(x_95);
lean_ctor_set(x_93, 0, x_12);
return x_93;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_12);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_98 = lean_ctor_get_uint8(x_89, sizeof(void*)*8);
x_99 = lean_ctor_get(x_89, 0);
x_100 = lean_ctor_get(x_89, 2);
x_101 = lean_ctor_get(x_89, 3);
x_102 = lean_ctor_get_uint8(x_89, sizeof(void*)*8 + 1);
x_103 = lean_ctor_get(x_89, 4);
x_104 = lean_ctor_get(x_89, 5);
x_105 = lean_ctor_get(x_89, 6);
x_106 = lean_ctor_get(x_89, 7);
x_107 = lean_ctor_get_uint8(x_89, sizeof(void*)*8 + 2);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_89);
x_108 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_108, 0, x_99);
lean_ctor_set(x_108, 1, x_22);
lean_ctor_set(x_108, 2, x_100);
lean_ctor_set(x_108, 3, x_101);
lean_ctor_set(x_108, 4, x_103);
lean_ctor_set(x_108, 5, x_104);
lean_ctor_set(x_108, 6, x_105);
lean_ctor_set(x_108, 7, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*8, x_98);
lean_ctor_set_uint8(x_108, sizeof(void*)*8 + 1, x_102);
lean_ctor_set_uint8(x_108, sizeof(void*)*8 + 2, x_107);
x_109 = lean_st_ref_set(x_1, x_108, x_90);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_12);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_21);
if (x_113 == 0)
{
return x_21;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_21, 0);
x_115 = lean_ctor_get(x_21, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_21);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_117 = !lean_is_exclusive(x_13);
if (x_117 == 0)
{
return x_13;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_13, 0);
x_119 = lean_ctor_get(x_13, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_13);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_9);
if (x_121 == 0)
{
return x_9;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_9, 0);
x_123 = lean_ctor_get(x_9, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_9);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
x_15 = l_Lean_Meta_whnfForall(x_14, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_7, x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_take(x_1, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_dec(x_24);
lean_inc(x_16);
lean_ctor_set(x_21, 1, x_16);
x_25 = lean_st_ref_set(x_1, x_21, x_22);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_16);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_30 = lean_ctor_get_uint8(x_21, sizeof(void*)*8);
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 2);
x_33 = lean_ctor_get(x_21, 3);
x_34 = lean_ctor_get_uint8(x_21, sizeof(void*)*8 + 1);
x_35 = lean_ctor_get(x_21, 4);
x_36 = lean_ctor_get(x_21, 5);
x_37 = lean_ctor_get(x_21, 6);
x_38 = lean_ctor_get(x_21, 7);
x_39 = lean_ctor_get_uint8(x_21, sizeof(void*)*8 + 2);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
lean_inc(x_16);
x_40 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_16);
lean_ctor_set(x_40, 2, x_32);
lean_ctor_set(x_40, 3, x_33);
lean_ctor_set(x_40, 4, x_35);
lean_ctor_set(x_40, 5, x_36);
lean_ctor_set(x_40, 6, x_37);
lean_ctor_set(x_40, 7, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*8, x_30);
lean_ctor_set_uint8(x_40, sizeof(void*)*8 + 1, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*8 + 2, x_39);
x_41 = lean_st_ref_set(x_1, x_40, x_22);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_16);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_7);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Expr_bindingName_x21(x_14);
lean_dec(x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Expr_bindingName_x21(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Expr_bindingDomain_x21(x_14);
lean_dec(x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Expr_bindingDomain_x21(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_List_filterAux___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_name_eq(x_14, x_1);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_3);
x_2 = x_13;
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_12);
x_2 = x_13;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_filterAux___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_List_filterAux___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_13, 3);
x_17 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(x_16, x_1);
lean_ctor_set(x_13, 3, x_17);
x_18 = lean_st_ref_set(x_2, x_13, x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_25 = lean_ctor_get_uint8(x_13, sizeof(void*)*8);
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
x_28 = lean_ctor_get(x_13, 2);
x_29 = lean_ctor_get(x_13, 3);
x_30 = lean_ctor_get_uint8(x_13, sizeof(void*)*8 + 1);
x_31 = lean_ctor_get(x_13, 4);
x_32 = lean_ctor_get(x_13, 5);
x_33 = lean_ctor_get(x_13, 6);
x_34 = lean_ctor_get(x_13, 7);
x_35 = lean_ctor_get_uint8(x_13, sizeof(void*)*8 + 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_36 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(x_29, x_1);
x_37 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_31);
lean_ctor_set(x_37, 5, x_32);
lean_ctor_set(x_37, 6, x_33);
lean_ctor_set(x_37, 7, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*8, x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 1, x_30);
lean_ctor_set_uint8(x_37, sizeof(void*)*8 + 2, x_35);
x_38 = lean_st_ref_set(x_2, x_37, x_14);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_1);
x_18 = l_Lean_mkApp(x_16, x_1);
x_19 = l_Lean_Expr_bindingBody_x21(x_17);
lean_dec(x_17);
x_20 = lean_expr_instantiate1(x_19, x_1);
lean_dec(x_1);
lean_dec(x_19);
lean_ctor_set(x_13, 1, x_20);
lean_ctor_set(x_13, 0, x_18);
x_21 = lean_st_ref_set(x_2, x_13, x_14);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_28 = lean_ctor_get_uint8(x_13, sizeof(void*)*8);
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
x_31 = lean_ctor_get(x_13, 2);
x_32 = lean_ctor_get(x_13, 3);
x_33 = lean_ctor_get_uint8(x_13, sizeof(void*)*8 + 1);
x_34 = lean_ctor_get(x_13, 4);
x_35 = lean_ctor_get(x_13, 5);
x_36 = lean_ctor_get(x_13, 6);
x_37 = lean_ctor_get(x_13, 7);
x_38 = lean_ctor_get_uint8(x_13, sizeof(void*)*8 + 2);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
lean_inc(x_1);
x_39 = l_Lean_mkApp(x_29, x_1);
x_40 = l_Lean_Expr_bindingBody_x21(x_30);
lean_dec(x_30);
x_41 = lean_expr_instantiate1(x_40, x_1);
lean_dec(x_1);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_31);
lean_ctor_set(x_42, 3, x_32);
lean_ctor_set(x_42, 4, x_34);
lean_ctor_set(x_42, 5, x_35);
lean_ctor_set(x_42, 6, x_36);
lean_ctor_set(x_42, 7, x_37);
lean_ctor_set_uint8(x_42, sizeof(void*)*8, x_28);
lean_ctor_set_uint8(x_42, sizeof(void*)*8 + 1, x_33);
lean_ctor_set_uint8(x_42, sizeof(void*)*8 + 2, x_38);
x_43 = lean_st_ref_set(x_2, x_42, x_14);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_20 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Lean_Elab_Term_elabTerm(x_18, x_19, x_20, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ensureArgType(x_24, x_22, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
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
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_21);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_15, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_dec(x_15);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_ctor_get(x_13, 0);
lean_inc(x_40);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_41 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ensureArgType(x_40, x_39, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 == x_3;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget(x_1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_Meta_inferType(x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_Expr_getOptParamDefault_x3f(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Expr_getAutoParamTactic_x3f(x_16);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 0)
{
size_t x_20; size_t x_21; 
lean_free_object(x_14);
x_20 = 1;
x_21 = x_2 + x_20;
x_2 = x_21;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
}
else
{
uint8_t x_25; lean_object* x_26; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_25 = 1;
x_26 = lean_box(x_25);
lean_ctor_set(x_14, 0, x_26);
return x_14;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = l_Lean_Expr_getOptParamDefault_x3f(x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = l_Lean_Expr_getAutoParamTactic_x3f(x_27);
lean_dec(x_27);
if (lean_obj_tag(x_30) == 0)
{
size_t x_31; size_t x_32; 
x_31 = 1;
x_32 = x_2 + x_31;
x_2 = x_32;
x_11 = x_28;
goto _start;
}
else
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_34 = 1;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
}
else
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_37 = 1;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_28);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_44 = 0;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_11);
return x_46;
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_5, x_6, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg___lambda__1), 11, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(x_1, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
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
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_11, x_11);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_23 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1(x_1, x_21, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1___boxed), 10, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
x_11 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_fTypeHasOptAutoParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
x_16 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_14, x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
return x_16;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_dec(x_5);
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_7(x_4, x_1, x_2, x_3, x_9, x_10, x_11, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_apply_3(x_6, x_1, x_2, x_3);
return x_15;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_6);
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_20 = lean_box_uint64(x_19);
x_21 = lean_apply_7(x_4, x_7, x_2, x_3, x_16, x_17, x_18, x_20);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_4);
x_22 = lean_apply_1(x_5, x_3);
return x_22;
}
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
x_26 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_27 = lean_box_uint64(x_26);
x_28 = lean_apply_7(x_4, x_7, x_2, x_3, x_23, x_24, x_25, x_27);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_4);
x_29 = lean_apply_3(x_6, x_7, x_2, x_3);
return x_29;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__2___rarg), 6, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_name_eq(x_3, x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_22; lean_object* x_23; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_7);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1___boxed), 2, 1);
lean_closure_set(x_22, 0, x_7);
lean_inc(x_3);
x_23 = l_List_find_x3f___rarg(x_22, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_7);
if (x_1 == 0)
{
uint8_t x_24; uint8_t x_25; 
x_24 = (uint8_t)((x_10 << 24) >> 61);
x_25 = l_Lean_BinderInfo_isExplicit(x_24);
if (x_25 == 0)
{
lean_dec(x_8);
lean_dec(x_4);
x_4 = x_9;
goto _start;
}
else
{
lean_object* x_27; 
x_27 = lean_box(0);
x_11 = x_27;
goto block_21;
}
}
else
{
lean_object* x_28; 
x_28 = lean_box(0);
x_11 = x_28;
goto block_21;
}
}
else
{
lean_object* x_29; 
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_4);
x_29 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(x_3, x_7);
lean_dec(x_7);
x_3 = x_29;
x_4 = x_9;
goto _start;
}
block_21:
{
uint8_t x_12; 
lean_dec(x_11);
x_12 = lean_nat_dec_lt(x_5, x_2);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isAutoParam(x_8);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isOptParam(x_8);
lean_dec(x_8);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_dec(x_4);
x_4 = x_9;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_4);
x_4 = x_9;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_4);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_2, x_18);
lean_dec(x_2);
x_2 = x_19;
x_4 = x_9;
goto _start;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_box(0);
return x_31;
}
}
else
{
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_4, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_4, 2);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_32);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1___boxed), 2, 1);
lean_closure_set(x_36, 0, x_32);
x_37 = l_List_find_x3f___rarg(x_36, x_3);
if (lean_obj_tag(x_37) == 0)
{
lean_dec(x_32);
if (x_1 == 0)
{
uint8_t x_38; uint8_t x_39; 
x_38 = (uint8_t)((x_35 << 24) >> 61);
x_39 = l_Lean_BinderInfo_isExplicit(x_38);
if (x_39 == 0)
{
lean_dec(x_33);
lean_dec(x_4);
x_2 = x_5;
x_4 = x_34;
goto _start;
}
else
{
uint8_t x_41; 
x_41 = l_Lean_Expr_isAutoParam(x_33);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = l_Lean_Expr_isOptParam(x_33);
lean_dec(x_33);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_34);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_4);
return x_43;
}
else
{
lean_dec(x_4);
x_2 = x_5;
x_4 = x_34;
goto _start;
}
}
else
{
lean_dec(x_33);
lean_dec(x_4);
x_2 = x_5;
x_4 = x_34;
goto _start;
}
}
}
else
{
uint8_t x_46; 
x_46 = l_Lean_Expr_isAutoParam(x_33);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Expr_isOptParam(x_33);
lean_dec(x_33);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_34);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_4);
return x_48;
}
else
{
lean_dec(x_4);
x_2 = x_5;
x_4 = x_34;
goto _start;
}
}
else
{
lean_dec(x_33);
lean_dec(x_4);
x_2 = x_5;
x_4 = x_34;
goto _start;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_4);
x_51 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(x_3, x_32);
lean_dec(x_32);
x_2 = x_5;
x_3 = x_51;
x_4 = x_34;
goto _start;
}
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_4);
return x_53;
}
}
else
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint64_t x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_4, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_4, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_4, 2);
lean_inc(x_56);
x_57 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_inc(x_54);
x_58 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1___boxed), 2, 1);
lean_closure_set(x_58, 0, x_54);
lean_inc(x_3);
x_59 = l_List_find_x3f___rarg(x_58, x_3);
if (lean_obj_tag(x_59) == 0)
{
lean_dec(x_54);
if (x_1 == 0)
{
uint8_t x_60; uint8_t x_61; 
x_60 = (uint8_t)((x_57 << 24) >> 61);
x_61 = l_Lean_BinderInfo_isExplicit(x_60);
if (x_61 == 0)
{
lean_dec(x_55);
lean_dec(x_4);
x_2 = x_5;
x_4 = x_56;
goto _start;
}
else
{
uint8_t x_63; 
x_63 = l_Lean_Expr_isAutoParam(x_55);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = l_Lean_Expr_isOptParam(x_55);
lean_dec(x_55);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_56);
lean_dec(x_3);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_4);
return x_65;
}
else
{
lean_dec(x_4);
x_2 = x_5;
x_4 = x_56;
goto _start;
}
}
else
{
lean_dec(x_55);
lean_dec(x_4);
x_2 = x_5;
x_4 = x_56;
goto _start;
}
}
}
else
{
uint8_t x_68; 
x_68 = l_Lean_Expr_isAutoParam(x_55);
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = l_Lean_Expr_isOptParam(x_55);
lean_dec(x_55);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_56);
lean_dec(x_3);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_4);
return x_70;
}
else
{
lean_dec(x_4);
x_2 = x_5;
x_4 = x_56;
goto _start;
}
}
else
{
lean_dec(x_55);
lean_dec(x_4);
x_2 = x_5;
x_4 = x_56;
goto _start;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_4);
x_73 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(x_3, x_54);
lean_dec(x_54);
x_2 = x_5;
x_3 = x_73;
x_4 = x_56;
goto _start;
}
}
else
{
lean_object* x_75; 
lean_dec(x_4);
lean_dec(x_3);
x_75 = lean_box(0);
return x_75;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(x_5, x_2, x_3, x_4);
return x_6;
}
}
uint8_t l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_shouldPropagateExpectedTypeFor(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Syntax_getKind(x_2);
x_4 = l_myMacro____x40_Init_Notation___hyg_14458____closed__13;
x_5 = lean_name_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_19475____closed__5;
x_7 = lean_name_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_myMacro____x40_Init_Notation___hyg_22690____closed__2;
x_9 = lean_name_eq(x_3, x_8);
lean_dec(x_3);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_3);
x_12 = 0;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = 0;
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = 0;
return x_14;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_shouldPropagateExpectedTypeFor___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_shouldPropagateExpectedTypeFor(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_9, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_16, 3);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_13);
lean_inc(x_11);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Std_PersistentArray_push___rarg(x_22, x_24);
lean_ctor_set(x_17, 0, x_25);
x_26 = lean_st_ref_set(x_9, x_16, x_18);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
lean_dec(x_17);
x_35 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_13);
lean_inc(x_11);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_11);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Std_PersistentArray_push___rarg(x_34, x_36);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_33);
lean_ctor_set(x_16, 3, x_38);
x_39 = lean_st_ref_set(x_9, x_16, x_18);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
x_46 = lean_ctor_get(x_16, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_47 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_48 = lean_ctor_get(x_17, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_49 = x_17;
} else {
 lean_dec_ref(x_17);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_13);
lean_inc(x_11);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_11);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Std_PersistentArray_push___rarg(x_48, x_51);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 1, 1);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_47);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_45);
lean_ctor_set(x_54, 2, x_46);
lean_ctor_set(x_54, 3, x_53);
x_55 = lean_st_ref_set(x_9, x_54, x_18);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_checkTraceOption(x_10, x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1090____closed__1;
x_2 = l_myMacro____x40_Init_Notation___hyg_2278____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("propagateExpectedType");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1;
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("etaArgs.size: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", numRemainingArgs: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", fType: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_shouldPropagateExpectedTypeFor(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_st_ref_get(x_8, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_16, 5);
lean_inc(x_19);
x_20 = l_Array_isEmpty___rarg(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_18;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_ctor_get_uint8(x_16, sizeof(void*)*8 + 2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_18;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_16, 4);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_18;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_17);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_Expr_isProp(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_198; lean_object* x_199; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_31 = lean_ctor_get(x_16, 2);
lean_inc(x_31);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_List_lengthAux___rarg(x_31, x_32);
lean_dec(x_31);
x_221 = lean_st_ref_get(x_8, x_17);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_222, 3);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_ctor_get_uint8(x_223, sizeof(void*)*1);
lean_dec(x_223);
if (x_224 == 0)
{
lean_object* x_225; uint8_t x_226; 
x_225 = lean_ctor_get(x_221, 1);
lean_inc(x_225);
lean_dec(x_221);
x_226 = 0;
x_198 = x_226;
x_199 = x_225;
goto block_220;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_227 = lean_ctor_get(x_221, 1);
lean_inc(x_227);
lean_dec(x_221);
x_228 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_229 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_228, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_227);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_unbox(x_230);
lean_dec(x_230);
x_198 = x_232;
x_199 = x_231;
goto block_220;
}
block_197:
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get_uint8(x_16, sizeof(void*)*8);
x_36 = lean_ctor_get(x_16, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_dec(x_16);
x_38 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(x_35, x_33, x_36, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_18;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Expr_hasLooseBVars(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_18);
x_43 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_41);
x_44 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_41, x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_95; lean_object* x_96; uint8_t x_109; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
x_109 = lean_unbox(x_46);
lean_dec(x_46);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_free_object(x_44);
x_110 = lean_st_ref_get(x_8, x_47);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_111, 3);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_ctor_get_uint8(x_112, sizeof(void*)*1);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_dec(x_110);
x_115 = 0;
x_95 = x_115;
x_96 = x_114;
goto block_108;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_116 = lean_ctor_get(x_110, 1);
lean_inc(x_116);
lean_dec(x_110);
x_117 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_118 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_117, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_116);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_unbox(x_119);
lean_dec(x_119);
x_95 = x_121;
x_96 = x_120;
goto block_108;
}
}
else
{
lean_object* x_122; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_122 = lean_box(0);
lean_ctor_set(x_44, 0, x_122);
return x_44;
}
block_94:
{
lean_object* x_49; 
lean_inc(x_8);
x_49 = l_Lean_Meta_isExprDefEq(x_29, x_41, x_5, x_6, x_7, x_8, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_8);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_49, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set(x_49, 0, x_54);
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_dec(x_49);
x_59 = lean_st_ref_get(x_8, x_58);
lean_dec(x_8);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_st_ref_take(x_2, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
uint8_t x_65; lean_object* x_66; uint8_t x_67; 
x_65 = 0;
lean_ctor_set_uint8(x_62, sizeof(void*)*8 + 2, x_65);
x_66 = lean_st_ref_set(x_2, x_62, x_63);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_73 = lean_ctor_get_uint8(x_62, sizeof(void*)*8);
x_74 = lean_ctor_get(x_62, 0);
x_75 = lean_ctor_get(x_62, 1);
x_76 = lean_ctor_get(x_62, 2);
x_77 = lean_ctor_get(x_62, 3);
x_78 = lean_ctor_get_uint8(x_62, sizeof(void*)*8 + 1);
x_79 = lean_ctor_get(x_62, 4);
x_80 = lean_ctor_get(x_62, 5);
x_81 = lean_ctor_get(x_62, 6);
x_82 = lean_ctor_get(x_62, 7);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_62);
x_83 = 0;
x_84 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_75);
lean_ctor_set(x_84, 2, x_76);
lean_ctor_set(x_84, 3, x_77);
lean_ctor_set(x_84, 4, x_79);
lean_ctor_set(x_84, 5, x_80);
lean_ctor_set(x_84, 6, x_81);
lean_ctor_set(x_84, 7, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*8, x_73);
lean_ctor_set_uint8(x_84, sizeof(void*)*8 + 1, x_78);
lean_ctor_set_uint8(x_84, sizeof(void*)*8 + 2, x_83);
x_85 = lean_st_ref_set(x_2, x_84, x_63);
lean_dec(x_2);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_8);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_49);
if (x_90 == 0)
{
return x_49;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_49, 0);
x_92 = lean_ctor_get(x_49, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_49);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
block_108:
{
if (x_95 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
x_48 = x_96;
goto block_94;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_inc(x_29);
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_29);
x_98 = l_Lean_KernelException_toMessageData___closed__15;
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Lean_Meta_isLevelDefEqAux___closed__5;
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_inc(x_41);
x_102 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_102, 0, x_41);
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_98);
x_105 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_106 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_105, x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_96);
lean_dec(x_4);
lean_dec(x_3);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_48 = x_107;
goto block_94;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_162; lean_object* x_163; uint8_t x_176; 
x_123 = lean_ctor_get(x_44, 0);
x_124 = lean_ctor_get(x_44, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_44);
x_176 = lean_unbox(x_123);
lean_dec(x_123);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_177 = lean_st_ref_get(x_8, x_124);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_178, 3);
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_ctor_get_uint8(x_179, sizeof(void*)*1);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
lean_dec(x_177);
x_182 = 0;
x_162 = x_182;
x_163 = x_181;
goto block_175;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_183 = lean_ctor_get(x_177, 1);
lean_inc(x_183);
lean_dec(x_177);
x_184 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_185 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_184, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_183);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_unbox(x_186);
lean_dec(x_186);
x_162 = x_188;
x_163 = x_187;
goto block_175;
}
}
else
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_124);
return x_190;
}
block_161:
{
lean_object* x_126; 
lean_inc(x_8);
x_126 = l_Lean_Meta_isExprDefEq(x_29, x_41, x_5, x_6, x_7, x_8, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_8);
lean_dec(x_2);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_130 = x_126;
} else {
 lean_dec_ref(x_126);
 x_130 = lean_box(0);
}
x_131 = lean_box(0);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_133 = lean_ctor_get(x_126, 1);
lean_inc(x_133);
lean_dec(x_126);
x_134 = lean_st_ref_get(x_8, x_133);
lean_dec(x_8);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_st_ref_take(x_2, x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_ctor_get_uint8(x_137, sizeof(void*)*8);
x_140 = lean_ctor_get(x_137, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
x_142 = lean_ctor_get(x_137, 2);
lean_inc(x_142);
x_143 = lean_ctor_get(x_137, 3);
lean_inc(x_143);
x_144 = lean_ctor_get_uint8(x_137, sizeof(void*)*8 + 1);
x_145 = lean_ctor_get(x_137, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_137, 5);
lean_inc(x_146);
x_147 = lean_ctor_get(x_137, 6);
lean_inc(x_147);
x_148 = lean_ctor_get(x_137, 7);
lean_inc(x_148);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 lean_ctor_release(x_137, 2);
 lean_ctor_release(x_137, 3);
 lean_ctor_release(x_137, 4);
 lean_ctor_release(x_137, 5);
 lean_ctor_release(x_137, 6);
 lean_ctor_release(x_137, 7);
 x_149 = x_137;
} else {
 lean_dec_ref(x_137);
 x_149 = lean_box(0);
}
x_150 = 0;
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 8, 3);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_140);
lean_ctor_set(x_151, 1, x_141);
lean_ctor_set(x_151, 2, x_142);
lean_ctor_set(x_151, 3, x_143);
lean_ctor_set(x_151, 4, x_145);
lean_ctor_set(x_151, 5, x_146);
lean_ctor_set(x_151, 6, x_147);
lean_ctor_set(x_151, 7, x_148);
lean_ctor_set_uint8(x_151, sizeof(void*)*8, x_139);
lean_ctor_set_uint8(x_151, sizeof(void*)*8 + 1, x_144);
lean_ctor_set_uint8(x_151, sizeof(void*)*8 + 2, x_150);
x_152 = lean_st_ref_set(x_2, x_151, x_138);
lean_dec(x_2);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
x_155 = lean_box(0);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_8);
lean_dec(x_2);
x_157 = lean_ctor_get(x_126, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_126, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_159 = x_126;
} else {
 lean_dec_ref(x_126);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
block_175:
{
if (x_162 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
x_125 = x_163;
goto block_161;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_inc(x_29);
x_164 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_164, 0, x_29);
x_165 = l_Lean_KernelException_toMessageData___closed__15;
x_166 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = l_Lean_Meta_isLevelDefEqAux___closed__5;
x_168 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
lean_inc(x_41);
x_169 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_169, 0, x_41);
x_170 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_165);
x_172 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_173 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_172, x_171, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_163);
lean_dec(x_4);
lean_dec(x_3);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_125 = x_174;
goto block_161;
}
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_191 = !lean_is_exclusive(x_44);
if (x_191 == 0)
{
return x_44;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_44, 0);
x_193 = lean_ctor_get(x_44, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_44);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_41);
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_195 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_18;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_34);
return x_196;
}
}
}
block_220:
{
if (x_198 == 0)
{
lean_dec(x_19);
x_34 = x_199;
goto block_197;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_200 = lean_array_get_size(x_19);
lean_dec(x_19);
x_201 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_200);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_201);
x_203 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5;
x_204 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
x_205 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7;
x_206 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
lean_inc(x_33);
x_207 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_33);
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_207);
x_209 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_208);
x_210 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9;
x_211 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_ctor_get(x_16, 1);
lean_inc(x_212);
x_213 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_213);
x_215 = l_Lean_KernelException_toMessageData___closed__15;
x_216 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_218 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_217, x_216, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_199);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_34 = x_219;
goto block_197;
}
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_233 = lean_st_ref_get(x_8, x_17);
lean_dec(x_8);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_235 = lean_st_ref_take(x_2, x_234);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = !lean_is_exclusive(x_236);
if (x_238 == 0)
{
uint8_t x_239; lean_object* x_240; uint8_t x_241; 
x_239 = 0;
lean_ctor_set_uint8(x_236, sizeof(void*)*8 + 2, x_239);
x_240 = lean_st_ref_set(x_2, x_236, x_237);
lean_dec(x_2);
x_241 = !lean_is_exclusive(x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_240, 0);
lean_dec(x_242);
x_243 = lean_box(0);
lean_ctor_set(x_240, 0, x_243);
return x_240;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_240, 1);
lean_inc(x_244);
lean_dec(x_240);
x_245 = lean_box(0);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
else
{
uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_247 = lean_ctor_get_uint8(x_236, sizeof(void*)*8);
x_248 = lean_ctor_get(x_236, 0);
x_249 = lean_ctor_get(x_236, 1);
x_250 = lean_ctor_get(x_236, 2);
x_251 = lean_ctor_get(x_236, 3);
x_252 = lean_ctor_get_uint8(x_236, sizeof(void*)*8 + 1);
x_253 = lean_ctor_get(x_236, 4);
x_254 = lean_ctor_get(x_236, 5);
x_255 = lean_ctor_get(x_236, 6);
x_256 = lean_ctor_get(x_236, 7);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_236);
x_257 = 0;
x_258 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_258, 0, x_248);
lean_ctor_set(x_258, 1, x_249);
lean_ctor_set(x_258, 2, x_250);
lean_ctor_set(x_258, 3, x_251);
lean_ctor_set(x_258, 4, x_253);
lean_ctor_set(x_258, 5, x_254);
lean_ctor_set(x_258, 6, x_255);
lean_ctor_set(x_258, 7, x_256);
lean_ctor_set_uint8(x_258, sizeof(void*)*8, x_247);
lean_ctor_set_uint8(x_258, sizeof(void*)*8 + 1, x_252);
lean_ctor_set_uint8(x_258, sizeof(void*)*8 + 2, x_257);
x_259 = lean_st_ref_set(x_2, x_258, x_237);
lean_dec(x_2);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_261 = x_259;
} else {
 lean_dec_ref(x_259);
 x_261 = lean_box(0);
}
x_262 = lean_box(0);
if (lean_is_scalar(x_261)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_261;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_260);
return x_263;
}
}
}
}
}
}
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_5, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___lambda__1), 10, 4);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
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
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_take(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_14, 5);
lean_inc(x_2);
x_18 = lean_array_push(x_17, x_2);
lean_ctor_set(x_14, 5, x_18);
x_19 = lean_st_ref_set(x_3, x_14, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_apply_8(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
return x_23;
}
else
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_24 = lean_ctor_get_uint8(x_14, sizeof(void*)*8);
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
x_27 = lean_ctor_get(x_14, 2);
x_28 = lean_ctor_get(x_14, 3);
x_29 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 1);
x_30 = lean_ctor_get(x_14, 4);
x_31 = lean_ctor_get(x_14, 5);
x_32 = lean_ctor_get(x_14, 6);
x_33 = lean_ctor_get(x_14, 7);
x_34 = lean_ctor_get_uint8(x_14, sizeof(void*)*8 + 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
lean_inc(x_2);
x_35 = lean_array_push(x_31, x_2);
x_36 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_26);
lean_ctor_set(x_36, 2, x_27);
lean_ctor_set(x_36, 3, x_28);
lean_ctor_set(x_36, 4, x_30);
lean_ctor_set(x_36, 5, x_35);
lean_ctor_set(x_36, 6, x_32);
lean_ctor_set(x_36, 7, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*8, x_24);
lean_ctor_set_uint8(x_36, sizeof(void*)*8 + 1, x_29);
lean_ctor_set_uint8(x_36, sizeof(void*)*8 + 2, x_34);
x_37 = lean_st_ref_set(x_3, x_36, x_15);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_apply_8(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_40);
return x_41;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___lambda__1), 10, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = 0;
x_18 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg(x_11, x_17, x_14, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_18;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = x_5 < x_4;
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
lean_dec(x_6);
x_17 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(x_17, x_2, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = x_5 + x_20;
x_22 = lean_box(0);
x_5 = x_21;
x_6 = x_22;
x_14 = x_19;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
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
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after etaArgs, ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_13 = l_Lean_Meta_inferType(x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_59; lean_object* x_60; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_73 = lean_st_ref_get(x_11, x_15);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_74, 3);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_ctor_get_uint8(x_75, sizeof(void*)*1);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = 0;
x_59 = x_78;
x_60 = x_77;
goto block_72;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
lean_dec(x_73);
lean_inc(x_2);
x_80 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_unbox(x_81);
lean_dec(x_81);
x_59 = x_83;
x_60 = x_82;
goto block_72;
}
block_58:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 4);
lean_inc(x_17);
lean_dec(x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_2);
x_18 = lean_box(0);
x_19 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_47 = lean_st_ref_get(x_11, x_16);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 3);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get_uint8(x_49, sizeof(void*)*1);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = 0;
x_21 = x_52;
x_22 = x_51;
goto block_46;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
lean_inc(x_2);
x_54 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unbox(x_55);
lean_dec(x_55);
x_21 = x_57;
x_22 = x_56;
goto block_46;
}
block_46:
{
if (x_21 == 0)
{
lean_object* x_23; 
lean_dec(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_isExprDefEq(x_20, x_14, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_3, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_20);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_20);
x_32 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___lambda__3___closed__3;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_KernelException_toMessageData___closed__15;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_2, x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_38 = l_Lean_Meta_isExprDefEq(x_20, x_14, x_8, x_9, x_10, x_11, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_3, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_39);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
block_72:
{
if (x_59 == 0)
{
x_16 = x_60;
goto block_58;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_inc(x_3);
x_61 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_61, 0, x_3);
x_62 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__3;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_inc(x_14);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_14);
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_KernelException_toMessageData___closed__15;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_inc(x_2);
x_70 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_2, x_69, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_60);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_16 = x_71;
goto block_58;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_13);
if (x_84 == 0)
{
return x_13;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_13, 0);
x_86 = lean_ctor_get(x_13, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_13);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalize");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1;
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_40 = lean_st_ref_get(x_7, x_13);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_15 = x_44;
goto block_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2;
x_47 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_46, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_15 = x_50;
goto block_39;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
lean_inc(x_14);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_14);
x_53 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_46, x_52, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_51);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_15 = x_54;
goto block_39;
}
}
block_39:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 6);
lean_inc(x_17);
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = lean_box(0);
lean_inc(x_14);
x_22 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1(x_14, x_16, x_17, x_19, x_20, x_21, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_17);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_12, 5);
lean_inc(x_24);
x_25 = l_Array_isEmpty___rarg(x_24);
if (x_25 == 0)
{
uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_26 = 0;
x_27 = 1;
lean_inc(x_4);
x_28 = l_Lean_Meta_mkLambdaFVars(x_24, x_14, x_26, x_27, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2;
x_32 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2(x_12, x_31, x_29, x_21, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_24);
x_37 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2;
x_38 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2(x_12, x_37, x_14, x_21, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
return x_38;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_17;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = 0;
x_15 = lean_box(0);
lean_inc(x_5);
x_16 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_13, x_14, x_15, x_5, x_6, x_7, x_8, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_8, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_take(x_2, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_22, 6);
x_26 = l_Lean_Expr_mvarId_x21(x_17);
x_27 = lean_array_push(x_25, x_26);
lean_ctor_set(x_22, 6, x_27);
x_28 = lean_st_ref_set(x_2, x_22, x_23);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
return x_32;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_33 = lean_ctor_get_uint8(x_22, sizeof(void*)*8);
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
x_36 = lean_ctor_get(x_22, 2);
x_37 = lean_ctor_get(x_22, 3);
x_38 = lean_ctor_get_uint8(x_22, sizeof(void*)*8 + 1);
x_39 = lean_ctor_get(x_22, 4);
x_40 = lean_ctor_get(x_22, 5);
x_41 = lean_ctor_get(x_22, 6);
x_42 = lean_ctor_get(x_22, 7);
x_43 = lean_ctor_get_uint8(x_22, sizeof(void*)*8 + 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_44 = l_Lean_Expr_mvarId_x21(x_17);
x_45 = lean_array_push(x_41, x_44);
x_46 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_46, 0, x_34);
lean_ctor_set(x_46, 1, x_35);
lean_ctor_set(x_46, 2, x_36);
lean_ctor_set(x_46, 3, x_37);
lean_ctor_set(x_46, 4, x_39);
lean_ctor_set(x_46, 5, x_40);
lean_ctor_set(x_46, 6, x_45);
lean_ctor_set(x_46, 7, x_42);
lean_ctor_set_uint8(x_46, sizeof(void*)*8, x_33);
lean_ctor_set_uint8(x_46, sizeof(void*)*8 + 1, x_38);
lean_ctor_set_uint8(x_46, sizeof(void*)*8 + 2, x_43);
x_47 = lean_st_ref_set(x_2, x_46, x_23);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_50);
return x_51;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_List_foldr___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___spec__1(x_1, x_2, x_5);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_LocalDecl_userName(x_1);
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
return x_6;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_nat_dec_le(x_17, x_7);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_6, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_6, x_21);
lean_dec(x_6);
x_32 = l_Lean_instInhabitedExpr;
x_33 = lean_array_get(x_32, x_2, x_7);
x_34 = l_Lean_Expr_fvarId_x21(x_33);
lean_dec(x_33);
lean_inc(x_12);
x_35 = l_Lean_Meta_getLocalDecl(x_34, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = 0;
x_39 = l_List_foldr___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___spec__1(x_36, x_38, x_1);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_inc(x_4);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_4);
x_23 = x_40;
x_24 = x_37;
goto block_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_41 = lean_st_ref_get(x_15, x_37);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_st_ref_get(x_13, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Expr_fvarId_x21(x_3);
x_48 = l_Lean_MetavarContext_localDeclDependsOn(x_46, x_36, x_47);
lean_dec(x_47);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_inc(x_4);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_4);
x_23 = x_50;
x_24 = x_45;
goto block_31;
}
else
{
lean_object* x_51; 
x_51 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__1;
x_23 = x_51;
x_24 = x_45;
goto block_31;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_35);
if (x_52 == 0)
{
return x_35;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_35, 0);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_35);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
block_31:
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_4);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_ctor_get(x_5, 2);
x_29 = lean_nat_add(x_7, x_28);
lean_dec(x_7);
x_6 = x_22;
x_7 = x_29;
x_8 = x_27;
x_16 = x_24;
goto _start;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_8);
lean_ctor_set(x_56, 1, x_16);
return x_56;
}
}
else
{
lean_object* x_57; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_8);
lean_ctor_set(x_57, 1, x_16);
return x_57;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__1___boxed), 9, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = l_Lean_instInhabitedExpr;
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get(x_12, x_2, x_13);
x_15 = lean_array_get_size(x_2);
x_16 = lean_unsigned_to_nat(1u);
lean_inc(x_15);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
x_18 = l_Array_findSomeM_x3f___rarg___closed__1;
lean_inc(x_7);
x_19 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___spec__2(x_1, x_2, x_14, x_18, x_17, x_15, x_16, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_17);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__2___closed__1;
x_24 = lean_box(0);
x_25 = lean_apply_9(x_23, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 3);
lean_inc(x_15);
x_16 = l_List_isEmpty___rarg(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_11);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__2___boxed), 11, 1);
lean_closure_set(x_18, 0, x_15);
x_19 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_17, x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
return x_19;
}
else
{
uint8_t x_20; lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = 0;
x_21 = lean_box(x_20);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_ctor_get(x_22, 3);
lean_inc(x_24);
x_25 = l_List_isEmpty___rarg(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__2___boxed), 11, 1);
lean_closure_set(x_27, 0, x_24);
x_28 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_26, x_27, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
return x_31;
}
}
}
}
lean_object* l_List_foldr___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_box(x_1);
x_9 = lean_apply_3(x_7, x_8, x_3, x_3);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
if (lean_obj_tag(x_10) == 4)
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_10, sizeof(void*)*2);
lean_dec(x_10);
x_14 = lean_box_uint64(x_13);
x_15 = lean_apply_4(x_5, x_2, x_11, x_12, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_apply_2(x_6, x_2, x_10);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_apply_2(x_4, x_17, x_3);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_box(x_1);
x_20 = lean_apply_3(x_7, x_19, x_2, x_3);
return x_20;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
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
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_SourceInfo_fromRef(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__2___rarg___boxed), 3, 0);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid autoParam, argument must be a constant");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
x_17 = lean_ctor_get_uint8(x_13, sizeof(void*)*8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_Expr_getOptParamDefault_x3f(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = l_Lean_Expr_getAutoParamTactic_x3f(x_18);
lean_dec(x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_13, 3);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_List_isEmpty___rarg(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_35 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_fTypeHasOptAutoParams(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_st_ref_get(x_8, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_st_ref_get(x_2, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*8 + 1);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_1);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
lean_dec(x_4);
lean_dec(x_2);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
lean_dec(x_35);
x_49 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_35);
if (x_50 == 0)
{
return x_35;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_35, 0);
x_52 = lean_ctor_get(x_35, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_35);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_13);
x_54 = lean_ctor_get(x_21, 0);
lean_inc(x_54);
lean_dec(x_21);
if (lean_obj_tag(x_54) == 4)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_get(x_8, x_19);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_7, 0);
lean_inc(x_60);
x_61 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(x_59, x_60, x_55);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_1);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_58);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
lean_dec(x_61);
x_67 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__2___rarg(x_7, x_8, x_58);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_69);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_71);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_myMacro____x40_Init_Notation___hyg_22690____closed__3;
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Array_empty___closed__1;
x_77 = lean_array_push(x_76, x_75);
x_78 = lean_array_push(x_76, x_66);
x_79 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17217____closed__3;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_array_push(x_77, x_80);
x_82 = l_myMacro____x40_Init_Notation___hyg_22690____closed__2;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_84);
x_85 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_73);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_87 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_88);
return x_89;
}
else
{
uint8_t x_90; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_87);
if (x_90 == 0)
{
return x_87;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 0);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_87);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_84);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_85);
if (x_94 == 0)
{
return x_85;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_85, 0);
x_96 = lean_ctor_get(x_85, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_85);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_54);
lean_dec(x_1);
x_98 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__2;
x_99 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1(x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_18);
lean_dec(x_13);
x_100 = lean_ctor_get(x_20, 0);
lean_inc(x_100);
lean_dec(x_20);
x_101 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_100, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_102);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_16, 1);
lean_inc(x_104);
lean_dec(x_16);
x_105 = lean_ctor_get(x_13, 3);
lean_inc(x_105);
lean_dec(x_13);
x_106 = l_List_isEmpty___rarg(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_107 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_104);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_111 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_110);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_107, 1);
lean_inc(x_112);
lean_dec(x_107);
x_113 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_112);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_107);
if (x_114 == 0)
{
return x_107;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_107, 0);
x_116 = lean_ctor_get(x_107, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_107);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; 
lean_dec(x_1);
x_118 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_104);
lean_dec(x_4);
lean_dec(x_2);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_13);
x_119 = lean_ctor_get(x_12, 1);
lean_inc(x_119);
lean_dec(x_12);
x_120 = lean_ctor_get(x_14, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_14, 1);
lean_inc(x_121);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_120);
x_122 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(x_120, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_124 = lean_st_ref_get(x_8, x_123);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_st_ref_take(x_2, x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = !lean_is_exclusive(x_127);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_127, 2);
lean_dec(x_130);
lean_ctor_set(x_127, 2, x_121);
x_131 = lean_st_ref_set(x_2, x_127, x_128);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_133 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(x_120, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_134);
return x_135;
}
else
{
uint8_t x_136; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_133);
if (x_136 == 0)
{
return x_133;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_133, 0);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_133);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_140 = lean_ctor_get_uint8(x_127, sizeof(void*)*8);
x_141 = lean_ctor_get(x_127, 0);
x_142 = lean_ctor_get(x_127, 1);
x_143 = lean_ctor_get(x_127, 3);
x_144 = lean_ctor_get_uint8(x_127, sizeof(void*)*8 + 1);
x_145 = lean_ctor_get(x_127, 4);
x_146 = lean_ctor_get(x_127, 5);
x_147 = lean_ctor_get(x_127, 6);
x_148 = lean_ctor_get(x_127, 7);
x_149 = lean_ctor_get_uint8(x_127, sizeof(void*)*8 + 2);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_127);
x_150 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_150, 0, x_141);
lean_ctor_set(x_150, 1, x_142);
lean_ctor_set(x_150, 2, x_121);
lean_ctor_set(x_150, 3, x_143);
lean_ctor_set(x_150, 4, x_145);
lean_ctor_set(x_150, 5, x_146);
lean_ctor_set(x_150, 6, x_147);
lean_ctor_set(x_150, 7, x_148);
lean_ctor_set_uint8(x_150, sizeof(void*)*8, x_140);
lean_ctor_set_uint8(x_150, sizeof(void*)*8 + 1, x_144);
lean_ctor_set_uint8(x_150, sizeof(void*)*8 + 2, x_149);
x_151 = lean_st_ref_set(x_2, x_150, x_128);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_153 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(x_120, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_155 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_154);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_158 = x_153;
} else {
 lean_dec_ref(x_153);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_122);
if (x_160 == 0)
{
return x_122;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_122, 0);
x_162 = lean_ctor_get(x_122, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_122);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*8);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_18;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get_usize(x_8, 2);
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
lean_object* x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get_usize(x_9, 2);
x_24 = lean_ctor_get(x_9, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
lean_object* x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_10, 1);
x_27 = lean_ctor_get_usize(x_10, 2);
x_28 = lean_ctor_get(x_10, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_11, 1);
x_31 = lean_ctor_get_usize(x_11, 2);
x_32 = lean_ctor_get(x_11, 0);
lean_dec(x_32);
x_33 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_34 = lean_string_dec_eq(x_30, x_33);
lean_dec(x_30);
if (x_34 == 0)
{
lean_object* x_35; 
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_26);
lean_free_object(x_9);
lean_dec(x_22);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_dec(x_15);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_2);
x_35 = lean_apply_1(x_3, x_1);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_1, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_1, 0);
lean_dec(x_38);
x_39 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_40 = lean_string_dec_eq(x_26, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_33);
x_41 = lean_apply_1(x_3, x_1);
return x_41;
}
else
{
lean_object* x_42; uint8_t x_43; 
lean_dec(x_26);
x_42 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_43 = lean_string_dec_eq(x_22, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_33);
lean_ctor_set(x_10, 1, x_39);
x_44 = lean_apply_1(x_3, x_1);
return x_44;
}
else
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_22);
x_45 = l_myMacro____x40_Init_Notation___hyg_14458____closed__12;
x_46 = lean_string_dec_eq(x_18, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_33);
lean_ctor_set(x_10, 1, x_39);
lean_ctor_set(x_9, 1, x_42);
x_47 = lean_apply_1(x_3, x_1);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_1);
lean_free_object(x_11);
lean_free_object(x_10);
lean_free_object(x_9);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_48 = lean_box_usize(x_31);
x_49 = lean_box_usize(x_27);
x_50 = lean_box_usize(x_23);
x_51 = lean_box_usize(x_19);
x_52 = lean_apply_6(x_2, x_15, x_13, x_48, x_49, x_50, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
lean_dec(x_1);
x_53 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_54 = lean_string_dec_eq(x_26, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_33);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_5);
lean_ctor_set(x_55, 1, x_13);
x_56 = lean_apply_1(x_3, x_55);
return x_56;
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_dec(x_26);
x_57 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_58 = lean_string_dec_eq(x_22, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_33);
lean_ctor_set(x_10, 1, x_53);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_13);
x_60 = lean_apply_1(x_3, x_59);
return x_60;
}
else
{
lean_object* x_61; uint8_t x_62; 
lean_dec(x_22);
x_61 = l_myMacro____x40_Init_Notation___hyg_14458____closed__12;
x_62 = lean_string_dec_eq(x_18, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_33);
lean_ctor_set(x_10, 1, x_53);
lean_ctor_set(x_9, 1, x_57);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_5);
lean_ctor_set(x_63, 1, x_13);
x_64 = lean_apply_1(x_3, x_63);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_11);
lean_free_object(x_10);
lean_free_object(x_9);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_65 = lean_box_usize(x_31);
x_66 = lean_box_usize(x_27);
x_67 = lean_box_usize(x_23);
x_68 = lean_box_usize(x_19);
x_69 = lean_apply_6(x_2, x_15, x_13, x_65, x_66, x_67, x_68);
return x_69;
}
}
}
}
}
}
else
{
lean_object* x_70; size_t x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_11, 1);
x_71 = lean_ctor_get_usize(x_11, 2);
lean_inc(x_70);
lean_dec(x_11);
x_72 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_73 = lean_string_dec_eq(x_70, x_72);
lean_dec(x_70);
if (x_73 == 0)
{
lean_object* x_74; 
lean_free_object(x_10);
lean_dec(x_26);
lean_free_object(x_9);
lean_dec(x_22);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_dec(x_15);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_2);
x_74 = lean_apply_1(x_3, x_1);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_75 = x_1;
} else {
 lean_dec_ref(x_1);
 x_75 = lean_box(0);
}
x_76 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_77 = lean_string_dec_eq(x_26, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_2);
x_78 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_78, 0, x_12);
lean_ctor_set(x_78, 1, x_72);
lean_ctor_set_usize(x_78, 2, x_71);
lean_ctor_set(x_10, 0, x_78);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_75;
}
lean_ctor_set(x_79, 0, x_5);
lean_ctor_set(x_79, 1, x_13);
x_80 = lean_apply_1(x_3, x_79);
return x_80;
}
else
{
lean_object* x_81; uint8_t x_82; 
lean_dec(x_26);
x_81 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_82 = lean_string_dec_eq(x_22, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_2);
x_83 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_83, 0, x_12);
lean_ctor_set(x_83, 1, x_72);
lean_ctor_set_usize(x_83, 2, x_71);
lean_ctor_set(x_10, 1, x_76);
lean_ctor_set(x_10, 0, x_83);
if (lean_is_scalar(x_75)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_75;
}
lean_ctor_set(x_84, 0, x_5);
lean_ctor_set(x_84, 1, x_13);
x_85 = lean_apply_1(x_3, x_84);
return x_85;
}
else
{
lean_object* x_86; uint8_t x_87; 
lean_dec(x_22);
x_86 = l_myMacro____x40_Init_Notation___hyg_14458____closed__12;
x_87 = lean_string_dec_eq(x_18, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_2);
x_88 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_88, 0, x_12);
lean_ctor_set(x_88, 1, x_72);
lean_ctor_set_usize(x_88, 2, x_71);
lean_ctor_set(x_10, 1, x_76);
lean_ctor_set(x_10, 0, x_88);
lean_ctor_set(x_9, 1, x_81);
if (lean_is_scalar(x_75)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_75;
}
lean_ctor_set(x_89, 0, x_5);
lean_ctor_set(x_89, 1, x_13);
x_90 = lean_apply_1(x_3, x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_75);
lean_free_object(x_10);
lean_free_object(x_9);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_91 = lean_box_usize(x_71);
x_92 = lean_box_usize(x_27);
x_93 = lean_box_usize(x_23);
x_94 = lean_box_usize(x_19);
x_95 = lean_apply_6(x_2, x_15, x_13, x_91, x_92, x_93, x_94);
return x_95;
}
}
}
}
}
}
else
{
lean_object* x_96; size_t x_97; lean_object* x_98; size_t x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_96 = lean_ctor_get(x_10, 1);
x_97 = lean_ctor_get_usize(x_10, 2);
lean_inc(x_96);
lean_dec(x_10);
x_98 = lean_ctor_get(x_11, 1);
lean_inc(x_98);
x_99 = lean_ctor_get_usize(x_11, 2);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_100 = x_11;
} else {
 lean_dec_ref(x_11);
 x_100 = lean_box(0);
}
x_101 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_102 = lean_string_dec_eq(x_98, x_101);
lean_dec(x_98);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_100);
lean_dec(x_96);
lean_free_object(x_9);
lean_dec(x_22);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_dec(x_15);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_2);
x_103 = lean_apply_1(x_3, x_1);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_104 = x_1;
} else {
 lean_dec_ref(x_1);
 x_104 = lean_box(0);
}
x_105 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_106 = lean_string_dec_eq(x_96, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_2);
if (lean_is_scalar(x_100)) {
 x_107 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_107 = x_100;
}
lean_ctor_set(x_107, 0, x_12);
lean_ctor_set(x_107, 1, x_101);
lean_ctor_set_usize(x_107, 2, x_99);
x_108 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_96);
lean_ctor_set_usize(x_108, 2, x_97);
lean_ctor_set(x_9, 0, x_108);
if (lean_is_scalar(x_104)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_104;
}
lean_ctor_set(x_109, 0, x_5);
lean_ctor_set(x_109, 1, x_13);
x_110 = lean_apply_1(x_3, x_109);
return x_110;
}
else
{
lean_object* x_111; uint8_t x_112; 
lean_dec(x_96);
x_111 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_112 = lean_string_dec_eq(x_22, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_2);
if (lean_is_scalar(x_100)) {
 x_113 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_113 = x_100;
}
lean_ctor_set(x_113, 0, x_12);
lean_ctor_set(x_113, 1, x_101);
lean_ctor_set_usize(x_113, 2, x_99);
x_114 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_105);
lean_ctor_set_usize(x_114, 2, x_97);
lean_ctor_set(x_9, 0, x_114);
if (lean_is_scalar(x_104)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_104;
}
lean_ctor_set(x_115, 0, x_5);
lean_ctor_set(x_115, 1, x_13);
x_116 = lean_apply_1(x_3, x_115);
return x_116;
}
else
{
lean_object* x_117; uint8_t x_118; 
lean_dec(x_22);
x_117 = l_myMacro____x40_Init_Notation___hyg_14458____closed__12;
x_118 = lean_string_dec_eq(x_18, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_2);
if (lean_is_scalar(x_100)) {
 x_119 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_119 = x_100;
}
lean_ctor_set(x_119, 0, x_12);
lean_ctor_set(x_119, 1, x_101);
lean_ctor_set_usize(x_119, 2, x_99);
x_120 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_105);
lean_ctor_set_usize(x_120, 2, x_97);
lean_ctor_set(x_9, 1, x_111);
lean_ctor_set(x_9, 0, x_120);
if (lean_is_scalar(x_104)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_104;
}
lean_ctor_set(x_121, 0, x_5);
lean_ctor_set(x_121, 1, x_13);
x_122 = lean_apply_1(x_3, x_121);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_104);
lean_dec(x_100);
lean_free_object(x_9);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_123 = lean_box_usize(x_99);
x_124 = lean_box_usize(x_97);
x_125 = lean_box_usize(x_23);
x_126 = lean_box_usize(x_19);
x_127 = lean_apply_6(x_2, x_15, x_13, x_123, x_124, x_125, x_126);
return x_127;
}
}
}
}
}
}
else
{
lean_object* x_128; size_t x_129; lean_object* x_130; size_t x_131; lean_object* x_132; lean_object* x_133; size_t x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_128 = lean_ctor_get(x_9, 1);
x_129 = lean_ctor_get_usize(x_9, 2);
lean_inc(x_128);
lean_dec(x_9);
x_130 = lean_ctor_get(x_10, 1);
lean_inc(x_130);
x_131 = lean_ctor_get_usize(x_10, 2);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_132 = x_10;
} else {
 lean_dec_ref(x_10);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_11, 1);
lean_inc(x_133);
x_134 = lean_ctor_get_usize(x_11, 2);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_135 = x_11;
} else {
 lean_dec_ref(x_11);
 x_135 = lean_box(0);
}
x_136 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_137 = lean_string_dec_eq(x_133, x_136);
lean_dec(x_133);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_135);
lean_dec(x_132);
lean_dec(x_130);
lean_dec(x_128);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_dec(x_15);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_2);
x_138 = lean_apply_1(x_3, x_1);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_139 = x_1;
} else {
 lean_dec_ref(x_1);
 x_139 = lean_box(0);
}
x_140 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_141 = lean_string_dec_eq(x_130, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_2);
if (lean_is_scalar(x_135)) {
 x_142 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_142 = x_135;
}
lean_ctor_set(x_142, 0, x_12);
lean_ctor_set(x_142, 1, x_136);
lean_ctor_set_usize(x_142, 2, x_134);
if (lean_is_scalar(x_132)) {
 x_143 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_143 = x_132;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_130);
lean_ctor_set_usize(x_143, 2, x_131);
x_144 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_128);
lean_ctor_set_usize(x_144, 2, x_129);
lean_ctor_set(x_8, 0, x_144);
if (lean_is_scalar(x_139)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_139;
}
lean_ctor_set(x_145, 0, x_5);
lean_ctor_set(x_145, 1, x_13);
x_146 = lean_apply_1(x_3, x_145);
return x_146;
}
else
{
lean_object* x_147; uint8_t x_148; 
lean_dec(x_130);
x_147 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_148 = lean_string_dec_eq(x_128, x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_2);
if (lean_is_scalar(x_135)) {
 x_149 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_149 = x_135;
}
lean_ctor_set(x_149, 0, x_12);
lean_ctor_set(x_149, 1, x_136);
lean_ctor_set_usize(x_149, 2, x_134);
if (lean_is_scalar(x_132)) {
 x_150 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_150 = x_132;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_140);
lean_ctor_set_usize(x_150, 2, x_131);
x_151 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_128);
lean_ctor_set_usize(x_151, 2, x_129);
lean_ctor_set(x_8, 0, x_151);
if (lean_is_scalar(x_139)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_139;
}
lean_ctor_set(x_152, 0, x_5);
lean_ctor_set(x_152, 1, x_13);
x_153 = lean_apply_1(x_3, x_152);
return x_153;
}
else
{
lean_object* x_154; uint8_t x_155; 
lean_dec(x_128);
x_154 = l_myMacro____x40_Init_Notation___hyg_14458____closed__12;
x_155 = lean_string_dec_eq(x_18, x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_2);
if (lean_is_scalar(x_135)) {
 x_156 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_156 = x_135;
}
lean_ctor_set(x_156, 0, x_12);
lean_ctor_set(x_156, 1, x_136);
lean_ctor_set_usize(x_156, 2, x_134);
if (lean_is_scalar(x_132)) {
 x_157 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_157 = x_132;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_140);
lean_ctor_set_usize(x_157, 2, x_131);
x_158 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_147);
lean_ctor_set_usize(x_158, 2, x_129);
lean_ctor_set(x_8, 0, x_158);
if (lean_is_scalar(x_139)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_139;
}
lean_ctor_set(x_159, 0, x_5);
lean_ctor_set(x_159, 1, x_13);
x_160 = lean_apply_1(x_3, x_159);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_139);
lean_dec(x_135);
lean_dec(x_132);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_161 = lean_box_usize(x_134);
x_162 = lean_box_usize(x_131);
x_163 = lean_box_usize(x_129);
x_164 = lean_box_usize(x_19);
x_165 = lean_apply_6(x_2, x_15, x_13, x_161, x_162, x_163, x_164);
return x_165;
}
}
}
}
}
}
else
{
lean_object* x_166; size_t x_167; lean_object* x_168; size_t x_169; lean_object* x_170; lean_object* x_171; size_t x_172; lean_object* x_173; lean_object* x_174; size_t x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_166 = lean_ctor_get(x_8, 1);
x_167 = lean_ctor_get_usize(x_8, 2);
lean_inc(x_166);
lean_dec(x_8);
x_168 = lean_ctor_get(x_9, 1);
lean_inc(x_168);
x_169 = lean_ctor_get_usize(x_9, 2);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_170 = x_9;
} else {
 lean_dec_ref(x_9);
 x_170 = lean_box(0);
}
x_171 = lean_ctor_get(x_10, 1);
lean_inc(x_171);
x_172 = lean_ctor_get_usize(x_10, 2);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_173 = x_10;
} else {
 lean_dec_ref(x_10);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_11, 1);
lean_inc(x_174);
x_175 = lean_ctor_get_usize(x_11, 2);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_176 = x_11;
} else {
 lean_dec_ref(x_11);
 x_176 = lean_box(0);
}
x_177 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_178 = lean_string_dec_eq(x_174, x_177);
lean_dec(x_174);
if (x_178 == 0)
{
lean_object* x_179; 
lean_dec(x_176);
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_168);
lean_dec(x_166);
lean_free_object(x_7);
lean_dec(x_15);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_2);
x_179 = lean_apply_1(x_3, x_1);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_180 = x_1;
} else {
 lean_dec_ref(x_1);
 x_180 = lean_box(0);
}
x_181 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_182 = lean_string_dec_eq(x_171, x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_2);
if (lean_is_scalar(x_176)) {
 x_183 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_183 = x_176;
}
lean_ctor_set(x_183, 0, x_12);
lean_ctor_set(x_183, 1, x_177);
lean_ctor_set_usize(x_183, 2, x_175);
if (lean_is_scalar(x_173)) {
 x_184 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_184 = x_173;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_171);
lean_ctor_set_usize(x_184, 2, x_172);
if (lean_is_scalar(x_170)) {
 x_185 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_185 = x_170;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_168);
lean_ctor_set_usize(x_185, 2, x_169);
x_186 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_166);
lean_ctor_set_usize(x_186, 2, x_167);
lean_ctor_set(x_7, 0, x_186);
if (lean_is_scalar(x_180)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_180;
}
lean_ctor_set(x_187, 0, x_5);
lean_ctor_set(x_187, 1, x_13);
x_188 = lean_apply_1(x_3, x_187);
return x_188;
}
else
{
lean_object* x_189; uint8_t x_190; 
lean_dec(x_171);
x_189 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_190 = lean_string_dec_eq(x_168, x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_2);
if (lean_is_scalar(x_176)) {
 x_191 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_191 = x_176;
}
lean_ctor_set(x_191, 0, x_12);
lean_ctor_set(x_191, 1, x_177);
lean_ctor_set_usize(x_191, 2, x_175);
if (lean_is_scalar(x_173)) {
 x_192 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_192 = x_173;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_181);
lean_ctor_set_usize(x_192, 2, x_172);
if (lean_is_scalar(x_170)) {
 x_193 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_193 = x_170;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_168);
lean_ctor_set_usize(x_193, 2, x_169);
x_194 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_166);
lean_ctor_set_usize(x_194, 2, x_167);
lean_ctor_set(x_7, 0, x_194);
if (lean_is_scalar(x_180)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_180;
}
lean_ctor_set(x_195, 0, x_5);
lean_ctor_set(x_195, 1, x_13);
x_196 = lean_apply_1(x_3, x_195);
return x_196;
}
else
{
lean_object* x_197; uint8_t x_198; 
lean_dec(x_168);
x_197 = l_myMacro____x40_Init_Notation___hyg_14458____closed__12;
x_198 = lean_string_dec_eq(x_166, x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_2);
if (lean_is_scalar(x_176)) {
 x_199 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_199 = x_176;
}
lean_ctor_set(x_199, 0, x_12);
lean_ctor_set(x_199, 1, x_177);
lean_ctor_set_usize(x_199, 2, x_175);
if (lean_is_scalar(x_173)) {
 x_200 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_200 = x_173;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_181);
lean_ctor_set_usize(x_200, 2, x_172);
if (lean_is_scalar(x_170)) {
 x_201 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_201 = x_170;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_189);
lean_ctor_set_usize(x_201, 2, x_169);
x_202 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_166);
lean_ctor_set_usize(x_202, 2, x_167);
lean_ctor_set(x_7, 0, x_202);
if (lean_is_scalar(x_180)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_180;
}
lean_ctor_set(x_203, 0, x_5);
lean_ctor_set(x_203, 1, x_13);
x_204 = lean_apply_1(x_3, x_203);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_180);
lean_dec(x_176);
lean_dec(x_173);
lean_dec(x_170);
lean_dec(x_166);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_205 = lean_box_usize(x_175);
x_206 = lean_box_usize(x_172);
x_207 = lean_box_usize(x_169);
x_208 = lean_box_usize(x_167);
x_209 = lean_apply_6(x_2, x_15, x_13, x_205, x_206, x_207, x_208);
return x_209;
}
}
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; size_t x_212; lean_object* x_213; lean_object* x_214; size_t x_215; lean_object* x_216; lean_object* x_217; size_t x_218; lean_object* x_219; lean_object* x_220; size_t x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_210 = lean_ctor_get(x_7, 1);
lean_inc(x_210);
lean_dec(x_7);
x_211 = lean_ctor_get(x_8, 1);
lean_inc(x_211);
x_212 = lean_ctor_get_usize(x_8, 2);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_213 = x_8;
} else {
 lean_dec_ref(x_8);
 x_213 = lean_box(0);
}
x_214 = lean_ctor_get(x_9, 1);
lean_inc(x_214);
x_215 = lean_ctor_get_usize(x_9, 2);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_216 = x_9;
} else {
 lean_dec_ref(x_9);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_10, 1);
lean_inc(x_217);
x_218 = lean_ctor_get_usize(x_10, 2);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_219 = x_10;
} else {
 lean_dec_ref(x_10);
 x_219 = lean_box(0);
}
x_220 = lean_ctor_get(x_11, 1);
lean_inc(x_220);
x_221 = lean_ctor_get_usize(x_11, 2);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_222 = x_11;
} else {
 lean_dec_ref(x_11);
 x_222 = lean_box(0);
}
x_223 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_224 = lean_string_dec_eq(x_220, x_223);
lean_dec(x_220);
if (x_224 == 0)
{
lean_object* x_225; 
lean_dec(x_222);
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_2);
x_225 = lean_apply_1(x_3, x_1);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_226 = x_1;
} else {
 lean_dec_ref(x_1);
 x_226 = lean_box(0);
}
x_227 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_228 = lean_string_dec_eq(x_217, x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_2);
if (lean_is_scalar(x_222)) {
 x_229 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_229 = x_222;
}
lean_ctor_set(x_229, 0, x_12);
lean_ctor_set(x_229, 1, x_223);
lean_ctor_set_usize(x_229, 2, x_221);
if (lean_is_scalar(x_219)) {
 x_230 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_230 = x_219;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_217);
lean_ctor_set_usize(x_230, 2, x_218);
if (lean_is_scalar(x_216)) {
 x_231 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_231 = x_216;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_214);
lean_ctor_set_usize(x_231, 2, x_215);
if (lean_is_scalar(x_213)) {
 x_232 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_232 = x_213;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_211);
lean_ctor_set_usize(x_232, 2, x_212);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_210);
lean_ctor_set(x_5, 0, x_233);
if (lean_is_scalar(x_226)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_226;
}
lean_ctor_set(x_234, 0, x_5);
lean_ctor_set(x_234, 1, x_13);
x_235 = lean_apply_1(x_3, x_234);
return x_235;
}
else
{
lean_object* x_236; uint8_t x_237; 
lean_dec(x_217);
x_236 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_237 = lean_string_dec_eq(x_214, x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_2);
if (lean_is_scalar(x_222)) {
 x_238 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_238 = x_222;
}
lean_ctor_set(x_238, 0, x_12);
lean_ctor_set(x_238, 1, x_223);
lean_ctor_set_usize(x_238, 2, x_221);
if (lean_is_scalar(x_219)) {
 x_239 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_239 = x_219;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_227);
lean_ctor_set_usize(x_239, 2, x_218);
if (lean_is_scalar(x_216)) {
 x_240 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_240 = x_216;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_214);
lean_ctor_set_usize(x_240, 2, x_215);
if (lean_is_scalar(x_213)) {
 x_241 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_241 = x_213;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_211);
lean_ctor_set_usize(x_241, 2, x_212);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_210);
lean_ctor_set(x_5, 0, x_242);
if (lean_is_scalar(x_226)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_226;
}
lean_ctor_set(x_243, 0, x_5);
lean_ctor_set(x_243, 1, x_13);
x_244 = lean_apply_1(x_3, x_243);
return x_244;
}
else
{
lean_object* x_245; uint8_t x_246; 
lean_dec(x_214);
x_245 = l_myMacro____x40_Init_Notation___hyg_14458____closed__12;
x_246 = lean_string_dec_eq(x_211, x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_2);
if (lean_is_scalar(x_222)) {
 x_247 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_247 = x_222;
}
lean_ctor_set(x_247, 0, x_12);
lean_ctor_set(x_247, 1, x_223);
lean_ctor_set_usize(x_247, 2, x_221);
if (lean_is_scalar(x_219)) {
 x_248 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_248 = x_219;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_227);
lean_ctor_set_usize(x_248, 2, x_218);
if (lean_is_scalar(x_216)) {
 x_249 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_249 = x_216;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_236);
lean_ctor_set_usize(x_249, 2, x_215);
if (lean_is_scalar(x_213)) {
 x_250 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_250 = x_213;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_211);
lean_ctor_set_usize(x_250, 2, x_212);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_210);
lean_ctor_set(x_5, 0, x_251);
if (lean_is_scalar(x_226)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_226;
}
lean_ctor_set(x_252, 0, x_5);
lean_ctor_set(x_252, 1, x_13);
x_253 = lean_apply_1(x_3, x_252);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_226);
lean_dec(x_222);
lean_dec(x_219);
lean_dec(x_216);
lean_dec(x_213);
lean_dec(x_211);
lean_free_object(x_5);
lean_dec(x_3);
x_254 = lean_box_usize(x_221);
x_255 = lean_box_usize(x_218);
x_256 = lean_box_usize(x_215);
x_257 = lean_box_usize(x_212);
x_258 = lean_apply_6(x_2, x_210, x_13, x_254, x_255, x_256, x_257);
return x_258;
}
}
}
}
}
}
else
{
lean_object* x_259; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_free_object(x_5);
lean_dec(x_7);
lean_dec(x_2);
x_259 = lean_apply_1(x_3, x_1);
return x_259;
}
}
else
{
lean_object* x_260; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_free_object(x_5);
lean_dec(x_7);
lean_dec(x_2);
x_260 = lean_apply_1(x_3, x_1);
return x_260;
}
}
else
{
lean_object* x_261; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_free_object(x_5);
lean_dec(x_7);
lean_dec(x_2);
x_261 = lean_apply_1(x_3, x_1);
return x_261;
}
}
else
{
lean_object* x_262; 
lean_dec(x_9);
lean_dec(x_8);
lean_free_object(x_5);
lean_dec(x_7);
lean_dec(x_2);
x_262 = lean_apply_1(x_3, x_1);
return x_262;
}
}
else
{
lean_object* x_263; 
lean_dec(x_8);
lean_free_object(x_5);
lean_dec(x_7);
lean_dec(x_2);
x_263 = lean_apply_1(x_3, x_1);
return x_263;
}
}
else
{
lean_object* x_264; 
lean_free_object(x_5);
lean_dec(x_7);
lean_dec(x_2);
x_264 = lean_apply_1(x_3, x_1);
return x_264;
}
}
else
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_5, 0);
lean_inc(x_265);
lean_dec(x_5);
if (lean_obj_tag(x_265) == 1)
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
if (lean_obj_tag(x_266) == 1)
{
lean_object* x_267; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
if (lean_obj_tag(x_267) == 1)
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 1)
{
lean_object* x_269; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
if (lean_obj_tag(x_269) == 1)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; size_t x_275; lean_object* x_276; lean_object* x_277; size_t x_278; lean_object* x_279; lean_object* x_280; size_t x_281; lean_object* x_282; lean_object* x_283; size_t x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_271 = lean_ctor_get(x_1, 1);
lean_inc(x_271);
x_272 = lean_ctor_get(x_265, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_273 = x_265;
} else {
 lean_dec_ref(x_265);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_266, 1);
lean_inc(x_274);
x_275 = lean_ctor_get_usize(x_266, 2);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_276 = x_266;
} else {
 lean_dec_ref(x_266);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_267, 1);
lean_inc(x_277);
x_278 = lean_ctor_get_usize(x_267, 2);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_279 = x_267;
} else {
 lean_dec_ref(x_267);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get(x_268, 1);
lean_inc(x_280);
x_281 = lean_ctor_get_usize(x_268, 2);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_282 = x_268;
} else {
 lean_dec_ref(x_268);
 x_282 = lean_box(0);
}
x_283 = lean_ctor_get(x_269, 1);
lean_inc(x_283);
x_284 = lean_ctor_get_usize(x_269, 2);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_285 = x_269;
} else {
 lean_dec_ref(x_269);
 x_285 = lean_box(0);
}
x_286 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_287 = lean_string_dec_eq(x_283, x_286);
lean_dec(x_283);
if (x_287 == 0)
{
lean_object* x_288; 
lean_dec(x_285);
lean_dec(x_282);
lean_dec(x_280);
lean_dec(x_279);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_2);
x_288 = lean_apply_1(x_3, x_1);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_289 = x_1;
} else {
 lean_dec_ref(x_1);
 x_289 = lean_box(0);
}
x_290 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_291 = lean_string_dec_eq(x_280, x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_2);
if (lean_is_scalar(x_285)) {
 x_292 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_292 = x_285;
}
lean_ctor_set(x_292, 0, x_270);
lean_ctor_set(x_292, 1, x_286);
lean_ctor_set_usize(x_292, 2, x_284);
if (lean_is_scalar(x_282)) {
 x_293 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_293 = x_282;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_280);
lean_ctor_set_usize(x_293, 2, x_281);
if (lean_is_scalar(x_279)) {
 x_294 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_294 = x_279;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_277);
lean_ctor_set_usize(x_294, 2, x_278);
if (lean_is_scalar(x_276)) {
 x_295 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_295 = x_276;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_274);
lean_ctor_set_usize(x_295, 2, x_275);
if (lean_is_scalar(x_273)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_273;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_272);
x_297 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_297, 0, x_296);
if (lean_is_scalar(x_289)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_289;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_271);
x_299 = lean_apply_1(x_3, x_298);
return x_299;
}
else
{
lean_object* x_300; uint8_t x_301; 
lean_dec(x_280);
x_300 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_301 = lean_string_dec_eq(x_277, x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_2);
if (lean_is_scalar(x_285)) {
 x_302 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_302 = x_285;
}
lean_ctor_set(x_302, 0, x_270);
lean_ctor_set(x_302, 1, x_286);
lean_ctor_set_usize(x_302, 2, x_284);
if (lean_is_scalar(x_282)) {
 x_303 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_303 = x_282;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_290);
lean_ctor_set_usize(x_303, 2, x_281);
if (lean_is_scalar(x_279)) {
 x_304 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_304 = x_279;
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_277);
lean_ctor_set_usize(x_304, 2, x_278);
if (lean_is_scalar(x_276)) {
 x_305 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_305 = x_276;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_274);
lean_ctor_set_usize(x_305, 2, x_275);
if (lean_is_scalar(x_273)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_273;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_272);
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_306);
if (lean_is_scalar(x_289)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_289;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_271);
x_309 = lean_apply_1(x_3, x_308);
return x_309;
}
else
{
lean_object* x_310; uint8_t x_311; 
lean_dec(x_277);
x_310 = l_myMacro____x40_Init_Notation___hyg_14458____closed__12;
x_311 = lean_string_dec_eq(x_274, x_310);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_2);
if (lean_is_scalar(x_285)) {
 x_312 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_312 = x_285;
}
lean_ctor_set(x_312, 0, x_270);
lean_ctor_set(x_312, 1, x_286);
lean_ctor_set_usize(x_312, 2, x_284);
if (lean_is_scalar(x_282)) {
 x_313 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_313 = x_282;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_290);
lean_ctor_set_usize(x_313, 2, x_281);
if (lean_is_scalar(x_279)) {
 x_314 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_314 = x_279;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_300);
lean_ctor_set_usize(x_314, 2, x_278);
if (lean_is_scalar(x_276)) {
 x_315 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_315 = x_276;
}
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_274);
lean_ctor_set_usize(x_315, 2, x_275);
if (lean_is_scalar(x_273)) {
 x_316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_316 = x_273;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_272);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_316);
if (lean_is_scalar(x_289)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_289;
}
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_271);
x_319 = lean_apply_1(x_3, x_318);
return x_319;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_289);
lean_dec(x_285);
lean_dec(x_282);
lean_dec(x_279);
lean_dec(x_276);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_3);
x_320 = lean_box_usize(x_284);
x_321 = lean_box_usize(x_281);
x_322 = lean_box_usize(x_278);
x_323 = lean_box_usize(x_275);
x_324 = lean_apply_6(x_2, x_272, x_271, x_320, x_321, x_322, x_323);
return x_324;
}
}
}
}
}
else
{
lean_object* x_325; 
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_2);
x_325 = lean_apply_1(x_3, x_1);
return x_325;
}
}
else
{
lean_object* x_326; 
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_2);
x_326 = lean_apply_1(x_3, x_1);
return x_326;
}
}
else
{
lean_object* x_327; 
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_2);
x_327 = lean_apply_1(x_3, x_1);
return x_327;
}
}
else
{
lean_object* x_328; 
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_2);
x_328 = lean_apply_1(x_3, x_1);
return x_328;
}
}
else
{
lean_object* x_329; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_2);
x_329 = lean_apply_1(x_3, x_1);
return x_329;
}
}
else
{
lean_object* x_330; 
lean_dec(x_265);
lean_dec(x_2);
x_330 = lean_apply_1(x_3, x_1);
return x_330;
}
}
}
else
{
lean_object* x_331; 
lean_dec(x_5);
lean_dec(x_2);
x_331 = lean_apply_1(x_3, x_1);
return x_331;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = 0;
x_17 = lean_box(x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_11, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_dec(x_27);
x_35 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_36 = lean_string_dec_eq(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
uint8_t x_37; lean_object* x_38; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_37 = 0;
x_38 = lean_box(x_37);
lean_ctor_set(x_11, 0, x_38);
return x_11;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_40 = lean_string_dec_eq(x_33, x_39);
lean_dec(x_33);
if (x_40 == 0)
{
uint8_t x_41; lean_object* x_42; 
lean_dec(x_32);
lean_dec(x_31);
x_41 = 0;
x_42 = lean_box(x_41);
lean_ctor_set(x_11, 0, x_42);
return x_11;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_44 = lean_string_dec_eq(x_32, x_43);
lean_dec(x_32);
if (x_44 == 0)
{
uint8_t x_45; lean_object* x_46; 
lean_dec(x_31);
x_45 = 0;
x_46 = lean_box(x_45);
lean_ctor_set(x_11, 0, x_46);
return x_11;
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = l_myMacro____x40_Init_Notation___hyg_14458____closed__12;
x_48 = lean_string_dec_eq(x_31, x_47);
lean_dec(x_31);
if (x_48 == 0)
{
uint8_t x_49; lean_object* x_50; 
x_49 = 0;
x_50 = lean_box(x_49);
lean_ctor_set(x_11, 0, x_50);
return x_11;
}
else
{
uint8_t x_51; lean_object* x_52; 
x_51 = 1;
x_52 = lean_box(x_51);
lean_ctor_set(x_11, 0, x_52);
return x_11;
}
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_53 = lean_ctor_get(x_11, 1);
lean_inc(x_53);
lean_dec(x_11);
x_54 = lean_ctor_get(x_24, 1);
lean_inc(x_54);
lean_dec(x_24);
x_55 = lean_ctor_get(x_25, 1);
lean_inc(x_55);
lean_dec(x_25);
x_56 = lean_ctor_get(x_26, 1);
lean_inc(x_56);
lean_dec(x_26);
x_57 = lean_ctor_get(x_27, 1);
lean_inc(x_57);
lean_dec(x_27);
x_58 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_59 = lean_string_dec_eq(x_57, x_58);
lean_dec(x_57);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
x_60 = 0;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_53);
return x_62;
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_64 = lean_string_dec_eq(x_56, x_63);
lean_dec(x_56);
if (x_64 == 0)
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_55);
lean_dec(x_54);
x_65 = 0;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_53);
return x_67;
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_69 = lean_string_dec_eq(x_55, x_68);
lean_dec(x_55);
if (x_69 == 0)
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_54);
x_70 = 0;
x_71 = lean_box(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_53);
return x_72;
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = l_myMacro____x40_Init_Notation___hyg_14458____closed__12;
x_74 = lean_string_dec_eq(x_54, x_73);
lean_dec(x_54);
if (x_74 == 0)
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_75 = 0;
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_53);
return x_77;
}
else
{
uint8_t x_78; lean_object* x_79; lean_object* x_80; 
x_78 = 1;
x_79 = lean_box(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_53);
return x_80;
}
}
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
x_81 = !lean_is_exclusive(x_11);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_11, 0);
lean_dec(x_82);
x_83 = 0;
x_84 = lean_box(x_83);
lean_ctor_set(x_11, 0, x_84);
return x_11;
}
else
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_11, 1);
lean_inc(x_85);
lean_dec(x_11);
x_86 = 0;
x_87 = lean_box(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
x_89 = !lean_is_exclusive(x_11);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_11, 0);
lean_dec(x_90);
x_91 = 0;
x_92 = lean_box(x_91);
lean_ctor_set(x_11, 0, x_92);
return x_11;
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_11, 1);
lean_inc(x_93);
lean_dec(x_11);
x_94 = 0;
x_95 = lean_box(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
x_97 = !lean_is_exclusive(x_11);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_11, 0);
lean_dec(x_98);
x_99 = 0;
x_100 = lean_box(x_99);
lean_ctor_set(x_11, 0, x_100);
return x_11;
}
else
{
lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_11, 1);
lean_inc(x_101);
lean_dec(x_11);
x_102 = 0;
x_103 = lean_box(x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_25);
lean_dec(x_24);
x_105 = !lean_is_exclusive(x_11);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_11, 0);
lean_dec(x_106);
x_107 = 0;
x_108 = lean_box(x_107);
lean_ctor_set(x_11, 0, x_108);
return x_11;
}
else
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_11, 1);
lean_inc(x_109);
lean_dec(x_11);
x_110 = 0;
x_111 = lean_box(x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_24);
x_113 = !lean_is_exclusive(x_11);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_11, 0);
lean_dec(x_114);
x_115 = 0;
x_116 = lean_box(x_115);
lean_ctor_set(x_11, 0, x_116);
return x_11;
}
else
{
lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_11, 1);
lean_inc(x_117);
lean_dec(x_11);
x_118 = 0;
x_119 = lean_box(x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_23);
x_121 = !lean_is_exclusive(x_11);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_11, 0);
lean_dec(x_122);
x_123 = 0;
x_124 = lean_box(x_123);
lean_ctor_set(x_11, 0, x_124);
return x_11;
}
else
{
lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_11, 1);
lean_inc(x_125);
lean_dec(x_11);
x_126 = 0;
x_127 = lean_box(x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_22);
x_129 = !lean_is_exclusive(x_11);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_11, 0);
lean_dec(x_130);
x_131 = 0;
x_132 = lean_box(x_131);
lean_ctor_set(x_11, 0, x_132);
return x_11;
}
else
{
lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_11, 1);
lean_inc(x_133);
lean_dec(x_11);
x_134 = 0;
x_135 = lean_box(x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
return x_136;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processInstImplicitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*8);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = 1;
x_21 = lean_box(0);
lean_inc(x_5);
x_22 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_19, x_20, x_21, x_5, x_6, x_7, x_8, x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Expr_mvarId_x21(x_23);
x_26 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_dec(x_12);
x_32 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = 1;
x_43 = lean_box(0);
lean_inc(x_5);
x_44 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_41, x_42, x_43, x_5, x_6, x_7, x_8, x_40);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_st_ref_get(x_8, x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_take(x_2, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_50, 2);
x_54 = l_List_tail_x21___rarg(x_53);
lean_dec(x_53);
lean_ctor_set(x_50, 2, x_54);
x_55 = lean_st_ref_set(x_2, x_50, x_51);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Expr_mvarId_x21(x_45);
x_58 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_59);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_61);
return x_62;
}
else
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_63 = lean_ctor_get_uint8(x_50, sizeof(void*)*8);
x_64 = lean_ctor_get(x_50, 0);
x_65 = lean_ctor_get(x_50, 1);
x_66 = lean_ctor_get(x_50, 2);
x_67 = lean_ctor_get(x_50, 3);
x_68 = lean_ctor_get_uint8(x_50, sizeof(void*)*8 + 1);
x_69 = lean_ctor_get(x_50, 4);
x_70 = lean_ctor_get(x_50, 5);
x_71 = lean_ctor_get(x_50, 6);
x_72 = lean_ctor_get(x_50, 7);
x_73 = lean_ctor_get_uint8(x_50, sizeof(void*)*8 + 2);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_50);
x_74 = l_List_tail_x21___rarg(x_66);
lean_dec(x_66);
x_75 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_65);
lean_ctor_set(x_75, 2, x_74);
lean_ctor_set(x_75, 3, x_67);
lean_ctor_set(x_75, 4, x_69);
lean_ctor_set(x_75, 5, x_70);
lean_ctor_set(x_75, 6, x_71);
lean_ctor_set(x_75, 7, x_72);
lean_ctor_set_uint8(x_75, sizeof(void*)*8, x_63);
lean_ctor_set_uint8(x_75, sizeof(void*)*8 + 1, x_68);
lean_ctor_set_uint8(x_75, sizeof(void*)*8 + 2, x_73);
x_76 = lean_st_ref_set(x_2, x_75, x_51);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Lean_Expr_mvarId_x21(x_45);
x_79 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(x_78, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_77);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_80);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_82);
return x_83;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
x_15 = l_List_isEmpty___rarg(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; 
lean_dec(x_13);
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_13, 3);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_List_isEmpty___rarg(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; 
x_20 = 1;
x_21 = lean_box(x_20);
lean_ctor_set(x_11, 0, x_21);
return x_11;
}
else
{
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
x_23 = lean_box(x_22);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
x_27 = l_List_isEmpty___rarg(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_24, 3);
lean_inc(x_31);
lean_dec(x_24);
x_32 = l_List_isEmpty___rarg(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_25);
return x_35;
}
else
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_36 = 0;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_25);
return x_38;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(x_1);
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 3:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(x_1);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_ElabAppArgs_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ElabAppArgs_main), 8, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_1, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Expr_isForall(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_14);
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_3);
lean_dec(x_1);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_8 = x_24;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = l_Lean_Expr_bindingName_x21(x_14);
x_31 = l_Lean_Expr_bindingInfo_x21(x_14);
lean_dec(x_14);
x_32 = lean_st_ref_get(x_7, x_15);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_get(x_1, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_30);
x_37 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1___boxed), 2, 1);
lean_closure_set(x_37, 0, x_30);
x_38 = lean_ctor_get(x_35, 3);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_List_find_x3f___rarg(x_37, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_30);
x_40 = lean_box(x_31);
switch (lean_obj_tag(x_40)) {
case 1:
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Elab_Term_ElabAppArgs_main___closed__1;
x_42 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg(x_41, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
return x_42;
}
case 3:
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_Elab_Term_ElabAppArgs_main___closed__1;
x_44 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processInstImplicitArg(x_43, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
return x_44;
}
default: 
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_40);
x_45 = l_Lean_Elab_Term_ElabAppArgs_main___closed__1;
x_46 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg(x_45, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_ctor_get(x_47, 2);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_48);
x_49 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(x_48, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg(x_30, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
lean_dec(x_30);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_53 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(x_48, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_8 = x_54;
goto _start;
}
else
{
uint8_t x_56; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_48);
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_49);
if (x_60 == 0)
{
return x_49;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_49, 0);
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_49);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_13);
if (x_64 == 0)
{
return x_13;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_13, 0);
x_66 = lean_ctor_get(x_13, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_13);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_propagateExpectedTypeFor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_propagateExpectedTypeFor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_propagateExpectedTypeFor_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_propagateExpectedTypeFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_getAppFn(x_1);
x_10 = l_Lean_Expr_constName_x3f(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_st_ref_get(x_7, x_8);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_Term_elabWithoutExpectedTypeAttr;
x_20 = l_Lean_TagAttribute_hasTag(x_19, x_18, x_14);
lean_dec(x_14);
lean_dec(x_18);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
uint8_t x_23; lean_object* x_24; 
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Term_elabWithoutExpectedTypeAttr;
x_29 = l_Lean_TagAttribute_hasTag(x_28, x_27, x_14);
lean_dec(x_14);
lean_dec(x_27);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 1;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_propagateExpectedTypeFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_propagateExpectedTypeFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Elab_Term_elabAppArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_propagateExpectedTypeFor(x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_to_list(lean_box(0), x_2);
x_20 = lean_array_to_list(lean_box(0), x_3);
x_21 = l_Array_empty___closed__1;
x_22 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_5);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_20);
lean_ctor_set(x_22, 4, x_7);
lean_ctor_set(x_22, 5, x_21);
lean_ctor_set(x_22, 6, x_21);
lean_ctor_set(x_22, 7, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*8, x_4);
lean_ctor_set_uint8(x_22, sizeof(void*)*8 + 1, x_6);
x_23 = lean_unbox(x_17);
lean_dec(x_17);
lean_ctor_set_uint8(x_22, sizeof(void*)*8 + 2, x_23);
x_24 = lean_st_ref_get(x_14, x_18);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_mk_ref(x_22, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_14);
lean_inc(x_27);
x_29 = l_Lean_Elab_Term_ElabAppArgs_main(x_27, x_9, x_10, x_11, x_12, x_13, x_14, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_st_ref_get(x_14, x_31);
lean_dec(x_14);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_get(x_27, x_33);
lean_dec(x_27);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_30);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_27);
lean_dec(x_14);
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_29);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAppArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("args");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAppArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1;
x_2 = l_Lean_Elab_Term_elabAppArgs___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAppArgs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_elabAppArgs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabAppArgs___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_elabAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_14 = l_Lean_Meta_inferType(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_Meta_instantiateMVars(x_15, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_42; lean_object* x_43; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_62 = lean_st_ref_get(x_12, x_19);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 3);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get_uint8(x_64, sizeof(void*)*1);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = 0;
x_42 = x_67;
x_43 = x_66;
goto block_61;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_dec(x_62);
x_69 = l_Lean_Elab_Term_elabAppArgs___closed__2;
x_70 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_69, x_7, x_8, x_9, x_10, x_11, x_12, x_68);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_unbox(x_71);
lean_dec(x_71);
x_42 = x_73;
x_43 = x_72;
goto block_61;
}
block_41:
{
uint8_t x_21; 
x_21 = l_Array_isEmpty___rarg(x_2);
if (x_21 == 0)
{
lean_object* x_22; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_18);
x_22 = l_Lean_Elab_Term_tryPostponeIfMVar(x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Term_elabAppArgs___lambda__1(x_1, x_3, x_2, x_5, x_18, x_6, x_4, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
lean_dec(x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = l_Array_isEmpty___rarg(x_3);
if (x_30 == 0)
{
lean_object* x_31; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_18);
x_31 = l_Lean_Elab_Term_tryPostponeIfMVar(x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_Term_elabAppArgs___lambda__1(x_1, x_3, x_2, x_5, x_18, x_6, x_4, x_32, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_32);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
x_40 = l_Lean_Elab_Term_elabAppArgs___lambda__1(x_1, x_3, x_2, x_5, x_18, x_6, x_4, x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
return x_40;
}
}
}
block_61:
{
if (x_42 == 0)
{
x_20 = x_43;
goto block_41;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_44 = l_Std_fmt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__2(x_5);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_Elab_Term_elabAppArgs___closed__4;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__6;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_1);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_1);
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Meta_mkHasTypeButIsExpectedMsg___closed__3;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_18);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_18);
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_KernelException_toMessageData___closed__15;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_Term_elabAppArgs___closed__2;
x_59 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_58, x_57, x_7, x_8, x_9, x_10, x_11, x_12, x_43);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_20 = x_60;
goto block_41;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_17);
if (x_74 == 0)
{
return x_17;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_17, 0);
x_76 = lean_ctor_get(x_17, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_17);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_14);
if (x_78 == 0)
{
return x_14;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_14, 0);
x_80 = lean_ctor_get(x_14, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_14);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabAppArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Lean_Elab_Term_elabAppArgs___lambda__1(x_1, x_2, x_3, x_16, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
return x_18;
}
}
lean_object* l_Lean_Elab_Term_elabAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Lean_Elab_Term_elabAppArgs(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = l_Lean_KernelException_toMessageData___closed__15;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_indentExpr(x_1);
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_indentExpr(x_2);
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
x_21 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___spec__1___rarg(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_6 < x_5;
if (x_8 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_uget(x_4, x_6);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_1, x_9, x_2);
if (lean_obj_tag(x_10) == 0)
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = x_6 + x_11;
{
size_t _tmp_5 = x_12;
lean_object* _tmp_6 = x_3;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_3);
x_4 = l_Lean_Name_append(x_2, x_3);
lean_inc(x_4);
lean_inc(x_1);
x_5 = lean_environment_find(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = l_Lean_mkPrivateName(x_1, x_4);
lean_inc(x_6);
lean_inc(x_1);
x_7 = lean_environment_find(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_isStructureLike(x_1, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
x_10 = l_Lean_getParentStructures(x_1, x_2);
x_11 = lean_box(0);
x_12 = lean_array_get_size(x_10);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = l_Array_findSomeM_x3f___rarg___closed__1;
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1(x_1, x_3, x_15, x_10, x_13, x_14, x_15);
lean_dec(x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
return x_11;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_7, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_7, 0, x_23);
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_6);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_5, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_4);
lean_ctor_set(x_5, 0, x_28);
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_5);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_4);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
x_9 = lean_apply_2(x_8, x_1, x_2);
return x_9;
}
case 1:
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_6);
x_11 = lean_apply_2(x_8, x_10, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_apply_3(x_6, x_12, x_13, x_14);
return x_15;
}
}
default: 
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_6);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_apply_3(x_7, x_1, x_16, x_17);
return x_18;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_3(x_3, x_19, x_20, x_21);
return x_22;
}
case 1:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
lean_dec(x_3);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_apply_4(x_4, x_23, x_24, x_25, x_26);
return x_27;
}
default: 
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_apply_3(x_5, x_28, x_29, x_30);
return x_31;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__3___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_box(0);
x_10 = l_Lean_mkConst(x_1, x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_throwUnknownConstant___rarg___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_KernelException_toMessageData___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___spec__2(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure has only ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" field(s)");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_getStructureFields(x_1, x_2);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_3, x_15);
x_17 = lean_array_get_size(x_14);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_4, x_5, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_2);
x_26 = l_Lean_isStructure(x_1, x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_13);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_array_fget(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
lean_inc(x_2);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
return x_31;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_st_ref_get(x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
lean_inc(x_16);
x_17 = l_Lean_isStructureLike(x_16, x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_1);
x_18 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__3;
x_19 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1(x_16, x_1, x_2, x_3, x_4, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_25;
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, index must be greater than 0");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', the environment does not contain '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("getOp");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation because environment does not contain '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Expr_getAppFn(x_2);
x_12 = l_Lean_Expr_constName_x3f(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3;
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_14;
}
case 1:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_dec(x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3;
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_Expr_isConst(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
x_20 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3;
x_21 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_22 = l_Lean_Expr_constName_x21(x_1);
lean_dec(x_1);
x_23 = l_Lean_Name_append(x_22, x_18);
lean_dec(x_22);
x_24 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___spec__1(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_24;
}
}
}
default: 
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__6;
x_26 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_26;
}
}
}
else
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
lean_dec(x_12);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_eq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2(x_27, x_28, x_1, x_2, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_28);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_1);
x_33 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__8;
x_34 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
case 1:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_12, 0);
lean_inc(x_39);
lean_dec(x_12);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
lean_dec(x_3);
x_41 = lean_st_ref_get(x_9, x_10);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_39);
lean_inc(x_45);
x_46 = l_Lean_isStructure(x_45, x_39);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_inc(x_40);
lean_inc(x_39);
x_47 = lean_name_mk_string(x_39, x_40);
x_48 = lean_ctor_get(x_8, 4);
x_49 = lean_box(0);
lean_inc(x_47);
x_50 = l_Lean_Name_replacePrefix(x_47, x_48, x_49);
x_51 = lean_ctor_get(x_6, 1);
lean_inc(x_51);
x_52 = lean_local_ctx_find_from_user_name(x_51, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_inc(x_40);
x_53 = lean_name_mk_string(x_49, x_40);
lean_inc(x_39);
x_54 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_45, x_39, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_free_object(x_41);
lean_dec(x_39);
x_55 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_56 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_60, 0, x_47);
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_KernelException_toMessageData___closed__3;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_63, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
lean_dec(x_6);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_47);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_54, 0);
lean_inc(x_65);
lean_dec(x_54);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_39);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_41, 0, x_68);
return x_41;
}
}
else
{
lean_object* x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_52, 0);
lean_inc(x_69);
lean_dec(x_52);
x_70 = l_Lean_LocalDecl_binderInfo(x_69);
x_71 = 4;
x_72 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206_(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_69);
lean_inc(x_40);
x_73 = lean_name_mk_string(x_49, x_40);
lean_inc(x_39);
x_74 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_45, x_39, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_free_object(x_41);
lean_dec(x_39);
x_75 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_76 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_80, 0, x_47);
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_KernelException_toMessageData___closed__3;
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_83, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
lean_dec(x_6);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_47);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_ctor_get(x_74, 0);
lean_inc(x_85);
lean_dec(x_74);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_39);
lean_ctor_set(x_88, 2, x_87);
lean_ctor_set(x_41, 0, x_88);
return x_41;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_45);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_89 = l_Lean_LocalDecl_toExpr(x_69);
lean_dec(x_69);
x_90 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_90, 0, x_39);
lean_ctor_set(x_90, 1, x_47);
lean_ctor_set(x_90, 2, x_89);
lean_ctor_set(x_41, 0, x_90);
return x_41;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_box(0);
lean_inc(x_40);
x_92 = lean_name_mk_string(x_91, x_40);
lean_inc(x_39);
lean_inc(x_45);
x_93 = l_Lean_findField_x3f(x_45, x_39, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_inc(x_40);
lean_inc(x_39);
x_94 = lean_name_mk_string(x_39, x_40);
x_95 = lean_ctor_get(x_8, 4);
lean_inc(x_94);
x_96 = l_Lean_Name_replacePrefix(x_94, x_95, x_91);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
x_98 = lean_local_ctx_find_from_user_name(x_97, x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
lean_inc(x_39);
x_99 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_45, x_39, x_92);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_free_object(x_41);
lean_dec(x_39);
x_100 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_101 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10;
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12;
x_104 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_105, 0, x_94);
x_106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_KernelException_toMessageData___closed__3;
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_108, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
lean_dec(x_6);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_94);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_110 = lean_ctor_get(x_99, 0);
lean_inc(x_110);
lean_dec(x_99);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_39);
lean_ctor_set(x_113, 2, x_112);
lean_ctor_set(x_41, 0, x_113);
return x_41;
}
}
else
{
lean_object* x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_98, 0);
lean_inc(x_114);
lean_dec(x_98);
x_115 = l_Lean_LocalDecl_binderInfo(x_114);
x_116 = 4;
x_117 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206_(x_115, x_116);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_114);
lean_inc(x_39);
x_118 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_45, x_39, x_92);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_free_object(x_41);
lean_dec(x_39);
x_119 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_120 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10;
x_121 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12;
x_123 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_124, 0, x_94);
x_125 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_KernelException_toMessageData___closed__3;
x_127 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_127, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
lean_dec(x_6);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_94);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_ctor_get(x_118, 0);
lean_inc(x_129);
lean_dec(x_118);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_39);
lean_ctor_set(x_132, 2, x_131);
lean_ctor_set(x_41, 0, x_132);
return x_41;
}
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_92);
lean_dec(x_45);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_133 = l_Lean_LocalDecl_toExpr(x_114);
lean_dec(x_114);
x_134 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_134, 0, x_39);
lean_ctor_set(x_134, 1, x_94);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_41, 0, x_134);
return x_41;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_45);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_135 = lean_ctor_get(x_93, 0);
lean_inc(x_135);
lean_dec(x_93);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_39);
lean_ctor_set(x_136, 2, x_92);
lean_ctor_set(x_41, 0, x_136);
return x_41;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_137 = lean_ctor_get(x_41, 0);
x_138 = lean_ctor_get(x_41, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_41);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
lean_inc(x_39);
lean_inc(x_139);
x_140 = l_Lean_isStructure(x_139, x_39);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_inc(x_40);
lean_inc(x_39);
x_141 = lean_name_mk_string(x_39, x_40);
x_142 = lean_ctor_get(x_8, 4);
x_143 = lean_box(0);
lean_inc(x_141);
x_144 = l_Lean_Name_replacePrefix(x_141, x_142, x_143);
x_145 = lean_ctor_get(x_6, 1);
lean_inc(x_145);
x_146 = lean_local_ctx_find_from_user_name(x_145, x_144);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_inc(x_40);
x_147 = lean_name_mk_string(x_143, x_40);
lean_inc(x_39);
x_148 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_139, x_39, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_39);
x_149 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_150 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10;
x_151 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
x_152 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12;
x_153 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_154, 0, x_141);
x_155 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_KernelException_toMessageData___closed__3;
x_157 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_157, x_4, x_5, x_6, x_7, x_8, x_9, x_138);
lean_dec(x_6);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_141);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_ctor_get(x_148, 0);
lean_inc(x_159);
lean_dec(x_148);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_39);
lean_ctor_set(x_162, 2, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_138);
return x_163;
}
}
else
{
lean_object* x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; 
x_164 = lean_ctor_get(x_146, 0);
lean_inc(x_164);
lean_dec(x_146);
x_165 = l_Lean_LocalDecl_binderInfo(x_164);
x_166 = 4;
x_167 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206_(x_165, x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_164);
lean_inc(x_40);
x_168 = lean_name_mk_string(x_143, x_40);
lean_inc(x_39);
x_169 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_139, x_39, x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_39);
x_170 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_171 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10;
x_172 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
x_173 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12;
x_174 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_175, 0, x_141);
x_176 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Lean_KernelException_toMessageData___closed__3;
x_178 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_178, x_4, x_5, x_6, x_7, x_8, x_9, x_138);
lean_dec(x_6);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_141);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_180 = lean_ctor_get(x_169, 0);
lean_inc(x_180);
lean_dec(x_169);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_39);
lean_ctor_set(x_183, 2, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_138);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_139);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_185 = l_Lean_LocalDecl_toExpr(x_164);
lean_dec(x_164);
x_186 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_186, 0, x_39);
lean_ctor_set(x_186, 1, x_141);
lean_ctor_set(x_186, 2, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_138);
return x_187;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_box(0);
lean_inc(x_40);
x_189 = lean_name_mk_string(x_188, x_40);
lean_inc(x_39);
lean_inc(x_139);
x_190 = l_Lean_findField_x3f(x_139, x_39, x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_inc(x_40);
lean_inc(x_39);
x_191 = lean_name_mk_string(x_39, x_40);
x_192 = lean_ctor_get(x_8, 4);
lean_inc(x_191);
x_193 = l_Lean_Name_replacePrefix(x_191, x_192, x_188);
x_194 = lean_ctor_get(x_6, 1);
lean_inc(x_194);
x_195 = lean_local_ctx_find_from_user_name(x_194, x_193);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
lean_inc(x_39);
x_196 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_139, x_39, x_189);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_39);
x_197 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_198 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10;
x_199 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12;
x_201 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_202, 0, x_191);
x_203 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Lean_KernelException_toMessageData___closed__3;
x_205 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_205, x_4, x_5, x_6, x_7, x_8, x_9, x_138);
lean_dec(x_6);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_191);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_207 = lean_ctor_get(x_196, 0);
lean_inc(x_207);
lean_dec(x_196);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_39);
lean_ctor_set(x_210, 2, x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_138);
return x_211;
}
}
else
{
lean_object* x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; 
x_212 = lean_ctor_get(x_195, 0);
lean_inc(x_212);
lean_dec(x_195);
x_213 = l_Lean_LocalDecl_binderInfo(x_212);
x_214 = 4;
x_215 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_206_(x_213, x_214);
if (x_215 == 0)
{
lean_object* x_216; 
lean_dec(x_212);
lean_inc(x_39);
x_216 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_139, x_39, x_189);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_39);
x_217 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_218 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10;
x_219 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
x_220 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12;
x_221 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_222, 0, x_191);
x_223 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
x_224 = l_Lean_KernelException_toMessageData___closed__3;
x_225 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
x_226 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_225, x_4, x_5, x_6, x_7, x_8, x_9, x_138);
lean_dec(x_6);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_191);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_227 = lean_ctor_get(x_216, 0);
lean_inc(x_227);
lean_dec(x_216);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_39);
lean_ctor_set(x_230, 2, x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_138);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_189);
lean_dec(x_139);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_232 = l_Lean_LocalDecl_toExpr(x_212);
lean_dec(x_212);
x_233 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_233, 0, x_39);
lean_ctor_set(x_233, 1, x_191);
lean_ctor_set(x_233, 2, x_232);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_138);
return x_234;
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_139);
lean_dec(x_40);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_235 = lean_ctor_get(x_190, 0);
lean_inc(x_235);
lean_dec(x_190);
x_236 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_39);
lean_ctor_set(x_236, 2, x_189);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_138);
return x_237;
}
}
}
}
default: 
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_238 = lean_ctor_get(x_12, 0);
lean_inc(x_238);
lean_dec(x_12);
x_239 = lean_ctor_get(x_3, 1);
lean_inc(x_239);
lean_dec(x_3);
x_240 = lean_st_ref_get(x_9, x_10);
x_241 = !lean_is_exclusive(x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_242 = lean_ctor_get(x_240, 0);
x_243 = lean_ctor_get(x_240, 1);
x_244 = lean_ctor_get(x_242, 0);
lean_inc(x_244);
lean_dec(x_242);
x_245 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13;
x_246 = lean_name_mk_string(x_238, x_245);
lean_inc(x_246);
x_247 = lean_environment_find(x_244, x_246);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_free_object(x_240);
lean_dec(x_239);
x_248 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_248, 0, x_246);
x_249 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15;
x_250 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
x_251 = l_Lean_KernelException_toMessageData___closed__3;
x_252 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_252, x_4, x_5, x_6, x_7, x_8, x_9, x_243);
lean_dec(x_6);
return x_253;
}
else
{
lean_object* x_254; 
lean_dec(x_247);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_254 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_254, 0, x_246);
lean_ctor_set(x_254, 1, x_239);
lean_ctor_set(x_240, 0, x_254);
return x_240;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_255 = lean_ctor_get(x_240, 0);
x_256 = lean_ctor_get(x_240, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_240);
x_257 = lean_ctor_get(x_255, 0);
lean_inc(x_257);
lean_dec(x_255);
x_258 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13;
x_259 = lean_name_mk_string(x_238, x_258);
lean_inc(x_259);
x_260 = lean_environment_find(x_257, x_259);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_239);
x_261 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_261, 0, x_259);
x_262 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15;
x_263 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_261);
x_264 = l_Lean_KernelException_toMessageData___closed__3;
x_265 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_266 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_265, x_4, x_5, x_6, x_7, x_8, x_9, x_256);
lean_dec(x_6);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_260);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_267 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_267, 0, x_259);
lean_ctor_set(x_267, 1, x_239);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_256);
return x_268;
}
}
}
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_13;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at_Lean_Meta_whnfCore___spec__2(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 7)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint8_t x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 2);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_11, sizeof(void*)*3);
x_18 = (uint8_t)((x_17 << 24) >> 61);
x_19 = l_Lean_BinderInfo_isExplicit(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_10);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_21 = 0;
x_22 = lean_box(0);
lean_inc(x_5);
x_23 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_20, x_21, x_22, x_5, x_6, x_7, x_8, x_13);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
x_26 = l_Lean_mkApp(x_1, x_24);
x_27 = lean_expr_instantiate1(x_16, x_24);
lean_dec(x_24);
lean_dec(x_16);
x_1 = x_26;
x_2 = x_27;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Expr_getOptParamDefault_x3f(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set(x_10, 0, x_30);
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_10);
lean_dec(x_11);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_31);
x_32 = l_Lean_mkApp(x_1, x_31);
x_33 = lean_expr_instantiate1(x_16, x_31);
lean_dec(x_31);
lean_dec(x_16);
x_1 = x_32;
x_2 = x_33;
x_9 = x_13;
goto _start;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; uint8_t x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_11, 2);
lean_inc(x_37);
x_38 = lean_ctor_get_uint64(x_11, sizeof(void*)*3);
x_39 = (uint8_t)((x_38 << 24) >> 61);
x_40 = l_Lean_BinderInfo_isExplicit(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_11);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_42 = 0;
x_43 = lean_box(0);
lean_inc(x_5);
x_44 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_41, x_42, x_43, x_5, x_6, x_7, x_8, x_35);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_45);
x_47 = l_Lean_mkApp(x_1, x_45);
x_48 = lean_expr_instantiate1(x_37, x_45);
lean_dec(x_45);
lean_dec(x_37);
x_1 = x_47;
x_2 = x_48;
x_9 = x_46;
goto _start;
}
else
{
lean_object* x_50; 
x_50 = l_Lean_Expr_getOptParamDefault_x3f(x_36);
lean_dec(x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_11);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_35);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_11);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec(x_50);
lean_inc(x_53);
x_54 = l_Lean_mkApp(x_1, x_53);
x_55 = lean_expr_instantiate1(x_37, x_53);
lean_dec(x_53);
lean_dec(x_37);
x_1 = x_54;
x_2 = x_55;
x_9 = x_35;
goto _start;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_10);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_10, 0);
lean_dec(x_58);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_11);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_10, 1);
lean_inc(x_60);
lean_dec(x_10);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_11);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_10);
if (x_63 == 0)
{
return x_10;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_10, 0);
x_65 = lean_ctor_get(x_10, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_10);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_3(x_2, x_1, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_apply_3(x_3, x_1, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 == x_3;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
x_14 = l_Lean_Elab_logException___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__1(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = x_2 + x_17;
x_2 = x_18;
x_4 = x_15;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
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
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_17);
x_18 = l_Lean_Elab_Term_tryPostponeIfMVar(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_17);
lean_inc(x_16);
x_20 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux(x_16, x_17, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_20, 0, x_13);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_13, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_13);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_28 = l_Lean_Meta_unfoldDefinition_x3f(x_17, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = lean_array_get_size(x_4);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_lt(x_34, x_33);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_33, x_33);
if (x_36 == 0)
{
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 0, x_26);
return x_28;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_28);
x_37 = 0;
x_38 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_39 = lean_box(0);
x_40 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(x_4, x_37, x_38, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_26);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_26);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_26);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_28, 1);
lean_inc(x_49);
lean_dec(x_28);
x_50 = lean_array_get_size(x_4);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_lt(x_51, x_50);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_26);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_50, x_50);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_26);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_58 = lean_box(0);
x_59 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(x_4, x_56, x_57, x_58, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
 lean_ctor_set_tag(x_62, 1);
}
lean_ctor_set(x_62, 0, x_26);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_26);
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_65 = x_59;
} else {
 lean_dec_ref(x_59);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_28, 1);
lean_inc(x_67);
lean_dec(x_28);
x_68 = lean_ctor_get(x_29, 0);
lean_inc(x_68);
lean_dec(x_29);
x_69 = lean_array_push(x_4, x_26);
x_2 = x_16;
x_3 = x_68;
x_4 = x_69;
x_11 = x_67;
goto _start;
}
}
else
{
uint8_t x_71; 
lean_dec(x_26);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_28);
if (x_71 == 0)
{
return x_28;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_28, 0);
x_73 = lean_ctor_get(x_28, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_28);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
else
{
uint8_t x_75; 
lean_free_object(x_13);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_18);
if (x_75 == 0)
{
return x_18;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_18, 0);
x_77 = lean_ctor_get(x_18, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_18);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_13, 0);
x_80 = lean_ctor_get(x_13, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_80);
x_81 = l_Lean_Elab_Term_tryPostponeIfMVar(x_80, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_80);
lean_inc(x_79);
x_83 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux(x_79, x_80, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_80);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_84);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_91 = l_Lean_Meta_unfoldDefinition_x3f(x_80, x_7, x_8, x_9, x_10, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_79);
lean_dec(x_1);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_95 = lean_array_get_size(x_4);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_nat_dec_lt(x_96, x_95);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_95);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_94)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_94;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_89);
lean_ctor_set(x_98, 1, x_93);
return x_98;
}
else
{
uint8_t x_99; 
x_99 = lean_nat_dec_le(x_95, x_95);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_95);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_94)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_94;
 lean_ctor_set_tag(x_100, 1);
}
lean_ctor_set(x_100, 0, x_89);
lean_ctor_set(x_100, 1, x_93);
return x_100;
}
else
{
size_t x_101; size_t x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_94);
x_101 = 0;
x_102 = lean_usize_of_nat(x_95);
lean_dec(x_95);
x_103 = lean_box(0);
x_104 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(x_4, x_101, x_102, x_103, x_5, x_6, x_7, x_8, x_9, x_10, x_93);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
 lean_ctor_set_tag(x_107, 1);
}
lean_ctor_set(x_107, 0, x_89);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_89);
x_108 = lean_ctor_get(x_104, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_104, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_110 = x_104;
} else {
 lean_dec_ref(x_104);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_91, 1);
lean_inc(x_112);
lean_dec(x_91);
x_113 = lean_ctor_get(x_92, 0);
lean_inc(x_113);
lean_dec(x_92);
x_114 = lean_array_push(x_4, x_89);
x_2 = x_79;
x_3 = x_113;
x_4 = x_114;
x_11 = x_112;
goto _start;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_89);
lean_dec(x_79);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_116 = lean_ctor_get(x_91, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_91, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_118 = x_91;
} else {
 lean_dec_ref(x_91);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_120 = lean_ctor_get(x_81, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_81, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_122 = x_81;
} else {
 lean_dec_ref(x_81);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_12);
if (x_124 == 0)
{
return x_12;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_12, 0);
x_126 = lean_ctor_get(x_12, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_12);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Meta_inferType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Array_empty___closed__1;
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop(x_2, x_1, x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("self");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
lean_inc(x_3);
x_14 = l_Lean_Elab_Term_mkConst(x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = lean_box(0);
x_19 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
x_21 = l_Lean_mkOptionalNode___closed__2;
x_22 = lean_array_push(x_21, x_20);
x_23 = lean_box(0);
x_24 = l_Array_empty___closed__1;
x_25 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_Elab_Term_elabAppArgs(x_15, x_22, x_24, x_23, x_25, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_1 = x_12;
x_2 = x_27;
x_9 = x_28;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to access field in parent structure");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_getPathToBaseStructure_x3f(x_14, x_1, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2;
x_17 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__3___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, function '");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has argument with the expected type");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nbut it cannot be used");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_nat_dec_le(x_16, x_7);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_6, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_6, x_20);
lean_dec(x_6);
x_22 = l_Lean_instInhabitedExpr;
x_23 = lean_array_get(x_22, x_2, x_7);
x_24 = l_Lean_Expr_fvarId_x21(x_23);
lean_dec(x_23);
lean_inc(x_11);
x_25 = l_Lean_Meta_getLocalDecl(x_24, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_LocalDecl_userName(x_26);
lean_dec(x_26);
x_29 = l_Lean_LocalDecl_userName(x_3);
x_30 = lean_name_eq(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_nat_add(x_7, x_31);
lean_dec(x_7);
x_33 = lean_box(0);
x_6 = x_21;
x_7 = x_32;
x_8 = x_33;
x_15 = x_27;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_21);
lean_dec(x_7);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_1);
x_36 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__2;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__4;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_indentExpr(x_4);
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__6;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_43, x_9, x_10, x_11, x_12, x_13, x_14, x_27);
lean_dec(x_11);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_25);
if (x_49 == 0)
{
return x_25;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_25, 0);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_25);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_8);
lean_ctor_set(x_53, 1, x_15);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_8);
lean_ctor_set(x_54, 1, x_15);
return x_54;
}
}
}
uint8_t l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = l_Lean_LocalDecl_userName(x_1);
x_5 = lean_name_eq(x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; 
x_13 = l_Lean_LocalDecl_binderInfo(x_1);
x_14 = l_Lean_BinderInfo_isExplicit(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_4, x_19);
lean_dec(x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_box(0);
x_23 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(x_2, x_3, x_4, x_5, x_21, x_1, x_19, x_22, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l_Lean_LocalDecl_userName(x_4);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_27);
x_30 = lean_array_push(x_7, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_10);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_23, 0, x_35);
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_dec(x_23);
x_37 = l_Lean_LocalDecl_userName(x_4);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_6);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_38);
x_41 = lean_array_push(x_7, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_9);
lean_ctor_set(x_44, 1, x_10);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_36);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_48 = !lean_is_exclusive(x_23);
if (x_48 == 0)
{
return x_23;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_23, 0);
x_50 = lean_ctor_get(x_23, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_23);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
if (x_11 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_21 = lean_box(0);
x_22 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__2(x_1, x_2, x_3, x_12, x_21, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_16);
lean_dec(x_14);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_3);
x_23 = lean_array_get_size(x_10);
x_24 = lean_nat_dec_le(x_12, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__3(x_4, x_5, x_6, x_1, x_7, x_8, x_9, x_10, x_2, x_12, x_25, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_26;
}
else
{
uint8_t x_27; uint8_t x_28; 
x_27 = l_Lean_LocalDecl_binderInfo(x_1);
x_28 = l_Lean_BinderInfo_isExplicit(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
x_30 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__3(x_4, x_5, x_6, x_1, x_7, x_8, x_9, x_10, x_2, x_12, x_29, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_8);
x_32 = l_Array_insertAt___rarg(x_10, x_12, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_9);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_12);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_20);
return x_38;
}
}
}
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
if (x_12 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_17, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 3);
lean_inc(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_27 = 2;
lean_ctor_set_uint8(x_22, 5, x_27);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_25);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_7);
x_29 = l_Lean_Meta_whnf(x_7, x_28, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Expr_consumeMData(x_30);
lean_dec(x_30);
x_33 = l_Lean_Expr_isAppOf(x_32, x_11);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_12, x_13, x_34, x_15, x_16, x_17, x_18, x_19, x_20, x_31);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_35;
}
else
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_36 = 1;
x_37 = lean_box(0);
x_38 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_36, x_13, x_37, x_15, x_16, x_17, x_18, x_19, x_20, x_31);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_29);
if (x_39 == 0)
{
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_29);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get_uint8(x_22, 0);
x_44 = lean_ctor_get_uint8(x_22, 1);
x_45 = lean_ctor_get_uint8(x_22, 2);
x_46 = lean_ctor_get_uint8(x_22, 3);
x_47 = lean_ctor_get_uint8(x_22, 4);
x_48 = lean_ctor_get_uint8(x_22, 6);
x_49 = lean_ctor_get_uint8(x_22, 7);
x_50 = lean_ctor_get_uint8(x_22, 8);
lean_dec(x_22);
x_51 = 2;
x_52 = lean_alloc_ctor(0, 0, 9);
lean_ctor_set_uint8(x_52, 0, x_43);
lean_ctor_set_uint8(x_52, 1, x_44);
lean_ctor_set_uint8(x_52, 2, x_45);
lean_ctor_set_uint8(x_52, 3, x_46);
lean_ctor_set_uint8(x_52, 4, x_47);
lean_ctor_set_uint8(x_52, 5, x_51);
lean_ctor_set_uint8(x_52, 6, x_48);
lean_ctor_set_uint8(x_52, 7, x_49);
lean_ctor_set_uint8(x_52, 8, x_50);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_23);
lean_ctor_set(x_53, 2, x_24);
lean_ctor_set(x_53, 3, x_25);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_7);
x_54 = l_Lean_Meta_whnf(x_7, x_53, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Expr_consumeMData(x_55);
lean_dec(x_55);
x_58 = l_Lean_Expr_isAppOf(x_57, x_11);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_box(0);
x_60 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_12, x_13, x_59, x_15, x_16, x_17, x_18, x_19, x_20, x_56);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_60;
}
else
{
uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_61 = 1;
x_62 = lean_box(0);
x_63 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_61, x_13, x_62, x_15, x_16, x_17, x_18, x_19, x_20, x_56);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_ctor_get(x_54, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_54, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_66 = x_54;
} else {
 lean_dec_ref(x_54);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_box(0);
x_69 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_12, x_13, x_68, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_69;
}
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_11, 1);
x_23 = lean_nat_dec_le(x_22, x_13);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_12, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_12, x_26);
lean_dec(x_12);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = l_Lean_instInhabitedExpr;
x_33 = lean_array_get(x_32, x_9, x_13);
x_34 = l_Lean_Expr_fvarId_x21(x_33);
lean_dec(x_33);
lean_inc(x_17);
x_35 = l_Lean_Meta_getLocalDecl(x_34, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_36);
x_38 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_38, 0, x_36);
x_39 = lean_array_get_size(x_30);
x_40 = l_Array_findIdx_x3f_loop___rarg(x_30, x_38, x_39, x_24, lean_box(0));
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_free_object(x_28);
x_41 = l_Lean_LocalDecl_type(x_36);
x_42 = l_Lean_Expr_consumeMData(x_41);
x_43 = l_Lean_Expr_isAppOf(x_42, x_1);
lean_dec(x_42);
if (x_43 == 0)
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_44 = 0;
x_45 = lean_box(0);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_4);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
lean_inc(x_10);
x_46 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__5(x_36, x_30, x_10, x_13, x_2, x_9, x_41, x_3, x_5, x_4, x_1, x_44, x_31, x_45, x_15, x_16, x_17, x_18, x_19, x_20, x_37);
lean_dec(x_36);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_dec(x_46);
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
x_56 = lean_ctor_get(x_11, 2);
x_57 = lean_nat_add(x_13, x_56);
lean_dec(x_13);
x_12 = x_27;
x_13 = x_57;
x_14 = x_55;
x_21 = x_54;
goto _start;
}
}
else
{
uint8_t x_59; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_46);
if (x_59 == 0)
{
return x_46;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_46, 0);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_46);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_63 = 1;
x_64 = lean_box(0);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_4);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
lean_inc(x_10);
x_65 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__5(x_36, x_30, x_10, x_13, x_2, x_9, x_41, x_3, x_5, x_4, x_1, x_63, x_31, x_64, x_15, x_16, x_17, x_18, x_19, x_20, x_37);
lean_dec(x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
lean_ctor_set(x_65, 0, x_69);
return x_65;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_dec(x_65);
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
lean_dec(x_66);
x_75 = lean_ctor_get(x_11, 2);
x_76 = lean_nat_add(x_13, x_75);
lean_dec(x_13);
x_12 = x_27;
x_13 = x_76;
x_14 = x_74;
x_21 = x_73;
goto _start;
}
}
else
{
uint8_t x_78; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_65);
if (x_78 == 0)
{
return x_65;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_65, 0);
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_65);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_36);
x_82 = lean_ctor_get(x_40, 0);
lean_inc(x_82);
lean_dec(x_40);
x_83 = l_Array_eraseIdx___rarg(x_30, x_82);
lean_dec(x_82);
lean_ctor_set(x_28, 0, x_83);
lean_inc(x_10);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_10);
lean_ctor_set(x_84, 1, x_28);
x_85 = lean_ctor_get(x_11, 2);
x_86 = lean_nat_add(x_13, x_85);
lean_dec(x_13);
x_12 = x_27;
x_13 = x_86;
x_14 = x_84;
x_21 = x_37;
goto _start;
}
}
else
{
uint8_t x_88; 
lean_free_object(x_28);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_35);
if (x_88 == 0)
{
return x_35;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_35, 0);
x_90 = lean_ctor_get(x_35, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_35);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_28, 0);
x_93 = lean_ctor_get(x_28, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_28);
x_94 = l_Lean_instInhabitedExpr;
x_95 = lean_array_get(x_94, x_9, x_13);
x_96 = l_Lean_Expr_fvarId_x21(x_95);
lean_dec(x_95);
lean_inc(x_17);
x_97 = l_Lean_Meta_getLocalDecl(x_96, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_98);
x_100 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_100, 0, x_98);
x_101 = lean_array_get_size(x_92);
x_102 = l_Array_findIdx_x3f_loop___rarg(x_92, x_100, x_101, x_24, lean_box(0));
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = l_Lean_LocalDecl_type(x_98);
x_104 = l_Lean_Expr_consumeMData(x_103);
x_105 = l_Lean_Expr_isAppOf(x_104, x_1);
lean_dec(x_104);
if (x_105 == 0)
{
uint8_t x_106; lean_object* x_107; lean_object* x_108; 
x_106 = 0;
x_107 = lean_box(0);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_4);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
lean_inc(x_10);
x_108 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__5(x_98, x_92, x_10, x_13, x_2, x_9, x_103, x_3, x_5, x_4, x_1, x_106, x_93, x_107, x_15, x_16, x_17, x_18, x_19, x_20, x_99);
lean_dec(x_98);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
lean_dec(x_109);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_dec(x_108);
x_115 = lean_ctor_get(x_109, 0);
lean_inc(x_115);
lean_dec(x_109);
x_116 = lean_ctor_get(x_11, 2);
x_117 = lean_nat_add(x_13, x_116);
lean_dec(x_13);
x_12 = x_27;
x_13 = x_117;
x_14 = x_115;
x_21 = x_114;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_119 = lean_ctor_get(x_108, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_108, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_121 = x_108;
} else {
 lean_dec_ref(x_108);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
uint8_t x_123; lean_object* x_124; lean_object* x_125; 
x_123 = 1;
x_124 = lean_box(0);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_4);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
lean_inc(x_10);
x_125 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__5(x_98, x_92, x_10, x_13, x_2, x_9, x_103, x_3, x_5, x_4, x_1, x_123, x_93, x_124, x_15, x_16, x_17, x_18, x_19, x_20, x_99);
lean_dec(x_98);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
lean_dec(x_126);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_127);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
lean_dec(x_125);
x_132 = lean_ctor_get(x_126, 0);
lean_inc(x_132);
lean_dec(x_126);
x_133 = lean_ctor_get(x_11, 2);
x_134 = lean_nat_add(x_13, x_133);
lean_dec(x_13);
x_12 = x_27;
x_13 = x_134;
x_14 = x_132;
x_21 = x_131;
goto _start;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = lean_ctor_get(x_125, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_125, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_138 = x_125;
} else {
 lean_dec_ref(x_125);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_98);
x_140 = lean_ctor_get(x_102, 0);
lean_inc(x_140);
lean_dec(x_102);
x_141 = l_Array_eraseIdx___rarg(x_92, x_140);
lean_dec(x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_93);
lean_inc(x_10);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_10);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_ctor_get(x_11, 2);
x_145 = lean_nat_add(x_13, x_144);
lean_dec(x_13);
x_12 = x_27;
x_13 = x_145;
x_14 = x_143;
x_21 = x_99;
goto _start;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_147 = lean_ctor_get(x_97, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_97, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_149 = x_97;
} else {
 lean_dec_ref(x_97);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
}
else
{
lean_object* x_151; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_14);
lean_ctor_set(x_151, 1, x_21);
return x_151;
}
}
else
{
lean_object* x_152; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_14);
lean_ctor_set(x_152, 1, x_21);
return x_152;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__1___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
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
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___rarg), 9, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not have argument with type (");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ...) that can be used, it must be explicit or implicit with an unique name");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_2);
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_array_get_size(x_9);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(1u);
lean_inc(x_18);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_box(0);
lean_inc(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_3);
x_25 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(x_2, x_3, x_4, x_5, x_1, x_6, x_7, x_8, x_9, x_22, x_21, x_18, x_19, x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
x_30 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1(x_3, x_2, x_29, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_25, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_33);
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_25);
if (x_37 == 0)
{
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_25, 0);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_25);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_instMonadControlReaderT___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4;
x_3 = l_instMonadControlT___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_instMonadControlReaderT___closed__3;
x_15 = l___private_Lean_Meta_Tactic_Intro_0__Lean_Meta_introNImp_loop___rarg___closed__4;
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___closed__1;
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__2___boxed), 17, 8);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_4);
lean_closure_set(x_17, 5, x_14);
lean_closure_set(x_17, 6, x_15);
lean_closure_set(x_17, 7, x_16);
x_18 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___rarg(x_6, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__4___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_11);
lean_dec(x_11);
x_22 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_1);
return x_22;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__5___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_unbox(x_12);
lean_dec(x_12);
x_23 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_1);
return x_23;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
lean_object* x_22; 
x_22 = l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_22;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_3(x_3, x_7, x_8, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_2(x_2, x_11, x_12);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_3(x_4, x_14, x_15, x_16);
return x_17;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_3(x_5, x_18, x_19, x_20);
return x_21;
}
default: 
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_apply_2(x_6, x_22, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__2___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_3(x_4, x_1, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__4___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
lean_inc(x_11);
lean_inc(x_1);
x_19 = l_Lean_Elab_Term_mkConst(x_1, x_18, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_LVal_getRef(x_2);
lean_inc(x_20);
x_23 = l_Lean_Elab_Term_addTermInfo(x_22, x_20, x_11, x_12, x_13, x_14, x_15, x_16, x_21);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_List_isEmpty___rarg(x_3);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_1);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_10);
x_27 = l_Lean_mkOptionalNode___closed__2;
x_28 = lean_array_push(x_27, x_26);
x_29 = lean_box(0);
x_30 = l_Array_empty___closed__1;
x_31 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_32 = l_Lean_Elab_Term_elabAppArgs(x_20, x_30, x_28, x_29, x_31, x_31, x_11, x_12, x_13, x_14, x_15, x_16, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_4, x_5, x_6, x_7, x_8, x_33, x_3, x_11, x_12, x_13, x_14, x_15, x_16, x_34);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_20);
x_40 = l_Lean_Meta_inferType(x_20, x_13, x_14, x_15, x_16, x_24);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_43 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(x_9, x_1, x_10, x_5, x_4, x_41, x_11, x_12, x_13, x_14, x_15, x_16, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = l_Lean_Elab_Term_elabAppArgs(x_20, x_47, x_46, x_6, x_7, x_8, x_11, x_12, x_13, x_14, x_15, x_16, x_45);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_43);
if (x_49 == 0)
{
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_43, 0);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_43);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_40);
if (x_53 == 0)
{
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_19);
if (x_57 == 0)
{
return x_19;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_19, 0);
x_59 = lean_ctor_get(x_19, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_19);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("idx");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Term_elabAppArgs(x_6, x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_16);
x_18 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal(x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_20, 2);
lean_inc(x_25);
lean_dec(x_20);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections(x_23, x_24, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Name_append(x_23, x_25);
lean_dec(x_23);
x_30 = lean_box(0);
lean_inc(x_8);
x_31 = l_Lean_Elab_Term_mkConst(x_29, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_Term_LVal_getRef(x_16);
lean_dec(x_16);
lean_inc(x_32);
x_35 = l_Lean_Elab_Term_addTermInfo(x_34, x_32, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_List_isEmpty___rarg(x_17);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_27);
x_39 = lean_box(0);
x_40 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_38);
x_42 = l_Lean_mkOptionalNode___closed__2;
x_43 = lean_array_push(x_42, x_41);
x_44 = lean_box(0);
x_45 = l_Array_empty___closed__1;
x_46 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_47 = l_Lean_Elab_Term_elabAppArgs(x_32, x_43, x_45, x_44, x_46, x_46, x_8, x_9, x_10, x_11, x_12, x_13, x_36);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_6 = x_48;
x_7 = x_17;
x_14 = x_49;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_17);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_27);
x_56 = lean_box(0);
x_57 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_55);
lean_inc(x_8);
x_59 = l_Lean_Elab_Term_addNamedArg(x_1, x_58, x_8, x_9, x_10, x_11, x_12, x_13, x_36);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Elab_Term_elabAppArgs(x_32, x_60, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_61);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_59, 0);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_59);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_31);
if (x_67 == 0)
{
return x_31;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_31, 0);
x_69 = lean_ctor_get(x_31, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_31);
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
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_26);
if (x_71 == 0)
{
return x_26;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_26, 0);
x_73 = lean_ctor_get(x_26, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_26);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
case 1:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_18, 1);
lean_inc(x_75);
lean_dec(x_18);
x_76 = lean_ctor_get(x_19, 0);
lean_inc(x_76);
lean_dec(x_19);
x_77 = lean_ctor_get(x_20, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_20, 1);
lean_inc(x_78);
lean_dec(x_20);
x_79 = l_Lean_mkProj(x_77, x_78, x_76);
x_80 = l_Lean_Elab_Term_LVal_getRef(x_16);
lean_dec(x_16);
lean_inc(x_79);
x_81 = l_Lean_Elab_Term_addTermInfo(x_80, x_79, x_8, x_9, x_10, x_11, x_12, x_13, x_75);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_6 = x_79;
x_7 = x_17;
x_14 = x_82;
goto _start;
}
case 2:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_18, 1);
lean_inc(x_84);
lean_dec(x_18);
x_85 = lean_ctor_get(x_19, 0);
lean_inc(x_85);
lean_dec(x_19);
x_86 = lean_ctor_get(x_20, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_20, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_20, 2);
lean_inc(x_88);
lean_dec(x_20);
x_89 = lean_name_eq(x_86, x_87);
if (x_89 == 0)
{
lean_object* x_90; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_90 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections(x_86, x_87, x_85, x_8, x_9, x_10, x_11, x_12, x_13, x_84);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(x_88, x_16, x_17, x_1, x_2, x_3, x_4, x_5, x_86, x_91, x_8, x_9, x_10, x_11, x_12, x_13, x_92);
lean_dec(x_16);
return x_93;
}
else
{
uint8_t x_94; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_90);
if (x_94 == 0)
{
return x_90;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_90, 0);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_90);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; 
lean_dec(x_87);
x_98 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(x_88, x_16, x_17, x_1, x_2, x_3, x_4, x_5, x_86, x_85, x_8, x_9, x_10, x_11, x_12, x_13, x_84);
lean_dec(x_16);
return x_98;
}
}
case 3:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_99 = lean_ctor_get(x_18, 1);
lean_inc(x_99);
lean_dec(x_18);
x_100 = lean_ctor_get(x_19, 0);
lean_inc(x_100);
lean_dec(x_19);
x_101 = lean_ctor_get(x_20, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_20, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_20, 2);
lean_inc(x_103);
lean_dec(x_20);
x_104 = l_Lean_Elab_Term_LVal_getRef(x_16);
lean_dec(x_16);
lean_inc(x_103);
x_105 = l_Lean_Elab_Term_addTermInfo(x_104, x_103, x_8, x_9, x_10, x_11, x_12, x_13, x_99);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = l_List_isEmpty___rarg(x_17);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
lean_dec(x_102);
lean_dec(x_101);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_100);
x_109 = l_Lean_mkOptionalNode___closed__2;
x_110 = lean_array_push(x_109, x_108);
x_111 = lean_box(0);
x_112 = l_Array_empty___closed__1;
x_113 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_114 = l_Lean_Elab_Term_elabAppArgs(x_103, x_112, x_110, x_111, x_113, x_113, x_8, x_9, x_10, x_11, x_12, x_13, x_106);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_6 = x_115;
x_7 = x_17;
x_14 = x_116;
goto _start;
}
else
{
uint8_t x_118; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_114);
if (x_118 == 0)
{
return x_114;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_114, 0);
x_120 = lean_ctor_get(x_114, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_114);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; 
lean_dec(x_17);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_103);
x_122 = l_Lean_Meta_inferType(x_103, x_10, x_11, x_12, x_13, x_106);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_125 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(x_101, x_102, x_100, x_2, x_1, x_123, x_8, x_9, x_10, x_11, x_12, x_13, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = l_Lean_Elab_Term_elabAppArgs(x_103, x_129, x_128, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_127);
return x_130;
}
else
{
uint8_t x_131; 
lean_dec(x_103);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_131 = !lean_is_exclusive(x_125);
if (x_131 == 0)
{
return x_125;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_125, 0);
x_133 = lean_ctor_get(x_125, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_125);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_122);
if (x_135 == 0)
{
return x_122;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_122, 0);
x_137 = lean_ctor_get(x_122, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_122);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
default: 
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_18, 1);
lean_inc(x_139);
lean_dec(x_18);
x_140 = lean_ctor_get(x_19, 0);
lean_inc(x_140);
lean_dec(x_19);
x_141 = lean_ctor_get(x_20, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_20, 1);
lean_inc(x_142);
lean_dec(x_20);
x_143 = lean_box(0);
lean_inc(x_8);
x_144 = l_Lean_Elab_Term_mkConst(x_141, x_143, x_8, x_9, x_10, x_11, x_12, x_13, x_139);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Elab_Term_LVal_getRef(x_16);
lean_dec(x_16);
lean_inc(x_145);
x_148 = l_Lean_Elab_Term_addTermInfo(x_147, x_145, x_8, x_9, x_10, x_11, x_12, x_13, x_146);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_150 = l_List_isEmpty___rarg(x_17);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; 
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_140);
x_152 = lean_box(0);
x_153 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_154 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_154, 2, x_151);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_142);
x_156 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
x_157 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_157, 0, x_152);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_157, 2, x_155);
x_158 = l_Lean_Syntax_mkApp___closed__1;
x_159 = lean_array_push(x_158, x_154);
x_160 = lean_array_push(x_159, x_157);
x_161 = lean_box(0);
x_162 = l_Array_empty___closed__1;
x_163 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_164 = l_Lean_Elab_Term_elabAppArgs(x_145, x_160, x_162, x_161, x_163, x_163, x_8, x_9, x_10, x_11, x_12, x_13, x_149);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_6 = x_165;
x_7 = x_17;
x_14 = x_166;
goto _start;
}
else
{
uint8_t x_168; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_168 = !lean_is_exclusive(x_164);
if (x_168 == 0)
{
return x_164;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_164, 0);
x_170 = lean_ctor_get(x_164, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_164);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_17);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_140);
x_173 = lean_box(0);
x_174 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_175 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
lean_ctor_set(x_175, 2, x_172);
lean_inc(x_8);
x_176 = l_Lean_Elab_Term_addNamedArg(x_1, x_175, x_8, x_9, x_10, x_11, x_12, x_13, x_149);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_142);
x_180 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
x_181 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_181, 0, x_173);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set(x_181, 2, x_179);
lean_inc(x_8);
x_182 = l_Lean_Elab_Term_addNamedArg(x_177, x_181, x_8, x_9, x_10, x_11, x_12, x_13, x_178);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l_Lean_Elab_Term_elabAppArgs(x_145, x_183, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_184);
return x_185;
}
else
{
uint8_t x_186; 
lean_dec(x_145);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_186 = !lean_is_exclusive(x_182);
if (x_186 == 0)
{
return x_182;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_182, 0);
x_188 = lean_ctor_get(x_182, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_182);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_145);
lean_dec(x_142);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_190 = !lean_is_exclusive(x_176);
if (x_190 == 0)
{
return x_176;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_176, 0);
x_192 = lean_ctor_get(x_176, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_176);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_144);
if (x_194 == 0)
{
return x_144;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_144, 0);
x_196 = lean_ctor_get(x_144, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_144);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_18);
if (x_198 == 0)
{
return x_18;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_18, 0);
x_200 = lean_ctor_get(x_18, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_18);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = lean_unbox(x_8);
lean_dec(x_8);
x_20 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_18, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_2);
return x_20;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of field notation with `@` modifier");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = l_List_isEmpty___rarg(x_2);
if (x_15 == 0)
{
if (x_6 == 0)
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_3, x_4, x_5, x_6, x_7, x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__2;
x_18 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
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
x_23 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_3, x_4, x_5, x_6, x_7, x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_23;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 == x_3;
if (x_12 == 0)
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 1;
x_14 = x_2 - x_13;
x_15 = lean_array_uget(x_1, x_14);
x_16 = l_Lean_Elab_Term_elabLevel(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_4);
x_2 = x_14;
x_4 = x_19;
x_11 = x_18;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_11);
return x_25;
}
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUnivs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_box(0);
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_15 = 0;
x_16 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(x_1, x_14, x_15, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Term_elabExplicitUnivs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_Elab_Term_elabExplicitUnivs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabExplicitUnivs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toName_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals_match__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_box(x_2);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
else
{
lean_dec(x_3);
if (x_2 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_2(x_5, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_2(x_4, x_11, x_12);
return x_13;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals_match__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals_match__1___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toName(x_4);
x_6 = l_Lean_Syntax_getId(x_3);
x_7 = l_Lean_Name_toString___closed__1;
x_8 = l_Lean_Name_toStringWithSep(x_7, x_6);
x_9 = lean_name_mk_string(x_5, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals(lean_object* x_1, uint8_t x_2) {
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
if (x_2 == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Syntax_getId(x_5);
x_8 = l_Lean_Name_toString___closed__1;
x_9 = l_Lean_Name_toStringWithSep(x_8, x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = 0;
x_13 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals(x_6, x_12);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = l_Lean_Syntax_getId(x_14);
x_17 = l_Lean_Name_toString___closed__1;
x_18 = l_Lean_Name_toStringWithSep(x_17, x_16);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = 0;
x_22 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals(x_15, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = l_Lean_Syntax_getId(x_25);
x_28 = l_Lean_Name_toString___closed__1;
x_29 = l_Lean_Name_toStringWithSep(x_28, x_27);
lean_inc(x_26);
lean_inc(x_25);
x_30 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toName(x_1);
lean_dec(x_1);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_31);
x_33 = 0;
x_34 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals(x_26, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_1);
x_38 = l_Lean_Syntax_getId(x_36);
x_39 = l_Lean_Name_toString___closed__1;
x_40 = l_Lean_Name_toStringWithSep(x_39, x_38);
lean_inc(x_37);
lean_inc(x_36);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
x_42 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toName(x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_43);
x_45 = 0;
x_46 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals(x_37, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals(x_1, x_3);
return x_4;
}
}
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_58; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_21);
x_24 = l_Lean_Elab_Term_addTermInfo(x_22, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = 1;
x_27 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals(x_23, x_26);
lean_inc(x_1);
x_28 = l_List_append___rarg(x_27, x_1);
x_29 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_25);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_58 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_21, x_28, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_12, x_13, x_14, x_15, x_31);
if (lean_obj_tag(x_58) == 0)
{
if (x_7 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_32);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Elab_Term_SavedState_restore(x_30, x_10, x_11, x_12, x_13, x_14, x_15, x_63);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 1);
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 0, x_59);
x_68 = lean_array_push(x_8, x_64);
x_8 = x_68;
x_9 = x_20;
x_16 = x_66;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_62);
x_72 = lean_array_push(x_8, x_71);
x_8 = x_72;
x_9 = x_20;
x_16 = x_70;
goto _start;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_58, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_58, 1);
lean_inc(x_75);
lean_dec(x_58);
x_76 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
x_77 = l_Lean_Elab_Term_ensureHasType(x_4, x_74, x_76, x_10, x_11, x_12, x_13, x_14, x_15, x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_32);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Elab_Term_SavedState_restore(x_30, x_10, x_11, x_12, x_13, x_14, x_15, x_82);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_83, 1);
x_86 = lean_ctor_get(x_83, 0);
lean_dec(x_86);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 0, x_78);
x_87 = lean_array_push(x_8, x_83);
x_8 = x_87;
x_9 = x_20;
x_16 = x_85;
goto _start;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_78);
lean_ctor_set(x_90, 1, x_81);
x_91 = lean_array_push(x_8, x_90);
x_8 = x_91;
x_9 = x_20;
x_16 = x_89;
goto _start;
}
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_77, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_77, 1);
lean_inc(x_94);
lean_dec(x_77);
x_33 = x_93;
x_34 = x_94;
goto block_57;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_58, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_58, 1);
lean_inc(x_96);
lean_dec(x_58);
x_33 = x_95;
x_34 = x_96;
goto block_57;
}
block_57:
{
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_32);
x_35 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_SavedState_restore(x_30, x_10, x_11, x_12, x_13, x_14, x_15, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 0, x_33);
x_42 = lean_array_push(x_8, x_38);
x_8 = x_42;
x_9 = x_20;
x_16 = x_40;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_36);
x_46 = lean_array_push(x_8, x_45);
x_8 = x_46;
x_9 = x_20;
x_16 = x_44;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_33, 0);
lean_inc(x_48);
x_49 = l_Lean_Elab_postponeExceptionId;
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_32)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_32;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_33);
lean_ctor_set(x_51, 1, x_34);
return x_51;
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_32);
x_52 = l_Lean_Elab_Term_SavedState_restore(x_30, x_10, x_11, x_12, x_13, x_14, x_15, x_34);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 0, x_33);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_33);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
}
}
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_58; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_21);
x_24 = l_Lean_Elab_Term_addTermInfo(x_22, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = 1;
x_27 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_toLVals(x_23, x_26);
lean_inc(x_1);
x_28 = l_List_append___rarg(x_27, x_1);
x_29 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_25);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_58 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_21, x_28, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_12, x_13, x_14, x_15, x_31);
if (lean_obj_tag(x_58) == 0)
{
if (x_7 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_32);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Elab_Term_SavedState_restore(x_30, x_10, x_11, x_12, x_13, x_14, x_15, x_63);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 1);
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 0, x_59);
x_68 = lean_array_push(x_8, x_64);
x_8 = x_68;
x_9 = x_20;
x_16 = x_66;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_62);
x_72 = lean_array_push(x_8, x_71);
x_8 = x_72;
x_9 = x_20;
x_16 = x_70;
goto _start;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_58, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_58, 1);
lean_inc(x_75);
lean_dec(x_58);
x_76 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
x_77 = l_Lean_Elab_Term_ensureHasType(x_4, x_74, x_76, x_10, x_11, x_12, x_13, x_14, x_15, x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_32);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Elab_Term_SavedState_restore(x_30, x_10, x_11, x_12, x_13, x_14, x_15, x_82);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_83, 1);
x_86 = lean_ctor_get(x_83, 0);
lean_dec(x_86);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 0, x_78);
x_87 = lean_array_push(x_8, x_83);
x_8 = x_87;
x_9 = x_20;
x_16 = x_85;
goto _start;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_78);
lean_ctor_set(x_90, 1, x_81);
x_91 = lean_array_push(x_8, x_90);
x_8 = x_91;
x_9 = x_20;
x_16 = x_89;
goto _start;
}
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_77, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_77, 1);
lean_inc(x_94);
lean_dec(x_77);
x_33 = x_93;
x_34 = x_94;
goto block_57;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_58, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_58, 1);
lean_inc(x_96);
lean_dec(x_58);
x_33 = x_95;
x_34 = x_96;
goto block_57;
}
block_57:
{
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_32);
x_35 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_SavedState_restore(x_30, x_10, x_11, x_12, x_13, x_14, x_15, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
x_41 = lean_ctor_get(x_38, 0);
lean_dec(x_41);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 0, x_33);
x_42 = lean_array_push(x_8, x_38);
x_8 = x_42;
x_9 = x_20;
x_16 = x_40;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_36);
x_46 = lean_array_push(x_8, x_45);
x_8 = x_46;
x_9 = x_20;
x_16 = x_44;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_33, 0);
lean_inc(x_48);
x_49 = l_Lean_Elab_postponeExceptionId;
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_32)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_32;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_33);
lean_ctor_set(x_51, 1, x_34);
return x_51;
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_32);
x_52 = l_Lean_Elab_Term_SavedState_restore(x_30, x_10, x_11, x_12, x_13, x_14, x_15, x_34);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 0, x_33);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_33);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_15, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 5);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 6);
lean_inc(x_24);
x_25 = lean_ctor_get(x_15, 7);
lean_inc(x_25);
x_26 = l_Lean_replaceRef(x_1, x_21);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_24);
lean_ctor_set(x_27, 7, x_25);
lean_inc(x_13);
lean_inc(x_11);
x_28 = l_Lean_Elab_Term_resolveName_x27(x_1, x_2, x_11, x_12, x_13, x_14, x_27, x_16, x_17);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_11, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_11, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_11, 4);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_11, sizeof(void*)*8);
x_37 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 2);
x_38 = lean_ctor_get(x_11, 5);
lean_inc(x_38);
x_39 = lean_ctor_get(x_11, 6);
lean_inc(x_39);
x_40 = lean_ctor_get(x_11, 7);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 3);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_List_lengthAux___rarg(x_29, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_dec_eq(x_43, x_44);
if (x_9 == 0)
{
uint8_t x_75; 
x_75 = lean_nat_dec_lt(x_44, x_43);
lean_dec(x_43);
x_46 = x_75;
goto block_74;
}
else
{
uint8_t x_76; 
lean_dec(x_43);
x_76 = 1;
x_46 = x_76;
goto block_74;
}
block_74:
{
if (x_45 == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_11);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_11, 7);
lean_dec(x_48);
x_49 = lean_ctor_get(x_11, 6);
lean_dec(x_49);
x_50 = lean_ctor_get(x_11, 5);
lean_dec(x_50);
x_51 = lean_ctor_get(x_11, 4);
lean_dec(x_51);
x_52 = lean_ctor_get(x_11, 3);
lean_dec(x_52);
x_53 = lean_ctor_get(x_11, 2);
lean_dec(x_53);
x_54 = lean_ctor_get(x_11, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_11, 0);
lean_dec(x_55);
x_56 = 0;
lean_ctor_set_uint8(x_11, sizeof(void*)*8 + 1, x_56);
x_57 = l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_46, x_10, x_29, x_11, x_12, x_13, x_14, x_15, x_16, x_30);
return x_57;
}
else
{
uint8_t x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_11);
x_58 = 0;
x_59 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_59, 0, x_31);
lean_ctor_set(x_59, 1, x_32);
lean_ctor_set(x_59, 2, x_33);
lean_ctor_set(x_59, 3, x_34);
lean_ctor_set(x_59, 4, x_35);
lean_ctor_set(x_59, 5, x_38);
lean_ctor_set(x_59, 6, x_39);
lean_ctor_set(x_59, 7, x_40);
lean_ctor_set_uint8(x_59, sizeof(void*)*8, x_36);
lean_ctor_set_uint8(x_59, sizeof(void*)*8 + 1, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*8 + 2, x_37);
lean_ctor_set_uint8(x_59, sizeof(void*)*8 + 3, x_41);
x_60 = l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_46, x_10, x_29, x_59, x_12, x_13, x_14, x_15, x_16, x_30);
return x_60;
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_11);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_11, 7);
lean_dec(x_62);
x_63 = lean_ctor_get(x_11, 6);
lean_dec(x_63);
x_64 = lean_ctor_get(x_11, 5);
lean_dec(x_64);
x_65 = lean_ctor_get(x_11, 4);
lean_dec(x_65);
x_66 = lean_ctor_get(x_11, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_11, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_11, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_11, 0);
lean_dec(x_69);
x_70 = l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_46, x_10, x_29, x_11, x_12, x_13, x_14, x_15, x_16, x_30);
return x_70;
}
else
{
uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 1);
lean_dec(x_11);
x_72 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_72, 0, x_31);
lean_ctor_set(x_72, 1, x_32);
lean_ctor_set(x_72, 2, x_33);
lean_ctor_set(x_72, 3, x_34);
lean_ctor_set(x_72, 4, x_35);
lean_ctor_set(x_72, 5, x_38);
lean_ctor_set(x_72, 6, x_39);
lean_ctor_set(x_72, 7, x_40);
lean_ctor_set_uint8(x_72, sizeof(void*)*8, x_36);
lean_ctor_set_uint8(x_72, sizeof(void*)*8 + 1, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*8 + 2, x_37);
lean_ctor_set_uint8(x_72, sizeof(void*)*8 + 3, x_41);
x_73 = l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_46, x_10, x_29, x_72, x_12, x_13, x_14, x_15, x_16, x_30);
return x_73;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_28);
if (x_77 == 0)
{
return x_28;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_28, 0);
x_79 = lean_ctor_get(x_28, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_28);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = lean_unbox(x_7);
lean_dec(x_7);
x_20 = l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1(x_1, x_2, x_3, x_4, x_17, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = lean_unbox(x_7);
lean_dec(x_7);
x_20 = l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(x_1, x_2, x_3, x_4, x_17, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = lean_unbox(x_8);
lean_dec(x_8);
x_20 = lean_unbox(x_9);
lean_dec(x_9);
x_21 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(x_1, x_2, x_3, x_4, x_5, x_6, x_18, x_19, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2___rarg), 1, 0);
return x_7;
}
}
lean_object* l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_Lean_Name_toString___closed__1;
x_8 = l_Lean_Name_toStringWithSep(x_7, x_5);
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(x_1, x_6);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = l_Lean_Name_toString___closed__1;
x_15 = l_Lean_Name_toStringWithSep(x_14, x_12);
x_16 = lean_box(0);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
x_18 = l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(x_1, x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = x_8 == x_9;
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_array_uget(x_7, x_8);
x_20 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(x_19, x_1, x_2, x_3, x_4, x_5, x_6, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = x_8 + x_24;
x_8 = x_25;
x_10 = x_22;
x_17 = x_23;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_17);
return x_31;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_push(x_1, x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("placeholders '_' cannot be used where a function is expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected occurrence of named pattern");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_349; lean_object* x_350; uint8_t x_351; 
lean_inc(x_1);
x_349 = l_Lean_Syntax_getKind(x_1);
x_350 = l_Lean_choiceKind;
x_351 = lean_name_eq(x_349, x_350);
lean_dec(x_349);
if (x_351 == 0)
{
lean_object* x_352; uint8_t x_353; 
x_352 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
lean_inc(x_1);
x_353 = l_Lean_Syntax_isOfKind(x_1, x_352);
if (x_353 == 0)
{
lean_object* x_354; uint8_t x_355; 
x_354 = l_Lean_Parser_Term_pipeProj___elambda__1___closed__2;
lean_inc(x_1);
x_355 = l_Lean_Syntax_isOfKind(x_1, x_354);
if (x_355 == 0)
{
lean_object* x_356; uint8_t x_357; 
x_356 = l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
lean_inc(x_1);
x_357 = l_Lean_Syntax_isOfKind(x_1, x_356);
if (x_357 == 0)
{
lean_object* x_358; uint8_t x_359; 
x_358 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
lean_inc(x_1);
x_359 = l_Lean_Syntax_isOfKind(x_1, x_358);
if (x_359 == 0)
{
lean_object* x_360; uint8_t x_361; 
x_360 = l_Lean_identKind___closed__2;
lean_inc(x_1);
x_361 = l_Lean_Syntax_isOfKind(x_1, x_360);
if (x_361 == 0)
{
lean_object* x_362; uint8_t x_363; 
x_362 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_inc(x_1);
x_363 = l_Lean_Syntax_isOfKind(x_1, x_362);
if (x_363 == 0)
{
lean_object* x_364; uint8_t x_365; 
x_364 = l_myMacro____x40_Init_NotationExtra___hyg_5659____closed__28;
lean_inc(x_1);
x_365 = l_Lean_Syntax_isOfKind(x_1, x_364);
if (x_365 == 0)
{
lean_object* x_366; uint8_t x_367; 
x_366 = l_myMacro____x40_Init_Notation___hyg_14458____closed__13;
lean_inc(x_1);
x_367 = l_Lean_Syntax_isOfKind(x_1, x_366);
if (x_367 == 0)
{
uint8_t x_368; uint8_t x_369; 
x_368 = l_List_isEmpty___rarg(x_2);
if (x_8 == 0)
{
uint8_t x_696; 
x_696 = 1;
x_369 = x_696;
goto block_695;
}
else
{
uint8_t x_697; 
x_697 = 0;
x_369 = x_697;
goto block_695;
}
block_695:
{
if (x_368 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_407; lean_object* x_408; uint8_t x_430; lean_object* x_431; 
x_370 = lean_box(0);
x_371 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_371, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_374 = x_371;
} else {
 lean_dec_ref(x_371);
 x_374 = lean_box(0);
}
x_430 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_431 = l_Lean_Elab_Term_elabTerm(x_1, x_370, x_369, x_430, x_10, x_11, x_12, x_13, x_14, x_15, x_373);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_434 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_432, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_433);
if (lean_obj_tag(x_434) == 0)
{
if (x_8 == 0)
{
lean_object* x_435; lean_object* x_436; 
lean_dec(x_374);
lean_dec(x_5);
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec(x_434);
x_407 = x_435;
x_408 = x_436;
goto block_429;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_434, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_434, 1);
lean_inc(x_438);
lean_dec(x_434);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_439 = l_Lean_Elab_Term_ensureHasType(x_5, x_437, x_370, x_10, x_11, x_12, x_13, x_14, x_15, x_438);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; 
lean_dec(x_374);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_407 = x_440;
x_408 = x_441;
goto block_429;
}
else
{
lean_object* x_442; lean_object* x_443; 
x_442 = lean_ctor_get(x_439, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_439, 1);
lean_inc(x_443);
lean_dec(x_439);
x_375 = x_442;
x_376 = x_443;
goto block_406;
}
}
}
else
{
lean_object* x_444; lean_object* x_445; 
lean_dec(x_5);
x_444 = lean_ctor_get(x_434, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_434, 1);
lean_inc(x_445);
lean_dec(x_434);
x_375 = x_444;
x_376 = x_445;
goto block_406;
}
}
else
{
lean_object* x_446; lean_object* x_447; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_446 = lean_ctor_get(x_431, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_431, 1);
lean_inc(x_447);
lean_dec(x_431);
x_375 = x_446;
x_376 = x_447;
goto block_406;
}
block_406:
{
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_377; uint8_t x_378; 
lean_dec(x_374);
x_377 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_376);
x_378 = !lean_is_exclusive(x_377);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; 
x_379 = lean_ctor_get(x_377, 0);
x_380 = lean_ctor_get(x_377, 1);
x_381 = l_Lean_Elab_Term_SavedState_restore(x_372, x_10, x_11, x_12, x_13, x_14, x_15, x_380);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_381, 1);
x_384 = lean_ctor_get(x_381, 0);
lean_dec(x_384);
lean_ctor_set_tag(x_381, 1);
lean_ctor_set(x_381, 1, x_379);
lean_ctor_set(x_381, 0, x_375);
x_385 = lean_array_push(x_9, x_381);
lean_ctor_set(x_377, 1, x_383);
lean_ctor_set(x_377, 0, x_385);
return x_377;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_381, 1);
lean_inc(x_386);
lean_dec(x_381);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_375);
lean_ctor_set(x_387, 1, x_379);
x_388 = lean_array_push(x_9, x_387);
lean_ctor_set(x_377, 1, x_386);
lean_ctor_set(x_377, 0, x_388);
return x_377;
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_389 = lean_ctor_get(x_377, 0);
x_390 = lean_ctor_get(x_377, 1);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_377);
x_391 = l_Lean_Elab_Term_SavedState_restore(x_372, x_10, x_11, x_12, x_13, x_14, x_15, x_390);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_392 = lean_ctor_get(x_391, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_393 = x_391;
} else {
 lean_dec_ref(x_391);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_393;
 lean_ctor_set_tag(x_394, 1);
}
lean_ctor_set(x_394, 0, x_375);
lean_ctor_set(x_394, 1, x_389);
x_395 = lean_array_push(x_9, x_394);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_392);
return x_396;
}
}
else
{
lean_object* x_397; lean_object* x_398; uint8_t x_399; 
lean_dec(x_9);
x_397 = lean_ctor_get(x_375, 0);
lean_inc(x_397);
x_398 = l_Lean_Elab_postponeExceptionId;
x_399 = lean_nat_dec_eq(x_397, x_398);
lean_dec(x_397);
if (x_399 == 0)
{
lean_object* x_400; 
lean_dec(x_372);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_374)) {
 x_400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_400 = x_374;
 lean_ctor_set_tag(x_400, 1);
}
lean_ctor_set(x_400, 0, x_375);
lean_ctor_set(x_400, 1, x_376);
return x_400;
}
else
{
lean_object* x_401; uint8_t x_402; 
lean_dec(x_374);
x_401 = l_Lean_Elab_Term_SavedState_restore(x_372, x_10, x_11, x_12, x_13, x_14, x_15, x_376);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_402 = !lean_is_exclusive(x_401);
if (x_402 == 0)
{
lean_object* x_403; 
x_403 = lean_ctor_get(x_401, 0);
lean_dec(x_403);
lean_ctor_set_tag(x_401, 1);
lean_ctor_set(x_401, 0, x_375);
return x_401;
}
else
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_401, 1);
lean_inc(x_404);
lean_dec(x_401);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_375);
lean_ctor_set(x_405, 1, x_404);
return x_405;
}
}
}
}
block_429:
{
lean_object* x_409; uint8_t x_410; 
x_409 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_408);
x_410 = !lean_is_exclusive(x_409);
if (x_410 == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; 
x_411 = lean_ctor_get(x_409, 0);
x_412 = lean_ctor_get(x_409, 1);
x_413 = l_Lean_Elab_Term_SavedState_restore(x_372, x_10, x_11, x_12, x_13, x_14, x_15, x_412);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_414 = !lean_is_exclusive(x_413);
if (x_414 == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_413, 1);
x_416 = lean_ctor_get(x_413, 0);
lean_dec(x_416);
lean_ctor_set(x_413, 1, x_411);
lean_ctor_set(x_413, 0, x_407);
x_417 = lean_array_push(x_9, x_413);
lean_ctor_set(x_409, 1, x_415);
lean_ctor_set(x_409, 0, x_417);
return x_409;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_413, 1);
lean_inc(x_418);
lean_dec(x_413);
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_407);
lean_ctor_set(x_419, 1, x_411);
x_420 = lean_array_push(x_9, x_419);
lean_ctor_set(x_409, 1, x_418);
lean_ctor_set(x_409, 0, x_420);
return x_409;
}
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_421 = lean_ctor_get(x_409, 0);
x_422 = lean_ctor_get(x_409, 1);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_409);
x_423 = l_Lean_Elab_Term_SavedState_restore(x_372, x_10, x_11, x_12, x_13, x_14, x_15, x_422);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_425 = x_423;
} else {
 lean_dec_ref(x_423);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(0, 2, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_407);
lean_ctor_set(x_426, 1, x_421);
x_427 = lean_array_push(x_9, x_426);
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_424);
return x_428;
}
}
}
else
{
uint8_t x_448; 
x_448 = l_Array_isEmpty___rarg(x_3);
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_486; lean_object* x_487; uint8_t x_509; lean_object* x_510; 
x_449 = lean_box(0);
x_450 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_453 = x_450;
} else {
 lean_dec_ref(x_450);
 x_453 = lean_box(0);
}
x_509 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_510 = l_Lean_Elab_Term_elabTerm(x_1, x_449, x_369, x_509, x_10, x_11, x_12, x_13, x_14, x_15, x_452);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_513 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_511, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_512);
if (lean_obj_tag(x_513) == 0)
{
if (x_8 == 0)
{
lean_object* x_514; lean_object* x_515; 
lean_dec(x_453);
lean_dec(x_5);
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_486 = x_514;
x_487 = x_515;
goto block_508;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_513, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_513, 1);
lean_inc(x_517);
lean_dec(x_513);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_518 = l_Lean_Elab_Term_ensureHasType(x_5, x_516, x_449, x_10, x_11, x_12, x_13, x_14, x_15, x_517);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; 
lean_dec(x_453);
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec(x_518);
x_486 = x_519;
x_487 = x_520;
goto block_508;
}
else
{
lean_object* x_521; lean_object* x_522; 
x_521 = lean_ctor_get(x_518, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_518, 1);
lean_inc(x_522);
lean_dec(x_518);
x_454 = x_521;
x_455 = x_522;
goto block_485;
}
}
}
else
{
lean_object* x_523; lean_object* x_524; 
lean_dec(x_5);
x_523 = lean_ctor_get(x_513, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_513, 1);
lean_inc(x_524);
lean_dec(x_513);
x_454 = x_523;
x_455 = x_524;
goto block_485;
}
}
else
{
lean_object* x_525; lean_object* x_526; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_525 = lean_ctor_get(x_510, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_510, 1);
lean_inc(x_526);
lean_dec(x_510);
x_454 = x_525;
x_455 = x_526;
goto block_485;
}
block_485:
{
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_456; uint8_t x_457; 
lean_dec(x_453);
x_456 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_455);
x_457 = !lean_is_exclusive(x_456);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; 
x_458 = lean_ctor_get(x_456, 0);
x_459 = lean_ctor_get(x_456, 1);
x_460 = l_Lean_Elab_Term_SavedState_restore(x_451, x_10, x_11, x_12, x_13, x_14, x_15, x_459);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_461 = !lean_is_exclusive(x_460);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_460, 1);
x_463 = lean_ctor_get(x_460, 0);
lean_dec(x_463);
lean_ctor_set_tag(x_460, 1);
lean_ctor_set(x_460, 1, x_458);
lean_ctor_set(x_460, 0, x_454);
x_464 = lean_array_push(x_9, x_460);
lean_ctor_set(x_456, 1, x_462);
lean_ctor_set(x_456, 0, x_464);
return x_456;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = lean_ctor_get(x_460, 1);
lean_inc(x_465);
lean_dec(x_460);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_454);
lean_ctor_set(x_466, 1, x_458);
x_467 = lean_array_push(x_9, x_466);
lean_ctor_set(x_456, 1, x_465);
lean_ctor_set(x_456, 0, x_467);
return x_456;
}
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_468 = lean_ctor_get(x_456, 0);
x_469 = lean_ctor_get(x_456, 1);
lean_inc(x_469);
lean_inc(x_468);
lean_dec(x_456);
x_470 = l_Lean_Elab_Term_SavedState_restore(x_451, x_10, x_11, x_12, x_13, x_14, x_15, x_469);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_471 = lean_ctor_get(x_470, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_472 = x_470;
} else {
 lean_dec_ref(x_470);
 x_472 = lean_box(0);
}
if (lean_is_scalar(x_472)) {
 x_473 = lean_alloc_ctor(1, 2, 0);
} else {
 x_473 = x_472;
 lean_ctor_set_tag(x_473, 1);
}
lean_ctor_set(x_473, 0, x_454);
lean_ctor_set(x_473, 1, x_468);
x_474 = lean_array_push(x_9, x_473);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_471);
return x_475;
}
}
else
{
lean_object* x_476; lean_object* x_477; uint8_t x_478; 
lean_dec(x_9);
x_476 = lean_ctor_get(x_454, 0);
lean_inc(x_476);
x_477 = l_Lean_Elab_postponeExceptionId;
x_478 = lean_nat_dec_eq(x_476, x_477);
lean_dec(x_476);
if (x_478 == 0)
{
lean_object* x_479; 
lean_dec(x_451);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_453)) {
 x_479 = lean_alloc_ctor(1, 2, 0);
} else {
 x_479 = x_453;
 lean_ctor_set_tag(x_479, 1);
}
lean_ctor_set(x_479, 0, x_454);
lean_ctor_set(x_479, 1, x_455);
return x_479;
}
else
{
lean_object* x_480; uint8_t x_481; 
lean_dec(x_453);
x_480 = l_Lean_Elab_Term_SavedState_restore(x_451, x_10, x_11, x_12, x_13, x_14, x_15, x_455);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_481 = !lean_is_exclusive(x_480);
if (x_481 == 0)
{
lean_object* x_482; 
x_482 = lean_ctor_get(x_480, 0);
lean_dec(x_482);
lean_ctor_set_tag(x_480, 1);
lean_ctor_set(x_480, 0, x_454);
return x_480;
}
else
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_ctor_get(x_480, 1);
lean_inc(x_483);
lean_dec(x_480);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_454);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
}
}
block_508:
{
lean_object* x_488; uint8_t x_489; 
x_488 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_487);
x_489 = !lean_is_exclusive(x_488);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; 
x_490 = lean_ctor_get(x_488, 0);
x_491 = lean_ctor_get(x_488, 1);
x_492 = l_Lean_Elab_Term_SavedState_restore(x_451, x_10, x_11, x_12, x_13, x_14, x_15, x_491);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_493 = !lean_is_exclusive(x_492);
if (x_493 == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_494 = lean_ctor_get(x_492, 1);
x_495 = lean_ctor_get(x_492, 0);
lean_dec(x_495);
lean_ctor_set(x_492, 1, x_490);
lean_ctor_set(x_492, 0, x_486);
x_496 = lean_array_push(x_9, x_492);
lean_ctor_set(x_488, 1, x_494);
lean_ctor_set(x_488, 0, x_496);
return x_488;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_497 = lean_ctor_get(x_492, 1);
lean_inc(x_497);
lean_dec(x_492);
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_486);
lean_ctor_set(x_498, 1, x_490);
x_499 = lean_array_push(x_9, x_498);
lean_ctor_set(x_488, 1, x_497);
lean_ctor_set(x_488, 0, x_499);
return x_488;
}
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_500 = lean_ctor_get(x_488, 0);
x_501 = lean_ctor_get(x_488, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_488);
x_502 = l_Lean_Elab_Term_SavedState_restore(x_451, x_10, x_11, x_12, x_13, x_14, x_15, x_501);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_503 = lean_ctor_get(x_502, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_504 = x_502;
} else {
 lean_dec_ref(x_502);
 x_504 = lean_box(0);
}
if (lean_is_scalar(x_504)) {
 x_505 = lean_alloc_ctor(0, 2, 0);
} else {
 x_505 = x_504;
}
lean_ctor_set(x_505, 0, x_486);
lean_ctor_set(x_505, 1, x_500);
x_506 = lean_array_push(x_9, x_505);
x_507 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_503);
return x_507;
}
}
}
else
{
uint8_t x_527; 
x_527 = l_Array_isEmpty___rarg(x_4);
if (x_527 == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_565; lean_object* x_566; uint8_t x_588; lean_object* x_589; 
x_528 = lean_box(0);
x_529 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_532 = x_529;
} else {
 lean_dec_ref(x_529);
 x_532 = lean_box(0);
}
x_588 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_589 = l_Lean_Elab_Term_elabTerm(x_1, x_528, x_369, x_588, x_10, x_11, x_12, x_13, x_14, x_15, x_531);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec(x_589);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_592 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_590, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_591);
if (lean_obj_tag(x_592) == 0)
{
if (x_8 == 0)
{
lean_object* x_593; lean_object* x_594; 
lean_dec(x_532);
lean_dec(x_5);
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_592, 1);
lean_inc(x_594);
lean_dec(x_592);
x_565 = x_593;
x_566 = x_594;
goto block_587;
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_595 = lean_ctor_get(x_592, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_592, 1);
lean_inc(x_596);
lean_dec(x_592);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_597 = l_Lean_Elab_Term_ensureHasType(x_5, x_595, x_528, x_10, x_11, x_12, x_13, x_14, x_15, x_596);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; lean_object* x_599; 
lean_dec(x_532);
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_597, 1);
lean_inc(x_599);
lean_dec(x_597);
x_565 = x_598;
x_566 = x_599;
goto block_587;
}
else
{
lean_object* x_600; lean_object* x_601; 
x_600 = lean_ctor_get(x_597, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_597, 1);
lean_inc(x_601);
lean_dec(x_597);
x_533 = x_600;
x_534 = x_601;
goto block_564;
}
}
}
else
{
lean_object* x_602; lean_object* x_603; 
lean_dec(x_5);
x_602 = lean_ctor_get(x_592, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_592, 1);
lean_inc(x_603);
lean_dec(x_592);
x_533 = x_602;
x_534 = x_603;
goto block_564;
}
}
else
{
lean_object* x_604; lean_object* x_605; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_604 = lean_ctor_get(x_589, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_589, 1);
lean_inc(x_605);
lean_dec(x_589);
x_533 = x_604;
x_534 = x_605;
goto block_564;
}
block_564:
{
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_535; uint8_t x_536; 
lean_dec(x_532);
x_535 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_534);
x_536 = !lean_is_exclusive(x_535);
if (x_536 == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; uint8_t x_540; 
x_537 = lean_ctor_get(x_535, 0);
x_538 = lean_ctor_get(x_535, 1);
x_539 = l_Lean_Elab_Term_SavedState_restore(x_530, x_10, x_11, x_12, x_13, x_14, x_15, x_538);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_540 = !lean_is_exclusive(x_539);
if (x_540 == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_ctor_get(x_539, 1);
x_542 = lean_ctor_get(x_539, 0);
lean_dec(x_542);
lean_ctor_set_tag(x_539, 1);
lean_ctor_set(x_539, 1, x_537);
lean_ctor_set(x_539, 0, x_533);
x_543 = lean_array_push(x_9, x_539);
lean_ctor_set(x_535, 1, x_541);
lean_ctor_set(x_535, 0, x_543);
return x_535;
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_544 = lean_ctor_get(x_539, 1);
lean_inc(x_544);
lean_dec(x_539);
x_545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_545, 0, x_533);
lean_ctor_set(x_545, 1, x_537);
x_546 = lean_array_push(x_9, x_545);
lean_ctor_set(x_535, 1, x_544);
lean_ctor_set(x_535, 0, x_546);
return x_535;
}
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_547 = lean_ctor_get(x_535, 0);
x_548 = lean_ctor_get(x_535, 1);
lean_inc(x_548);
lean_inc(x_547);
lean_dec(x_535);
x_549 = l_Lean_Elab_Term_SavedState_restore(x_530, x_10, x_11, x_12, x_13, x_14, x_15, x_548);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_550 = lean_ctor_get(x_549, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_551 = x_549;
} else {
 lean_dec_ref(x_549);
 x_551 = lean_box(0);
}
if (lean_is_scalar(x_551)) {
 x_552 = lean_alloc_ctor(1, 2, 0);
} else {
 x_552 = x_551;
 lean_ctor_set_tag(x_552, 1);
}
lean_ctor_set(x_552, 0, x_533);
lean_ctor_set(x_552, 1, x_547);
x_553 = lean_array_push(x_9, x_552);
x_554 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_554, 0, x_553);
lean_ctor_set(x_554, 1, x_550);
return x_554;
}
}
else
{
lean_object* x_555; lean_object* x_556; uint8_t x_557; 
lean_dec(x_9);
x_555 = lean_ctor_get(x_533, 0);
lean_inc(x_555);
x_556 = l_Lean_Elab_postponeExceptionId;
x_557 = lean_nat_dec_eq(x_555, x_556);
lean_dec(x_555);
if (x_557 == 0)
{
lean_object* x_558; 
lean_dec(x_530);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_532)) {
 x_558 = lean_alloc_ctor(1, 2, 0);
} else {
 x_558 = x_532;
 lean_ctor_set_tag(x_558, 1);
}
lean_ctor_set(x_558, 0, x_533);
lean_ctor_set(x_558, 1, x_534);
return x_558;
}
else
{
lean_object* x_559; uint8_t x_560; 
lean_dec(x_532);
x_559 = l_Lean_Elab_Term_SavedState_restore(x_530, x_10, x_11, x_12, x_13, x_14, x_15, x_534);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_560 = !lean_is_exclusive(x_559);
if (x_560 == 0)
{
lean_object* x_561; 
x_561 = lean_ctor_get(x_559, 0);
lean_dec(x_561);
lean_ctor_set_tag(x_559, 1);
lean_ctor_set(x_559, 0, x_533);
return x_559;
}
else
{
lean_object* x_562; lean_object* x_563; 
x_562 = lean_ctor_get(x_559, 1);
lean_inc(x_562);
lean_dec(x_559);
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_533);
lean_ctor_set(x_563, 1, x_562);
return x_563;
}
}
}
}
block_587:
{
lean_object* x_567; uint8_t x_568; 
x_567 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_566);
x_568 = !lean_is_exclusive(x_567);
if (x_568 == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; 
x_569 = lean_ctor_get(x_567, 0);
x_570 = lean_ctor_get(x_567, 1);
x_571 = l_Lean_Elab_Term_SavedState_restore(x_530, x_10, x_11, x_12, x_13, x_14, x_15, x_570);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_572 = !lean_is_exclusive(x_571);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_573 = lean_ctor_get(x_571, 1);
x_574 = lean_ctor_get(x_571, 0);
lean_dec(x_574);
lean_ctor_set(x_571, 1, x_569);
lean_ctor_set(x_571, 0, x_565);
x_575 = lean_array_push(x_9, x_571);
lean_ctor_set(x_567, 1, x_573);
lean_ctor_set(x_567, 0, x_575);
return x_567;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_576 = lean_ctor_get(x_571, 1);
lean_inc(x_576);
lean_dec(x_571);
x_577 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_577, 0, x_565);
lean_ctor_set(x_577, 1, x_569);
x_578 = lean_array_push(x_9, x_577);
lean_ctor_set(x_567, 1, x_576);
lean_ctor_set(x_567, 0, x_578);
return x_567;
}
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_579 = lean_ctor_get(x_567, 0);
x_580 = lean_ctor_get(x_567, 1);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_567);
x_581 = l_Lean_Elab_Term_SavedState_restore(x_530, x_10, x_11, x_12, x_13, x_14, x_15, x_580);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_582 = lean_ctor_get(x_581, 1);
lean_inc(x_582);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 lean_ctor_release(x_581, 1);
 x_583 = x_581;
} else {
 lean_dec_ref(x_581);
 x_583 = lean_box(0);
}
if (lean_is_scalar(x_583)) {
 x_584 = lean_alloc_ctor(0, 2, 0);
} else {
 x_584 = x_583;
}
lean_ctor_set(x_584, 0, x_565);
lean_ctor_set(x_584, 1, x_579);
x_585 = lean_array_push(x_9, x_584);
x_586 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_582);
return x_586;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_8 == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; uint8_t x_633; lean_object* x_634; 
x_606 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_609 = x_606;
} else {
 lean_dec_ref(x_606);
 x_609 = lean_box(0);
}
x_633 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_634 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_633, x_633, x_10, x_11, x_12, x_13, x_14, x_15, x_608);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; uint8_t x_641; 
lean_dec(x_609);
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
lean_dec(x_634);
x_637 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_636);
x_638 = lean_ctor_get(x_637, 0);
lean_inc(x_638);
x_639 = lean_ctor_get(x_637, 1);
lean_inc(x_639);
lean_dec(x_637);
x_640 = l_Lean_Elab_Term_SavedState_restore(x_607, x_10, x_11, x_12, x_13, x_14, x_15, x_639);
x_641 = !lean_is_exclusive(x_640);
if (x_641 == 0)
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_642 = lean_ctor_get(x_640, 1);
x_643 = lean_ctor_get(x_640, 0);
lean_dec(x_643);
lean_ctor_set(x_640, 1, x_638);
lean_ctor_set(x_640, 0, x_635);
x_644 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_640, x_10, x_11, x_12, x_13, x_14, x_15, x_642);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_644;
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_645 = lean_ctor_get(x_640, 1);
lean_inc(x_645);
lean_dec(x_640);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_635);
lean_ctor_set(x_646, 1, x_638);
x_647 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_646, x_10, x_11, x_12, x_13, x_14, x_15, x_645);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_647;
}
}
else
{
lean_object* x_648; lean_object* x_649; 
x_648 = lean_ctor_get(x_634, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_634, 1);
lean_inc(x_649);
lean_dec(x_634);
x_610 = x_648;
x_611 = x_649;
goto block_632;
}
block_632:
{
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; uint8_t x_616; 
lean_dec(x_609);
x_612 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_611);
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec(x_612);
x_615 = l_Lean_Elab_Term_SavedState_restore(x_607, x_10, x_11, x_12, x_13, x_14, x_15, x_614);
x_616 = !lean_is_exclusive(x_615);
if (x_616 == 0)
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_617 = lean_ctor_get(x_615, 1);
x_618 = lean_ctor_get(x_615, 0);
lean_dec(x_618);
lean_ctor_set_tag(x_615, 1);
lean_ctor_set(x_615, 1, x_613);
lean_ctor_set(x_615, 0, x_610);
x_619 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_615, x_10, x_11, x_12, x_13, x_14, x_15, x_617);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_619;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_ctor_get(x_615, 1);
lean_inc(x_620);
lean_dec(x_615);
x_621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_621, 0, x_610);
lean_ctor_set(x_621, 1, x_613);
x_622 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_621, x_10, x_11, x_12, x_13, x_14, x_15, x_620);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_622;
}
}
else
{
lean_object* x_623; lean_object* x_624; uint8_t x_625; 
lean_dec(x_9);
x_623 = lean_ctor_get(x_610, 0);
lean_inc(x_623);
x_624 = l_Lean_Elab_postponeExceptionId;
x_625 = lean_nat_dec_eq(x_623, x_624);
lean_dec(x_623);
if (x_625 == 0)
{
lean_object* x_626; 
lean_dec(x_607);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_609)) {
 x_626 = lean_alloc_ctor(1, 2, 0);
} else {
 x_626 = x_609;
 lean_ctor_set_tag(x_626, 1);
}
lean_ctor_set(x_626, 0, x_610);
lean_ctor_set(x_626, 1, x_611);
return x_626;
}
else
{
lean_object* x_627; uint8_t x_628; 
lean_dec(x_609);
x_627 = l_Lean_Elab_Term_SavedState_restore(x_607, x_10, x_11, x_12, x_13, x_14, x_15, x_611);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_628 = !lean_is_exclusive(x_627);
if (x_628 == 0)
{
lean_object* x_629; 
x_629 = lean_ctor_get(x_627, 0);
lean_dec(x_629);
lean_ctor_set_tag(x_627, 1);
lean_ctor_set(x_627, 0, x_610);
return x_627;
}
else
{
lean_object* x_630; lean_object* x_631; 
x_630 = lean_ctor_get(x_627, 1);
lean_inc(x_630);
lean_dec(x_627);
x_631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_631, 0, x_610);
lean_ctor_set(x_631, 1, x_630);
return x_631;
}
}
}
}
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_678; lean_object* x_679; 
x_650 = lean_box(0);
x_651 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
if (lean_is_exclusive(x_651)) {
 lean_ctor_release(x_651, 0);
 lean_ctor_release(x_651, 1);
 x_654 = x_651;
} else {
 lean_dec_ref(x_651);
 x_654 = lean_box(0);
}
x_678 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_679 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_369, x_678, x_650, x_10, x_11, x_12, x_13, x_14, x_15, x_653);
if (lean_obj_tag(x_679) == 0)
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; uint8_t x_686; 
lean_dec(x_654);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_679, 1);
lean_inc(x_681);
lean_dec(x_679);
x_682 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_681);
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_682, 1);
lean_inc(x_684);
lean_dec(x_682);
x_685 = l_Lean_Elab_Term_SavedState_restore(x_652, x_10, x_11, x_12, x_13, x_14, x_15, x_684);
x_686 = !lean_is_exclusive(x_685);
if (x_686 == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_687 = lean_ctor_get(x_685, 1);
x_688 = lean_ctor_get(x_685, 0);
lean_dec(x_688);
lean_ctor_set(x_685, 1, x_683);
lean_ctor_set(x_685, 0, x_680);
x_689 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_685, x_10, x_11, x_12, x_13, x_14, x_15, x_687);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_689;
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_690 = lean_ctor_get(x_685, 1);
lean_inc(x_690);
lean_dec(x_685);
x_691 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_691, 0, x_680);
lean_ctor_set(x_691, 1, x_683);
x_692 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_691, x_10, x_11, x_12, x_13, x_14, x_15, x_690);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_692;
}
}
else
{
lean_object* x_693; lean_object* x_694; 
x_693 = lean_ctor_get(x_679, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_679, 1);
lean_inc(x_694);
lean_dec(x_679);
x_655 = x_693;
x_656 = x_694;
goto block_677;
}
block_677:
{
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; uint8_t x_661; 
lean_dec(x_654);
x_657 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_656);
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
lean_dec(x_657);
x_660 = l_Lean_Elab_Term_SavedState_restore(x_652, x_10, x_11, x_12, x_13, x_14, x_15, x_659);
x_661 = !lean_is_exclusive(x_660);
if (x_661 == 0)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_662 = lean_ctor_get(x_660, 1);
x_663 = lean_ctor_get(x_660, 0);
lean_dec(x_663);
lean_ctor_set_tag(x_660, 1);
lean_ctor_set(x_660, 1, x_658);
lean_ctor_set(x_660, 0, x_655);
x_664 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_660, x_10, x_11, x_12, x_13, x_14, x_15, x_662);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_664;
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_660, 1);
lean_inc(x_665);
lean_dec(x_660);
x_666 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_666, 0, x_655);
lean_ctor_set(x_666, 1, x_658);
x_667 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_666, x_10, x_11, x_12, x_13, x_14, x_15, x_665);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_667;
}
}
else
{
lean_object* x_668; lean_object* x_669; uint8_t x_670; 
lean_dec(x_9);
x_668 = lean_ctor_get(x_655, 0);
lean_inc(x_668);
x_669 = l_Lean_Elab_postponeExceptionId;
x_670 = lean_nat_dec_eq(x_668, x_669);
lean_dec(x_668);
if (x_670 == 0)
{
lean_object* x_671; 
lean_dec(x_652);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_654)) {
 x_671 = lean_alloc_ctor(1, 2, 0);
} else {
 x_671 = x_654;
 lean_ctor_set_tag(x_671, 1);
}
lean_ctor_set(x_671, 0, x_655);
lean_ctor_set(x_671, 1, x_656);
return x_671;
}
else
{
lean_object* x_672; uint8_t x_673; 
lean_dec(x_654);
x_672 = l_Lean_Elab_Term_SavedState_restore(x_652, x_10, x_11, x_12, x_13, x_14, x_15, x_656);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_673 = !lean_is_exclusive(x_672);
if (x_673 == 0)
{
lean_object* x_674; 
x_674 = lean_ctor_get(x_672, 0);
lean_dec(x_674);
lean_ctor_set_tag(x_672, 1);
lean_ctor_set(x_672, 0, x_655);
return x_672;
}
else
{
lean_object* x_675; lean_object* x_676; 
x_675 = lean_ctor_get(x_672, 1);
lean_inc(x_675);
lean_dec(x_672);
x_676 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_676, 0, x_655);
lean_ctor_set(x_676, 1, x_675);
return x_676;
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
else
{
lean_object* x_698; lean_object* x_699; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_698 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__2;
x_699 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1(x_698, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_699;
}
}
else
{
lean_object* x_700; lean_object* x_701; uint8_t x_702; 
x_700 = lean_unsigned_to_nat(1u);
x_701 = l_Lean_Syntax_getArg(x_1, x_700);
lean_inc(x_701);
x_702 = l_Lean_Syntax_isOfKind(x_701, x_360);
if (x_702 == 0)
{
uint8_t x_703; 
lean_inc(x_701);
x_703 = l_Lean_Syntax_isOfKind(x_701, x_362);
if (x_703 == 0)
{
lean_object* x_704; 
lean_dec(x_701);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_704 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2___rarg(x_16);
return x_704;
}
else
{
lean_object* x_705; lean_object* x_706; uint8_t x_707; 
x_705 = lean_unsigned_to_nat(0u);
x_706 = l_Lean_Syntax_getArg(x_701, x_705);
lean_dec(x_701);
x_707 = l_Lean_Syntax_isOfKind(x_706, x_360);
if (x_707 == 0)
{
lean_object* x_708; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_708 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2___rarg(x_16);
return x_708;
}
else
{
lean_object* x_709; uint8_t x_710; 
x_709 = l_Lean_Syntax_getArg(x_1, x_700);
lean_dec(x_1);
x_710 = 1;
x_1 = x_709;
x_6 = x_710;
goto _start;
}
}
}
else
{
uint8_t x_712; 
lean_dec(x_1);
x_712 = 1;
x_1 = x_701;
x_6 = x_712;
goto _start;
}
}
}
else
{
lean_object* x_714; lean_object* x_715; uint8_t x_716; 
x_714 = lean_unsigned_to_nat(0u);
x_715 = l_Lean_Syntax_getArg(x_1, x_714);
lean_inc(x_715);
x_716 = l_Lean_Syntax_isOfKind(x_715, x_360);
if (x_716 == 0)
{
uint8_t x_717; uint8_t x_718; 
lean_dec(x_715);
x_717 = l_List_isEmpty___rarg(x_2);
if (x_8 == 0)
{
uint8_t x_1045; 
x_1045 = 1;
x_718 = x_1045;
goto block_1044;
}
else
{
uint8_t x_1046; 
x_1046 = 0;
x_718 = x_1046;
goto block_1044;
}
block_1044:
{
if (x_717 == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_756; lean_object* x_757; uint8_t x_779; lean_object* x_780; 
x_719 = lean_box(0);
x_720 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_720, 1);
lean_inc(x_722);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 lean_ctor_release(x_720, 1);
 x_723 = x_720;
} else {
 lean_dec_ref(x_720);
 x_723 = lean_box(0);
}
x_779 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_780 = l_Lean_Elab_Term_elabTerm(x_1, x_719, x_718, x_779, x_10, x_11, x_12, x_13, x_14, x_15, x_722);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
lean_dec(x_780);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_783 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_781, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_782);
if (lean_obj_tag(x_783) == 0)
{
if (x_8 == 0)
{
lean_object* x_784; lean_object* x_785; 
lean_dec(x_723);
lean_dec(x_5);
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
lean_dec(x_783);
x_756 = x_784;
x_757 = x_785;
goto block_778;
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_786 = lean_ctor_get(x_783, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_783, 1);
lean_inc(x_787);
lean_dec(x_783);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_788 = l_Lean_Elab_Term_ensureHasType(x_5, x_786, x_719, x_10, x_11, x_12, x_13, x_14, x_15, x_787);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; lean_object* x_790; 
lean_dec(x_723);
x_789 = lean_ctor_get(x_788, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_788, 1);
lean_inc(x_790);
lean_dec(x_788);
x_756 = x_789;
x_757 = x_790;
goto block_778;
}
else
{
lean_object* x_791; lean_object* x_792; 
x_791 = lean_ctor_get(x_788, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_788, 1);
lean_inc(x_792);
lean_dec(x_788);
x_724 = x_791;
x_725 = x_792;
goto block_755;
}
}
}
else
{
lean_object* x_793; lean_object* x_794; 
lean_dec(x_5);
x_793 = lean_ctor_get(x_783, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_783, 1);
lean_inc(x_794);
lean_dec(x_783);
x_724 = x_793;
x_725 = x_794;
goto block_755;
}
}
else
{
lean_object* x_795; lean_object* x_796; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_795 = lean_ctor_get(x_780, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_780, 1);
lean_inc(x_796);
lean_dec(x_780);
x_724 = x_795;
x_725 = x_796;
goto block_755;
}
block_755:
{
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_726; uint8_t x_727; 
lean_dec(x_723);
x_726 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_725);
x_727 = !lean_is_exclusive(x_726);
if (x_727 == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; uint8_t x_731; 
x_728 = lean_ctor_get(x_726, 0);
x_729 = lean_ctor_get(x_726, 1);
x_730 = l_Lean_Elab_Term_SavedState_restore(x_721, x_10, x_11, x_12, x_13, x_14, x_15, x_729);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_731 = !lean_is_exclusive(x_730);
if (x_731 == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_732 = lean_ctor_get(x_730, 1);
x_733 = lean_ctor_get(x_730, 0);
lean_dec(x_733);
lean_ctor_set_tag(x_730, 1);
lean_ctor_set(x_730, 1, x_728);
lean_ctor_set(x_730, 0, x_724);
x_734 = lean_array_push(x_9, x_730);
lean_ctor_set(x_726, 1, x_732);
lean_ctor_set(x_726, 0, x_734);
return x_726;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_735 = lean_ctor_get(x_730, 1);
lean_inc(x_735);
lean_dec(x_730);
x_736 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_736, 0, x_724);
lean_ctor_set(x_736, 1, x_728);
x_737 = lean_array_push(x_9, x_736);
lean_ctor_set(x_726, 1, x_735);
lean_ctor_set(x_726, 0, x_737);
return x_726;
}
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_738 = lean_ctor_get(x_726, 0);
x_739 = lean_ctor_get(x_726, 1);
lean_inc(x_739);
lean_inc(x_738);
lean_dec(x_726);
x_740 = l_Lean_Elab_Term_SavedState_restore(x_721, x_10, x_11, x_12, x_13, x_14, x_15, x_739);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_741 = lean_ctor_get(x_740, 1);
lean_inc(x_741);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 lean_ctor_release(x_740, 1);
 x_742 = x_740;
} else {
 lean_dec_ref(x_740);
 x_742 = lean_box(0);
}
if (lean_is_scalar(x_742)) {
 x_743 = lean_alloc_ctor(1, 2, 0);
} else {
 x_743 = x_742;
 lean_ctor_set_tag(x_743, 1);
}
lean_ctor_set(x_743, 0, x_724);
lean_ctor_set(x_743, 1, x_738);
x_744 = lean_array_push(x_9, x_743);
x_745 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_745, 0, x_744);
lean_ctor_set(x_745, 1, x_741);
return x_745;
}
}
else
{
lean_object* x_746; lean_object* x_747; uint8_t x_748; 
lean_dec(x_9);
x_746 = lean_ctor_get(x_724, 0);
lean_inc(x_746);
x_747 = l_Lean_Elab_postponeExceptionId;
x_748 = lean_nat_dec_eq(x_746, x_747);
lean_dec(x_746);
if (x_748 == 0)
{
lean_object* x_749; 
lean_dec(x_721);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_723)) {
 x_749 = lean_alloc_ctor(1, 2, 0);
} else {
 x_749 = x_723;
 lean_ctor_set_tag(x_749, 1);
}
lean_ctor_set(x_749, 0, x_724);
lean_ctor_set(x_749, 1, x_725);
return x_749;
}
else
{
lean_object* x_750; uint8_t x_751; 
lean_dec(x_723);
x_750 = l_Lean_Elab_Term_SavedState_restore(x_721, x_10, x_11, x_12, x_13, x_14, x_15, x_725);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_751 = !lean_is_exclusive(x_750);
if (x_751 == 0)
{
lean_object* x_752; 
x_752 = lean_ctor_get(x_750, 0);
lean_dec(x_752);
lean_ctor_set_tag(x_750, 1);
lean_ctor_set(x_750, 0, x_724);
return x_750;
}
else
{
lean_object* x_753; lean_object* x_754; 
x_753 = lean_ctor_get(x_750, 1);
lean_inc(x_753);
lean_dec(x_750);
x_754 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_754, 0, x_724);
lean_ctor_set(x_754, 1, x_753);
return x_754;
}
}
}
}
block_778:
{
lean_object* x_758; uint8_t x_759; 
x_758 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_757);
x_759 = !lean_is_exclusive(x_758);
if (x_759 == 0)
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; uint8_t x_763; 
x_760 = lean_ctor_get(x_758, 0);
x_761 = lean_ctor_get(x_758, 1);
x_762 = l_Lean_Elab_Term_SavedState_restore(x_721, x_10, x_11, x_12, x_13, x_14, x_15, x_761);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_763 = !lean_is_exclusive(x_762);
if (x_763 == 0)
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_764 = lean_ctor_get(x_762, 1);
x_765 = lean_ctor_get(x_762, 0);
lean_dec(x_765);
lean_ctor_set(x_762, 1, x_760);
lean_ctor_set(x_762, 0, x_756);
x_766 = lean_array_push(x_9, x_762);
lean_ctor_set(x_758, 1, x_764);
lean_ctor_set(x_758, 0, x_766);
return x_758;
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_767 = lean_ctor_get(x_762, 1);
lean_inc(x_767);
lean_dec(x_762);
x_768 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_768, 0, x_756);
lean_ctor_set(x_768, 1, x_760);
x_769 = lean_array_push(x_9, x_768);
lean_ctor_set(x_758, 1, x_767);
lean_ctor_set(x_758, 0, x_769);
return x_758;
}
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; 
x_770 = lean_ctor_get(x_758, 0);
x_771 = lean_ctor_get(x_758, 1);
lean_inc(x_771);
lean_inc(x_770);
lean_dec(x_758);
x_772 = l_Lean_Elab_Term_SavedState_restore(x_721, x_10, x_11, x_12, x_13, x_14, x_15, x_771);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_773 = lean_ctor_get(x_772, 1);
lean_inc(x_773);
if (lean_is_exclusive(x_772)) {
 lean_ctor_release(x_772, 0);
 lean_ctor_release(x_772, 1);
 x_774 = x_772;
} else {
 lean_dec_ref(x_772);
 x_774 = lean_box(0);
}
if (lean_is_scalar(x_774)) {
 x_775 = lean_alloc_ctor(0, 2, 0);
} else {
 x_775 = x_774;
}
lean_ctor_set(x_775, 0, x_756);
lean_ctor_set(x_775, 1, x_770);
x_776 = lean_array_push(x_9, x_775);
x_777 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_777, 0, x_776);
lean_ctor_set(x_777, 1, x_773);
return x_777;
}
}
}
else
{
uint8_t x_797; 
x_797 = l_Array_isEmpty___rarg(x_3);
if (x_797 == 0)
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_835; lean_object* x_836; uint8_t x_858; lean_object* x_859; 
x_798 = lean_box(0);
x_799 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_800 = lean_ctor_get(x_799, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_799, 1);
lean_inc(x_801);
if (lean_is_exclusive(x_799)) {
 lean_ctor_release(x_799, 0);
 lean_ctor_release(x_799, 1);
 x_802 = x_799;
} else {
 lean_dec_ref(x_799);
 x_802 = lean_box(0);
}
x_858 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_859 = l_Lean_Elab_Term_elabTerm(x_1, x_798, x_718, x_858, x_10, x_11, x_12, x_13, x_14, x_15, x_801);
if (lean_obj_tag(x_859) == 0)
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; 
x_860 = lean_ctor_get(x_859, 0);
lean_inc(x_860);
x_861 = lean_ctor_get(x_859, 1);
lean_inc(x_861);
lean_dec(x_859);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_862 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_860, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_861);
if (lean_obj_tag(x_862) == 0)
{
if (x_8 == 0)
{
lean_object* x_863; lean_object* x_864; 
lean_dec(x_802);
lean_dec(x_5);
x_863 = lean_ctor_get(x_862, 0);
lean_inc(x_863);
x_864 = lean_ctor_get(x_862, 1);
lean_inc(x_864);
lean_dec(x_862);
x_835 = x_863;
x_836 = x_864;
goto block_857;
}
else
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_865 = lean_ctor_get(x_862, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_862, 1);
lean_inc(x_866);
lean_dec(x_862);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_867 = l_Lean_Elab_Term_ensureHasType(x_5, x_865, x_798, x_10, x_11, x_12, x_13, x_14, x_15, x_866);
if (lean_obj_tag(x_867) == 0)
{
lean_object* x_868; lean_object* x_869; 
lean_dec(x_802);
x_868 = lean_ctor_get(x_867, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_867, 1);
lean_inc(x_869);
lean_dec(x_867);
x_835 = x_868;
x_836 = x_869;
goto block_857;
}
else
{
lean_object* x_870; lean_object* x_871; 
x_870 = lean_ctor_get(x_867, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_867, 1);
lean_inc(x_871);
lean_dec(x_867);
x_803 = x_870;
x_804 = x_871;
goto block_834;
}
}
}
else
{
lean_object* x_872; lean_object* x_873; 
lean_dec(x_5);
x_872 = lean_ctor_get(x_862, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_862, 1);
lean_inc(x_873);
lean_dec(x_862);
x_803 = x_872;
x_804 = x_873;
goto block_834;
}
}
else
{
lean_object* x_874; lean_object* x_875; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_874 = lean_ctor_get(x_859, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_859, 1);
lean_inc(x_875);
lean_dec(x_859);
x_803 = x_874;
x_804 = x_875;
goto block_834;
}
block_834:
{
if (lean_obj_tag(x_803) == 0)
{
lean_object* x_805; uint8_t x_806; 
lean_dec(x_802);
x_805 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_804);
x_806 = !lean_is_exclusive(x_805);
if (x_806 == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; uint8_t x_810; 
x_807 = lean_ctor_get(x_805, 0);
x_808 = lean_ctor_get(x_805, 1);
x_809 = l_Lean_Elab_Term_SavedState_restore(x_800, x_10, x_11, x_12, x_13, x_14, x_15, x_808);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_810 = !lean_is_exclusive(x_809);
if (x_810 == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; 
x_811 = lean_ctor_get(x_809, 1);
x_812 = lean_ctor_get(x_809, 0);
lean_dec(x_812);
lean_ctor_set_tag(x_809, 1);
lean_ctor_set(x_809, 1, x_807);
lean_ctor_set(x_809, 0, x_803);
x_813 = lean_array_push(x_9, x_809);
lean_ctor_set(x_805, 1, x_811);
lean_ctor_set(x_805, 0, x_813);
return x_805;
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_814 = lean_ctor_get(x_809, 1);
lean_inc(x_814);
lean_dec(x_809);
x_815 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_815, 0, x_803);
lean_ctor_set(x_815, 1, x_807);
x_816 = lean_array_push(x_9, x_815);
lean_ctor_set(x_805, 1, x_814);
lean_ctor_set(x_805, 0, x_816);
return x_805;
}
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_817 = lean_ctor_get(x_805, 0);
x_818 = lean_ctor_get(x_805, 1);
lean_inc(x_818);
lean_inc(x_817);
lean_dec(x_805);
x_819 = l_Lean_Elab_Term_SavedState_restore(x_800, x_10, x_11, x_12, x_13, x_14, x_15, x_818);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_820 = lean_ctor_get(x_819, 1);
lean_inc(x_820);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_821 = x_819;
} else {
 lean_dec_ref(x_819);
 x_821 = lean_box(0);
}
if (lean_is_scalar(x_821)) {
 x_822 = lean_alloc_ctor(1, 2, 0);
} else {
 x_822 = x_821;
 lean_ctor_set_tag(x_822, 1);
}
lean_ctor_set(x_822, 0, x_803);
lean_ctor_set(x_822, 1, x_817);
x_823 = lean_array_push(x_9, x_822);
x_824 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_824, 0, x_823);
lean_ctor_set(x_824, 1, x_820);
return x_824;
}
}
else
{
lean_object* x_825; lean_object* x_826; uint8_t x_827; 
lean_dec(x_9);
x_825 = lean_ctor_get(x_803, 0);
lean_inc(x_825);
x_826 = l_Lean_Elab_postponeExceptionId;
x_827 = lean_nat_dec_eq(x_825, x_826);
lean_dec(x_825);
if (x_827 == 0)
{
lean_object* x_828; 
lean_dec(x_800);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_802)) {
 x_828 = lean_alloc_ctor(1, 2, 0);
} else {
 x_828 = x_802;
 lean_ctor_set_tag(x_828, 1);
}
lean_ctor_set(x_828, 0, x_803);
lean_ctor_set(x_828, 1, x_804);
return x_828;
}
else
{
lean_object* x_829; uint8_t x_830; 
lean_dec(x_802);
x_829 = l_Lean_Elab_Term_SavedState_restore(x_800, x_10, x_11, x_12, x_13, x_14, x_15, x_804);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_830 = !lean_is_exclusive(x_829);
if (x_830 == 0)
{
lean_object* x_831; 
x_831 = lean_ctor_get(x_829, 0);
lean_dec(x_831);
lean_ctor_set_tag(x_829, 1);
lean_ctor_set(x_829, 0, x_803);
return x_829;
}
else
{
lean_object* x_832; lean_object* x_833; 
x_832 = lean_ctor_get(x_829, 1);
lean_inc(x_832);
lean_dec(x_829);
x_833 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_833, 0, x_803);
lean_ctor_set(x_833, 1, x_832);
return x_833;
}
}
}
}
block_857:
{
lean_object* x_837; uint8_t x_838; 
x_837 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_836);
x_838 = !lean_is_exclusive(x_837);
if (x_838 == 0)
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; uint8_t x_842; 
x_839 = lean_ctor_get(x_837, 0);
x_840 = lean_ctor_get(x_837, 1);
x_841 = l_Lean_Elab_Term_SavedState_restore(x_800, x_10, x_11, x_12, x_13, x_14, x_15, x_840);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_842 = !lean_is_exclusive(x_841);
if (x_842 == 0)
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_843 = lean_ctor_get(x_841, 1);
x_844 = lean_ctor_get(x_841, 0);
lean_dec(x_844);
lean_ctor_set(x_841, 1, x_839);
lean_ctor_set(x_841, 0, x_835);
x_845 = lean_array_push(x_9, x_841);
lean_ctor_set(x_837, 1, x_843);
lean_ctor_set(x_837, 0, x_845);
return x_837;
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_846 = lean_ctor_get(x_841, 1);
lean_inc(x_846);
lean_dec(x_841);
x_847 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_847, 0, x_835);
lean_ctor_set(x_847, 1, x_839);
x_848 = lean_array_push(x_9, x_847);
lean_ctor_set(x_837, 1, x_846);
lean_ctor_set(x_837, 0, x_848);
return x_837;
}
}
else
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
x_849 = lean_ctor_get(x_837, 0);
x_850 = lean_ctor_get(x_837, 1);
lean_inc(x_850);
lean_inc(x_849);
lean_dec(x_837);
x_851 = l_Lean_Elab_Term_SavedState_restore(x_800, x_10, x_11, x_12, x_13, x_14, x_15, x_850);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_852 = lean_ctor_get(x_851, 1);
lean_inc(x_852);
if (lean_is_exclusive(x_851)) {
 lean_ctor_release(x_851, 0);
 lean_ctor_release(x_851, 1);
 x_853 = x_851;
} else {
 lean_dec_ref(x_851);
 x_853 = lean_box(0);
}
if (lean_is_scalar(x_853)) {
 x_854 = lean_alloc_ctor(0, 2, 0);
} else {
 x_854 = x_853;
}
lean_ctor_set(x_854, 0, x_835);
lean_ctor_set(x_854, 1, x_849);
x_855 = lean_array_push(x_9, x_854);
x_856 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_852);
return x_856;
}
}
}
else
{
uint8_t x_876; 
x_876 = l_Array_isEmpty___rarg(x_4);
if (x_876 == 0)
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_914; lean_object* x_915; uint8_t x_937; lean_object* x_938; 
x_877 = lean_box(0);
x_878 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 x_881 = x_878;
} else {
 lean_dec_ref(x_878);
 x_881 = lean_box(0);
}
x_937 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_938 = l_Lean_Elab_Term_elabTerm(x_1, x_877, x_718, x_937, x_10, x_11, x_12, x_13, x_14, x_15, x_880);
if (lean_obj_tag(x_938) == 0)
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; 
x_939 = lean_ctor_get(x_938, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_938, 1);
lean_inc(x_940);
lean_dec(x_938);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_941 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_939, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_940);
if (lean_obj_tag(x_941) == 0)
{
if (x_8 == 0)
{
lean_object* x_942; lean_object* x_943; 
lean_dec(x_881);
lean_dec(x_5);
x_942 = lean_ctor_get(x_941, 0);
lean_inc(x_942);
x_943 = lean_ctor_get(x_941, 1);
lean_inc(x_943);
lean_dec(x_941);
x_914 = x_942;
x_915 = x_943;
goto block_936;
}
else
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; 
x_944 = lean_ctor_get(x_941, 0);
lean_inc(x_944);
x_945 = lean_ctor_get(x_941, 1);
lean_inc(x_945);
lean_dec(x_941);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_946 = l_Lean_Elab_Term_ensureHasType(x_5, x_944, x_877, x_10, x_11, x_12, x_13, x_14, x_15, x_945);
if (lean_obj_tag(x_946) == 0)
{
lean_object* x_947; lean_object* x_948; 
lean_dec(x_881);
x_947 = lean_ctor_get(x_946, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_946, 1);
lean_inc(x_948);
lean_dec(x_946);
x_914 = x_947;
x_915 = x_948;
goto block_936;
}
else
{
lean_object* x_949; lean_object* x_950; 
x_949 = lean_ctor_get(x_946, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_946, 1);
lean_inc(x_950);
lean_dec(x_946);
x_882 = x_949;
x_883 = x_950;
goto block_913;
}
}
}
else
{
lean_object* x_951; lean_object* x_952; 
lean_dec(x_5);
x_951 = lean_ctor_get(x_941, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_941, 1);
lean_inc(x_952);
lean_dec(x_941);
x_882 = x_951;
x_883 = x_952;
goto block_913;
}
}
else
{
lean_object* x_953; lean_object* x_954; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_953 = lean_ctor_get(x_938, 0);
lean_inc(x_953);
x_954 = lean_ctor_get(x_938, 1);
lean_inc(x_954);
lean_dec(x_938);
x_882 = x_953;
x_883 = x_954;
goto block_913;
}
block_913:
{
if (lean_obj_tag(x_882) == 0)
{
lean_object* x_884; uint8_t x_885; 
lean_dec(x_881);
x_884 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_883);
x_885 = !lean_is_exclusive(x_884);
if (x_885 == 0)
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; uint8_t x_889; 
x_886 = lean_ctor_get(x_884, 0);
x_887 = lean_ctor_get(x_884, 1);
x_888 = l_Lean_Elab_Term_SavedState_restore(x_879, x_10, x_11, x_12, x_13, x_14, x_15, x_887);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_889 = !lean_is_exclusive(x_888);
if (x_889 == 0)
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; 
x_890 = lean_ctor_get(x_888, 1);
x_891 = lean_ctor_get(x_888, 0);
lean_dec(x_891);
lean_ctor_set_tag(x_888, 1);
lean_ctor_set(x_888, 1, x_886);
lean_ctor_set(x_888, 0, x_882);
x_892 = lean_array_push(x_9, x_888);
lean_ctor_set(x_884, 1, x_890);
lean_ctor_set(x_884, 0, x_892);
return x_884;
}
else
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; 
x_893 = lean_ctor_get(x_888, 1);
lean_inc(x_893);
lean_dec(x_888);
x_894 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_894, 0, x_882);
lean_ctor_set(x_894, 1, x_886);
x_895 = lean_array_push(x_9, x_894);
lean_ctor_set(x_884, 1, x_893);
lean_ctor_set(x_884, 0, x_895);
return x_884;
}
}
else
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; 
x_896 = lean_ctor_get(x_884, 0);
x_897 = lean_ctor_get(x_884, 1);
lean_inc(x_897);
lean_inc(x_896);
lean_dec(x_884);
x_898 = l_Lean_Elab_Term_SavedState_restore(x_879, x_10, x_11, x_12, x_13, x_14, x_15, x_897);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_899 = lean_ctor_get(x_898, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_900 = x_898;
} else {
 lean_dec_ref(x_898);
 x_900 = lean_box(0);
}
if (lean_is_scalar(x_900)) {
 x_901 = lean_alloc_ctor(1, 2, 0);
} else {
 x_901 = x_900;
 lean_ctor_set_tag(x_901, 1);
}
lean_ctor_set(x_901, 0, x_882);
lean_ctor_set(x_901, 1, x_896);
x_902 = lean_array_push(x_9, x_901);
x_903 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_903, 0, x_902);
lean_ctor_set(x_903, 1, x_899);
return x_903;
}
}
else
{
lean_object* x_904; lean_object* x_905; uint8_t x_906; 
lean_dec(x_9);
x_904 = lean_ctor_get(x_882, 0);
lean_inc(x_904);
x_905 = l_Lean_Elab_postponeExceptionId;
x_906 = lean_nat_dec_eq(x_904, x_905);
lean_dec(x_904);
if (x_906 == 0)
{
lean_object* x_907; 
lean_dec(x_879);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_881)) {
 x_907 = lean_alloc_ctor(1, 2, 0);
} else {
 x_907 = x_881;
 lean_ctor_set_tag(x_907, 1);
}
lean_ctor_set(x_907, 0, x_882);
lean_ctor_set(x_907, 1, x_883);
return x_907;
}
else
{
lean_object* x_908; uint8_t x_909; 
lean_dec(x_881);
x_908 = l_Lean_Elab_Term_SavedState_restore(x_879, x_10, x_11, x_12, x_13, x_14, x_15, x_883);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_909 = !lean_is_exclusive(x_908);
if (x_909 == 0)
{
lean_object* x_910; 
x_910 = lean_ctor_get(x_908, 0);
lean_dec(x_910);
lean_ctor_set_tag(x_908, 1);
lean_ctor_set(x_908, 0, x_882);
return x_908;
}
else
{
lean_object* x_911; lean_object* x_912; 
x_911 = lean_ctor_get(x_908, 1);
lean_inc(x_911);
lean_dec(x_908);
x_912 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_912, 0, x_882);
lean_ctor_set(x_912, 1, x_911);
return x_912;
}
}
}
}
block_936:
{
lean_object* x_916; uint8_t x_917; 
x_916 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_915);
x_917 = !lean_is_exclusive(x_916);
if (x_917 == 0)
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; uint8_t x_921; 
x_918 = lean_ctor_get(x_916, 0);
x_919 = lean_ctor_get(x_916, 1);
x_920 = l_Lean_Elab_Term_SavedState_restore(x_879, x_10, x_11, x_12, x_13, x_14, x_15, x_919);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_921 = !lean_is_exclusive(x_920);
if (x_921 == 0)
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; 
x_922 = lean_ctor_get(x_920, 1);
x_923 = lean_ctor_get(x_920, 0);
lean_dec(x_923);
lean_ctor_set(x_920, 1, x_918);
lean_ctor_set(x_920, 0, x_914);
x_924 = lean_array_push(x_9, x_920);
lean_ctor_set(x_916, 1, x_922);
lean_ctor_set(x_916, 0, x_924);
return x_916;
}
else
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; 
x_925 = lean_ctor_get(x_920, 1);
lean_inc(x_925);
lean_dec(x_920);
x_926 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_926, 0, x_914);
lean_ctor_set(x_926, 1, x_918);
x_927 = lean_array_push(x_9, x_926);
lean_ctor_set(x_916, 1, x_925);
lean_ctor_set(x_916, 0, x_927);
return x_916;
}
}
else
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_928 = lean_ctor_get(x_916, 0);
x_929 = lean_ctor_get(x_916, 1);
lean_inc(x_929);
lean_inc(x_928);
lean_dec(x_916);
x_930 = l_Lean_Elab_Term_SavedState_restore(x_879, x_10, x_11, x_12, x_13, x_14, x_15, x_929);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_931 = lean_ctor_get(x_930, 1);
lean_inc(x_931);
if (lean_is_exclusive(x_930)) {
 lean_ctor_release(x_930, 0);
 lean_ctor_release(x_930, 1);
 x_932 = x_930;
} else {
 lean_dec_ref(x_930);
 x_932 = lean_box(0);
}
if (lean_is_scalar(x_932)) {
 x_933 = lean_alloc_ctor(0, 2, 0);
} else {
 x_933 = x_932;
}
lean_ctor_set(x_933, 0, x_914);
lean_ctor_set(x_933, 1, x_928);
x_934 = lean_array_push(x_9, x_933);
x_935 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_935, 0, x_934);
lean_ctor_set(x_935, 1, x_931);
return x_935;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_8 == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; uint8_t x_982; lean_object* x_983; 
x_955 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_956 = lean_ctor_get(x_955, 0);
lean_inc(x_956);
x_957 = lean_ctor_get(x_955, 1);
lean_inc(x_957);
if (lean_is_exclusive(x_955)) {
 lean_ctor_release(x_955, 0);
 lean_ctor_release(x_955, 1);
 x_958 = x_955;
} else {
 lean_dec_ref(x_955);
 x_958 = lean_box(0);
}
x_982 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_983 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_982, x_982, x_10, x_11, x_12, x_13, x_14, x_15, x_957);
if (lean_obj_tag(x_983) == 0)
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; uint8_t x_990; 
lean_dec(x_958);
x_984 = lean_ctor_get(x_983, 0);
lean_inc(x_984);
x_985 = lean_ctor_get(x_983, 1);
lean_inc(x_985);
lean_dec(x_983);
x_986 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_985);
x_987 = lean_ctor_get(x_986, 0);
lean_inc(x_987);
x_988 = lean_ctor_get(x_986, 1);
lean_inc(x_988);
lean_dec(x_986);
x_989 = l_Lean_Elab_Term_SavedState_restore(x_956, x_10, x_11, x_12, x_13, x_14, x_15, x_988);
x_990 = !lean_is_exclusive(x_989);
if (x_990 == 0)
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_991 = lean_ctor_get(x_989, 1);
x_992 = lean_ctor_get(x_989, 0);
lean_dec(x_992);
lean_ctor_set(x_989, 1, x_987);
lean_ctor_set(x_989, 0, x_984);
x_993 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_989, x_10, x_11, x_12, x_13, x_14, x_15, x_991);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_993;
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; 
x_994 = lean_ctor_get(x_989, 1);
lean_inc(x_994);
lean_dec(x_989);
x_995 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_995, 0, x_984);
lean_ctor_set(x_995, 1, x_987);
x_996 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_995, x_10, x_11, x_12, x_13, x_14, x_15, x_994);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_996;
}
}
else
{
lean_object* x_997; lean_object* x_998; 
x_997 = lean_ctor_get(x_983, 0);
lean_inc(x_997);
x_998 = lean_ctor_get(x_983, 1);
lean_inc(x_998);
lean_dec(x_983);
x_959 = x_997;
x_960 = x_998;
goto block_981;
}
block_981:
{
if (lean_obj_tag(x_959) == 0)
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; uint8_t x_965; 
lean_dec(x_958);
x_961 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_960);
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_961, 1);
lean_inc(x_963);
lean_dec(x_961);
x_964 = l_Lean_Elab_Term_SavedState_restore(x_956, x_10, x_11, x_12, x_13, x_14, x_15, x_963);
x_965 = !lean_is_exclusive(x_964);
if (x_965 == 0)
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; 
x_966 = lean_ctor_get(x_964, 1);
x_967 = lean_ctor_get(x_964, 0);
lean_dec(x_967);
lean_ctor_set_tag(x_964, 1);
lean_ctor_set(x_964, 1, x_962);
lean_ctor_set(x_964, 0, x_959);
x_968 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_964, x_10, x_11, x_12, x_13, x_14, x_15, x_966);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_968;
}
else
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; 
x_969 = lean_ctor_get(x_964, 1);
lean_inc(x_969);
lean_dec(x_964);
x_970 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_970, 0, x_959);
lean_ctor_set(x_970, 1, x_962);
x_971 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_970, x_10, x_11, x_12, x_13, x_14, x_15, x_969);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_971;
}
}
else
{
lean_object* x_972; lean_object* x_973; uint8_t x_974; 
lean_dec(x_9);
x_972 = lean_ctor_get(x_959, 0);
lean_inc(x_972);
x_973 = l_Lean_Elab_postponeExceptionId;
x_974 = lean_nat_dec_eq(x_972, x_973);
lean_dec(x_972);
if (x_974 == 0)
{
lean_object* x_975; 
lean_dec(x_956);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_958)) {
 x_975 = lean_alloc_ctor(1, 2, 0);
} else {
 x_975 = x_958;
 lean_ctor_set_tag(x_975, 1);
}
lean_ctor_set(x_975, 0, x_959);
lean_ctor_set(x_975, 1, x_960);
return x_975;
}
else
{
lean_object* x_976; uint8_t x_977; 
lean_dec(x_958);
x_976 = l_Lean_Elab_Term_SavedState_restore(x_956, x_10, x_11, x_12, x_13, x_14, x_15, x_960);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_977 = !lean_is_exclusive(x_976);
if (x_977 == 0)
{
lean_object* x_978; 
x_978 = lean_ctor_get(x_976, 0);
lean_dec(x_978);
lean_ctor_set_tag(x_976, 1);
lean_ctor_set(x_976, 0, x_959);
return x_976;
}
else
{
lean_object* x_979; lean_object* x_980; 
x_979 = lean_ctor_get(x_976, 1);
lean_inc(x_979);
lean_dec(x_976);
x_980 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_980, 0, x_959);
lean_ctor_set(x_980, 1, x_979);
return x_980;
}
}
}
}
}
else
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; uint8_t x_1027; lean_object* x_1028; 
x_999 = lean_box(0);
x_1000 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_1001 = lean_ctor_get(x_1000, 0);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_1000, 1);
lean_inc(x_1002);
if (lean_is_exclusive(x_1000)) {
 lean_ctor_release(x_1000, 0);
 lean_ctor_release(x_1000, 1);
 x_1003 = x_1000;
} else {
 lean_dec_ref(x_1000);
 x_1003 = lean_box(0);
}
x_1027 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1028 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_718, x_1027, x_999, x_10, x_11, x_12, x_13, x_14, x_15, x_1002);
if (lean_obj_tag(x_1028) == 0)
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; uint8_t x_1035; 
lean_dec(x_1003);
x_1029 = lean_ctor_get(x_1028, 0);
lean_inc(x_1029);
x_1030 = lean_ctor_get(x_1028, 1);
lean_inc(x_1030);
lean_dec(x_1028);
x_1031 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1030);
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
x_1033 = lean_ctor_get(x_1031, 1);
lean_inc(x_1033);
lean_dec(x_1031);
x_1034 = l_Lean_Elab_Term_SavedState_restore(x_1001, x_10, x_11, x_12, x_13, x_14, x_15, x_1033);
x_1035 = !lean_is_exclusive(x_1034);
if (x_1035 == 0)
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1036 = lean_ctor_get(x_1034, 1);
x_1037 = lean_ctor_get(x_1034, 0);
lean_dec(x_1037);
lean_ctor_set(x_1034, 1, x_1032);
lean_ctor_set(x_1034, 0, x_1029);
x_1038 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1034, x_10, x_11, x_12, x_13, x_14, x_15, x_1036);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1038;
}
else
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1039 = lean_ctor_get(x_1034, 1);
lean_inc(x_1039);
lean_dec(x_1034);
x_1040 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1040, 0, x_1029);
lean_ctor_set(x_1040, 1, x_1032);
x_1041 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1040, x_10, x_11, x_12, x_13, x_14, x_15, x_1039);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1041;
}
}
else
{
lean_object* x_1042; lean_object* x_1043; 
x_1042 = lean_ctor_get(x_1028, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1028, 1);
lean_inc(x_1043);
lean_dec(x_1028);
x_1004 = x_1042;
x_1005 = x_1043;
goto block_1026;
}
block_1026:
{
if (lean_obj_tag(x_1004) == 0)
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; uint8_t x_1010; 
lean_dec(x_1003);
x_1006 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1005);
x_1007 = lean_ctor_get(x_1006, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_1006, 1);
lean_inc(x_1008);
lean_dec(x_1006);
x_1009 = l_Lean_Elab_Term_SavedState_restore(x_1001, x_10, x_11, x_12, x_13, x_14, x_15, x_1008);
x_1010 = !lean_is_exclusive(x_1009);
if (x_1010 == 0)
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_1011 = lean_ctor_get(x_1009, 1);
x_1012 = lean_ctor_get(x_1009, 0);
lean_dec(x_1012);
lean_ctor_set_tag(x_1009, 1);
lean_ctor_set(x_1009, 1, x_1007);
lean_ctor_set(x_1009, 0, x_1004);
x_1013 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1009, x_10, x_11, x_12, x_13, x_14, x_15, x_1011);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1013;
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1014 = lean_ctor_get(x_1009, 1);
lean_inc(x_1014);
lean_dec(x_1009);
x_1015 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1015, 0, x_1004);
lean_ctor_set(x_1015, 1, x_1007);
x_1016 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1015, x_10, x_11, x_12, x_13, x_14, x_15, x_1014);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1016;
}
}
else
{
lean_object* x_1017; lean_object* x_1018; uint8_t x_1019; 
lean_dec(x_9);
x_1017 = lean_ctor_get(x_1004, 0);
lean_inc(x_1017);
x_1018 = l_Lean_Elab_postponeExceptionId;
x_1019 = lean_nat_dec_eq(x_1017, x_1018);
lean_dec(x_1017);
if (x_1019 == 0)
{
lean_object* x_1020; 
lean_dec(x_1001);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_1003)) {
 x_1020 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1020 = x_1003;
 lean_ctor_set_tag(x_1020, 1);
}
lean_ctor_set(x_1020, 0, x_1004);
lean_ctor_set(x_1020, 1, x_1005);
return x_1020;
}
else
{
lean_object* x_1021; uint8_t x_1022; 
lean_dec(x_1003);
x_1021 = l_Lean_Elab_Term_SavedState_restore(x_1001, x_10, x_11, x_12, x_13, x_14, x_15, x_1005);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1022 = !lean_is_exclusive(x_1021);
if (x_1022 == 0)
{
lean_object* x_1023; 
x_1023 = lean_ctor_get(x_1021, 0);
lean_dec(x_1023);
lean_ctor_set_tag(x_1021, 1);
lean_ctor_set(x_1021, 0, x_1004);
return x_1021;
}
else
{
lean_object* x_1024; lean_object* x_1025; 
x_1024 = lean_ctor_get(x_1021, 1);
lean_inc(x_1024);
lean_dec(x_1021);
x_1025 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1025, 0, x_1004);
lean_ctor_set(x_1025, 1, x_1024);
return x_1025;
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
else
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
x_1047 = lean_unsigned_to_nat(2u);
x_1048 = l_Lean_Syntax_getArg(x_1, x_1047);
lean_dec(x_1);
x_1049 = l_Lean_Syntax_getArgs(x_1048);
lean_dec(x_1048);
x_1050 = l_Lean_Syntax_SepArray_getElems___rarg(x_1049);
lean_dec(x_1049);
x_1051 = l_Lean_Elab_Term_elabExplicitUnivs(x_1050, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1050);
if (lean_obj_tag(x_1051) == 0)
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
x_1052 = lean_ctor_get(x_1051, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1051, 1);
lean_inc(x_1053);
lean_dec(x_1051);
x_1054 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(x_715, x_1052, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_1053);
return x_1054;
}
else
{
uint8_t x_1055; 
lean_dec(x_715);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1055 = !lean_is_exclusive(x_1051);
if (x_1055 == 0)
{
return x_1051;
}
else
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; 
x_1056 = lean_ctor_get(x_1051, 0);
x_1057 = lean_ctor_get(x_1051, 1);
lean_inc(x_1057);
lean_inc(x_1056);
lean_dec(x_1051);
x_1058 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1058, 0, x_1056);
lean_ctor_set(x_1058, 1, x_1057);
return x_1058;
}
}
}
}
}
else
{
lean_object* x_1059; lean_object* x_1060; 
x_1059 = lean_box(0);
x_1060 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(x_1, x_1059, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_1060;
}
}
else
{
lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; uint8_t x_1064; 
x_1061 = lean_unsigned_to_nat(0u);
x_1062 = l_Lean_Syntax_getArg(x_1, x_1061);
x_1063 = l_Lean_identKind___closed__2;
x_1064 = l_Lean_Syntax_isOfKind(x_1062, x_1063);
if (x_1064 == 0)
{
uint8_t x_1065; uint8_t x_1066; 
x_1065 = l_List_isEmpty___rarg(x_2);
if (x_8 == 0)
{
uint8_t x_1393; 
x_1393 = 1;
x_1066 = x_1393;
goto block_1392;
}
else
{
uint8_t x_1394; 
x_1394 = 0;
x_1066 = x_1394;
goto block_1392;
}
block_1392:
{
if (x_1065 == 0)
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1104; lean_object* x_1105; uint8_t x_1127; lean_object* x_1128; 
x_1067 = lean_box(0);
x_1068 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_1069 = lean_ctor_get(x_1068, 0);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_1068, 1);
lean_inc(x_1070);
if (lean_is_exclusive(x_1068)) {
 lean_ctor_release(x_1068, 0);
 lean_ctor_release(x_1068, 1);
 x_1071 = x_1068;
} else {
 lean_dec_ref(x_1068);
 x_1071 = lean_box(0);
}
x_1127 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1128 = l_Lean_Elab_Term_elabTerm(x_1, x_1067, x_1066, x_1127, x_10, x_11, x_12, x_13, x_14, x_15, x_1070);
if (lean_obj_tag(x_1128) == 0)
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
x_1129 = lean_ctor_get(x_1128, 0);
lean_inc(x_1129);
x_1130 = lean_ctor_get(x_1128, 1);
lean_inc(x_1130);
lean_dec(x_1128);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_1131 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_1129, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_1130);
if (lean_obj_tag(x_1131) == 0)
{
if (x_8 == 0)
{
lean_object* x_1132; lean_object* x_1133; 
lean_dec(x_1071);
lean_dec(x_5);
x_1132 = lean_ctor_get(x_1131, 0);
lean_inc(x_1132);
x_1133 = lean_ctor_get(x_1131, 1);
lean_inc(x_1133);
lean_dec(x_1131);
x_1104 = x_1132;
x_1105 = x_1133;
goto block_1126;
}
else
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; 
x_1134 = lean_ctor_get(x_1131, 0);
lean_inc(x_1134);
x_1135 = lean_ctor_get(x_1131, 1);
lean_inc(x_1135);
lean_dec(x_1131);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1136 = l_Lean_Elab_Term_ensureHasType(x_5, x_1134, x_1067, x_10, x_11, x_12, x_13, x_14, x_15, x_1135);
if (lean_obj_tag(x_1136) == 0)
{
lean_object* x_1137; lean_object* x_1138; 
lean_dec(x_1071);
x_1137 = lean_ctor_get(x_1136, 0);
lean_inc(x_1137);
x_1138 = lean_ctor_get(x_1136, 1);
lean_inc(x_1138);
lean_dec(x_1136);
x_1104 = x_1137;
x_1105 = x_1138;
goto block_1126;
}
else
{
lean_object* x_1139; lean_object* x_1140; 
x_1139 = lean_ctor_get(x_1136, 0);
lean_inc(x_1139);
x_1140 = lean_ctor_get(x_1136, 1);
lean_inc(x_1140);
lean_dec(x_1136);
x_1072 = x_1139;
x_1073 = x_1140;
goto block_1103;
}
}
}
else
{
lean_object* x_1141; lean_object* x_1142; 
lean_dec(x_5);
x_1141 = lean_ctor_get(x_1131, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1131, 1);
lean_inc(x_1142);
lean_dec(x_1131);
x_1072 = x_1141;
x_1073 = x_1142;
goto block_1103;
}
}
else
{
lean_object* x_1143; lean_object* x_1144; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1143 = lean_ctor_get(x_1128, 0);
lean_inc(x_1143);
x_1144 = lean_ctor_get(x_1128, 1);
lean_inc(x_1144);
lean_dec(x_1128);
x_1072 = x_1143;
x_1073 = x_1144;
goto block_1103;
}
block_1103:
{
if (lean_obj_tag(x_1072) == 0)
{
lean_object* x_1074; uint8_t x_1075; 
lean_dec(x_1071);
x_1074 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1073);
x_1075 = !lean_is_exclusive(x_1074);
if (x_1075 == 0)
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; uint8_t x_1079; 
x_1076 = lean_ctor_get(x_1074, 0);
x_1077 = lean_ctor_get(x_1074, 1);
x_1078 = l_Lean_Elab_Term_SavedState_restore(x_1069, x_10, x_11, x_12, x_13, x_14, x_15, x_1077);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1079 = !lean_is_exclusive(x_1078);
if (x_1079 == 0)
{
lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; 
x_1080 = lean_ctor_get(x_1078, 1);
x_1081 = lean_ctor_get(x_1078, 0);
lean_dec(x_1081);
lean_ctor_set_tag(x_1078, 1);
lean_ctor_set(x_1078, 1, x_1076);
lean_ctor_set(x_1078, 0, x_1072);
x_1082 = lean_array_push(x_9, x_1078);
lean_ctor_set(x_1074, 1, x_1080);
lean_ctor_set(x_1074, 0, x_1082);
return x_1074;
}
else
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; 
x_1083 = lean_ctor_get(x_1078, 1);
lean_inc(x_1083);
lean_dec(x_1078);
x_1084 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1084, 0, x_1072);
lean_ctor_set(x_1084, 1, x_1076);
x_1085 = lean_array_push(x_9, x_1084);
lean_ctor_set(x_1074, 1, x_1083);
lean_ctor_set(x_1074, 0, x_1085);
return x_1074;
}
}
else
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; 
x_1086 = lean_ctor_get(x_1074, 0);
x_1087 = lean_ctor_get(x_1074, 1);
lean_inc(x_1087);
lean_inc(x_1086);
lean_dec(x_1074);
x_1088 = l_Lean_Elab_Term_SavedState_restore(x_1069, x_10, x_11, x_12, x_13, x_14, x_15, x_1087);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1089 = lean_ctor_get(x_1088, 1);
lean_inc(x_1089);
if (lean_is_exclusive(x_1088)) {
 lean_ctor_release(x_1088, 0);
 lean_ctor_release(x_1088, 1);
 x_1090 = x_1088;
} else {
 lean_dec_ref(x_1088);
 x_1090 = lean_box(0);
}
if (lean_is_scalar(x_1090)) {
 x_1091 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1091 = x_1090;
 lean_ctor_set_tag(x_1091, 1);
}
lean_ctor_set(x_1091, 0, x_1072);
lean_ctor_set(x_1091, 1, x_1086);
x_1092 = lean_array_push(x_9, x_1091);
x_1093 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1093, 0, x_1092);
lean_ctor_set(x_1093, 1, x_1089);
return x_1093;
}
}
else
{
lean_object* x_1094; lean_object* x_1095; uint8_t x_1096; 
lean_dec(x_9);
x_1094 = lean_ctor_get(x_1072, 0);
lean_inc(x_1094);
x_1095 = l_Lean_Elab_postponeExceptionId;
x_1096 = lean_nat_dec_eq(x_1094, x_1095);
lean_dec(x_1094);
if (x_1096 == 0)
{
lean_object* x_1097; 
lean_dec(x_1069);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_1071)) {
 x_1097 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1097 = x_1071;
 lean_ctor_set_tag(x_1097, 1);
}
lean_ctor_set(x_1097, 0, x_1072);
lean_ctor_set(x_1097, 1, x_1073);
return x_1097;
}
else
{
lean_object* x_1098; uint8_t x_1099; 
lean_dec(x_1071);
x_1098 = l_Lean_Elab_Term_SavedState_restore(x_1069, x_10, x_11, x_12, x_13, x_14, x_15, x_1073);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1099 = !lean_is_exclusive(x_1098);
if (x_1099 == 0)
{
lean_object* x_1100; 
x_1100 = lean_ctor_get(x_1098, 0);
lean_dec(x_1100);
lean_ctor_set_tag(x_1098, 1);
lean_ctor_set(x_1098, 0, x_1072);
return x_1098;
}
else
{
lean_object* x_1101; lean_object* x_1102; 
x_1101 = lean_ctor_get(x_1098, 1);
lean_inc(x_1101);
lean_dec(x_1098);
x_1102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1102, 0, x_1072);
lean_ctor_set(x_1102, 1, x_1101);
return x_1102;
}
}
}
}
block_1126:
{
lean_object* x_1106; uint8_t x_1107; 
x_1106 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1105);
x_1107 = !lean_is_exclusive(x_1106);
if (x_1107 == 0)
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; uint8_t x_1111; 
x_1108 = lean_ctor_get(x_1106, 0);
x_1109 = lean_ctor_get(x_1106, 1);
x_1110 = l_Lean_Elab_Term_SavedState_restore(x_1069, x_10, x_11, x_12, x_13, x_14, x_15, x_1109);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1111 = !lean_is_exclusive(x_1110);
if (x_1111 == 0)
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
x_1112 = lean_ctor_get(x_1110, 1);
x_1113 = lean_ctor_get(x_1110, 0);
lean_dec(x_1113);
lean_ctor_set(x_1110, 1, x_1108);
lean_ctor_set(x_1110, 0, x_1104);
x_1114 = lean_array_push(x_9, x_1110);
lean_ctor_set(x_1106, 1, x_1112);
lean_ctor_set(x_1106, 0, x_1114);
return x_1106;
}
else
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
x_1115 = lean_ctor_get(x_1110, 1);
lean_inc(x_1115);
lean_dec(x_1110);
x_1116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1116, 0, x_1104);
lean_ctor_set(x_1116, 1, x_1108);
x_1117 = lean_array_push(x_9, x_1116);
lean_ctor_set(x_1106, 1, x_1115);
lean_ctor_set(x_1106, 0, x_1117);
return x_1106;
}
}
else
{
lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; 
x_1118 = lean_ctor_get(x_1106, 0);
x_1119 = lean_ctor_get(x_1106, 1);
lean_inc(x_1119);
lean_inc(x_1118);
lean_dec(x_1106);
x_1120 = l_Lean_Elab_Term_SavedState_restore(x_1069, x_10, x_11, x_12, x_13, x_14, x_15, x_1119);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1121 = lean_ctor_get(x_1120, 1);
lean_inc(x_1121);
if (lean_is_exclusive(x_1120)) {
 lean_ctor_release(x_1120, 0);
 lean_ctor_release(x_1120, 1);
 x_1122 = x_1120;
} else {
 lean_dec_ref(x_1120);
 x_1122 = lean_box(0);
}
if (lean_is_scalar(x_1122)) {
 x_1123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1123 = x_1122;
}
lean_ctor_set(x_1123, 0, x_1104);
lean_ctor_set(x_1123, 1, x_1118);
x_1124 = lean_array_push(x_9, x_1123);
x_1125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1125, 0, x_1124);
lean_ctor_set(x_1125, 1, x_1121);
return x_1125;
}
}
}
else
{
uint8_t x_1145; 
x_1145 = l_Array_isEmpty___rarg(x_3);
if (x_1145 == 0)
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1183; lean_object* x_1184; uint8_t x_1206; lean_object* x_1207; 
x_1146 = lean_box(0);
x_1147 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_1148 = lean_ctor_get(x_1147, 0);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1147, 1);
lean_inc(x_1149);
if (lean_is_exclusive(x_1147)) {
 lean_ctor_release(x_1147, 0);
 lean_ctor_release(x_1147, 1);
 x_1150 = x_1147;
} else {
 lean_dec_ref(x_1147);
 x_1150 = lean_box(0);
}
x_1206 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1207 = l_Lean_Elab_Term_elabTerm(x_1, x_1146, x_1066, x_1206, x_10, x_11, x_12, x_13, x_14, x_15, x_1149);
if (lean_obj_tag(x_1207) == 0)
{
lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; 
x_1208 = lean_ctor_get(x_1207, 0);
lean_inc(x_1208);
x_1209 = lean_ctor_get(x_1207, 1);
lean_inc(x_1209);
lean_dec(x_1207);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_1210 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_1208, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_1209);
if (lean_obj_tag(x_1210) == 0)
{
if (x_8 == 0)
{
lean_object* x_1211; lean_object* x_1212; 
lean_dec(x_1150);
lean_dec(x_5);
x_1211 = lean_ctor_get(x_1210, 0);
lean_inc(x_1211);
x_1212 = lean_ctor_get(x_1210, 1);
lean_inc(x_1212);
lean_dec(x_1210);
x_1183 = x_1211;
x_1184 = x_1212;
goto block_1205;
}
else
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
x_1213 = lean_ctor_get(x_1210, 0);
lean_inc(x_1213);
x_1214 = lean_ctor_get(x_1210, 1);
lean_inc(x_1214);
lean_dec(x_1210);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1215 = l_Lean_Elab_Term_ensureHasType(x_5, x_1213, x_1146, x_10, x_11, x_12, x_13, x_14, x_15, x_1214);
if (lean_obj_tag(x_1215) == 0)
{
lean_object* x_1216; lean_object* x_1217; 
lean_dec(x_1150);
x_1216 = lean_ctor_get(x_1215, 0);
lean_inc(x_1216);
x_1217 = lean_ctor_get(x_1215, 1);
lean_inc(x_1217);
lean_dec(x_1215);
x_1183 = x_1216;
x_1184 = x_1217;
goto block_1205;
}
else
{
lean_object* x_1218; lean_object* x_1219; 
x_1218 = lean_ctor_get(x_1215, 0);
lean_inc(x_1218);
x_1219 = lean_ctor_get(x_1215, 1);
lean_inc(x_1219);
lean_dec(x_1215);
x_1151 = x_1218;
x_1152 = x_1219;
goto block_1182;
}
}
}
else
{
lean_object* x_1220; lean_object* x_1221; 
lean_dec(x_5);
x_1220 = lean_ctor_get(x_1210, 0);
lean_inc(x_1220);
x_1221 = lean_ctor_get(x_1210, 1);
lean_inc(x_1221);
lean_dec(x_1210);
x_1151 = x_1220;
x_1152 = x_1221;
goto block_1182;
}
}
else
{
lean_object* x_1222; lean_object* x_1223; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1222 = lean_ctor_get(x_1207, 0);
lean_inc(x_1222);
x_1223 = lean_ctor_get(x_1207, 1);
lean_inc(x_1223);
lean_dec(x_1207);
x_1151 = x_1222;
x_1152 = x_1223;
goto block_1182;
}
block_1182:
{
if (lean_obj_tag(x_1151) == 0)
{
lean_object* x_1153; uint8_t x_1154; 
lean_dec(x_1150);
x_1153 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1152);
x_1154 = !lean_is_exclusive(x_1153);
if (x_1154 == 0)
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; uint8_t x_1158; 
x_1155 = lean_ctor_get(x_1153, 0);
x_1156 = lean_ctor_get(x_1153, 1);
x_1157 = l_Lean_Elab_Term_SavedState_restore(x_1148, x_10, x_11, x_12, x_13, x_14, x_15, x_1156);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1158 = !lean_is_exclusive(x_1157);
if (x_1158 == 0)
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
x_1159 = lean_ctor_get(x_1157, 1);
x_1160 = lean_ctor_get(x_1157, 0);
lean_dec(x_1160);
lean_ctor_set_tag(x_1157, 1);
lean_ctor_set(x_1157, 1, x_1155);
lean_ctor_set(x_1157, 0, x_1151);
x_1161 = lean_array_push(x_9, x_1157);
lean_ctor_set(x_1153, 1, x_1159);
lean_ctor_set(x_1153, 0, x_1161);
return x_1153;
}
else
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
x_1162 = lean_ctor_get(x_1157, 1);
lean_inc(x_1162);
lean_dec(x_1157);
x_1163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1163, 0, x_1151);
lean_ctor_set(x_1163, 1, x_1155);
x_1164 = lean_array_push(x_9, x_1163);
lean_ctor_set(x_1153, 1, x_1162);
lean_ctor_set(x_1153, 0, x_1164);
return x_1153;
}
}
else
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
x_1165 = lean_ctor_get(x_1153, 0);
x_1166 = lean_ctor_get(x_1153, 1);
lean_inc(x_1166);
lean_inc(x_1165);
lean_dec(x_1153);
x_1167 = l_Lean_Elab_Term_SavedState_restore(x_1148, x_10, x_11, x_12, x_13, x_14, x_15, x_1166);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1168 = lean_ctor_get(x_1167, 1);
lean_inc(x_1168);
if (lean_is_exclusive(x_1167)) {
 lean_ctor_release(x_1167, 0);
 lean_ctor_release(x_1167, 1);
 x_1169 = x_1167;
} else {
 lean_dec_ref(x_1167);
 x_1169 = lean_box(0);
}
if (lean_is_scalar(x_1169)) {
 x_1170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1170 = x_1169;
 lean_ctor_set_tag(x_1170, 1);
}
lean_ctor_set(x_1170, 0, x_1151);
lean_ctor_set(x_1170, 1, x_1165);
x_1171 = lean_array_push(x_9, x_1170);
x_1172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1172, 0, x_1171);
lean_ctor_set(x_1172, 1, x_1168);
return x_1172;
}
}
else
{
lean_object* x_1173; lean_object* x_1174; uint8_t x_1175; 
lean_dec(x_9);
x_1173 = lean_ctor_get(x_1151, 0);
lean_inc(x_1173);
x_1174 = l_Lean_Elab_postponeExceptionId;
x_1175 = lean_nat_dec_eq(x_1173, x_1174);
lean_dec(x_1173);
if (x_1175 == 0)
{
lean_object* x_1176; 
lean_dec(x_1148);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_1150)) {
 x_1176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1176 = x_1150;
 lean_ctor_set_tag(x_1176, 1);
}
lean_ctor_set(x_1176, 0, x_1151);
lean_ctor_set(x_1176, 1, x_1152);
return x_1176;
}
else
{
lean_object* x_1177; uint8_t x_1178; 
lean_dec(x_1150);
x_1177 = l_Lean_Elab_Term_SavedState_restore(x_1148, x_10, x_11, x_12, x_13, x_14, x_15, x_1152);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1178 = !lean_is_exclusive(x_1177);
if (x_1178 == 0)
{
lean_object* x_1179; 
x_1179 = lean_ctor_get(x_1177, 0);
lean_dec(x_1179);
lean_ctor_set_tag(x_1177, 1);
lean_ctor_set(x_1177, 0, x_1151);
return x_1177;
}
else
{
lean_object* x_1180; lean_object* x_1181; 
x_1180 = lean_ctor_get(x_1177, 1);
lean_inc(x_1180);
lean_dec(x_1177);
x_1181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1181, 0, x_1151);
lean_ctor_set(x_1181, 1, x_1180);
return x_1181;
}
}
}
}
block_1205:
{
lean_object* x_1185; uint8_t x_1186; 
x_1185 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1184);
x_1186 = !lean_is_exclusive(x_1185);
if (x_1186 == 0)
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; uint8_t x_1190; 
x_1187 = lean_ctor_get(x_1185, 0);
x_1188 = lean_ctor_get(x_1185, 1);
x_1189 = l_Lean_Elab_Term_SavedState_restore(x_1148, x_10, x_11, x_12, x_13, x_14, x_15, x_1188);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1190 = !lean_is_exclusive(x_1189);
if (x_1190 == 0)
{
lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; 
x_1191 = lean_ctor_get(x_1189, 1);
x_1192 = lean_ctor_get(x_1189, 0);
lean_dec(x_1192);
lean_ctor_set(x_1189, 1, x_1187);
lean_ctor_set(x_1189, 0, x_1183);
x_1193 = lean_array_push(x_9, x_1189);
lean_ctor_set(x_1185, 1, x_1191);
lean_ctor_set(x_1185, 0, x_1193);
return x_1185;
}
else
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; 
x_1194 = lean_ctor_get(x_1189, 1);
lean_inc(x_1194);
lean_dec(x_1189);
x_1195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1195, 0, x_1183);
lean_ctor_set(x_1195, 1, x_1187);
x_1196 = lean_array_push(x_9, x_1195);
lean_ctor_set(x_1185, 1, x_1194);
lean_ctor_set(x_1185, 0, x_1196);
return x_1185;
}
}
else
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; 
x_1197 = lean_ctor_get(x_1185, 0);
x_1198 = lean_ctor_get(x_1185, 1);
lean_inc(x_1198);
lean_inc(x_1197);
lean_dec(x_1185);
x_1199 = l_Lean_Elab_Term_SavedState_restore(x_1148, x_10, x_11, x_12, x_13, x_14, x_15, x_1198);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1200 = lean_ctor_get(x_1199, 1);
lean_inc(x_1200);
if (lean_is_exclusive(x_1199)) {
 lean_ctor_release(x_1199, 0);
 lean_ctor_release(x_1199, 1);
 x_1201 = x_1199;
} else {
 lean_dec_ref(x_1199);
 x_1201 = lean_box(0);
}
if (lean_is_scalar(x_1201)) {
 x_1202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1202 = x_1201;
}
lean_ctor_set(x_1202, 0, x_1183);
lean_ctor_set(x_1202, 1, x_1197);
x_1203 = lean_array_push(x_9, x_1202);
x_1204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1204, 0, x_1203);
lean_ctor_set(x_1204, 1, x_1200);
return x_1204;
}
}
}
else
{
uint8_t x_1224; 
x_1224 = l_Array_isEmpty___rarg(x_4);
if (x_1224 == 0)
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1262; lean_object* x_1263; uint8_t x_1285; lean_object* x_1286; 
x_1225 = lean_box(0);
x_1226 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_1227 = lean_ctor_get(x_1226, 0);
lean_inc(x_1227);
x_1228 = lean_ctor_get(x_1226, 1);
lean_inc(x_1228);
if (lean_is_exclusive(x_1226)) {
 lean_ctor_release(x_1226, 0);
 lean_ctor_release(x_1226, 1);
 x_1229 = x_1226;
} else {
 lean_dec_ref(x_1226);
 x_1229 = lean_box(0);
}
x_1285 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1286 = l_Lean_Elab_Term_elabTerm(x_1, x_1225, x_1066, x_1285, x_10, x_11, x_12, x_13, x_14, x_15, x_1228);
if (lean_obj_tag(x_1286) == 0)
{
lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; 
x_1287 = lean_ctor_get(x_1286, 0);
lean_inc(x_1287);
x_1288 = lean_ctor_get(x_1286, 1);
lean_inc(x_1288);
lean_dec(x_1286);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_1289 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_1287, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_1288);
if (lean_obj_tag(x_1289) == 0)
{
if (x_8 == 0)
{
lean_object* x_1290; lean_object* x_1291; 
lean_dec(x_1229);
lean_dec(x_5);
x_1290 = lean_ctor_get(x_1289, 0);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1289, 1);
lean_inc(x_1291);
lean_dec(x_1289);
x_1262 = x_1290;
x_1263 = x_1291;
goto block_1284;
}
else
{
lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; 
x_1292 = lean_ctor_get(x_1289, 0);
lean_inc(x_1292);
x_1293 = lean_ctor_get(x_1289, 1);
lean_inc(x_1293);
lean_dec(x_1289);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1294 = l_Lean_Elab_Term_ensureHasType(x_5, x_1292, x_1225, x_10, x_11, x_12, x_13, x_14, x_15, x_1293);
if (lean_obj_tag(x_1294) == 0)
{
lean_object* x_1295; lean_object* x_1296; 
lean_dec(x_1229);
x_1295 = lean_ctor_get(x_1294, 0);
lean_inc(x_1295);
x_1296 = lean_ctor_get(x_1294, 1);
lean_inc(x_1296);
lean_dec(x_1294);
x_1262 = x_1295;
x_1263 = x_1296;
goto block_1284;
}
else
{
lean_object* x_1297; lean_object* x_1298; 
x_1297 = lean_ctor_get(x_1294, 0);
lean_inc(x_1297);
x_1298 = lean_ctor_get(x_1294, 1);
lean_inc(x_1298);
lean_dec(x_1294);
x_1230 = x_1297;
x_1231 = x_1298;
goto block_1261;
}
}
}
else
{
lean_object* x_1299; lean_object* x_1300; 
lean_dec(x_5);
x_1299 = lean_ctor_get(x_1289, 0);
lean_inc(x_1299);
x_1300 = lean_ctor_get(x_1289, 1);
lean_inc(x_1300);
lean_dec(x_1289);
x_1230 = x_1299;
x_1231 = x_1300;
goto block_1261;
}
}
else
{
lean_object* x_1301; lean_object* x_1302; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1301 = lean_ctor_get(x_1286, 0);
lean_inc(x_1301);
x_1302 = lean_ctor_get(x_1286, 1);
lean_inc(x_1302);
lean_dec(x_1286);
x_1230 = x_1301;
x_1231 = x_1302;
goto block_1261;
}
block_1261:
{
if (lean_obj_tag(x_1230) == 0)
{
lean_object* x_1232; uint8_t x_1233; 
lean_dec(x_1229);
x_1232 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1231);
x_1233 = !lean_is_exclusive(x_1232);
if (x_1233 == 0)
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; uint8_t x_1237; 
x_1234 = lean_ctor_get(x_1232, 0);
x_1235 = lean_ctor_get(x_1232, 1);
x_1236 = l_Lean_Elab_Term_SavedState_restore(x_1227, x_10, x_11, x_12, x_13, x_14, x_15, x_1235);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1237 = !lean_is_exclusive(x_1236);
if (x_1237 == 0)
{
lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; 
x_1238 = lean_ctor_get(x_1236, 1);
x_1239 = lean_ctor_get(x_1236, 0);
lean_dec(x_1239);
lean_ctor_set_tag(x_1236, 1);
lean_ctor_set(x_1236, 1, x_1234);
lean_ctor_set(x_1236, 0, x_1230);
x_1240 = lean_array_push(x_9, x_1236);
lean_ctor_set(x_1232, 1, x_1238);
lean_ctor_set(x_1232, 0, x_1240);
return x_1232;
}
else
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; 
x_1241 = lean_ctor_get(x_1236, 1);
lean_inc(x_1241);
lean_dec(x_1236);
x_1242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1242, 0, x_1230);
lean_ctor_set(x_1242, 1, x_1234);
x_1243 = lean_array_push(x_9, x_1242);
lean_ctor_set(x_1232, 1, x_1241);
lean_ctor_set(x_1232, 0, x_1243);
return x_1232;
}
}
else
{
lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
x_1244 = lean_ctor_get(x_1232, 0);
x_1245 = lean_ctor_get(x_1232, 1);
lean_inc(x_1245);
lean_inc(x_1244);
lean_dec(x_1232);
x_1246 = l_Lean_Elab_Term_SavedState_restore(x_1227, x_10, x_11, x_12, x_13, x_14, x_15, x_1245);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1247 = lean_ctor_get(x_1246, 1);
lean_inc(x_1247);
if (lean_is_exclusive(x_1246)) {
 lean_ctor_release(x_1246, 0);
 lean_ctor_release(x_1246, 1);
 x_1248 = x_1246;
} else {
 lean_dec_ref(x_1246);
 x_1248 = lean_box(0);
}
if (lean_is_scalar(x_1248)) {
 x_1249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1249 = x_1248;
 lean_ctor_set_tag(x_1249, 1);
}
lean_ctor_set(x_1249, 0, x_1230);
lean_ctor_set(x_1249, 1, x_1244);
x_1250 = lean_array_push(x_9, x_1249);
x_1251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1251, 0, x_1250);
lean_ctor_set(x_1251, 1, x_1247);
return x_1251;
}
}
else
{
lean_object* x_1252; lean_object* x_1253; uint8_t x_1254; 
lean_dec(x_9);
x_1252 = lean_ctor_get(x_1230, 0);
lean_inc(x_1252);
x_1253 = l_Lean_Elab_postponeExceptionId;
x_1254 = lean_nat_dec_eq(x_1252, x_1253);
lean_dec(x_1252);
if (x_1254 == 0)
{
lean_object* x_1255; 
lean_dec(x_1227);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_1229)) {
 x_1255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1255 = x_1229;
 lean_ctor_set_tag(x_1255, 1);
}
lean_ctor_set(x_1255, 0, x_1230);
lean_ctor_set(x_1255, 1, x_1231);
return x_1255;
}
else
{
lean_object* x_1256; uint8_t x_1257; 
lean_dec(x_1229);
x_1256 = l_Lean_Elab_Term_SavedState_restore(x_1227, x_10, x_11, x_12, x_13, x_14, x_15, x_1231);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1257 = !lean_is_exclusive(x_1256);
if (x_1257 == 0)
{
lean_object* x_1258; 
x_1258 = lean_ctor_get(x_1256, 0);
lean_dec(x_1258);
lean_ctor_set_tag(x_1256, 1);
lean_ctor_set(x_1256, 0, x_1230);
return x_1256;
}
else
{
lean_object* x_1259; lean_object* x_1260; 
x_1259 = lean_ctor_get(x_1256, 1);
lean_inc(x_1259);
lean_dec(x_1256);
x_1260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1260, 0, x_1230);
lean_ctor_set(x_1260, 1, x_1259);
return x_1260;
}
}
}
}
block_1284:
{
lean_object* x_1264; uint8_t x_1265; 
x_1264 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1263);
x_1265 = !lean_is_exclusive(x_1264);
if (x_1265 == 0)
{
lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; uint8_t x_1269; 
x_1266 = lean_ctor_get(x_1264, 0);
x_1267 = lean_ctor_get(x_1264, 1);
x_1268 = l_Lean_Elab_Term_SavedState_restore(x_1227, x_10, x_11, x_12, x_13, x_14, x_15, x_1267);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1269 = !lean_is_exclusive(x_1268);
if (x_1269 == 0)
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
x_1270 = lean_ctor_get(x_1268, 1);
x_1271 = lean_ctor_get(x_1268, 0);
lean_dec(x_1271);
lean_ctor_set(x_1268, 1, x_1266);
lean_ctor_set(x_1268, 0, x_1262);
x_1272 = lean_array_push(x_9, x_1268);
lean_ctor_set(x_1264, 1, x_1270);
lean_ctor_set(x_1264, 0, x_1272);
return x_1264;
}
else
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; 
x_1273 = lean_ctor_get(x_1268, 1);
lean_inc(x_1273);
lean_dec(x_1268);
x_1274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1274, 0, x_1262);
lean_ctor_set(x_1274, 1, x_1266);
x_1275 = lean_array_push(x_9, x_1274);
lean_ctor_set(x_1264, 1, x_1273);
lean_ctor_set(x_1264, 0, x_1275);
return x_1264;
}
}
else
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; 
x_1276 = lean_ctor_get(x_1264, 0);
x_1277 = lean_ctor_get(x_1264, 1);
lean_inc(x_1277);
lean_inc(x_1276);
lean_dec(x_1264);
x_1278 = l_Lean_Elab_Term_SavedState_restore(x_1227, x_10, x_11, x_12, x_13, x_14, x_15, x_1277);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1279 = lean_ctor_get(x_1278, 1);
lean_inc(x_1279);
if (lean_is_exclusive(x_1278)) {
 lean_ctor_release(x_1278, 0);
 lean_ctor_release(x_1278, 1);
 x_1280 = x_1278;
} else {
 lean_dec_ref(x_1278);
 x_1280 = lean_box(0);
}
if (lean_is_scalar(x_1280)) {
 x_1281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1281 = x_1280;
}
lean_ctor_set(x_1281, 0, x_1262);
lean_ctor_set(x_1281, 1, x_1276);
x_1282 = lean_array_push(x_9, x_1281);
x_1283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1283, 0, x_1282);
lean_ctor_set(x_1283, 1, x_1279);
return x_1283;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_8 == 0)
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; uint8_t x_1330; lean_object* x_1331; 
x_1303 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_1304 = lean_ctor_get(x_1303, 0);
lean_inc(x_1304);
x_1305 = lean_ctor_get(x_1303, 1);
lean_inc(x_1305);
if (lean_is_exclusive(x_1303)) {
 lean_ctor_release(x_1303, 0);
 lean_ctor_release(x_1303, 1);
 x_1306 = x_1303;
} else {
 lean_dec_ref(x_1303);
 x_1306 = lean_box(0);
}
x_1330 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1331 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_1330, x_1330, x_10, x_11, x_12, x_13, x_14, x_15, x_1305);
if (lean_obj_tag(x_1331) == 0)
{
lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; uint8_t x_1338; 
lean_dec(x_1306);
x_1332 = lean_ctor_get(x_1331, 0);
lean_inc(x_1332);
x_1333 = lean_ctor_get(x_1331, 1);
lean_inc(x_1333);
lean_dec(x_1331);
x_1334 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1333);
x_1335 = lean_ctor_get(x_1334, 0);
lean_inc(x_1335);
x_1336 = lean_ctor_get(x_1334, 1);
lean_inc(x_1336);
lean_dec(x_1334);
x_1337 = l_Lean_Elab_Term_SavedState_restore(x_1304, x_10, x_11, x_12, x_13, x_14, x_15, x_1336);
x_1338 = !lean_is_exclusive(x_1337);
if (x_1338 == 0)
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
x_1339 = lean_ctor_get(x_1337, 1);
x_1340 = lean_ctor_get(x_1337, 0);
lean_dec(x_1340);
lean_ctor_set(x_1337, 1, x_1335);
lean_ctor_set(x_1337, 0, x_1332);
x_1341 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1337, x_10, x_11, x_12, x_13, x_14, x_15, x_1339);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1341;
}
else
{
lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
x_1342 = lean_ctor_get(x_1337, 1);
lean_inc(x_1342);
lean_dec(x_1337);
x_1343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1343, 0, x_1332);
lean_ctor_set(x_1343, 1, x_1335);
x_1344 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1343, x_10, x_11, x_12, x_13, x_14, x_15, x_1342);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1344;
}
}
else
{
lean_object* x_1345; lean_object* x_1346; 
x_1345 = lean_ctor_get(x_1331, 0);
lean_inc(x_1345);
x_1346 = lean_ctor_get(x_1331, 1);
lean_inc(x_1346);
lean_dec(x_1331);
x_1307 = x_1345;
x_1308 = x_1346;
goto block_1329;
}
block_1329:
{
if (lean_obj_tag(x_1307) == 0)
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; uint8_t x_1313; 
lean_dec(x_1306);
x_1309 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1308);
x_1310 = lean_ctor_get(x_1309, 0);
lean_inc(x_1310);
x_1311 = lean_ctor_get(x_1309, 1);
lean_inc(x_1311);
lean_dec(x_1309);
x_1312 = l_Lean_Elab_Term_SavedState_restore(x_1304, x_10, x_11, x_12, x_13, x_14, x_15, x_1311);
x_1313 = !lean_is_exclusive(x_1312);
if (x_1313 == 0)
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; 
x_1314 = lean_ctor_get(x_1312, 1);
x_1315 = lean_ctor_get(x_1312, 0);
lean_dec(x_1315);
lean_ctor_set_tag(x_1312, 1);
lean_ctor_set(x_1312, 1, x_1310);
lean_ctor_set(x_1312, 0, x_1307);
x_1316 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1312, x_10, x_11, x_12, x_13, x_14, x_15, x_1314);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1316;
}
else
{
lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; 
x_1317 = lean_ctor_get(x_1312, 1);
lean_inc(x_1317);
lean_dec(x_1312);
x_1318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1318, 0, x_1307);
lean_ctor_set(x_1318, 1, x_1310);
x_1319 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1318, x_10, x_11, x_12, x_13, x_14, x_15, x_1317);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1319;
}
}
else
{
lean_object* x_1320; lean_object* x_1321; uint8_t x_1322; 
lean_dec(x_9);
x_1320 = lean_ctor_get(x_1307, 0);
lean_inc(x_1320);
x_1321 = l_Lean_Elab_postponeExceptionId;
x_1322 = lean_nat_dec_eq(x_1320, x_1321);
lean_dec(x_1320);
if (x_1322 == 0)
{
lean_object* x_1323; 
lean_dec(x_1304);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_1306)) {
 x_1323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1323 = x_1306;
 lean_ctor_set_tag(x_1323, 1);
}
lean_ctor_set(x_1323, 0, x_1307);
lean_ctor_set(x_1323, 1, x_1308);
return x_1323;
}
else
{
lean_object* x_1324; uint8_t x_1325; 
lean_dec(x_1306);
x_1324 = l_Lean_Elab_Term_SavedState_restore(x_1304, x_10, x_11, x_12, x_13, x_14, x_15, x_1308);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1325 = !lean_is_exclusive(x_1324);
if (x_1325 == 0)
{
lean_object* x_1326; 
x_1326 = lean_ctor_get(x_1324, 0);
lean_dec(x_1326);
lean_ctor_set_tag(x_1324, 1);
lean_ctor_set(x_1324, 0, x_1307);
return x_1324;
}
else
{
lean_object* x_1327; lean_object* x_1328; 
x_1327 = lean_ctor_get(x_1324, 1);
lean_inc(x_1327);
lean_dec(x_1324);
x_1328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1328, 0, x_1307);
lean_ctor_set(x_1328, 1, x_1327);
return x_1328;
}
}
}
}
}
else
{
lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; uint8_t x_1375; lean_object* x_1376; 
x_1347 = lean_box(0);
x_1348 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_1349 = lean_ctor_get(x_1348, 0);
lean_inc(x_1349);
x_1350 = lean_ctor_get(x_1348, 1);
lean_inc(x_1350);
if (lean_is_exclusive(x_1348)) {
 lean_ctor_release(x_1348, 0);
 lean_ctor_release(x_1348, 1);
 x_1351 = x_1348;
} else {
 lean_dec_ref(x_1348);
 x_1351 = lean_box(0);
}
x_1375 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1376 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_1066, x_1375, x_1347, x_10, x_11, x_12, x_13, x_14, x_15, x_1350);
if (lean_obj_tag(x_1376) == 0)
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; uint8_t x_1383; 
lean_dec(x_1351);
x_1377 = lean_ctor_get(x_1376, 0);
lean_inc(x_1377);
x_1378 = lean_ctor_get(x_1376, 1);
lean_inc(x_1378);
lean_dec(x_1376);
x_1379 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1378);
x_1380 = lean_ctor_get(x_1379, 0);
lean_inc(x_1380);
x_1381 = lean_ctor_get(x_1379, 1);
lean_inc(x_1381);
lean_dec(x_1379);
x_1382 = l_Lean_Elab_Term_SavedState_restore(x_1349, x_10, x_11, x_12, x_13, x_14, x_15, x_1381);
x_1383 = !lean_is_exclusive(x_1382);
if (x_1383 == 0)
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
x_1384 = lean_ctor_get(x_1382, 1);
x_1385 = lean_ctor_get(x_1382, 0);
lean_dec(x_1385);
lean_ctor_set(x_1382, 1, x_1380);
lean_ctor_set(x_1382, 0, x_1377);
x_1386 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1382, x_10, x_11, x_12, x_13, x_14, x_15, x_1384);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1386;
}
else
{
lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; 
x_1387 = lean_ctor_get(x_1382, 1);
lean_inc(x_1387);
lean_dec(x_1382);
x_1388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1388, 0, x_1377);
lean_ctor_set(x_1388, 1, x_1380);
x_1389 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1388, x_10, x_11, x_12, x_13, x_14, x_15, x_1387);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1389;
}
}
else
{
lean_object* x_1390; lean_object* x_1391; 
x_1390 = lean_ctor_get(x_1376, 0);
lean_inc(x_1390);
x_1391 = lean_ctor_get(x_1376, 1);
lean_inc(x_1391);
lean_dec(x_1376);
x_1352 = x_1390;
x_1353 = x_1391;
goto block_1374;
}
block_1374:
{
if (lean_obj_tag(x_1352) == 0)
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; uint8_t x_1358; 
lean_dec(x_1351);
x_1354 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1353);
x_1355 = lean_ctor_get(x_1354, 0);
lean_inc(x_1355);
x_1356 = lean_ctor_get(x_1354, 1);
lean_inc(x_1356);
lean_dec(x_1354);
x_1357 = l_Lean_Elab_Term_SavedState_restore(x_1349, x_10, x_11, x_12, x_13, x_14, x_15, x_1356);
x_1358 = !lean_is_exclusive(x_1357);
if (x_1358 == 0)
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; 
x_1359 = lean_ctor_get(x_1357, 1);
x_1360 = lean_ctor_get(x_1357, 0);
lean_dec(x_1360);
lean_ctor_set_tag(x_1357, 1);
lean_ctor_set(x_1357, 1, x_1355);
lean_ctor_set(x_1357, 0, x_1352);
x_1361 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1357, x_10, x_11, x_12, x_13, x_14, x_15, x_1359);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1361;
}
else
{
lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; 
x_1362 = lean_ctor_get(x_1357, 1);
lean_inc(x_1362);
lean_dec(x_1357);
x_1363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1363, 0, x_1352);
lean_ctor_set(x_1363, 1, x_1355);
x_1364 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1363, x_10, x_11, x_12, x_13, x_14, x_15, x_1362);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1364;
}
}
else
{
lean_object* x_1365; lean_object* x_1366; uint8_t x_1367; 
lean_dec(x_9);
x_1365 = lean_ctor_get(x_1352, 0);
lean_inc(x_1365);
x_1366 = l_Lean_Elab_postponeExceptionId;
x_1367 = lean_nat_dec_eq(x_1365, x_1366);
lean_dec(x_1365);
if (x_1367 == 0)
{
lean_object* x_1368; 
lean_dec(x_1349);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_1351)) {
 x_1368 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1368 = x_1351;
 lean_ctor_set_tag(x_1368, 1);
}
lean_ctor_set(x_1368, 0, x_1352);
lean_ctor_set(x_1368, 1, x_1353);
return x_1368;
}
else
{
lean_object* x_1369; uint8_t x_1370; 
lean_dec(x_1351);
x_1369 = l_Lean_Elab_Term_SavedState_restore(x_1349, x_10, x_11, x_12, x_13, x_14, x_15, x_1353);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1370 = !lean_is_exclusive(x_1369);
if (x_1370 == 0)
{
lean_object* x_1371; 
x_1371 = lean_ctor_get(x_1369, 0);
lean_dec(x_1371);
lean_ctor_set_tag(x_1369, 1);
lean_ctor_set(x_1369, 0, x_1352);
return x_1369;
}
else
{
lean_object* x_1372; lean_object* x_1373; 
x_1372 = lean_ctor_get(x_1369, 1);
lean_inc(x_1372);
lean_dec(x_1369);
x_1373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1373, 0, x_1352);
lean_ctor_set(x_1373, 1, x_1372);
return x_1373;
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
else
{
lean_object* x_1395; lean_object* x_1396; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1395 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__4;
x_1396 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1(x_1395, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_1396;
}
}
}
else
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; 
x_1397 = lean_unsigned_to_nat(0u);
x_1398 = l_Lean_Syntax_getArg(x_1, x_1397);
x_1399 = lean_unsigned_to_nat(1u);
x_1400 = l_Lean_Syntax_getArg(x_1, x_1399);
x_1401 = lean_unsigned_to_nat(2u);
x_1402 = l_Lean_Syntax_getArg(x_1, x_1401);
lean_dec(x_1);
x_1403 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1403, 0, x_1400);
lean_ctor_set(x_1403, 1, x_1402);
x_1404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1404, 0, x_1403);
lean_ctor_set(x_1404, 1, x_2);
x_1 = x_1398;
x_2 = x_1404;
goto _start;
}
}
else
{
lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; uint8_t x_1413; 
x_1406 = lean_unsigned_to_nat(0u);
x_1407 = l_Lean_Syntax_getArg(x_1, x_1406);
x_1408 = lean_unsigned_to_nat(2u);
x_1409 = l_Lean_Syntax_getArg(x_1, x_1408);
x_1410 = lean_unsigned_to_nat(3u);
x_1411 = l_Lean_Syntax_getArg(x_1, x_1410);
x_1412 = l_Lean_nullKind___closed__2;
lean_inc(x_1411);
x_1413 = l_Lean_Syntax_isOfKind(x_1411, x_1412);
if (x_1413 == 0)
{
lean_object* x_1414; 
lean_dec(x_1411);
lean_dec(x_1409);
lean_dec(x_1407);
x_1414 = lean_box(0);
x_17 = x_1414;
goto block_348;
}
else
{
lean_object* x_1415; lean_object* x_1416; uint8_t x_1417; 
x_1415 = l_Lean_Syntax_getArgs(x_1411);
lean_dec(x_1411);
x_1416 = lean_array_get_size(x_1415);
lean_dec(x_1415);
x_1417 = lean_nat_dec_eq(x_1416, x_1406);
lean_dec(x_1416);
if (x_1417 == 0)
{
lean_object* x_1418; 
lean_dec(x_1409);
lean_dec(x_1407);
x_1418 = lean_box(0);
x_17 = x_1418;
goto block_348;
}
else
{
lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; 
lean_dec(x_1);
x_1419 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_14, x_15, x_16);
x_1420 = lean_ctor_get(x_1419, 0);
lean_inc(x_1420);
x_1421 = lean_ctor_get(x_1419, 1);
lean_inc(x_1421);
lean_dec(x_1419);
x_1422 = l_Lean_Elab_Term_getCurrMacroScope(x_10, x_11, x_12, x_13, x_14, x_15, x_1421);
x_1423 = lean_ctor_get(x_1422, 1);
lean_inc(x_1423);
lean_dec(x_1422);
x_1424 = l_Lean_Elab_Term_getMainModule___rarg(x_15, x_1423);
x_1425 = lean_ctor_get(x_1424, 1);
lean_inc(x_1425);
lean_dec(x_1424);
x_1426 = l_Array_empty___closed__1;
x_1427 = lean_array_push(x_1426, x_1407);
x_1428 = l_Lean_Name_toString___closed__1;
x_1429 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1429, 0, x_1420);
lean_ctor_set(x_1429, 1, x_1428);
x_1430 = lean_array_push(x_1427, x_1429);
x_1431 = lean_array_push(x_1430, x_1409);
x_1432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1432, 0, x_352);
lean_ctor_set(x_1432, 1, x_1431);
x_1 = x_1432;
x_16 = x_1425;
goto _start;
}
}
}
}
else
{
lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; uint8_t x_1439; 
x_1434 = lean_unsigned_to_nat(0u);
x_1435 = l_Lean_Syntax_getArg(x_1, x_1434);
x_1436 = lean_unsigned_to_nat(2u);
x_1437 = l_Lean_Syntax_getArg(x_1, x_1436);
x_1438 = l_Lean_fieldIdxKind___closed__2;
lean_inc(x_1437);
x_1439 = l_Lean_Syntax_isOfKind(x_1437, x_1438);
if (x_1439 == 0)
{
lean_object* x_1440; uint8_t x_1441; 
x_1440 = l_Lean_identKind___closed__2;
lean_inc(x_1437);
x_1441 = l_Lean_Syntax_isOfKind(x_1437, x_1440);
if (x_1441 == 0)
{
uint8_t x_1442; uint8_t x_1443; 
lean_dec(x_1437);
lean_dec(x_1435);
x_1442 = l_List_isEmpty___rarg(x_2);
if (x_8 == 0)
{
uint8_t x_1770; 
x_1770 = 1;
x_1443 = x_1770;
goto block_1769;
}
else
{
uint8_t x_1771; 
x_1771 = 0;
x_1443 = x_1771;
goto block_1769;
}
block_1769:
{
if (x_1442 == 0)
{
lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1481; lean_object* x_1482; uint8_t x_1504; lean_object* x_1505; 
x_1444 = lean_box(0);
x_1445 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_1446 = lean_ctor_get(x_1445, 0);
lean_inc(x_1446);
x_1447 = lean_ctor_get(x_1445, 1);
lean_inc(x_1447);
if (lean_is_exclusive(x_1445)) {
 lean_ctor_release(x_1445, 0);
 lean_ctor_release(x_1445, 1);
 x_1448 = x_1445;
} else {
 lean_dec_ref(x_1445);
 x_1448 = lean_box(0);
}
x_1504 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1505 = l_Lean_Elab_Term_elabTerm(x_1, x_1444, x_1443, x_1504, x_10, x_11, x_12, x_13, x_14, x_15, x_1447);
if (lean_obj_tag(x_1505) == 0)
{
lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; 
x_1506 = lean_ctor_get(x_1505, 0);
lean_inc(x_1506);
x_1507 = lean_ctor_get(x_1505, 1);
lean_inc(x_1507);
lean_dec(x_1505);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_1508 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_1506, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_1507);
if (lean_obj_tag(x_1508) == 0)
{
if (x_8 == 0)
{
lean_object* x_1509; lean_object* x_1510; 
lean_dec(x_1448);
lean_dec(x_5);
x_1509 = lean_ctor_get(x_1508, 0);
lean_inc(x_1509);
x_1510 = lean_ctor_get(x_1508, 1);
lean_inc(x_1510);
lean_dec(x_1508);
x_1481 = x_1509;
x_1482 = x_1510;
goto block_1503;
}
else
{
lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; 
x_1511 = lean_ctor_get(x_1508, 0);
lean_inc(x_1511);
x_1512 = lean_ctor_get(x_1508, 1);
lean_inc(x_1512);
lean_dec(x_1508);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1513 = l_Lean_Elab_Term_ensureHasType(x_5, x_1511, x_1444, x_10, x_11, x_12, x_13, x_14, x_15, x_1512);
if (lean_obj_tag(x_1513) == 0)
{
lean_object* x_1514; lean_object* x_1515; 
lean_dec(x_1448);
x_1514 = lean_ctor_get(x_1513, 0);
lean_inc(x_1514);
x_1515 = lean_ctor_get(x_1513, 1);
lean_inc(x_1515);
lean_dec(x_1513);
x_1481 = x_1514;
x_1482 = x_1515;
goto block_1503;
}
else
{
lean_object* x_1516; lean_object* x_1517; 
x_1516 = lean_ctor_get(x_1513, 0);
lean_inc(x_1516);
x_1517 = lean_ctor_get(x_1513, 1);
lean_inc(x_1517);
lean_dec(x_1513);
x_1449 = x_1516;
x_1450 = x_1517;
goto block_1480;
}
}
}
else
{
lean_object* x_1518; lean_object* x_1519; 
lean_dec(x_5);
x_1518 = lean_ctor_get(x_1508, 0);
lean_inc(x_1518);
x_1519 = lean_ctor_get(x_1508, 1);
lean_inc(x_1519);
lean_dec(x_1508);
x_1449 = x_1518;
x_1450 = x_1519;
goto block_1480;
}
}
else
{
lean_object* x_1520; lean_object* x_1521; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1520 = lean_ctor_get(x_1505, 0);
lean_inc(x_1520);
x_1521 = lean_ctor_get(x_1505, 1);
lean_inc(x_1521);
lean_dec(x_1505);
x_1449 = x_1520;
x_1450 = x_1521;
goto block_1480;
}
block_1480:
{
if (lean_obj_tag(x_1449) == 0)
{
lean_object* x_1451; uint8_t x_1452; 
lean_dec(x_1448);
x_1451 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1450);
x_1452 = !lean_is_exclusive(x_1451);
if (x_1452 == 0)
{
lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; uint8_t x_1456; 
x_1453 = lean_ctor_get(x_1451, 0);
x_1454 = lean_ctor_get(x_1451, 1);
x_1455 = l_Lean_Elab_Term_SavedState_restore(x_1446, x_10, x_11, x_12, x_13, x_14, x_15, x_1454);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1456 = !lean_is_exclusive(x_1455);
if (x_1456 == 0)
{
lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; 
x_1457 = lean_ctor_get(x_1455, 1);
x_1458 = lean_ctor_get(x_1455, 0);
lean_dec(x_1458);
lean_ctor_set_tag(x_1455, 1);
lean_ctor_set(x_1455, 1, x_1453);
lean_ctor_set(x_1455, 0, x_1449);
x_1459 = lean_array_push(x_9, x_1455);
lean_ctor_set(x_1451, 1, x_1457);
lean_ctor_set(x_1451, 0, x_1459);
return x_1451;
}
else
{
lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; 
x_1460 = lean_ctor_get(x_1455, 1);
lean_inc(x_1460);
lean_dec(x_1455);
x_1461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1461, 0, x_1449);
lean_ctor_set(x_1461, 1, x_1453);
x_1462 = lean_array_push(x_9, x_1461);
lean_ctor_set(x_1451, 1, x_1460);
lean_ctor_set(x_1451, 0, x_1462);
return x_1451;
}
}
else
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; 
x_1463 = lean_ctor_get(x_1451, 0);
x_1464 = lean_ctor_get(x_1451, 1);
lean_inc(x_1464);
lean_inc(x_1463);
lean_dec(x_1451);
x_1465 = l_Lean_Elab_Term_SavedState_restore(x_1446, x_10, x_11, x_12, x_13, x_14, x_15, x_1464);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1466 = lean_ctor_get(x_1465, 1);
lean_inc(x_1466);
if (lean_is_exclusive(x_1465)) {
 lean_ctor_release(x_1465, 0);
 lean_ctor_release(x_1465, 1);
 x_1467 = x_1465;
} else {
 lean_dec_ref(x_1465);
 x_1467 = lean_box(0);
}
if (lean_is_scalar(x_1467)) {
 x_1468 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1468 = x_1467;
 lean_ctor_set_tag(x_1468, 1);
}
lean_ctor_set(x_1468, 0, x_1449);
lean_ctor_set(x_1468, 1, x_1463);
x_1469 = lean_array_push(x_9, x_1468);
x_1470 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1470, 0, x_1469);
lean_ctor_set(x_1470, 1, x_1466);
return x_1470;
}
}
else
{
lean_object* x_1471; lean_object* x_1472; uint8_t x_1473; 
lean_dec(x_9);
x_1471 = lean_ctor_get(x_1449, 0);
lean_inc(x_1471);
x_1472 = l_Lean_Elab_postponeExceptionId;
x_1473 = lean_nat_dec_eq(x_1471, x_1472);
lean_dec(x_1471);
if (x_1473 == 0)
{
lean_object* x_1474; 
lean_dec(x_1446);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_1448)) {
 x_1474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1474 = x_1448;
 lean_ctor_set_tag(x_1474, 1);
}
lean_ctor_set(x_1474, 0, x_1449);
lean_ctor_set(x_1474, 1, x_1450);
return x_1474;
}
else
{
lean_object* x_1475; uint8_t x_1476; 
lean_dec(x_1448);
x_1475 = l_Lean_Elab_Term_SavedState_restore(x_1446, x_10, x_11, x_12, x_13, x_14, x_15, x_1450);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1476 = !lean_is_exclusive(x_1475);
if (x_1476 == 0)
{
lean_object* x_1477; 
x_1477 = lean_ctor_get(x_1475, 0);
lean_dec(x_1477);
lean_ctor_set_tag(x_1475, 1);
lean_ctor_set(x_1475, 0, x_1449);
return x_1475;
}
else
{
lean_object* x_1478; lean_object* x_1479; 
x_1478 = lean_ctor_get(x_1475, 1);
lean_inc(x_1478);
lean_dec(x_1475);
x_1479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1479, 0, x_1449);
lean_ctor_set(x_1479, 1, x_1478);
return x_1479;
}
}
}
}
block_1503:
{
lean_object* x_1483; uint8_t x_1484; 
x_1483 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1482);
x_1484 = !lean_is_exclusive(x_1483);
if (x_1484 == 0)
{
lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; uint8_t x_1488; 
x_1485 = lean_ctor_get(x_1483, 0);
x_1486 = lean_ctor_get(x_1483, 1);
x_1487 = l_Lean_Elab_Term_SavedState_restore(x_1446, x_10, x_11, x_12, x_13, x_14, x_15, x_1486);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1488 = !lean_is_exclusive(x_1487);
if (x_1488 == 0)
{
lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; 
x_1489 = lean_ctor_get(x_1487, 1);
x_1490 = lean_ctor_get(x_1487, 0);
lean_dec(x_1490);
lean_ctor_set(x_1487, 1, x_1485);
lean_ctor_set(x_1487, 0, x_1481);
x_1491 = lean_array_push(x_9, x_1487);
lean_ctor_set(x_1483, 1, x_1489);
lean_ctor_set(x_1483, 0, x_1491);
return x_1483;
}
else
{
lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; 
x_1492 = lean_ctor_get(x_1487, 1);
lean_inc(x_1492);
lean_dec(x_1487);
x_1493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1493, 0, x_1481);
lean_ctor_set(x_1493, 1, x_1485);
x_1494 = lean_array_push(x_9, x_1493);
lean_ctor_set(x_1483, 1, x_1492);
lean_ctor_set(x_1483, 0, x_1494);
return x_1483;
}
}
else
{
lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; 
x_1495 = lean_ctor_get(x_1483, 0);
x_1496 = lean_ctor_get(x_1483, 1);
lean_inc(x_1496);
lean_inc(x_1495);
lean_dec(x_1483);
x_1497 = l_Lean_Elab_Term_SavedState_restore(x_1446, x_10, x_11, x_12, x_13, x_14, x_15, x_1496);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1498 = lean_ctor_get(x_1497, 1);
lean_inc(x_1498);
if (lean_is_exclusive(x_1497)) {
 lean_ctor_release(x_1497, 0);
 lean_ctor_release(x_1497, 1);
 x_1499 = x_1497;
} else {
 lean_dec_ref(x_1497);
 x_1499 = lean_box(0);
}
if (lean_is_scalar(x_1499)) {
 x_1500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1500 = x_1499;
}
lean_ctor_set(x_1500, 0, x_1481);
lean_ctor_set(x_1500, 1, x_1495);
x_1501 = lean_array_push(x_9, x_1500);
x_1502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1502, 0, x_1501);
lean_ctor_set(x_1502, 1, x_1498);
return x_1502;
}
}
}
else
{
uint8_t x_1522; 
x_1522 = l_Array_isEmpty___rarg(x_3);
if (x_1522 == 0)
{
lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1560; lean_object* x_1561; uint8_t x_1583; lean_object* x_1584; 
x_1523 = lean_box(0);
x_1524 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_1525 = lean_ctor_get(x_1524, 0);
lean_inc(x_1525);
x_1526 = lean_ctor_get(x_1524, 1);
lean_inc(x_1526);
if (lean_is_exclusive(x_1524)) {
 lean_ctor_release(x_1524, 0);
 lean_ctor_release(x_1524, 1);
 x_1527 = x_1524;
} else {
 lean_dec_ref(x_1524);
 x_1527 = lean_box(0);
}
x_1583 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1584 = l_Lean_Elab_Term_elabTerm(x_1, x_1523, x_1443, x_1583, x_10, x_11, x_12, x_13, x_14, x_15, x_1526);
if (lean_obj_tag(x_1584) == 0)
{
lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; 
x_1585 = lean_ctor_get(x_1584, 0);
lean_inc(x_1585);
x_1586 = lean_ctor_get(x_1584, 1);
lean_inc(x_1586);
lean_dec(x_1584);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_1587 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_1585, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_1586);
if (lean_obj_tag(x_1587) == 0)
{
if (x_8 == 0)
{
lean_object* x_1588; lean_object* x_1589; 
lean_dec(x_1527);
lean_dec(x_5);
x_1588 = lean_ctor_get(x_1587, 0);
lean_inc(x_1588);
x_1589 = lean_ctor_get(x_1587, 1);
lean_inc(x_1589);
lean_dec(x_1587);
x_1560 = x_1588;
x_1561 = x_1589;
goto block_1582;
}
else
{
lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; 
x_1590 = lean_ctor_get(x_1587, 0);
lean_inc(x_1590);
x_1591 = lean_ctor_get(x_1587, 1);
lean_inc(x_1591);
lean_dec(x_1587);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1592 = l_Lean_Elab_Term_ensureHasType(x_5, x_1590, x_1523, x_10, x_11, x_12, x_13, x_14, x_15, x_1591);
if (lean_obj_tag(x_1592) == 0)
{
lean_object* x_1593; lean_object* x_1594; 
lean_dec(x_1527);
x_1593 = lean_ctor_get(x_1592, 0);
lean_inc(x_1593);
x_1594 = lean_ctor_get(x_1592, 1);
lean_inc(x_1594);
lean_dec(x_1592);
x_1560 = x_1593;
x_1561 = x_1594;
goto block_1582;
}
else
{
lean_object* x_1595; lean_object* x_1596; 
x_1595 = lean_ctor_get(x_1592, 0);
lean_inc(x_1595);
x_1596 = lean_ctor_get(x_1592, 1);
lean_inc(x_1596);
lean_dec(x_1592);
x_1528 = x_1595;
x_1529 = x_1596;
goto block_1559;
}
}
}
else
{
lean_object* x_1597; lean_object* x_1598; 
lean_dec(x_5);
x_1597 = lean_ctor_get(x_1587, 0);
lean_inc(x_1597);
x_1598 = lean_ctor_get(x_1587, 1);
lean_inc(x_1598);
lean_dec(x_1587);
x_1528 = x_1597;
x_1529 = x_1598;
goto block_1559;
}
}
else
{
lean_object* x_1599; lean_object* x_1600; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1599 = lean_ctor_get(x_1584, 0);
lean_inc(x_1599);
x_1600 = lean_ctor_get(x_1584, 1);
lean_inc(x_1600);
lean_dec(x_1584);
x_1528 = x_1599;
x_1529 = x_1600;
goto block_1559;
}
block_1559:
{
if (lean_obj_tag(x_1528) == 0)
{
lean_object* x_1530; uint8_t x_1531; 
lean_dec(x_1527);
x_1530 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1529);
x_1531 = !lean_is_exclusive(x_1530);
if (x_1531 == 0)
{
lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; uint8_t x_1535; 
x_1532 = lean_ctor_get(x_1530, 0);
x_1533 = lean_ctor_get(x_1530, 1);
x_1534 = l_Lean_Elab_Term_SavedState_restore(x_1525, x_10, x_11, x_12, x_13, x_14, x_15, x_1533);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1535 = !lean_is_exclusive(x_1534);
if (x_1535 == 0)
{
lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; 
x_1536 = lean_ctor_get(x_1534, 1);
x_1537 = lean_ctor_get(x_1534, 0);
lean_dec(x_1537);
lean_ctor_set_tag(x_1534, 1);
lean_ctor_set(x_1534, 1, x_1532);
lean_ctor_set(x_1534, 0, x_1528);
x_1538 = lean_array_push(x_9, x_1534);
lean_ctor_set(x_1530, 1, x_1536);
lean_ctor_set(x_1530, 0, x_1538);
return x_1530;
}
else
{
lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; 
x_1539 = lean_ctor_get(x_1534, 1);
lean_inc(x_1539);
lean_dec(x_1534);
x_1540 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1540, 0, x_1528);
lean_ctor_set(x_1540, 1, x_1532);
x_1541 = lean_array_push(x_9, x_1540);
lean_ctor_set(x_1530, 1, x_1539);
lean_ctor_set(x_1530, 0, x_1541);
return x_1530;
}
}
else
{
lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; 
x_1542 = lean_ctor_get(x_1530, 0);
x_1543 = lean_ctor_get(x_1530, 1);
lean_inc(x_1543);
lean_inc(x_1542);
lean_dec(x_1530);
x_1544 = l_Lean_Elab_Term_SavedState_restore(x_1525, x_10, x_11, x_12, x_13, x_14, x_15, x_1543);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1545 = lean_ctor_get(x_1544, 1);
lean_inc(x_1545);
if (lean_is_exclusive(x_1544)) {
 lean_ctor_release(x_1544, 0);
 lean_ctor_release(x_1544, 1);
 x_1546 = x_1544;
} else {
 lean_dec_ref(x_1544);
 x_1546 = lean_box(0);
}
if (lean_is_scalar(x_1546)) {
 x_1547 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1547 = x_1546;
 lean_ctor_set_tag(x_1547, 1);
}
lean_ctor_set(x_1547, 0, x_1528);
lean_ctor_set(x_1547, 1, x_1542);
x_1548 = lean_array_push(x_9, x_1547);
x_1549 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1549, 0, x_1548);
lean_ctor_set(x_1549, 1, x_1545);
return x_1549;
}
}
else
{
lean_object* x_1550; lean_object* x_1551; uint8_t x_1552; 
lean_dec(x_9);
x_1550 = lean_ctor_get(x_1528, 0);
lean_inc(x_1550);
x_1551 = l_Lean_Elab_postponeExceptionId;
x_1552 = lean_nat_dec_eq(x_1550, x_1551);
lean_dec(x_1550);
if (x_1552 == 0)
{
lean_object* x_1553; 
lean_dec(x_1525);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_1527)) {
 x_1553 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1553 = x_1527;
 lean_ctor_set_tag(x_1553, 1);
}
lean_ctor_set(x_1553, 0, x_1528);
lean_ctor_set(x_1553, 1, x_1529);
return x_1553;
}
else
{
lean_object* x_1554; uint8_t x_1555; 
lean_dec(x_1527);
x_1554 = l_Lean_Elab_Term_SavedState_restore(x_1525, x_10, x_11, x_12, x_13, x_14, x_15, x_1529);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1555 = !lean_is_exclusive(x_1554);
if (x_1555 == 0)
{
lean_object* x_1556; 
x_1556 = lean_ctor_get(x_1554, 0);
lean_dec(x_1556);
lean_ctor_set_tag(x_1554, 1);
lean_ctor_set(x_1554, 0, x_1528);
return x_1554;
}
else
{
lean_object* x_1557; lean_object* x_1558; 
x_1557 = lean_ctor_get(x_1554, 1);
lean_inc(x_1557);
lean_dec(x_1554);
x_1558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1558, 0, x_1528);
lean_ctor_set(x_1558, 1, x_1557);
return x_1558;
}
}
}
}
block_1582:
{
lean_object* x_1562; uint8_t x_1563; 
x_1562 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1561);
x_1563 = !lean_is_exclusive(x_1562);
if (x_1563 == 0)
{
lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; uint8_t x_1567; 
x_1564 = lean_ctor_get(x_1562, 0);
x_1565 = lean_ctor_get(x_1562, 1);
x_1566 = l_Lean_Elab_Term_SavedState_restore(x_1525, x_10, x_11, x_12, x_13, x_14, x_15, x_1565);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1567 = !lean_is_exclusive(x_1566);
if (x_1567 == 0)
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; 
x_1568 = lean_ctor_get(x_1566, 1);
x_1569 = lean_ctor_get(x_1566, 0);
lean_dec(x_1569);
lean_ctor_set(x_1566, 1, x_1564);
lean_ctor_set(x_1566, 0, x_1560);
x_1570 = lean_array_push(x_9, x_1566);
lean_ctor_set(x_1562, 1, x_1568);
lean_ctor_set(x_1562, 0, x_1570);
return x_1562;
}
else
{
lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; 
x_1571 = lean_ctor_get(x_1566, 1);
lean_inc(x_1571);
lean_dec(x_1566);
x_1572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1572, 0, x_1560);
lean_ctor_set(x_1572, 1, x_1564);
x_1573 = lean_array_push(x_9, x_1572);
lean_ctor_set(x_1562, 1, x_1571);
lean_ctor_set(x_1562, 0, x_1573);
return x_1562;
}
}
else
{
lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; 
x_1574 = lean_ctor_get(x_1562, 0);
x_1575 = lean_ctor_get(x_1562, 1);
lean_inc(x_1575);
lean_inc(x_1574);
lean_dec(x_1562);
x_1576 = l_Lean_Elab_Term_SavedState_restore(x_1525, x_10, x_11, x_12, x_13, x_14, x_15, x_1575);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1577 = lean_ctor_get(x_1576, 1);
lean_inc(x_1577);
if (lean_is_exclusive(x_1576)) {
 lean_ctor_release(x_1576, 0);
 lean_ctor_release(x_1576, 1);
 x_1578 = x_1576;
} else {
 lean_dec_ref(x_1576);
 x_1578 = lean_box(0);
}
if (lean_is_scalar(x_1578)) {
 x_1579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1579 = x_1578;
}
lean_ctor_set(x_1579, 0, x_1560);
lean_ctor_set(x_1579, 1, x_1574);
x_1580 = lean_array_push(x_9, x_1579);
x_1581 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1581, 0, x_1580);
lean_ctor_set(x_1581, 1, x_1577);
return x_1581;
}
}
}
else
{
uint8_t x_1601; 
x_1601 = l_Array_isEmpty___rarg(x_4);
if (x_1601 == 0)
{
lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1639; lean_object* x_1640; uint8_t x_1662; lean_object* x_1663; 
x_1602 = lean_box(0);
x_1603 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_1604 = lean_ctor_get(x_1603, 0);
lean_inc(x_1604);
x_1605 = lean_ctor_get(x_1603, 1);
lean_inc(x_1605);
if (lean_is_exclusive(x_1603)) {
 lean_ctor_release(x_1603, 0);
 lean_ctor_release(x_1603, 1);
 x_1606 = x_1603;
} else {
 lean_dec_ref(x_1603);
 x_1606 = lean_box(0);
}
x_1662 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1663 = l_Lean_Elab_Term_elabTerm(x_1, x_1602, x_1443, x_1662, x_10, x_11, x_12, x_13, x_14, x_15, x_1605);
if (lean_obj_tag(x_1663) == 0)
{
lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; 
x_1664 = lean_ctor_get(x_1663, 0);
lean_inc(x_1664);
x_1665 = lean_ctor_get(x_1663, 1);
lean_inc(x_1665);
lean_dec(x_1663);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_1666 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_1664, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_1665);
if (lean_obj_tag(x_1666) == 0)
{
if (x_8 == 0)
{
lean_object* x_1667; lean_object* x_1668; 
lean_dec(x_1606);
lean_dec(x_5);
x_1667 = lean_ctor_get(x_1666, 0);
lean_inc(x_1667);
x_1668 = lean_ctor_get(x_1666, 1);
lean_inc(x_1668);
lean_dec(x_1666);
x_1639 = x_1667;
x_1640 = x_1668;
goto block_1661;
}
else
{
lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; 
x_1669 = lean_ctor_get(x_1666, 0);
lean_inc(x_1669);
x_1670 = lean_ctor_get(x_1666, 1);
lean_inc(x_1670);
lean_dec(x_1666);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1671 = l_Lean_Elab_Term_ensureHasType(x_5, x_1669, x_1602, x_10, x_11, x_12, x_13, x_14, x_15, x_1670);
if (lean_obj_tag(x_1671) == 0)
{
lean_object* x_1672; lean_object* x_1673; 
lean_dec(x_1606);
x_1672 = lean_ctor_get(x_1671, 0);
lean_inc(x_1672);
x_1673 = lean_ctor_get(x_1671, 1);
lean_inc(x_1673);
lean_dec(x_1671);
x_1639 = x_1672;
x_1640 = x_1673;
goto block_1661;
}
else
{
lean_object* x_1674; lean_object* x_1675; 
x_1674 = lean_ctor_get(x_1671, 0);
lean_inc(x_1674);
x_1675 = lean_ctor_get(x_1671, 1);
lean_inc(x_1675);
lean_dec(x_1671);
x_1607 = x_1674;
x_1608 = x_1675;
goto block_1638;
}
}
}
else
{
lean_object* x_1676; lean_object* x_1677; 
lean_dec(x_5);
x_1676 = lean_ctor_get(x_1666, 0);
lean_inc(x_1676);
x_1677 = lean_ctor_get(x_1666, 1);
lean_inc(x_1677);
lean_dec(x_1666);
x_1607 = x_1676;
x_1608 = x_1677;
goto block_1638;
}
}
else
{
lean_object* x_1678; lean_object* x_1679; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1678 = lean_ctor_get(x_1663, 0);
lean_inc(x_1678);
x_1679 = lean_ctor_get(x_1663, 1);
lean_inc(x_1679);
lean_dec(x_1663);
x_1607 = x_1678;
x_1608 = x_1679;
goto block_1638;
}
block_1638:
{
if (lean_obj_tag(x_1607) == 0)
{
lean_object* x_1609; uint8_t x_1610; 
lean_dec(x_1606);
x_1609 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1608);
x_1610 = !lean_is_exclusive(x_1609);
if (x_1610 == 0)
{
lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; uint8_t x_1614; 
x_1611 = lean_ctor_get(x_1609, 0);
x_1612 = lean_ctor_get(x_1609, 1);
x_1613 = l_Lean_Elab_Term_SavedState_restore(x_1604, x_10, x_11, x_12, x_13, x_14, x_15, x_1612);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1614 = !lean_is_exclusive(x_1613);
if (x_1614 == 0)
{
lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; 
x_1615 = lean_ctor_get(x_1613, 1);
x_1616 = lean_ctor_get(x_1613, 0);
lean_dec(x_1616);
lean_ctor_set_tag(x_1613, 1);
lean_ctor_set(x_1613, 1, x_1611);
lean_ctor_set(x_1613, 0, x_1607);
x_1617 = lean_array_push(x_9, x_1613);
lean_ctor_set(x_1609, 1, x_1615);
lean_ctor_set(x_1609, 0, x_1617);
return x_1609;
}
else
{
lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; 
x_1618 = lean_ctor_get(x_1613, 1);
lean_inc(x_1618);
lean_dec(x_1613);
x_1619 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1619, 0, x_1607);
lean_ctor_set(x_1619, 1, x_1611);
x_1620 = lean_array_push(x_9, x_1619);
lean_ctor_set(x_1609, 1, x_1618);
lean_ctor_set(x_1609, 0, x_1620);
return x_1609;
}
}
else
{
lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; 
x_1621 = lean_ctor_get(x_1609, 0);
x_1622 = lean_ctor_get(x_1609, 1);
lean_inc(x_1622);
lean_inc(x_1621);
lean_dec(x_1609);
x_1623 = l_Lean_Elab_Term_SavedState_restore(x_1604, x_10, x_11, x_12, x_13, x_14, x_15, x_1622);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1624 = lean_ctor_get(x_1623, 1);
lean_inc(x_1624);
if (lean_is_exclusive(x_1623)) {
 lean_ctor_release(x_1623, 0);
 lean_ctor_release(x_1623, 1);
 x_1625 = x_1623;
} else {
 lean_dec_ref(x_1623);
 x_1625 = lean_box(0);
}
if (lean_is_scalar(x_1625)) {
 x_1626 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1626 = x_1625;
 lean_ctor_set_tag(x_1626, 1);
}
lean_ctor_set(x_1626, 0, x_1607);
lean_ctor_set(x_1626, 1, x_1621);
x_1627 = lean_array_push(x_9, x_1626);
x_1628 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1628, 0, x_1627);
lean_ctor_set(x_1628, 1, x_1624);
return x_1628;
}
}
else
{
lean_object* x_1629; lean_object* x_1630; uint8_t x_1631; 
lean_dec(x_9);
x_1629 = lean_ctor_get(x_1607, 0);
lean_inc(x_1629);
x_1630 = l_Lean_Elab_postponeExceptionId;
x_1631 = lean_nat_dec_eq(x_1629, x_1630);
lean_dec(x_1629);
if (x_1631 == 0)
{
lean_object* x_1632; 
lean_dec(x_1604);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_1606)) {
 x_1632 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1632 = x_1606;
 lean_ctor_set_tag(x_1632, 1);
}
lean_ctor_set(x_1632, 0, x_1607);
lean_ctor_set(x_1632, 1, x_1608);
return x_1632;
}
else
{
lean_object* x_1633; uint8_t x_1634; 
lean_dec(x_1606);
x_1633 = l_Lean_Elab_Term_SavedState_restore(x_1604, x_10, x_11, x_12, x_13, x_14, x_15, x_1608);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1634 = !lean_is_exclusive(x_1633);
if (x_1634 == 0)
{
lean_object* x_1635; 
x_1635 = lean_ctor_get(x_1633, 0);
lean_dec(x_1635);
lean_ctor_set_tag(x_1633, 1);
lean_ctor_set(x_1633, 0, x_1607);
return x_1633;
}
else
{
lean_object* x_1636; lean_object* x_1637; 
x_1636 = lean_ctor_get(x_1633, 1);
lean_inc(x_1636);
lean_dec(x_1633);
x_1637 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1637, 0, x_1607);
lean_ctor_set(x_1637, 1, x_1636);
return x_1637;
}
}
}
}
block_1661:
{
lean_object* x_1641; uint8_t x_1642; 
x_1641 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1640);
x_1642 = !lean_is_exclusive(x_1641);
if (x_1642 == 0)
{
lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; uint8_t x_1646; 
x_1643 = lean_ctor_get(x_1641, 0);
x_1644 = lean_ctor_get(x_1641, 1);
x_1645 = l_Lean_Elab_Term_SavedState_restore(x_1604, x_10, x_11, x_12, x_13, x_14, x_15, x_1644);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1646 = !lean_is_exclusive(x_1645);
if (x_1646 == 0)
{
lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; 
x_1647 = lean_ctor_get(x_1645, 1);
x_1648 = lean_ctor_get(x_1645, 0);
lean_dec(x_1648);
lean_ctor_set(x_1645, 1, x_1643);
lean_ctor_set(x_1645, 0, x_1639);
x_1649 = lean_array_push(x_9, x_1645);
lean_ctor_set(x_1641, 1, x_1647);
lean_ctor_set(x_1641, 0, x_1649);
return x_1641;
}
else
{
lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; 
x_1650 = lean_ctor_get(x_1645, 1);
lean_inc(x_1650);
lean_dec(x_1645);
x_1651 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1651, 0, x_1639);
lean_ctor_set(x_1651, 1, x_1643);
x_1652 = lean_array_push(x_9, x_1651);
lean_ctor_set(x_1641, 1, x_1650);
lean_ctor_set(x_1641, 0, x_1652);
return x_1641;
}
}
else
{
lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; 
x_1653 = lean_ctor_get(x_1641, 0);
x_1654 = lean_ctor_get(x_1641, 1);
lean_inc(x_1654);
lean_inc(x_1653);
lean_dec(x_1641);
x_1655 = l_Lean_Elab_Term_SavedState_restore(x_1604, x_10, x_11, x_12, x_13, x_14, x_15, x_1654);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1656 = lean_ctor_get(x_1655, 1);
lean_inc(x_1656);
if (lean_is_exclusive(x_1655)) {
 lean_ctor_release(x_1655, 0);
 lean_ctor_release(x_1655, 1);
 x_1657 = x_1655;
} else {
 lean_dec_ref(x_1655);
 x_1657 = lean_box(0);
}
if (lean_is_scalar(x_1657)) {
 x_1658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1658 = x_1657;
}
lean_ctor_set(x_1658, 0, x_1639);
lean_ctor_set(x_1658, 1, x_1653);
x_1659 = lean_array_push(x_9, x_1658);
x_1660 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1660, 0, x_1659);
lean_ctor_set(x_1660, 1, x_1656);
return x_1660;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_8 == 0)
{
lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; uint8_t x_1707; lean_object* x_1708; 
x_1680 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_1681 = lean_ctor_get(x_1680, 0);
lean_inc(x_1681);
x_1682 = lean_ctor_get(x_1680, 1);
lean_inc(x_1682);
if (lean_is_exclusive(x_1680)) {
 lean_ctor_release(x_1680, 0);
 lean_ctor_release(x_1680, 1);
 x_1683 = x_1680;
} else {
 lean_dec_ref(x_1680);
 x_1683 = lean_box(0);
}
x_1707 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1708 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_1707, x_1707, x_10, x_11, x_12, x_13, x_14, x_15, x_1682);
if (lean_obj_tag(x_1708) == 0)
{
lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; uint8_t x_1715; 
lean_dec(x_1683);
x_1709 = lean_ctor_get(x_1708, 0);
lean_inc(x_1709);
x_1710 = lean_ctor_get(x_1708, 1);
lean_inc(x_1710);
lean_dec(x_1708);
x_1711 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1710);
x_1712 = lean_ctor_get(x_1711, 0);
lean_inc(x_1712);
x_1713 = lean_ctor_get(x_1711, 1);
lean_inc(x_1713);
lean_dec(x_1711);
x_1714 = l_Lean_Elab_Term_SavedState_restore(x_1681, x_10, x_11, x_12, x_13, x_14, x_15, x_1713);
x_1715 = !lean_is_exclusive(x_1714);
if (x_1715 == 0)
{
lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; 
x_1716 = lean_ctor_get(x_1714, 1);
x_1717 = lean_ctor_get(x_1714, 0);
lean_dec(x_1717);
lean_ctor_set(x_1714, 1, x_1712);
lean_ctor_set(x_1714, 0, x_1709);
x_1718 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1714, x_10, x_11, x_12, x_13, x_14, x_15, x_1716);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1718;
}
else
{
lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; 
x_1719 = lean_ctor_get(x_1714, 1);
lean_inc(x_1719);
lean_dec(x_1714);
x_1720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1720, 0, x_1709);
lean_ctor_set(x_1720, 1, x_1712);
x_1721 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1720, x_10, x_11, x_12, x_13, x_14, x_15, x_1719);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1721;
}
}
else
{
lean_object* x_1722; lean_object* x_1723; 
x_1722 = lean_ctor_get(x_1708, 0);
lean_inc(x_1722);
x_1723 = lean_ctor_get(x_1708, 1);
lean_inc(x_1723);
lean_dec(x_1708);
x_1684 = x_1722;
x_1685 = x_1723;
goto block_1706;
}
block_1706:
{
if (lean_obj_tag(x_1684) == 0)
{
lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; uint8_t x_1690; 
lean_dec(x_1683);
x_1686 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1685);
x_1687 = lean_ctor_get(x_1686, 0);
lean_inc(x_1687);
x_1688 = lean_ctor_get(x_1686, 1);
lean_inc(x_1688);
lean_dec(x_1686);
x_1689 = l_Lean_Elab_Term_SavedState_restore(x_1681, x_10, x_11, x_12, x_13, x_14, x_15, x_1688);
x_1690 = !lean_is_exclusive(x_1689);
if (x_1690 == 0)
{
lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; 
x_1691 = lean_ctor_get(x_1689, 1);
x_1692 = lean_ctor_get(x_1689, 0);
lean_dec(x_1692);
lean_ctor_set_tag(x_1689, 1);
lean_ctor_set(x_1689, 1, x_1687);
lean_ctor_set(x_1689, 0, x_1684);
x_1693 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1689, x_10, x_11, x_12, x_13, x_14, x_15, x_1691);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1693;
}
else
{
lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; 
x_1694 = lean_ctor_get(x_1689, 1);
lean_inc(x_1694);
lean_dec(x_1689);
x_1695 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1695, 0, x_1684);
lean_ctor_set(x_1695, 1, x_1687);
x_1696 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1695, x_10, x_11, x_12, x_13, x_14, x_15, x_1694);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1696;
}
}
else
{
lean_object* x_1697; lean_object* x_1698; uint8_t x_1699; 
lean_dec(x_9);
x_1697 = lean_ctor_get(x_1684, 0);
lean_inc(x_1697);
x_1698 = l_Lean_Elab_postponeExceptionId;
x_1699 = lean_nat_dec_eq(x_1697, x_1698);
lean_dec(x_1697);
if (x_1699 == 0)
{
lean_object* x_1700; 
lean_dec(x_1681);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_1683)) {
 x_1700 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1700 = x_1683;
 lean_ctor_set_tag(x_1700, 1);
}
lean_ctor_set(x_1700, 0, x_1684);
lean_ctor_set(x_1700, 1, x_1685);
return x_1700;
}
else
{
lean_object* x_1701; uint8_t x_1702; 
lean_dec(x_1683);
x_1701 = l_Lean_Elab_Term_SavedState_restore(x_1681, x_10, x_11, x_12, x_13, x_14, x_15, x_1685);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1702 = !lean_is_exclusive(x_1701);
if (x_1702 == 0)
{
lean_object* x_1703; 
x_1703 = lean_ctor_get(x_1701, 0);
lean_dec(x_1703);
lean_ctor_set_tag(x_1701, 1);
lean_ctor_set(x_1701, 0, x_1684);
return x_1701;
}
else
{
lean_object* x_1704; lean_object* x_1705; 
x_1704 = lean_ctor_get(x_1701, 1);
lean_inc(x_1704);
lean_dec(x_1701);
x_1705 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1705, 0, x_1684);
lean_ctor_set(x_1705, 1, x_1704);
return x_1705;
}
}
}
}
}
else
{
lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; uint8_t x_1752; lean_object* x_1753; 
x_1724 = lean_box(0);
x_1725 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_1726 = lean_ctor_get(x_1725, 0);
lean_inc(x_1726);
x_1727 = lean_ctor_get(x_1725, 1);
lean_inc(x_1727);
if (lean_is_exclusive(x_1725)) {
 lean_ctor_release(x_1725, 0);
 lean_ctor_release(x_1725, 1);
 x_1728 = x_1725;
} else {
 lean_dec_ref(x_1725);
 x_1728 = lean_box(0);
}
x_1752 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1753 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_1443, x_1752, x_1724, x_10, x_11, x_12, x_13, x_14, x_15, x_1727);
if (lean_obj_tag(x_1753) == 0)
{
lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; uint8_t x_1760; 
lean_dec(x_1728);
x_1754 = lean_ctor_get(x_1753, 0);
lean_inc(x_1754);
x_1755 = lean_ctor_get(x_1753, 1);
lean_inc(x_1755);
lean_dec(x_1753);
x_1756 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1755);
x_1757 = lean_ctor_get(x_1756, 0);
lean_inc(x_1757);
x_1758 = lean_ctor_get(x_1756, 1);
lean_inc(x_1758);
lean_dec(x_1756);
x_1759 = l_Lean_Elab_Term_SavedState_restore(x_1726, x_10, x_11, x_12, x_13, x_14, x_15, x_1758);
x_1760 = !lean_is_exclusive(x_1759);
if (x_1760 == 0)
{
lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; 
x_1761 = lean_ctor_get(x_1759, 1);
x_1762 = lean_ctor_get(x_1759, 0);
lean_dec(x_1762);
lean_ctor_set(x_1759, 1, x_1757);
lean_ctor_set(x_1759, 0, x_1754);
x_1763 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1759, x_10, x_11, x_12, x_13, x_14, x_15, x_1761);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1763;
}
else
{
lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; 
x_1764 = lean_ctor_get(x_1759, 1);
lean_inc(x_1764);
lean_dec(x_1759);
x_1765 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1765, 0, x_1754);
lean_ctor_set(x_1765, 1, x_1757);
x_1766 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1765, x_10, x_11, x_12, x_13, x_14, x_15, x_1764);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1766;
}
}
else
{
lean_object* x_1767; lean_object* x_1768; 
x_1767 = lean_ctor_get(x_1753, 0);
lean_inc(x_1767);
x_1768 = lean_ctor_get(x_1753, 1);
lean_inc(x_1768);
lean_dec(x_1753);
x_1729 = x_1767;
x_1730 = x_1768;
goto block_1751;
}
block_1751:
{
if (lean_obj_tag(x_1729) == 0)
{
lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; uint8_t x_1735; 
lean_dec(x_1728);
x_1731 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1730);
x_1732 = lean_ctor_get(x_1731, 0);
lean_inc(x_1732);
x_1733 = lean_ctor_get(x_1731, 1);
lean_inc(x_1733);
lean_dec(x_1731);
x_1734 = l_Lean_Elab_Term_SavedState_restore(x_1726, x_10, x_11, x_12, x_13, x_14, x_15, x_1733);
x_1735 = !lean_is_exclusive(x_1734);
if (x_1735 == 0)
{
lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; 
x_1736 = lean_ctor_get(x_1734, 1);
x_1737 = lean_ctor_get(x_1734, 0);
lean_dec(x_1737);
lean_ctor_set_tag(x_1734, 1);
lean_ctor_set(x_1734, 1, x_1732);
lean_ctor_set(x_1734, 0, x_1729);
x_1738 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1734, x_10, x_11, x_12, x_13, x_14, x_15, x_1736);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1738;
}
else
{
lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; 
x_1739 = lean_ctor_get(x_1734, 1);
lean_inc(x_1739);
lean_dec(x_1734);
x_1740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1740, 0, x_1729);
lean_ctor_set(x_1740, 1, x_1732);
x_1741 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1740, x_10, x_11, x_12, x_13, x_14, x_15, x_1739);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1741;
}
}
else
{
lean_object* x_1742; lean_object* x_1743; uint8_t x_1744; 
lean_dec(x_9);
x_1742 = lean_ctor_get(x_1729, 0);
lean_inc(x_1742);
x_1743 = l_Lean_Elab_postponeExceptionId;
x_1744 = lean_nat_dec_eq(x_1742, x_1743);
lean_dec(x_1742);
if (x_1744 == 0)
{
lean_object* x_1745; 
lean_dec(x_1726);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_1728)) {
 x_1745 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1745 = x_1728;
 lean_ctor_set_tag(x_1745, 1);
}
lean_ctor_set(x_1745, 0, x_1729);
lean_ctor_set(x_1745, 1, x_1730);
return x_1745;
}
else
{
lean_object* x_1746; uint8_t x_1747; 
lean_dec(x_1728);
x_1746 = l_Lean_Elab_Term_SavedState_restore(x_1726, x_10, x_11, x_12, x_13, x_14, x_15, x_1730);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1747 = !lean_is_exclusive(x_1746);
if (x_1747 == 0)
{
lean_object* x_1748; 
x_1748 = lean_ctor_get(x_1746, 0);
lean_dec(x_1748);
lean_ctor_set_tag(x_1746, 1);
lean_ctor_set(x_1746, 0, x_1729);
return x_1746;
}
else
{
lean_object* x_1749; lean_object* x_1750; 
x_1749 = lean_ctor_get(x_1746, 1);
lean_inc(x_1749);
lean_dec(x_1746);
x_1750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1750, 0, x_1729);
lean_ctor_set(x_1750, 1, x_1749);
return x_1750;
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
else
{
lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; 
lean_dec(x_1);
x_1772 = l_Lean_Syntax_getId(x_1437);
x_1773 = lean_erase_macro_scopes(x_1772);
x_1774 = l_Lean_Name_components(x_1773);
x_1775 = l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(x_1437, x_1774);
x_1776 = l_List_append___rarg(x_1775, x_2);
x_1 = x_1435;
x_2 = x_1776;
goto _start;
}
}
else
{
lean_object* x_1778; lean_object* x_1779; 
lean_dec(x_1);
x_1778 = l_Lean_fieldIdxKind;
x_1779 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_1778, x_1437);
if (lean_obj_tag(x_1779) == 0)
{
lean_object* x_1780; lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; 
x_1780 = l_instInhabitedNat;
x_1781 = l_Option_get_x21___rarg___closed__4;
x_1782 = lean_panic_fn(x_1780, x_1781);
x_1783 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1783, 0, x_1437);
lean_ctor_set(x_1783, 1, x_1782);
x_1784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1784, 0, x_1783);
lean_ctor_set(x_1784, 1, x_2);
x_1 = x_1435;
x_2 = x_1784;
goto _start;
}
else
{
lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; 
x_1786 = lean_ctor_get(x_1779, 0);
lean_inc(x_1786);
lean_dec(x_1779);
x_1787 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1787, 0, x_1437);
lean_ctor_set(x_1787, 1, x_1786);
x_1788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1788, 0, x_1787);
lean_ctor_set(x_1788, 1, x_2);
x_1 = x_1435;
x_2 = x_1788;
goto _start;
}
}
}
}
else
{
lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; uint8_t x_1793; 
x_1790 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_1791 = lean_array_get_size(x_1790);
x_1792 = lean_unsigned_to_nat(0u);
x_1793 = lean_nat_dec_lt(x_1792, x_1791);
if (x_1793 == 0)
{
lean_object* x_1794; 
lean_dec(x_1791);
lean_dec(x_1790);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1794 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1794, 0, x_9);
lean_ctor_set(x_1794, 1, x_16);
return x_1794;
}
else
{
uint8_t x_1795; 
x_1795 = !lean_is_exclusive(x_10);
if (x_1795 == 0)
{
uint8_t x_1796; uint8_t x_1797; 
x_1796 = 0;
lean_ctor_set_uint8(x_10, sizeof(void*)*8 + 1, x_1796);
x_1797 = lean_nat_dec_le(x_1791, x_1791);
if (x_1797 == 0)
{
lean_object* x_1798; 
lean_dec(x_10);
lean_dec(x_1791);
lean_dec(x_1790);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1798 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1798, 0, x_9);
lean_ctor_set(x_1798, 1, x_16);
return x_1798;
}
else
{
size_t x_1799; size_t x_1800; lean_object* x_1801; 
x_1799 = 0;
x_1800 = lean_usize_of_nat(x_1791);
lean_dec(x_1791);
x_1801 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__4(x_2, x_3, x_4, x_5, x_6, x_7, x_1790, x_1799, x_1800, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1790);
return x_1801;
}
}
else
{
lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; uint8_t x_1807; uint8_t x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; uint8_t x_1812; uint8_t x_1813; lean_object* x_1814; uint8_t x_1815; 
x_1802 = lean_ctor_get(x_10, 0);
x_1803 = lean_ctor_get(x_10, 1);
x_1804 = lean_ctor_get(x_10, 2);
x_1805 = lean_ctor_get(x_10, 3);
x_1806 = lean_ctor_get(x_10, 4);
x_1807 = lean_ctor_get_uint8(x_10, sizeof(void*)*8);
x_1808 = lean_ctor_get_uint8(x_10, sizeof(void*)*8 + 2);
x_1809 = lean_ctor_get(x_10, 5);
x_1810 = lean_ctor_get(x_10, 6);
x_1811 = lean_ctor_get(x_10, 7);
x_1812 = lean_ctor_get_uint8(x_10, sizeof(void*)*8 + 3);
lean_inc(x_1811);
lean_inc(x_1810);
lean_inc(x_1809);
lean_inc(x_1806);
lean_inc(x_1805);
lean_inc(x_1804);
lean_inc(x_1803);
lean_inc(x_1802);
lean_dec(x_10);
x_1813 = 0;
x_1814 = lean_alloc_ctor(0, 8, 4);
lean_ctor_set(x_1814, 0, x_1802);
lean_ctor_set(x_1814, 1, x_1803);
lean_ctor_set(x_1814, 2, x_1804);
lean_ctor_set(x_1814, 3, x_1805);
lean_ctor_set(x_1814, 4, x_1806);
lean_ctor_set(x_1814, 5, x_1809);
lean_ctor_set(x_1814, 6, x_1810);
lean_ctor_set(x_1814, 7, x_1811);
lean_ctor_set_uint8(x_1814, sizeof(void*)*8, x_1807);
lean_ctor_set_uint8(x_1814, sizeof(void*)*8 + 1, x_1813);
lean_ctor_set_uint8(x_1814, sizeof(void*)*8 + 2, x_1808);
lean_ctor_set_uint8(x_1814, sizeof(void*)*8 + 3, x_1812);
x_1815 = lean_nat_dec_le(x_1791, x_1791);
if (x_1815 == 0)
{
lean_object* x_1816; 
lean_dec(x_1814);
lean_dec(x_1791);
lean_dec(x_1790);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1816 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1816, 0, x_9);
lean_ctor_set(x_1816, 1, x_16);
return x_1816;
}
else
{
size_t x_1817; size_t x_1818; lean_object* x_1819; 
x_1817 = 0;
x_1818 = lean_usize_of_nat(x_1791);
lean_dec(x_1791);
x_1819 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__4(x_2, x_3, x_4, x_5, x_6, x_7, x_1790, x_1817, x_1818, x_9, x_1814, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1790);
return x_1819;
}
}
}
}
block_348:
{
uint8_t x_18; uint8_t x_19; 
lean_dec(x_17);
x_18 = l_List_isEmpty___rarg(x_2);
if (x_8 == 0)
{
uint8_t x_346; 
x_346 = 1;
x_19 = x_346;
goto block_345;
}
else
{
uint8_t x_347; 
x_347 = 0;
x_19 = x_347;
goto block_345;
}
block_345:
{
if (x_18 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_57; lean_object* x_58; uint8_t x_80; lean_object* x_81; 
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_80 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_81 = l_Lean_Elab_Term_elabTerm(x_1, x_20, x_19, x_80, x_10, x_11, x_12, x_13, x_14, x_15, x_23);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_84 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_83);
if (lean_obj_tag(x_84) == 0)
{
if (x_8 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_24);
lean_dec(x_5);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_57 = x_85;
x_58 = x_86;
goto block_79;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_89 = l_Lean_Elab_Term_ensureHasType(x_5, x_87, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_24);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_57 = x_90;
x_58 = x_91;
goto block_79;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
lean_dec(x_89);
x_25 = x_92;
x_26 = x_93;
goto block_56;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_5);
x_94 = lean_ctor_get(x_84, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_84, 1);
lean_inc(x_95);
lean_dec(x_84);
x_25 = x_94;
x_26 = x_95;
goto block_56;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_ctor_get(x_81, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_81, 1);
lean_inc(x_97);
lean_dec(x_81);
x_25 = x_96;
x_26 = x_97;
goto block_56;
}
block_56:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = l_Lean_Elab_Term_SavedState_restore(x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 1);
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 0, x_25);
x_35 = lean_array_push(x_9, x_31);
lean_ctor_set(x_27, 1, x_33);
lean_ctor_set(x_27, 0, x_35);
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_29);
x_38 = lean_array_push(x_9, x_37);
lean_ctor_set(x_27, 1, x_36);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_27);
x_41 = l_Lean_Elab_Term_SavedState_restore(x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
 lean_ctor_set_tag(x_44, 1);
}
lean_ctor_set(x_44, 0, x_25);
lean_ctor_set(x_44, 1, x_39);
x_45 = lean_array_push(x_9, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_9);
x_47 = lean_ctor_get(x_25, 0);
lean_inc(x_47);
x_48 = l_Lean_Elab_postponeExceptionId;
x_49 = lean_nat_dec_eq(x_47, x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_24)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_24;
 lean_ctor_set_tag(x_50, 1);
}
lean_ctor_set(x_50, 0, x_25);
lean_ctor_set(x_50, 1, x_26);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_dec(x_24);
x_51 = l_Lean_Elab_Term_SavedState_restore(x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_25);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_25);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
block_79:
{
lean_object* x_59; uint8_t x_60; 
x_59 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_58);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
x_63 = l_Lean_Elab_Term_SavedState_restore(x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_62);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 1);
x_66 = lean_ctor_get(x_63, 0);
lean_dec(x_66);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 0, x_57);
x_67 = lean_array_push(x_9, x_63);
lean_ctor_set(x_59, 1, x_65);
lean_ctor_set(x_59, 0, x_67);
return x_59;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_57);
lean_ctor_set(x_69, 1, x_61);
x_70 = lean_array_push(x_9, x_69);
lean_ctor_set(x_59, 1, x_68);
lean_ctor_set(x_59, 0, x_70);
return x_59;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_59, 0);
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_59);
x_73 = l_Lean_Elab_Term_SavedState_restore(x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_72);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_57);
lean_ctor_set(x_76, 1, x_71);
x_77 = lean_array_push(x_9, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
return x_78;
}
}
}
else
{
uint8_t x_98; 
x_98 = l_Array_isEmpty___rarg(x_3);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_136; lean_object* x_137; uint8_t x_159; lean_object* x_160; 
x_99 = lean_box(0);
x_100 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_159 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_160 = l_Lean_Elab_Term_elabTerm(x_1, x_99, x_19, x_159, x_10, x_11, x_12, x_13, x_14, x_15, x_102);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_163 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_161, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_162);
if (lean_obj_tag(x_163) == 0)
{
if (x_8 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_103);
lean_dec(x_5);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_136 = x_164;
x_137 = x_165;
goto block_158;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_163, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_163, 1);
lean_inc(x_167);
lean_dec(x_163);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_168 = l_Lean_Elab_Term_ensureHasType(x_5, x_166, x_99, x_10, x_11, x_12, x_13, x_14, x_15, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_103);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_136 = x_169;
x_137 = x_170;
goto block_158;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_168, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_168, 1);
lean_inc(x_172);
lean_dec(x_168);
x_104 = x_171;
x_105 = x_172;
goto block_135;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_5);
x_173 = lean_ctor_get(x_163, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_163, 1);
lean_inc(x_174);
lean_dec(x_163);
x_104 = x_173;
x_105 = x_174;
goto block_135;
}
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_175 = lean_ctor_get(x_160, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_160, 1);
lean_inc(x_176);
lean_dec(x_160);
x_104 = x_175;
x_105 = x_176;
goto block_135;
}
block_135:
{
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_106; uint8_t x_107; 
lean_dec(x_103);
x_106 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_105);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_ctor_get(x_106, 1);
x_110 = l_Lean_Elab_Term_SavedState_restore(x_101, x_10, x_11, x_12, x_13, x_14, x_15, x_109);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_110, 1);
x_113 = lean_ctor_get(x_110, 0);
lean_dec(x_113);
lean_ctor_set_tag(x_110, 1);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set(x_110, 0, x_104);
x_114 = lean_array_push(x_9, x_110);
lean_ctor_set(x_106, 1, x_112);
lean_ctor_set(x_106, 0, x_114);
return x_106;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_104);
lean_ctor_set(x_116, 1, x_108);
x_117 = lean_array_push(x_9, x_116);
lean_ctor_set(x_106, 1, x_115);
lean_ctor_set(x_106, 0, x_117);
return x_106;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_106, 0);
x_119 = lean_ctor_get(x_106, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_106);
x_120 = l_Lean_Elab_Term_SavedState_restore(x_101, x_10, x_11, x_12, x_13, x_14, x_15, x_119);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
 lean_ctor_set_tag(x_123, 1);
}
lean_ctor_set(x_123, 0, x_104);
lean_ctor_set(x_123, 1, x_118);
x_124 = lean_array_push(x_9, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_121);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_9);
x_126 = lean_ctor_get(x_104, 0);
lean_inc(x_126);
x_127 = l_Lean_Elab_postponeExceptionId;
x_128 = lean_nat_dec_eq(x_126, x_127);
lean_dec(x_126);
if (x_128 == 0)
{
lean_object* x_129; 
lean_dec(x_101);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_103)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_103;
 lean_ctor_set_tag(x_129, 1);
}
lean_ctor_set(x_129, 0, x_104);
lean_ctor_set(x_129, 1, x_105);
return x_129;
}
else
{
lean_object* x_130; uint8_t x_131; 
lean_dec(x_103);
x_130 = l_Lean_Elab_Term_SavedState_restore(x_101, x_10, x_11, x_12, x_13, x_14, x_15, x_105);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_130, 0);
lean_dec(x_132);
lean_ctor_set_tag(x_130, 1);
lean_ctor_set(x_130, 0, x_104);
return x_130;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_104);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
block_158:
{
lean_object* x_138; uint8_t x_139; 
x_138 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_137);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_ctor_get(x_138, 1);
x_142 = l_Lean_Elab_Term_SavedState_restore(x_101, x_10, x_11, x_12, x_13, x_14, x_15, x_141);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_142, 1);
x_145 = lean_ctor_get(x_142, 0);
lean_dec(x_145);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 0, x_136);
x_146 = lean_array_push(x_9, x_142);
lean_ctor_set(x_138, 1, x_144);
lean_ctor_set(x_138, 0, x_146);
return x_138;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_dec(x_142);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_136);
lean_ctor_set(x_148, 1, x_140);
x_149 = lean_array_push(x_9, x_148);
lean_ctor_set(x_138, 1, x_147);
lean_ctor_set(x_138, 0, x_149);
return x_138;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_150 = lean_ctor_get(x_138, 0);
x_151 = lean_ctor_get(x_138, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_138);
x_152 = l_Lean_Elab_Term_SavedState_restore(x_101, x_10, x_11, x_12, x_13, x_14, x_15, x_151);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_136);
lean_ctor_set(x_155, 1, x_150);
x_156 = lean_array_push(x_9, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_153);
return x_157;
}
}
}
else
{
uint8_t x_177; 
x_177 = l_Array_isEmpty___rarg(x_4);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_215; lean_object* x_216; uint8_t x_238; lean_object* x_239; 
x_178 = lean_box(0);
x_179 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_182 = x_179;
} else {
 lean_dec_ref(x_179);
 x_182 = lean_box(0);
}
x_238 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_239 = l_Lean_Elab_Term_elabTerm(x_1, x_178, x_19, x_238, x_10, x_11, x_12, x_13, x_14, x_15, x_181);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_242 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_240, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_241);
if (lean_obj_tag(x_242) == 0)
{
if (x_8 == 0)
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_182);
lean_dec(x_5);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_215 = x_243;
x_216 = x_244;
goto block_237;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_242, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_242, 1);
lean_inc(x_246);
lean_dec(x_242);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_247 = l_Lean_Elab_Term_ensureHasType(x_5, x_245, x_178, x_10, x_11, x_12, x_13, x_14, x_15, x_246);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_182);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_215 = x_248;
x_216 = x_249;
goto block_237;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_247, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_247, 1);
lean_inc(x_251);
lean_dec(x_247);
x_183 = x_250;
x_184 = x_251;
goto block_214;
}
}
}
else
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_5);
x_252 = lean_ctor_get(x_242, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_242, 1);
lean_inc(x_253);
lean_dec(x_242);
x_183 = x_252;
x_184 = x_253;
goto block_214;
}
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_254 = lean_ctor_get(x_239, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_239, 1);
lean_inc(x_255);
lean_dec(x_239);
x_183 = x_254;
x_184 = x_255;
goto block_214;
}
block_214:
{
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_185; uint8_t x_186; 
lean_dec(x_182);
x_185 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_184);
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_187 = lean_ctor_get(x_185, 0);
x_188 = lean_ctor_get(x_185, 1);
x_189 = l_Lean_Elab_Term_SavedState_restore(x_180, x_10, x_11, x_12, x_13, x_14, x_15, x_188);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_190 = !lean_is_exclusive(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_189, 1);
x_192 = lean_ctor_get(x_189, 0);
lean_dec(x_192);
lean_ctor_set_tag(x_189, 1);
lean_ctor_set(x_189, 1, x_187);
lean_ctor_set(x_189, 0, x_183);
x_193 = lean_array_push(x_9, x_189);
lean_ctor_set(x_185, 1, x_191);
lean_ctor_set(x_185, 0, x_193);
return x_185;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_189, 1);
lean_inc(x_194);
lean_dec(x_189);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_183);
lean_ctor_set(x_195, 1, x_187);
x_196 = lean_array_push(x_9, x_195);
lean_ctor_set(x_185, 1, x_194);
lean_ctor_set(x_185, 0, x_196);
return x_185;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_197 = lean_ctor_get(x_185, 0);
x_198 = lean_ctor_get(x_185, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_185);
x_199 = l_Lean_Elab_Term_SavedState_restore(x_180, x_10, x_11, x_12, x_13, x_14, x_15, x_198);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_201 = x_199;
} else {
 lean_dec_ref(x_199);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
 lean_ctor_set_tag(x_202, 1);
}
lean_ctor_set(x_202, 0, x_183);
lean_ctor_set(x_202, 1, x_197);
x_203 = lean_array_push(x_9, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_200);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; 
lean_dec(x_9);
x_205 = lean_ctor_get(x_183, 0);
lean_inc(x_205);
x_206 = l_Lean_Elab_postponeExceptionId;
x_207 = lean_nat_dec_eq(x_205, x_206);
lean_dec(x_205);
if (x_207 == 0)
{
lean_object* x_208; 
lean_dec(x_180);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_182)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_182;
 lean_ctor_set_tag(x_208, 1);
}
lean_ctor_set(x_208, 0, x_183);
lean_ctor_set(x_208, 1, x_184);
return x_208;
}
else
{
lean_object* x_209; uint8_t x_210; 
lean_dec(x_182);
x_209 = l_Lean_Elab_Term_SavedState_restore(x_180, x_10, x_11, x_12, x_13, x_14, x_15, x_184);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_209, 0);
lean_dec(x_211);
lean_ctor_set_tag(x_209, 1);
lean_ctor_set(x_209, 0, x_183);
return x_209;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec(x_209);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_183);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
}
block_237:
{
lean_object* x_217; uint8_t x_218; 
x_217 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_216);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_219 = lean_ctor_get(x_217, 0);
x_220 = lean_ctor_get(x_217, 1);
x_221 = l_Lean_Elab_Term_SavedState_restore(x_180, x_10, x_11, x_12, x_13, x_14, x_15, x_220);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_221, 1);
x_224 = lean_ctor_get(x_221, 0);
lean_dec(x_224);
lean_ctor_set(x_221, 1, x_219);
lean_ctor_set(x_221, 0, x_215);
x_225 = lean_array_push(x_9, x_221);
lean_ctor_set(x_217, 1, x_223);
lean_ctor_set(x_217, 0, x_225);
return x_217;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_221, 1);
lean_inc(x_226);
lean_dec(x_221);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_215);
lean_ctor_set(x_227, 1, x_219);
x_228 = lean_array_push(x_9, x_227);
lean_ctor_set(x_217, 1, x_226);
lean_ctor_set(x_217, 0, x_228);
return x_217;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_229 = lean_ctor_get(x_217, 0);
x_230 = lean_ctor_get(x_217, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_217);
x_231 = l_Lean_Elab_Term_SavedState_restore(x_180, x_10, x_11, x_12, x_13, x_14, x_15, x_230);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_215);
lean_ctor_set(x_234, 1, x_229);
x_235 = lean_array_push(x_9, x_234);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_232);
return x_236;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_8 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_283; lean_object* x_284; 
x_256 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_259 = x_256;
} else {
 lean_dec_ref(x_256);
 x_259 = lean_box(0);
}
x_283 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_284 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_283, x_283, x_10, x_11, x_12, x_13, x_14, x_15, x_258);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
lean_dec(x_259);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_286);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = l_Lean_Elab_Term_SavedState_restore(x_257, x_10, x_11, x_12, x_13, x_14, x_15, x_289);
x_291 = !lean_is_exclusive(x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_290, 1);
x_293 = lean_ctor_get(x_290, 0);
lean_dec(x_293);
lean_ctor_set(x_290, 1, x_288);
lean_ctor_set(x_290, 0, x_285);
x_294 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_290, x_10, x_11, x_12, x_13, x_14, x_15, x_292);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_290, 1);
lean_inc(x_295);
lean_dec(x_290);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_285);
lean_ctor_set(x_296, 1, x_288);
x_297 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_296, x_10, x_11, x_12, x_13, x_14, x_15, x_295);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_284, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_284, 1);
lean_inc(x_299);
lean_dec(x_284);
x_260 = x_298;
x_261 = x_299;
goto block_282;
}
block_282:
{
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
lean_dec(x_259);
x_262 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_261);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = l_Lean_Elab_Term_SavedState_restore(x_257, x_10, x_11, x_12, x_13, x_14, x_15, x_264);
x_266 = !lean_is_exclusive(x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_265, 1);
x_268 = lean_ctor_get(x_265, 0);
lean_dec(x_268);
lean_ctor_set_tag(x_265, 1);
lean_ctor_set(x_265, 1, x_263);
lean_ctor_set(x_265, 0, x_260);
x_269 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_265, x_10, x_11, x_12, x_13, x_14, x_15, x_267);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_265, 1);
lean_inc(x_270);
lean_dec(x_265);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_260);
lean_ctor_set(x_271, 1, x_263);
x_272 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_271, x_10, x_11, x_12, x_13, x_14, x_15, x_270);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; 
lean_dec(x_9);
x_273 = lean_ctor_get(x_260, 0);
lean_inc(x_273);
x_274 = l_Lean_Elab_postponeExceptionId;
x_275 = lean_nat_dec_eq(x_273, x_274);
lean_dec(x_273);
if (x_275 == 0)
{
lean_object* x_276; 
lean_dec(x_257);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_259)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_259;
 lean_ctor_set_tag(x_276, 1);
}
lean_ctor_set(x_276, 0, x_260);
lean_ctor_set(x_276, 1, x_261);
return x_276;
}
else
{
lean_object* x_277; uint8_t x_278; 
lean_dec(x_259);
x_277 = l_Lean_Elab_Term_SavedState_restore(x_257, x_10, x_11, x_12, x_13, x_14, x_15, x_261);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_278 = !lean_is_exclusive(x_277);
if (x_278 == 0)
{
lean_object* x_279; 
x_279 = lean_ctor_get(x_277, 0);
lean_dec(x_279);
lean_ctor_set_tag(x_277, 1);
lean_ctor_set(x_277, 0, x_260);
return x_277;
}
else
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_277, 1);
lean_inc(x_280);
lean_dec(x_277);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_260);
lean_ctor_set(x_281, 1, x_280);
return x_281;
}
}
}
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_328; lean_object* x_329; 
x_300 = lean_box(0);
x_301 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_304 = x_301;
} else {
 lean_dec_ref(x_301);
 x_304 = lean_box(0);
}
x_328 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_329 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_19, x_328, x_300, x_10, x_11, x_12, x_13, x_14, x_15, x_303);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
lean_dec(x_304);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
x_332 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_331);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = l_Lean_Elab_Term_SavedState_restore(x_302, x_10, x_11, x_12, x_13, x_14, x_15, x_334);
x_336 = !lean_is_exclusive(x_335);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_335, 1);
x_338 = lean_ctor_get(x_335, 0);
lean_dec(x_338);
lean_ctor_set(x_335, 1, x_333);
lean_ctor_set(x_335, 0, x_330);
x_339 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_335, x_10, x_11, x_12, x_13, x_14, x_15, x_337);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_335, 1);
lean_inc(x_340);
lean_dec(x_335);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_330);
lean_ctor_set(x_341, 1, x_333);
x_342 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_341, x_10, x_11, x_12, x_13, x_14, x_15, x_340);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_342;
}
}
else
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_329, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_329, 1);
lean_inc(x_344);
lean_dec(x_329);
x_305 = x_343;
x_306 = x_344;
goto block_327;
}
block_327:
{
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
lean_dec(x_304);
x_307 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_306);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = l_Lean_Elab_Term_SavedState_restore(x_302, x_10, x_11, x_12, x_13, x_14, x_15, x_309);
x_311 = !lean_is_exclusive(x_310);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_310, 1);
x_313 = lean_ctor_get(x_310, 0);
lean_dec(x_313);
lean_ctor_set_tag(x_310, 1);
lean_ctor_set(x_310, 1, x_308);
lean_ctor_set(x_310, 0, x_305);
x_314 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_310, x_10, x_11, x_12, x_13, x_14, x_15, x_312);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_314;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_310, 1);
lean_inc(x_315);
lean_dec(x_310);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_305);
lean_ctor_set(x_316, 1, x_308);
x_317 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_316, x_10, x_11, x_12, x_13, x_14, x_15, x_315);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_317;
}
}
else
{
lean_object* x_318; lean_object* x_319; uint8_t x_320; 
lean_dec(x_9);
x_318 = lean_ctor_get(x_305, 0);
lean_inc(x_318);
x_319 = l_Lean_Elab_postponeExceptionId;
x_320 = lean_nat_dec_eq(x_318, x_319);
lean_dec(x_318);
if (x_320 == 0)
{
lean_object* x_321; 
lean_dec(x_302);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_304)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_304;
 lean_ctor_set_tag(x_321, 1);
}
lean_ctor_set(x_321, 0, x_305);
lean_ctor_set(x_321, 1, x_306);
return x_321;
}
else
{
lean_object* x_322; uint8_t x_323; 
lean_dec(x_304);
x_322 = l_Lean_Elab_Term_SavedState_restore(x_302, x_10, x_11, x_12, x_13, x_14, x_15, x_306);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_323 = !lean_is_exclusive(x_322);
if (x_323 == 0)
{
lean_object* x_324; 
x_324 = lean_ctor_get(x_322, 0);
lean_dec(x_324);
lean_ctor_set_tag(x_322, 1);
lean_ctor_set(x_322, 0, x_305);
return x_322;
}
else
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_ctor_get(x_322, 1);
lean_inc(x_325);
lean_dec(x_322);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_305);
lean_ctor_set(x_326, 1, x_325);
return x_326;
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
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__4___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_unbox(x_5);
lean_dec(x_5);
x_19 = lean_unbox(x_6);
lean_dec(x_6);
x_20 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_21 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_22 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__4(x_1, x_2, x_3, x_4, x_18, x_19, x_7, x_20, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_7);
return x_22;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = lean_unbox(x_8);
lean_dec(x_8);
x_20 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess(x_6);
x_8 = 1;
x_9 = x_2 + x_8;
if (x_7 == 0)
{
lean_dec(x_6);
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_11; 
x_11 = lean_array_push(x_4, x_6);
x_2 = x_9;
x_4 = x_11;
goto _start;
}
}
else
{
return x_4;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Array_empty___closed__1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Array_empty___closed__1;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Array_empty___closed__1;
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = 0;
x_6 = l_Lean_Syntax_getPos_x3f(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
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
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg___boxed), 3, 0);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_myMacro____x40_Init_Notation___hyg_15378____closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg(x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Exception_getRef(x_1);
x_13 = 0;
x_14 = l_Lean_Syntax_getPos_x3f(x_12, x_13);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_11);
x_15 = l_Lean_Exception_toMessageData(x_1);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_nat_dec_eq(x_11, x_16);
lean_dec(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_18 = lean_ctor_get(x_2, 1);
x_19 = l_Lean_FileMap_toPosition(x_18, x_16);
lean_dec(x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_KernelException_toMessageData___closed__15;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_substCore___lambda__1___closed__3;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Exception_toMessageData(x_1);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
lean_ctor_set(x_9, 0, x_35);
return x_9;
}
else
{
lean_object* x_36; 
lean_dec(x_16);
x_36 = l_Lean_Exception_toMessageData(x_1);
lean_ctor_set(x_9, 0, x_36);
return x_9;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_9, 0);
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_9);
x_39 = l_Lean_Exception_getRef(x_1);
x_40 = 0;
x_41 = l_Lean_Syntax_getPos_x3f(x_39, x_40);
lean_dec(x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_37);
x_42 = l_Lean_Exception_toMessageData(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_nat_dec_eq(x_37, x_44);
lean_dec(x_37);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_46 = lean_ctor_get(x_2, 1);
x_47 = l_Lean_FileMap_toPosition(x_46, x_44);
lean_dec(x_44);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_KernelException_toMessageData___closed__15;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_dec(x_47);
x_56 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_substCore___lambda__1___closed__3;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Exception_toMessageData(x_1);
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_51);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_38);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_44);
x_65 = l_Lean_Exception_toMessageData(x_1);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_38);
return x_66;
}
}
}
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_array_to_list(lean_box(0), x_1);
x_3 = l_Lean_Elab_goalsToMessageData___closed__2;
x_4 = l_Lean_MessageData_joinSep(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_indentD(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.App");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.App.0.Lean.Elab.Term.mergeFailures");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1;
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(874u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_2 < x_1;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = x_3;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = x_14;
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
x_18 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_19 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3;
x_20 = lean_panic_fn(x_18, x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = lean_apply_7(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = x_2 + x_24;
x_26 = x_22;
x_27 = lean_array_uset(x_16, x_2, x_26);
x_2 = x_25;
x_3 = x_27;
x_10 = x_23;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = 1;
x_38 = x_2 + x_37;
x_39 = x_35;
x_40 = lean_array_uset(x_16, x_2, x_39);
x_2 = x_38;
x_3 = x_40;
x_10 = x_36;
goto _start;
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("overloaded, errors ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = x_1;
x_12 = lean_box_usize(x_10);
x_13 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___boxed__const__1;
x_14 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___boxed), 10, 3);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_11);
x_15 = x_14;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_16 = lean_apply_7(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList(x_17);
x_20 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_KernelException_toMessageData___closed__15;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__2___rarg(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.App.0.Lean.Elab.Term.elabAppAux");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1;
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(891u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 < x_3;
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = x_5;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_5, x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_5, x_4, x_9);
x_11 = x_8;
x_12 = 1;
x_13 = x_4 + x_12;
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_2);
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_1);
lean_ctor_set(x_20, 3, x_2);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_22 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = x_22;
x_24 = lean_array_uset(x_10, x_4, x_23);
x_4 = x_13;
x_5 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_11);
x_26 = l_Lean_instInhabitedMessageData;
x_27 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2;
x_28 = lean_panic_fn(x_26, x_27);
x_29 = x_28;
x_30 = lean_array_uset(x_10, x_4, x_29);
x_4 = x_13;
x_5 = x_30;
goto _start;
}
}
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_22 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_23);
return x_24;
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous, possible interpretations ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedExpr;
x_2 = l_Lean_Elab_Term_instInhabitedTermElabResult___rarg(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = 0;
x_15 = l_Array_empty___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(x_1, x_13, x_2, x_3, x_5, x_14, x_4, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_get_size(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess(x_17);
x_23 = lean_array_get_size(x_22);
x_24 = lean_nat_dec_eq(x_23, x_20);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_nat_dec_lt(x_20, x_23);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_23);
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 3);
x_28 = l_Lean_replaceRef(x_1, x_27);
lean_dec(x_27);
lean_dec(x_1);
lean_ctor_set(x_10, 3, x_28);
x_29 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
x_32 = lean_ctor_get(x_10, 2);
x_33 = lean_ctor_get(x_10, 3);
x_34 = lean_ctor_get(x_10, 4);
x_35 = lean_ctor_get(x_10, 5);
x_36 = lean_ctor_get(x_10, 6);
x_37 = lean_ctor_get(x_10, 7);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_38 = l_Lean_replaceRef(x_1, x_33);
lean_dec(x_33);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_31);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_39, 4, x_34);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_39, 6, x_36);
lean_ctor_set(x_39, 7, x_37);
x_40 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg(x_17, x_6, x_7, x_8, x_9, x_39, x_11, x_18);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_17);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_42);
x_43 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_44 = 0;
x_45 = x_22;
x_46 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1(x_41, x_42, x_43, x_44, x_45);
x_47 = x_46;
x_48 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList(x_47);
x_49 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_KernelException_toMessageData___closed__15;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_throwErrorAt___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__2(x_1, x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_1);
x_54 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__3;
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_array_get(x_54, x_22, x_55);
lean_dec(x_22);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Elab_Term_SavedState_restore(x_58, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_56, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
lean_dec(x_56);
x_66 = l_Lean_Elab_Term_SavedState_restore(x_65, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_71 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__3;
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_array_get(x_71, x_17, x_72);
lean_dec(x_17);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Term_SavedState_restore(x_75, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_74);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_73, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_73, 1);
lean_inc(x_82);
lean_dec(x_73);
x_83 = l_Lean_Elab_Term_SavedState_restore(x_82, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
lean_ctor_set_tag(x_83, 1);
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_16);
if (x_88 == 0)
{
return x_16;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_16, 0);
x_90 = lean_ctor_get(x_16, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_16);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_expandArgs_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandArgs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandArgs_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandArgs_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandArgs_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandArgs_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_expandArgs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_expandArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_expandArgs___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_22 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_expandArgs___spec__2(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_23);
return x_24;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected '..'");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 == x_3;
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_1, x_2);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_17 = l_Lean_Syntax_getKind(x_13);
x_18 = l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
x_19 = lean_name_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Parser_Term_ellipsis___elambda__1___closed__2;
x_21 = lean_name_eq(x_17, x_20);
lean_dec(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_13);
x_23 = lean_array_push(x_16, x_22);
lean_ctor_set(x_4, 1, x_23);
x_24 = 1;
x_25 = x_2 + x_24;
x_2 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_free_object(x_4);
lean_dec(x_16);
lean_dec(x_15);
x_27 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___closed__2;
x_28 = l_Lean_throwErrorAt___at_Lean_Elab_Term_expandArgs___spec__1(x_13, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_13);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_17);
x_33 = lean_unsigned_to_nat(1u);
x_34 = l_Lean_Syntax_getArg(x_13, x_33);
x_35 = l_Lean_Syntax_getId(x_34);
lean_dec(x_34);
x_36 = lean_erase_macro_scopes(x_35);
x_37 = lean_unsigned_to_nat(3u);
x_38 = l_Lean_Syntax_getArg(x_13, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_13);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_5);
x_41 = l_Lean_Elab_Term_addNamedArg(x_15, x_40, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_ctor_set(x_4, 0, x_42);
x_44 = 1;
x_45 = x_2 + x_44;
x_2 = x_45;
x_11 = x_43;
goto _start;
}
else
{
uint8_t x_47; 
lean_free_object(x_4);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_41);
if (x_47 == 0)
{
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_41, 0);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_41);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_4, 0);
x_52 = lean_ctor_get(x_4, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_4);
lean_inc(x_13);
x_53 = l_Lean_Syntax_getKind(x_13);
x_54 = l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
x_55 = lean_name_eq(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Parser_Term_ellipsis___elambda__1___closed__2;
x_57 = lean_name_eq(x_53, x_56);
lean_dec(x_53);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; 
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_13);
x_59 = lean_array_push(x_52, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_51);
lean_ctor_set(x_60, 1, x_59);
x_61 = 1;
x_62 = x_2 + x_61;
x_2 = x_62;
x_4 = x_60;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_52);
lean_dec(x_51);
x_64 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___closed__2;
x_65 = l_Lean_throwErrorAt___at_Lean_Elab_Term_expandArgs___spec__1(x_13, x_64, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_13);
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
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_53);
x_70 = lean_unsigned_to_nat(1u);
x_71 = l_Lean_Syntax_getArg(x_13, x_70);
x_72 = l_Lean_Syntax_getId(x_71);
lean_dec(x_71);
x_73 = lean_erase_macro_scopes(x_72);
x_74 = lean_unsigned_to_nat(3u);
x_75 = l_Lean_Syntax_getArg(x_13, x_74);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_13);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_76);
lean_inc(x_5);
x_78 = l_Lean_Elab_Term_addNamedArg(x_51, x_77, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; size_t x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_52);
x_82 = 1;
x_83 = x_2 + x_82;
x_2 = x_83;
x_4 = x_81;
x_11 = x_80;
goto _start;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_52);
lean_dec(x_9);
lean_dec(x_5);
x_85 = lean_ctor_get(x_78, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_87 = x_78;
} else {
 lean_dec_ref(x_78);
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
}
else
{
lean_object* x_89; 
lean_dec(x_9);
lean_dec(x_5);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_4);
lean_ctor_set(x_89, 1, x_11);
return x_89;
}
}
}
lean_object* l_Lean_Elab_Term_expandArgs(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_79; 
x_79 = l_Array_isEmpty___rarg(x_1);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_1);
x_81 = l_Lean_Parser_Term_ellipsis___elambda__1___closed__2;
x_82 = l_Lean_Syntax_isOfKind(x_80, x_81);
if (x_82 == 0)
{
uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_83 = 0;
x_84 = lean_box(x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_84);
x_10 = x_85;
goto block_78;
}
else
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_array_pop(x_1);
x_87 = 1;
x_88 = lean_box(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_10 = x_89;
goto block_78;
}
}
else
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_90 = 0;
x_91 = lean_box(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
x_10 = x_92;
goto block_78;
}
block_78:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_array_get_size(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
x_17 = l_Array_empty___closed__1;
lean_ctor_set(x_10, 0, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_14, x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
x_21 = l_Array_empty___closed__1;
lean_ctor_set(x_10, 0, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_26 = l_Array_split___rarg___closed__1;
x_27 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3(x_12, x_24, x_25, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_ctor_set(x_29, 1, x_13);
lean_ctor_set(x_29, 0, x_32);
lean_ctor_set(x_10, 1, x_29);
lean_ctor_set(x_10, 0, x_31);
lean_ctor_set(x_27, 0, x_10);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_13);
lean_ctor_set(x_10, 1, x_35);
lean_ctor_set(x_10, 0, x_33);
lean_ctor_set(x_27, 0, x_10);
return x_27;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_40 = x_36;
} else {
 lean_dec_ref(x_36);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_13);
lean_ctor_set(x_10, 1, x_41);
lean_ctor_set(x_10, 0, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_10);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_free_object(x_10);
lean_dec(x_13);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
return x_27;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_27, 0);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_27);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_10, 0);
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_10);
x_49 = lean_array_get_size(x_47);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_lt(x_50, x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_7);
lean_dec(x_3);
x_52 = l_Array_empty___closed__1;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_9);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_49, x_49);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_7);
lean_dec(x_3);
x_57 = l_Array_empty___closed__1;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_48);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_9);
return x_60;
}
else
{
size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; 
x_61 = 0;
x_62 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_63 = l_Array_split___rarg___closed__1;
x_64 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3(x_47, x_61, x_62, x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_47);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
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
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_48);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_71);
if (lean_is_scalar(x_67)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_67;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_66);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_48);
x_74 = lean_ctor_get(x_64, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_64, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_76 = x_64;
} else {
 lean_dec_ref(x_64);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_expandArgs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_expandArgs___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_expandArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at_Lean_Elab_Term_expandArgs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_expandArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_Term_expandArgs(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_expandApp_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_expandApp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandApp_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandApp(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Lean_Elab_Term_expandArgs(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_15, 1);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Syntax_getArg(x_1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_15, 1, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_15);
lean_ctor_set(x_14, 0, x_30);
return x_14;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_34 = x_16;
} else {
 lean_dec_ref(x_16);
 x_34 = lean_box(0);
}
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Syntax_getArg(x_1, x_35);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_33);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_14, 0, x_39);
return x_14;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_dec(x_14);
x_41 = lean_ctor_get(x_15, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_42 = x_15;
} else {
 lean_dec_ref(x_15);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_16, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_45 = x_16;
} else {
 lean_dec_ref(x_16);
 x_45 = lean_box(0);
}
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Lean_Syntax_getArg(x_1, x_46);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_44);
if (lean_is_scalar(x_42)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_42;
}
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_40);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_14);
if (x_52 == 0)
{
return x_14;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_14, 0);
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_14);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_Term_expandApp(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabApp_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_apply_4(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_elabApp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabApp_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabApp___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(x_12, x_13, x_14, x_16, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandApp___boxed), 9, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabApp___spec__1___lambda__1), 9, 1);
lean_closure_set(x_13, 0, x_2);
x_19 = l_Lean_Meta_getResetPostponed(x_5, x_6, x_7, x_8, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l_Lean_Meta_processPostponed(x_10, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_23);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(x_3, x_4, x_5, x_6, x_7, x_8, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_setPostponed(x_20, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_box(0);
x_39 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___rarg___lambda__1(x_20, x_23, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_14 = x_40;
x_15 = x_41;
goto block_18;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_dec(x_25);
x_44 = l_Lean_Meta_setPostponed(x_20, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_42);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_4);
lean_dec(x_3);
x_49 = lean_ctor_get(x_22, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_22, 1);
lean_inc(x_50);
lean_dec(x_22);
x_51 = l_Lean_Meta_setPostponed(x_20, x_5, x_6, x_7, x_8, x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_49);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
lean_object* l_Lean_Elab_Term_elabApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabApp), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_myMacro____x40_Init_Notation___hyg_2278____closed__4;
x_4 = l___regBuiltin_Lean_Elab_Term_elabApp___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = l_Array_empty___closed__1;
x_11 = 0;
x_12 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(x_1, x_10, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_elabIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabIdent), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_identKind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabNamedPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNamedPattern), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_namedPattern___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabExplicitUniv), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("|>.");
return x_1;
}
}
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_10, x_11, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Term_getCurrMacroScope(x_6, x_7, x_8, x_9, x_10, x_11, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Elab_Term_getMainModule___rarg(x_11, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Array_empty___closed__1;
x_25 = lean_array_push(x_24, x_1);
x_26 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1___lambda__1___closed__1;
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_array_push(x_25, x_27);
x_29 = lean_array_push(x_28, x_2);
x_30 = l_myMacro____x40_Init_Notation___hyg_1481____closed__8;
x_31 = lean_array_push(x_29, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_unbox(x_16);
lean_dec(x_16);
x_34 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(x_32, x_14, x_15, x_33, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
return x_34;
}
}
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandArgs___boxed), 9, 2);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1___lambda__1), 12, 4);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_4);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_5);
x_25 = l_Lean_Meta_getResetPostponed(x_8, x_9, x_10, x_11, x_12);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_28 = l_ReaderT_bind___at_Lean_Elab_Term_instMonadLogTermElabM___spec__2___rarg(x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_31 = l_Lean_Meta_processPostponed(x_16, x_8, x_9, x_10, x_11, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_29);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_35 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_throwStuckAtUniverseCnstr(x_6, x_7, x_8, x_9, x_10, x_11, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_setPostponed(x_26, x_8, x_9, x_10, x_11, x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_36);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_dec(x_31);
x_44 = lean_box(0);
x_45 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___rarg___lambda__1(x_26, x_29, x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_20 = x_46;
x_21 = x_47;
goto block_24;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_6);
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_dec(x_31);
x_50 = l_Lean_Meta_setPostponed(x_26, x_8, x_9, x_10, x_11, x_49);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set_tag(x_50, 1);
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_7);
lean_dec(x_6);
x_55 = lean_ctor_get(x_28, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_28, 1);
lean_inc(x_56);
lean_dec(x_28);
x_57 = l_Lean_Meta_setPostponed(x_26, x_8, x_9, x_10, x_11, x_56);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
lean_object* l_Lean_Elab_Term_elabPipeProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Parser_Term_pipeProj___elambda__1___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1(x_1, x_10, x_14, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_17;
}
}
}
lean_object* l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabPipeProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabPipeProj), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabPipeProj(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_pipeProj___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabPipeProj___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_myMacro____x40_Init_NotationExtra___hyg_5659____closed__28;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_identKind___closed__2;
lean_inc(x_14);
x_16 = l_Lean_Syntax_isOfKind(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
lean_inc(x_14);
x_18 = l_Lean_Syntax_isOfKind(x_14, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_1);
x_19 = l_myMacro____x40_Init_Notation___hyg_13856____closed__8;
lean_inc(x_14);
x_20 = l_Lean_Syntax_isOfKind(x_14, x_19);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_21 = 1;
x_22 = 0;
x_23 = l_Lean_Elab_Term_elabTerm(x_14, x_2, x_21, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Syntax_getArg(x_14, x_13);
x_25 = l_Lean_nullKind___closed__2;
lean_inc(x_24);
x_26 = l_Lean_Syntax_isOfKind(x_24, x_25);
if (x_26 == 0)
{
uint8_t x_27; uint8_t x_28; lean_object* x_29; 
lean_dec(x_24);
x_27 = 1;
x_28 = 0;
x_29 = l_Lean_Elab_Term_elabTerm(x_14, x_2, x_27, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = l_Lean_Syntax_getArgs(x_24);
x_31 = lean_array_get_size(x_30);
lean_dec(x_30);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_dec_eq(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
uint8_t x_34; uint8_t x_35; lean_object* x_36; 
lean_dec(x_24);
x_34 = 1;
x_35 = 0;
x_36 = l_Lean_Elab_Term_elabTerm(x_14, x_2, x_34, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lean_Syntax_getArg(x_24, x_37);
x_39 = l_Lean_Syntax_getArg(x_24, x_13);
lean_dec(x_24);
lean_inc(x_39);
x_40 = l_Lean_Syntax_isOfKind(x_39, x_25);
if (x_40 == 0)
{
uint8_t x_41; uint8_t x_42; lean_object* x_43; 
lean_dec(x_39);
lean_dec(x_38);
x_41 = 1;
x_42 = 0;
x_43 = l_Lean_Elab_Term_elabTerm(x_14, x_2, x_41, x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = l_Lean_Syntax_getArgs(x_39);
lean_dec(x_39);
x_45 = lean_array_get_size(x_44);
lean_dec(x_44);
x_46 = lean_nat_dec_eq(x_45, x_37);
lean_dec(x_45);
if (x_46 == 0)
{
uint8_t x_47; uint8_t x_48; lean_object* x_49; 
lean_dec(x_38);
x_47 = 1;
x_48 = 0;
x_49 = l_Lean_Elab_Term_elabTerm(x_14, x_2, x_47, x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_49;
}
else
{
uint8_t x_50; uint8_t x_51; lean_object* x_52; 
lean_dec(x_14);
x_50 = 1;
x_51 = 0;
x_52 = l_Lean_Elab_Term_elabTerm(x_38, x_2, x_50, x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_52;
}
}
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Lean_Syntax_getArg(x_14, x_53);
x_55 = l_Lean_Syntax_isOfKind(x_54, x_15);
if (x_55 == 0)
{
uint8_t x_56; uint8_t x_57; lean_object* x_58; 
lean_dec(x_1);
x_56 = 1;
x_57 = 0;
x_58 = l_Lean_Elab_Term_elabTerm(x_14, x_2, x_56, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_58;
}
else
{
lean_object* x_59; 
lean_dec(x_14);
x_59 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_59;
}
}
}
else
{
lean_object* x_60; 
lean_dec(x_14);
x_60 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_60;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabExplicit), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_myMacro____x40_Init_NotationExtra___hyg_5659____closed__28;
x_4 = l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabChoice), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_choiceKind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabProj), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_4 = l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrayRef), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_8911_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_FindMVar(lean_object*);
lean_object* initialize_Lean_Parser_Term(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_App(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__1 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__1();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__1);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__2 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__2();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__2);
l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__3 = _init_l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__3();
lean_mark_persistent(l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4____closed__3);
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_elabWithoutExpectedTypeAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_elabWithoutExpectedTypeAttr);
lean_dec_ref(res);
l_Lean_Elab_Term_instInhabitedArg___closed__1 = _init_l_Lean_Elab_Term_instInhabitedArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_instInhabitedArg___closed__1);
l_Lean_Elab_Term_instInhabitedArg = _init_l_Lean_Elab_Term_instInhabitedArg();
lean_mark_persistent(l_Lean_Elab_Term_instInhabitedArg);
l_Lean_Elab_Term_NamedArg_ref___default = _init_l_Lean_Elab_Term_NamedArg_ref___default();
lean_mark_persistent(l_Lean_Elab_Term_NamedArg_ref___default);
l_Lean_Elab_Term_instInhabitedNamedArg___closed__1 = _init_l_Lean_Elab_Term_instInhabitedNamedArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_instInhabitedNamedArg___closed__1);
l_Lean_Elab_Term_instInhabitedNamedArg = _init_l_Lean_Elab_Term_instInhabitedNamedArg();
lean_mark_persistent(l_Lean_Elab_Term_instInhabitedNamedArg);
l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__1 = _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__1);
l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2 = _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2);
l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__3 = _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__3);
l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__4 = _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__4);
l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__5 = _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__5);
l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__6 = _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__6);
l_Lean_Elab_Term_addNamedArg___closed__1 = _init_l_Lean_Elab_Term_addNamedArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__1);
l_Lean_Elab_Term_addNamedArg___closed__2 = _init_l_Lean_Elab_Term_addNamedArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__2);
l_Lean_Elab_Term_addNamedArg___closed__3 = _init_l_Lean_Elab_Term_addNamedArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__3);
l_Lean_Elab_Term_addNamedArg___closed__4 = _init_l_Lean_Elab_Term_addNamedArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__4);
l_Lean_Elab_Term_ElabAppArgs_State_ellipsis___default = _init_l_Lean_Elab_Term_ElabAppArgs_State_ellipsis___default();
l_Lean_Elab_Term_ElabAppArgs_State_etaArgs___default = _init_l_Lean_Elab_Term_ElabAppArgs_State_etaArgs___default();
lean_mark_persistent(l_Lean_Elab_Term_ElabAppArgs_State_etaArgs___default);
l_Lean_Elab_Term_ElabAppArgs_State_toSetErrorCtx___default = _init_l_Lean_Elab_Term_ElabAppArgs_State_toSetErrorCtx___default();
lean_mark_persistent(l_Lean_Elab_Term_ElabAppArgs_State_toSetErrorCtx___default);
l_Lean_Elab_Term_ElabAppArgs_State_instMVars___default = _init_l_Lean_Elab_Term_ElabAppArgs_State_instMVars___default();
lean_mark_persistent(l_Lean_Elab_Term_ElabAppArgs_State_instMVars___default);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__2___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_anyNamedArgDependsOnCurrent___lambda__2___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__2);
l_Lean_Elab_Term_ElabAppArgs_main___closed__1 = _init_l_Lean_Elab_Term_ElabAppArgs_main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ElabAppArgs_main___closed__1);
l_Lean_Elab_Term_elabAppArgs___closed__1 = _init_l_Lean_Elab_Term_elabAppArgs___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabAppArgs___closed__1);
l_Lean_Elab_Term_elabAppArgs___closed__2 = _init_l_Lean_Elab_Term_elabAppArgs___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabAppArgs___closed__2);
l_Lean_Elab_Term_elabAppArgs___closed__3 = _init_l_Lean_Elab_Term_elabAppArgs___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabAppArgs___closed__3);
l_Lean_Elab_Term_elabAppArgs___closed__4 = _init_l_Lean_Elab_Term_elabAppArgs___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_elabAppArgs___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__5 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__5);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__6 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__6);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__7 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__7);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__8 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__8);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__9 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__9);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15);
l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1);
l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2 = _init_l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2);
l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__2);
l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__3 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__3);
l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__4 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__4);
l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__5 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__5();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__5);
l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__6 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__6();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___closed__6);
l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___boxed__const__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___boxed__const__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__3);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_expandArgs___spec__3___closed__2);
l___regBuiltin_Lean_Elab_Term_elabApp___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabApp___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabApp___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabApp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabIdent(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabNamedPattern(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabExplicitUniv(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1___lambda__1___closed__1 = _init_l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_withoutPostponingUniverseConstraints___at_Lean_Elab_Term_elabPipeProj___spec__1___lambda__1___closed__1);
l___regBuiltin_Lean_Elab_Term_elabPipeProj___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabPipeProj___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabPipeProj___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabPipeProj(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabChoice(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabProj___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabProj___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProj___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabProj(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabArrayRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_8911_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
