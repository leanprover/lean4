// Lean compiler output
// Module: Lean.Elab.App
// Imports: Lean.Util.FindMVar Lean.Elab.Term Lean.Elab.Binders
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
lean_object* l_Lean_Elab_Term_addNamedArg___closed__5;
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_7__hasOnlyTypeMVar___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__23;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__13;
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
extern lean_object* l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_14__resolveLValLoop___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__elabAppLVals___closed__3;
lean_object* l___private_Lean_Elab_App_9__nextArgIsHole___boxed(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_23__toMessageData___closed__1;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUniv___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind___closed__2;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_14__resolveLValLoop___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__3;
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l___private_Lean_Elab_App_21__elabAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_16__mkBaseProjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
lean_object* l_Lean_Elab_getPosition___at___private_Lean_Elab_App_23__toMessageData___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__6;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__7;
extern lean_object* l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__7;
lean_object* l___private_Lean_Elab_App_5__getForallBody(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp___closed__1;
uint8_t l___private_Lean_Elab_App_9__nextArgIsHole(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_12__throwLValError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__17;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__10;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp(lean_object*);
lean_object* l___private_Lean_Elab_App_23__toMessageData(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__8;
extern lean_object* l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__9;
extern lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Lean_Elab_App_23__toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__27;
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_26__expandApp___closed__1;
lean_object* l___private_Lean_Elab_App_26__expandApp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_3__mkArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__4;
lean_object* l___private_Lean_Elab_App_17__addLValArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabId(lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__6;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__2;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppFn___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef(lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__5;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
lean_object* l_Lean_Elab_Term_NamedArg_inhabited;
extern lean_object* l_Lean_mkAppStx___closed__8;
extern lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__5;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__1;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_20__elabAppFnId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawIdent(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__2;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__3;
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
extern lean_object* l_Lean_Format_repr___main___closed__13;
extern lean_object* l_Lean_Parser_Term_proj___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__3;
lean_object* l___private_Lean_Elab_App_21__elabAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__8;
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__1;
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__3;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__14;
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__5;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__28;
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__18;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__15;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_6__hasTypeMVar___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__13;
uint8_t l___private_Lean_Elab_App_7__hasOnlyTypeMVar(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_App_25__elabAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__4;
lean_object* l_Lean_Elab_Term_getLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__7;
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_Inhabited;
extern lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7;
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__9;
lean_object* l_Lean_Elab_Term_elabId(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Syntax_6__formatInfo___closed__1;
lean_object* l___private_Lean_Elab_App_14__resolveLValLoop___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__6;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_5__getForallBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__6;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__5;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__14;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__3;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__25;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_24__mergeFailures___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceInfo___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__7;
lean_object* l___private_Lean_Elab_App_16__mkBaseProjections___closed__3;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkConst___closed__4;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited___closed__1;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUniv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_hasToString(lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__8;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_17__addLValArg___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___private_Lean_Elab_App_12__throwLValError(lean_object*);
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__4;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__22;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_15__resolveLVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAtom(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice(lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_26__expandApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_26__expandApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_App_6__hasTypeMVar(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__10;
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__4;
extern lean_object* l_Lean_Options_empty;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__11;
lean_object* l_Lean_Elab_Term_elabApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__1;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__3;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_elabChoice(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_2__elabArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__1;
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l___private_Lean_Elab_App_15__resolveLVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_TermElabResult_inhabited;
lean_object* l_List_map___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__1(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_24__mergeFailures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
extern lean_object* l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_1__ensureArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__12;
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_27__regTraceClasses(lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Term_elabProj(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofArray(lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___main(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_17__addLValArg___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__1;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
extern lean_object* l_Lean_mkAppStx___closed__5;
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__16;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__2;
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_20__elabAppFnId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Elab_Term_registerSyntheticMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_paren___elambda__1___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppFn___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_25__elabAppAux___closed__2;
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_throwError___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
lean_object* l___regBuiltin_Lean_Elab_Term_elabId___closed__1;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__10;
lean_object* l_Lean_Elab_Term_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_25__elabAppAux___closed__1;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__20;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__2;
lean_object* l___private_Lean_Elab_App_12__throwLValError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__getSuccess(lean_object*);
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__mergeFailures___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___closed__10;
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1;
lean_object* l___private_Lean_Elab_App_14__resolveLValLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Elab_Term_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_26__expandApp(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__11;
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__19;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData___main(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Lean_Elab_App_16__mkBaseProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__1;
lean_object* l___private_Lean_Elab_App_16__mkBaseProjections___closed__1;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__1;
extern lean_object* l_Lean_KernelException_toMessageData___closed__12;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_App_3__mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__11;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__elabAppLVals___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__4;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__1;
lean_object* l_Lean_Elab_Term_Arg_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l___private_Lean_Elab_App_17__addLValArg___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawIdent___closed__1;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__2;
extern lean_object* l_Lean_Meta_Exception_toStr___closed__6;
uint8_t l_Lean_Position_DecidableEq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_App_8__propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_16__mkBaseProjections___closed__2;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__11;
lean_object* l_Array_contains___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__26;
extern lean_object* l_Nat_Inhabited;
lean_object* l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__2;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l___private_Lean_Elab_App_25__elabAppAux___closed__3;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__9;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyResult(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabRawIdent(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__8;
lean_object* l___private_Lean_Elab_App_24__mergeFailures(lean_object*);
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
extern lean_object* l_Lean_Format_repr___main___closed__16;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___closed__12;
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_25__elabAppAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUniv___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__addLValArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__elabAppLVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
lean_object* l___private_Lean_Elab_App_19__elabAppLVals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__4;
lean_object* l___private_Lean_Elab_App_19__elabAppLVals___closed__1;
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_22__getSuccess___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__2;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__7;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_inhabited;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* _init_l_Lean_Elab_Term_Arg_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Arg_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_Arg_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_Arg_hasToString(lean_object* x_1) {
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
x_6 = l_Lean_Syntax_formatStxAux___main(x_3, x_4, x_5, x_2);
x_7 = l_Lean_Options_empty;
x_8 = l_Lean_Format_pretty(x_6, x_7);
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
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_System_FilePath_dirName___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
x_5 = l_Prod_HasRepr___rarg___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lean_formatEntry___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_ctor_get(x_1, 1);
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
x_14 = l_Lean_Syntax_formatStxAux___main(x_11, x_12, x_13, x_10);
x_15 = l_Lean_Options_empty;
x_16 = l_Lean_Format_pretty(x_14, x_15);
x_17 = lean_string_append(x_8, x_16);
lean_dec(x_16);
x_18 = l_Option_HasRepr___rarg___closed__3;
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
x_23 = l_Option_HasRepr___rarg___closed__3;
x_24 = lean_string_append(x_22, x_23);
return x_24;
}
}
}
lean_object* _init_l_Lean_Elab_Term_NamedArg_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Arg_inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_NamedArg_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_NamedArg_inhabited___closed__1;
return x_1;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("argument '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' was already set");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(x_2, x_3, x_2, x_6, x_7);
lean_dec(x_6);
lean_inc(x_3);
x_9 = lean_array_push(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_9);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l_System_FilePath_dirName___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_11);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Elab_Term_addNamedArg___closed__3;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_Term_addNamedArg___closed__6;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Term_throwError___rarg(x_1, x_19, x_4, x_5);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_addNamedArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_10);
x_13 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_10, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
lean_inc(x_1);
x_18 = l_Lean_Elab_Term_registerSyntheticMVar(x_1, x_10, x_17, x_4, x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_3 = x_12;
x_5 = x_19;
goto _start;
}
else
{
lean_object* x_21; 
lean_dec(x_10);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_3 = x_12;
x_5 = x_21;
goto _start;
}
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_synthesizeAppInstMVars(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_1__ensureArgType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Elab_Term_inferType(x_1, x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
x_12 = l_Lean_Elab_Term_ensureHasTypeAux(x_1, x_10, x_8, x_3, x_11, x_5, x_9);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Lean_Elab_App_2__elabArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
lean_inc(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
x_9 = 1;
lean_inc(x_5);
x_10 = l_Lean_Elab_Term_elabTermAux___main(x_8, x_9, x_9, x_7, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_App_1__ensureArgType(x_1, x_2, x_11, x_4, x_5, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = l___private_Lean_Elab_App_1__ensureArgType(x_1, x_2, x_18, x_4, x_5, x_6);
return x_19;
}
}
}
lean_object* l___private_Lean_Elab_App_3__mkArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Term_mkFreshAnonymousName___rarg(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = 0;
x_9 = l_Lean_mkForall(x_7, x_8, x_1, x_2);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = 0;
x_13 = l_Lean_mkForall(x_10, x_12, x_1, x_2);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
lean_object* l___private_Lean_Elab_App_3__mkArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_App_3__mkArrow(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeFun");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_4__tryCoeFun___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toStr___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_4__tryCoeFun___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeFun");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_4__tryCoeFun___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_4__tryCoeFun___closed__4;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_4__tryCoeFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_4);
x_6 = l_Lean_Elab_Term_mkFreshLevelMVar(x_1, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
x_9 = l_Lean_mkSort(x_7);
lean_inc(x_2);
x_10 = l___private_Lean_Elab_App_3__mkArrow(x_2, x_9, x_4, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = 0;
x_15 = lean_box(0);
lean_inc(x_4);
x_16 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_13, x_14, x_15, x_4, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_4);
lean_inc(x_2);
x_19 = l_Lean_Elab_Term_getLevel(x_1, x_2, x_4, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Elab_App_4__tryCoeFun___closed__2;
lean_inc(x_24);
x_26 = l_Lean_mkConst(x_25, x_24);
x_27 = l_Lean_mkAppStx___closed__9;
lean_inc(x_2);
x_28 = lean_array_push(x_27, x_2);
lean_inc(x_17);
x_29 = lean_array_push(x_28, x_17);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_29, x_29, x_30, x_26);
lean_dec(x_29);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = 1;
lean_inc(x_4);
x_34 = l_Lean_Elab_Term_mkFreshExprMVar(x_1, x_32, x_33, x_15, x_4, x_21);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_52 = l_Lean_Expr_mvarId_x21(x_35);
x_53 = lean_ctor_get(x_4, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_4, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_4, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_4, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_4, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_4, 5);
lean_inc(x_58);
x_59 = lean_ctor_get(x_4, 6);
lean_inc(x_59);
x_60 = lean_ctor_get(x_4, 7);
lean_inc(x_60);
x_61 = lean_ctor_get(x_4, 8);
lean_inc(x_61);
x_62 = lean_ctor_get(x_4, 9);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_64 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_65 = 0;
x_66 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_66, 0, x_53);
lean_ctor_set(x_66, 1, x_54);
lean_ctor_set(x_66, 2, x_55);
lean_ctor_set(x_66, 3, x_56);
lean_ctor_set(x_66, 4, x_57);
lean_ctor_set(x_66, 5, x_58);
lean_ctor_set(x_66, 6, x_59);
lean_ctor_set(x_66, 7, x_60);
lean_ctor_set(x_66, 8, x_61);
lean_ctor_set(x_66, 9, x_62);
lean_ctor_set_uint8(x_66, sizeof(void*)*10, x_63);
lean_ctor_set_uint8(x_66, sizeof(void*)*10 + 1, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*10 + 2, x_65);
x_67 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_52, x_66, x_36);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_unbox(x_68);
lean_dec(x_68);
x_38 = x_70;
x_39 = x_69;
goto block_51;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_dec(x_67);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
lean_dec(x_71);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get(x_82, 4);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l___private_Lean_Elab_App_4__tryCoeFun___closed__7;
x_85 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_Lean_Elab_Term_throwError___rarg(x_1, x_85, x_4, x_72);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
return x_86;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
else
{
lean_object* x_91; 
x_91 = lean_box(0);
x_73 = x_91;
goto block_80;
}
}
else
{
lean_object* x_92; 
x_92 = lean_box(0);
x_73 = x_92;
goto block_80;
}
block_80:
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_73);
x_74 = l___private_Lean_Elab_App_4__tryCoeFun___closed__4;
x_75 = l_Lean_Elab_Term_throwError___rarg(x_1, x_74, x_4, x_72);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
block_51:
{
if (x_38 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
x_40 = l___private_Lean_Elab_App_4__tryCoeFun___closed__4;
x_41 = l_Lean_Elab_Term_throwError___rarg(x_1, x_40, x_4, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_4);
x_42 = l___private_Lean_Elab_App_4__tryCoeFun___closed__6;
x_43 = l_Lean_mkConst(x_42, x_24);
x_44 = l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_45 = lean_array_push(x_44, x_2);
x_46 = lean_array_push(x_45, x_17);
x_47 = lean_array_push(x_46, x_3);
x_48 = lean_array_push(x_47, x_35);
x_49 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_48, x_48, x_30, x_43);
lean_dec(x_48);
if (lean_is_scalar(x_37)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_37;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_39);
return x_50;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_93 = !lean_is_exclusive(x_19);
if (x_93 == 0)
{
return x_19;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_19, 0);
x_95 = lean_ctor_get(x_19, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_19);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_App_4__tryCoeFun(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
}
}
}
lean_object* l___private_Lean_Elab_App_5__getForallBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1(x_4, x_2, x_8);
lean_dec(x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; uint8_t x_11; 
x_10 = (uint8_t)((x_7 << 24) >> 61);
x_11 = l_Lean_BinderInfo_isExplicit(x_10);
if (x_11 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
x_3 = x_6;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_8, x_1);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isAutoParam(x_5);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Expr_isOptParam(x_5);
lean_dec(x_5);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_3);
return x_16;
}
else
{
lean_dec(x_3);
x_3 = x_6;
goto _start;
}
}
else
{
lean_dec(x_5);
lean_dec(x_3);
x_3 = x_6;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_1, x_19);
lean_dec(x_1);
x_1 = x_20;
x_3 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_3);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
lean_dec(x_9);
x_23 = l_Array_eraseIdx___rarg(x_2, x_22);
lean_dec(x_22);
x_2 = x_23;
x_3 = x_6;
goto _start;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_1, x_25);
lean_dec(x_1);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = l_Array_isEmpty___rarg(x_2);
lean_dec(x_2);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_3);
x_29 = lean_box(0);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_3);
return x_30;
}
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_5__getForallBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_App_5__getForallBody___main(x_1, x_2, x_3);
return x_4;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_name_eq(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_contains___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__2(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_1, 6);
x_6 = l_Array_contains___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(x_5, x_4);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
}
else
{
return x_3;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_Expr_hasMVar(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasMVar(x_9);
if (x_11 == 0)
{
return x_3;
}
else
{
x_2 = x_9;
goto _start;
}
}
else
{
lean_object* x_13; 
x_13 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__3(x_1, x_8, x_3);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_hasMVar(x_9);
if (x_14 == 0)
{
return x_13;
}
else
{
x_2 = x_9;
x_3 = x_13;
goto _start;
}
}
else
{
return x_13;
}
}
}
else
{
return x_3;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasMVar(x_17);
if (x_19 == 0)
{
return x_3;
}
else
{
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_21; 
x_21 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__3(x_1, x_16, x_3);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasMVar(x_17);
if (x_22 == 0)
{
return x_21;
}
else
{
x_2 = x_17;
x_3 = x_21;
goto _start;
}
}
else
{
return x_21;
}
}
}
else
{
return x_3;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = l_Lean_Expr_hasMVar(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasMVar(x_25);
if (x_27 == 0)
{
return x_3;
}
else
{
x_2 = x_25;
goto _start;
}
}
else
{
lean_object* x_29; 
x_29 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__3(x_1, x_24, x_3);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_hasMVar(x_25);
if (x_30 == 0)
{
return x_29;
}
else
{
x_2 = x_25;
x_3 = x_29;
goto _start;
}
}
else
{
return x_29;
}
}
}
else
{
return x_3;
}
}
case 8:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_hasMVar(x_32);
if (x_43 == 0)
{
x_35 = x_3;
goto block_42;
}
else
{
lean_object* x_44; 
x_44 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__3(x_1, x_32, x_3);
if (lean_obj_tag(x_44) == 0)
{
x_35 = x_44;
goto block_42;
}
else
{
return x_44;
}
}
}
else
{
return x_3;
}
block_42:
{
uint8_t x_36; 
x_36 = l_Lean_Expr_hasMVar(x_33);
if (x_36 == 0)
{
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Expr_hasMVar(x_34);
if (x_37 == 0)
{
return x_35;
}
else
{
x_2 = x_34;
x_3 = x_35;
goto _start;
}
}
else
{
return x_35;
}
}
else
{
lean_object* x_39; 
x_39 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__3(x_1, x_33, x_35);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Expr_hasMVar(x_34);
if (x_40 == 0)
{
return x_39;
}
else
{
x_2 = x_34;
x_3 = x_39;
goto _start;
}
}
else
{
return x_39;
}
}
}
}
case 10:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_2, 1);
x_46 = l_Lean_Expr_hasMVar(x_45);
if (x_46 == 0)
{
return x_3;
}
else
{
x_2 = x_45;
goto _start;
}
}
else
{
return x_3;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_2, 2);
x_49 = l_Lean_Expr_hasMVar(x_48);
if (x_49 == 0)
{
return x_3;
}
else
{
x_2 = x_48;
goto _start;
}
}
else
{
return x_3;
}
}
default: 
{
return x_3;
}
}
}
}
uint8_t l___private_Lean_Elab_App_6__hasTypeMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__3(x_1, x_2, x_3);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_contains___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_6__hasTypeMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_App_6__hasTypeMVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_1, 6);
x_6 = l_Array_contains___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
return x_3;
}
}
else
{
return x_3;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_Expr_hasMVar(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasMVar(x_9);
if (x_11 == 0)
{
return x_3;
}
else
{
x_2 = x_9;
goto _start;
}
}
else
{
lean_object* x_13; 
x_13 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_8, x_3);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_hasMVar(x_9);
if (x_14 == 0)
{
return x_13;
}
else
{
x_2 = x_9;
x_3 = x_13;
goto _start;
}
}
else
{
return x_13;
}
}
}
else
{
return x_3;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasMVar(x_17);
if (x_19 == 0)
{
return x_3;
}
else
{
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_21; 
x_21 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_16, x_3);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasMVar(x_17);
if (x_22 == 0)
{
return x_21;
}
else
{
x_2 = x_17;
x_3 = x_21;
goto _start;
}
}
else
{
return x_21;
}
}
}
else
{
return x_3;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = l_Lean_Expr_hasMVar(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasMVar(x_25);
if (x_27 == 0)
{
return x_3;
}
else
{
x_2 = x_25;
goto _start;
}
}
else
{
lean_object* x_29; 
x_29 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_24, x_3);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_hasMVar(x_25);
if (x_30 == 0)
{
return x_29;
}
else
{
x_2 = x_25;
x_3 = x_29;
goto _start;
}
}
else
{
return x_29;
}
}
}
else
{
return x_3;
}
}
case 8:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_hasMVar(x_32);
if (x_43 == 0)
{
x_35 = x_3;
goto block_42;
}
else
{
lean_object* x_44; 
x_44 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_32, x_3);
if (lean_obj_tag(x_44) == 0)
{
x_35 = x_44;
goto block_42;
}
else
{
return x_44;
}
}
}
else
{
return x_3;
}
block_42:
{
uint8_t x_36; 
x_36 = l_Lean_Expr_hasMVar(x_33);
if (x_36 == 0)
{
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Expr_hasMVar(x_34);
if (x_37 == 0)
{
return x_35;
}
else
{
x_2 = x_34;
x_3 = x_35;
goto _start;
}
}
else
{
return x_35;
}
}
else
{
lean_object* x_39; 
x_39 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_33, x_35);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Expr_hasMVar(x_34);
if (x_40 == 0)
{
return x_39;
}
else
{
x_2 = x_34;
x_3 = x_39;
goto _start;
}
}
else
{
return x_39;
}
}
}
}
case 10:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_2, 1);
x_46 = l_Lean_Expr_hasMVar(x_45);
if (x_46 == 0)
{
return x_3;
}
else
{
x_2 = x_45;
goto _start;
}
}
else
{
return x_3;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_2, 2);
x_49 = l_Lean_Expr_hasMVar(x_48);
if (x_49 == 0)
{
return x_3;
}
else
{
x_2 = x_48;
goto _start;
}
}
else
{
return x_3;
}
}
default: 
{
return x_3;
}
}
}
}
uint8_t l___private_Lean_Elab_App_7__hasOnlyTypeMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_7__hasOnlyTypeMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_App_7__hasOnlyTypeMVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_8__propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 6);
lean_inc(x_7);
x_8 = l_Array_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_nat_sub(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_ctor_get(x_1, 4);
lean_inc(x_17);
x_18 = l___private_Lean_Elab_App_5__getForallBody___main(x_16, x_17, x_2);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Expr_hasLooseBVars(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l___private_Lean_Elab_App_6__hasTypeMVar(x_1, x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = l___private_Lean_Elab_App_7__hasOnlyTypeMVar(x_1, x_21);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = l_Lean_Elab_Term_isDefEq(x_29, x_12, x_21, x_3, x_4);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_4);
return x_42;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_4);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_4);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_4);
return x_48;
}
}
}
uint8_t l___private_Lean_Elab_App_9__nextArgIsHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_array_fget(x_3, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
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
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l_Lean_mkAppStx___closed__1;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_20 = 0;
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_mkAppStx___closed__3;
x_22 = lean_string_dec_eq(x_16, x_21);
lean_dec(x_16);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_14);
x_23 = 0;
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_mkAppStx___closed__5;
x_25 = lean_string_dec_eq(x_15, x_24);
lean_dec(x_15);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_14);
x_26 = 0;
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_mkHole___closed__1;
x_28 = lean_string_dec_eq(x_14, x_27);
lean_dec(x_14);
return x_28;
}
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_29 = 0;
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_30 = 0;
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_31 = 0;
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_9);
x_32 = 0;
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_9);
x_33 = 0;
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_8);
x_34 = 0;
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_7);
x_35 = 0;
return x_35;
}
}
}
}
lean_object* l___private_Lean_Elab_App_9__nextArgIsHole___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_9__nextArgIsHole(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Lean_mkAppStx___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalize");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1;
x_2 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit parameter '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is missing, unused named arguments ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid autoParam, argument must be a constant");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("begin");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__13;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__14;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 6);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_Elab_Term_whnfForall(x_6, x_3, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 7)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint64_t x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_16, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_16, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_16, 2);
lean_inc(x_92);
x_93 = lean_ctor_get_uint64(x_16, sizeof(void*)*3);
x_94 = lean_unsigned_to_nat(0u);
x_95 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_90, x_11, x_94);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = (uint8_t)((x_93 << 24) >> 61);
switch (x_96) {
case 0:
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; uint8_t x_102; 
x_97 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_98 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_98, 0, x_6);
lean_ctor_set(x_98, 1, x_7);
lean_ctor_set(x_98, 2, x_8);
lean_ctor_set(x_98, 3, x_10);
lean_ctor_set(x_98, 4, x_11);
lean_ctor_set(x_98, 5, x_12);
lean_ctor_set(x_98, 6, x_13);
lean_ctor_set_uint8(x_98, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_98, sizeof(void*)*7 + 1, x_97);
x_99 = lean_array_get_size(x_7);
x_100 = lean_nat_dec_lt(x_10, x_99);
lean_dec(x_99);
lean_inc(x_4);
lean_inc(x_1);
x_101 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_17);
x_102 = !lean_is_exclusive(x_1);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_1, 6);
lean_dec(x_103);
x_104 = lean_ctor_get(x_1, 5);
lean_dec(x_104);
x_105 = lean_ctor_get(x_1, 4);
lean_dec(x_105);
x_106 = lean_ctor_get(x_1, 3);
lean_dec(x_106);
x_107 = lean_ctor_get(x_1, 2);
lean_dec(x_107);
x_108 = lean_ctor_get(x_1, 1);
lean_dec(x_108);
x_109 = lean_ctor_get(x_1, 0);
lean_dec(x_109);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_101, 1);
lean_inc(x_110);
lean_dec(x_101);
if (x_100 == 0)
{
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_165; 
x_165 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_91);
x_167 = lean_box(0);
x_111 = x_167;
goto block_164;
}
else
{
lean_object* x_168; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
lean_dec(x_166);
if (lean_obj_tag(x_168) == 4)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec(x_168);
x_170 = l_Lean_Elab_Term_getEnv___rarg(x_110);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_171, x_169);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = l_Lean_Elab_Term_throwError___rarg(x_6, x_176, x_4, x_172);
lean_dec(x_6);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_178 = lean_ctor_get(x_173, 0);
lean_inc(x_178);
lean_dec(x_173);
x_179 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_172);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_181 = l_Lean_Elab_Term_getMainModule___rarg(x_180);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = l_Lean_Syntax_getArgs(x_178);
lean_dec(x_178);
x_184 = l_Array_empty___closed__1;
x_185 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_183, x_183, x_94, x_184);
lean_dec(x_183);
x_186 = l_Lean_nullKind___closed__2;
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
x_188 = lean_array_push(x_184, x_187);
x_189 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_192 = lean_array_push(x_191, x_190);
x_193 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_194 = lean_array_push(x_192, x_193);
x_195 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
x_197 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_198 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_199 = lean_nat_sub(x_198, x_94);
lean_dec(x_198);
x_200 = lean_unsigned_to_nat(1u);
x_201 = lean_nat_sub(x_199, x_200);
lean_dec(x_199);
x_202 = l_Lean_Expr_getRevArg_x21___main(x_91, x_201);
lean_dec(x_91);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_203, 0, x_196);
lean_inc(x_4);
lean_inc(x_2);
x_204 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_203, x_202, x_4, x_182);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
lean_inc(x_205);
x_207 = l_Lean_mkApp(x_2, x_205);
x_208 = lean_expr_instantiate1(x_92, x_205);
lean_dec(x_205);
lean_dec(x_92);
x_1 = x_98;
x_2 = x_207;
x_3 = x_208;
x_5 = x_206;
goto _start;
}
else
{
uint8_t x_210; 
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_210 = !lean_is_exclusive(x_204);
if (x_210 == 0)
{
return x_204;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_204, 0);
x_212 = lean_ctor_get(x_204, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_204);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_197, 0);
lean_inc(x_214);
lean_dec(x_197);
x_215 = l_Lean_Syntax_replaceInfo___main(x_214, x_196);
x_216 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_216, 0, x_215);
lean_inc(x_4);
lean_inc(x_2);
x_217 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_216, x_202, x_4, x_182);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
lean_inc(x_218);
x_220 = l_Lean_mkApp(x_2, x_218);
x_221 = lean_expr_instantiate1(x_92, x_218);
lean_dec(x_218);
lean_dec(x_92);
x_1 = x_98;
x_2 = x_220;
x_3 = x_221;
x_5 = x_219;
goto _start;
}
else
{
uint8_t x_223; 
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_223 = !lean_is_exclusive(x_217);
if (x_223 == 0)
{
return x_217;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_217, 0);
x_225 = lean_ctor_get(x_217, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_217);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
}
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_168);
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_227 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_228 = l_Lean_Elab_Term_throwError___rarg(x_6, x_227, x_4, x_110);
lean_dec(x_6);
return x_228;
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_229 = lean_ctor_get(x_165, 0);
lean_inc(x_229);
lean_dec(x_165);
lean_inc(x_229);
x_230 = l_Lean_mkApp(x_2, x_229);
x_231 = lean_expr_instantiate1(x_92, x_229);
lean_dec(x_229);
lean_dec(x_92);
x_1 = x_98;
x_2 = x_230;
x_3 = x_231;
x_5 = x_110;
goto _start;
}
}
else
{
lean_object* x_233; 
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_91);
x_233 = lean_box(0);
x_111 = x_233;
goto block_164;
}
}
else
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_98);
lean_dec(x_90);
lean_dec(x_3);
x_234 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_235 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_234, x_91, x_4, x_110);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = lean_unsigned_to_nat(1u);
x_239 = lean_nat_add(x_10, x_238);
lean_dec(x_10);
lean_ctor_set(x_1, 3, x_239);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_97);
lean_inc(x_236);
x_240 = l_Lean_mkApp(x_2, x_236);
x_241 = lean_expr_instantiate1(x_92, x_236);
lean_dec(x_236);
lean_dec(x_92);
x_2 = x_240;
x_3 = x_241;
x_5 = x_237;
goto _start;
}
else
{
uint8_t x_243; 
lean_free_object(x_1);
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_243 = !lean_is_exclusive(x_235);
if (x_243 == 0)
{
return x_235;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_235, 0);
x_245 = lean_ctor_get(x_235, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_235);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
block_164:
{
uint8_t x_112; 
lean_dec(x_111);
x_112 = l_Array_isEmpty___rarg(x_11);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_113 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_113, 0, x_90);
x_114 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_115 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_117 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = x_11;
x_119 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_118);
x_120 = x_119;
x_121 = l_Array_toList___rarg(x_120);
lean_dec(x_120);
x_122 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_121);
x_123 = l_Array_HasRepr___rarg___closed__1;
x_124 = lean_string_append(x_123, x_122);
lean_dec(x_122);
x_125 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_127, 0, x_117);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_Elab_Term_throwError___rarg(x_6, x_127, x_4, x_110);
lean_dec(x_6);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
lean_dec(x_90);
lean_dec(x_11);
x_156 = l_Lean_Elab_Term_getOptions(x_4, x_110);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_160 = l_Lean_checkTraceOption(x_157, x_159);
lean_dec(x_157);
if (x_160 == 0)
{
x_129 = x_158;
goto block_155;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_inc(x_2);
x_161 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_161, 0, x_2);
lean_inc(x_4);
x_162 = l_Lean_Elab_Term_logTrace(x_159, x_6, x_161, x_4, x_158);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_129 = x_163;
goto block_155;
}
block_155:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_130; 
lean_dec(x_3);
x_130 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_129);
lean_dec(x_12);
if (lean_obj_tag(x_130) == 0)
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_130, 0);
lean_dec(x_132);
lean_ctor_set(x_130, 0, x_2);
return x_130;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_2);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_dec(x_2);
x_135 = !lean_is_exclusive(x_130);
if (x_135 == 0)
{
return x_130;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_130, 0);
x_137 = lean_ctor_get(x_130, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_130);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_8, 0);
lean_inc(x_139);
lean_dec(x_8);
lean_inc(x_4);
x_140 = l_Lean_Elab_Term_isDefEq(x_6, x_139, x_3, x_4, x_129);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_141);
lean_dec(x_12);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_142, 0);
lean_dec(x_144);
lean_ctor_set(x_142, 0, x_2);
return x_142;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_2);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
else
{
uint8_t x_147; 
lean_dec(x_2);
x_147 = !lean_is_exclusive(x_142);
if (x_147 == 0)
{
return x_142;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_142, 0);
x_149 = lean_ctor_get(x_142, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_142);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_151 = !lean_is_exclusive(x_140);
if (x_151 == 0)
{
return x_140;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_140, 0);
x_153 = lean_ctor_get(x_140, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_140);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
}
}
}
else
{
uint8_t x_247; 
lean_free_object(x_1);
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_247 = !lean_is_exclusive(x_101);
if (x_247 == 0)
{
return x_101;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_101, 0);
x_249 = lean_ctor_get(x_101, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_101);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_101, 1);
lean_inc(x_251);
lean_dec(x_101);
if (x_100 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_304; 
x_304 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; 
x_305 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; 
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_91);
x_306 = lean_box(0);
x_252 = x_306;
goto block_303;
}
else
{
lean_object* x_307; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_307 = lean_ctor_get(x_305, 0);
lean_inc(x_307);
lean_dec(x_305);
if (lean_obj_tag(x_307) == 4)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
lean_dec(x_307);
x_309 = l_Lean_Elab_Term_getEnv___rarg(x_251);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
x_312 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_310, x_308);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
lean_dec(x_312);
x_314 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_314, 0, x_313);
x_315 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_315, 0, x_314);
x_316 = l_Lean_Elab_Term_throwError___rarg(x_6, x_315, x_4, x_311);
lean_dec(x_6);
return x_316;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_317 = lean_ctor_get(x_312, 0);
lean_inc(x_317);
lean_dec(x_312);
x_318 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_311);
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
lean_dec(x_318);
x_320 = l_Lean_Elab_Term_getMainModule___rarg(x_319);
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec(x_320);
x_322 = l_Lean_Syntax_getArgs(x_317);
lean_dec(x_317);
x_323 = l_Array_empty___closed__1;
x_324 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_322, x_322, x_94, x_323);
lean_dec(x_322);
x_325 = l_Lean_nullKind___closed__2;
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_324);
x_327 = lean_array_push(x_323, x_326);
x_328 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_327);
x_330 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_331 = lean_array_push(x_330, x_329);
x_332 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_333 = lean_array_push(x_331, x_332);
x_334 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_333);
x_336 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_337 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_338 = lean_nat_sub(x_337, x_94);
lean_dec(x_337);
x_339 = lean_unsigned_to_nat(1u);
x_340 = lean_nat_sub(x_338, x_339);
lean_dec(x_338);
x_341 = l_Lean_Expr_getRevArg_x21___main(x_91, x_340);
lean_dec(x_91);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_342, 0, x_335);
lean_inc(x_4);
lean_inc(x_2);
x_343 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_342, x_341, x_4, x_321);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
lean_inc(x_344);
x_346 = l_Lean_mkApp(x_2, x_344);
x_347 = lean_expr_instantiate1(x_92, x_344);
lean_dec(x_344);
lean_dec(x_92);
x_1 = x_98;
x_2 = x_346;
x_3 = x_347;
x_5 = x_345;
goto _start;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_349 = lean_ctor_get(x_343, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_343, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_351 = x_343;
} else {
 lean_dec_ref(x_343);
 x_351 = lean_box(0);
}
if (lean_is_scalar(x_351)) {
 x_352 = lean_alloc_ctor(1, 2, 0);
} else {
 x_352 = x_351;
}
lean_ctor_set(x_352, 0, x_349);
lean_ctor_set(x_352, 1, x_350);
return x_352;
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_353 = lean_ctor_get(x_336, 0);
lean_inc(x_353);
lean_dec(x_336);
x_354 = l_Lean_Syntax_replaceInfo___main(x_353, x_335);
x_355 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_355, 0, x_354);
lean_inc(x_4);
lean_inc(x_2);
x_356 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_355, x_341, x_4, x_321);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
lean_inc(x_357);
x_359 = l_Lean_mkApp(x_2, x_357);
x_360 = lean_expr_instantiate1(x_92, x_357);
lean_dec(x_357);
lean_dec(x_92);
x_1 = x_98;
x_2 = x_359;
x_3 = x_360;
x_5 = x_358;
goto _start;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_362 = lean_ctor_get(x_356, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_356, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_364 = x_356;
} else {
 lean_dec_ref(x_356);
 x_364 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(1, 2, 0);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_362);
lean_ctor_set(x_365, 1, x_363);
return x_365;
}
}
}
}
else
{
lean_object* x_366; lean_object* x_367; 
lean_dec(x_307);
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_366 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_367 = l_Lean_Elab_Term_throwError___rarg(x_6, x_366, x_4, x_251);
lean_dec(x_6);
return x_367;
}
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_368 = lean_ctor_get(x_304, 0);
lean_inc(x_368);
lean_dec(x_304);
lean_inc(x_368);
x_369 = l_Lean_mkApp(x_2, x_368);
x_370 = lean_expr_instantiate1(x_92, x_368);
lean_dec(x_368);
lean_dec(x_92);
x_1 = x_98;
x_2 = x_369;
x_3 = x_370;
x_5 = x_251;
goto _start;
}
}
else
{
lean_object* x_372; 
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_91);
x_372 = lean_box(0);
x_252 = x_372;
goto block_303;
}
}
else
{
lean_object* x_373; lean_object* x_374; 
lean_dec(x_98);
lean_dec(x_90);
lean_dec(x_3);
x_373 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_374 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_373, x_91, x_4, x_251);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
x_377 = lean_unsigned_to_nat(1u);
x_378 = lean_nat_add(x_10, x_377);
lean_dec(x_10);
x_379 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_379, 0, x_6);
lean_ctor_set(x_379, 1, x_7);
lean_ctor_set(x_379, 2, x_8);
lean_ctor_set(x_379, 3, x_378);
lean_ctor_set(x_379, 4, x_11);
lean_ctor_set(x_379, 5, x_12);
lean_ctor_set(x_379, 6, x_13);
lean_ctor_set_uint8(x_379, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_379, sizeof(void*)*7 + 1, x_97);
lean_inc(x_375);
x_380 = l_Lean_mkApp(x_2, x_375);
x_381 = lean_expr_instantiate1(x_92, x_375);
lean_dec(x_375);
lean_dec(x_92);
x_1 = x_379;
x_2 = x_380;
x_3 = x_381;
x_5 = x_376;
goto _start;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_383 = lean_ctor_get(x_374, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_374, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 lean_ctor_release(x_374, 1);
 x_385 = x_374;
} else {
 lean_dec_ref(x_374);
 x_385 = lean_box(0);
}
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 2, 0);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_383);
lean_ctor_set(x_386, 1, x_384);
return x_386;
}
}
block_303:
{
uint8_t x_253; 
lean_dec(x_252);
x_253 = l_Array_isEmpty___rarg(x_11);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_254 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_254, 0, x_90);
x_255 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_256 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_254);
x_257 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_258 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
x_259 = x_11;
x_260 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_259);
x_261 = x_260;
x_262 = l_Array_toList___rarg(x_261);
lean_dec(x_261);
x_263 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_262);
x_264 = l_Array_HasRepr___rarg___closed__1;
x_265 = lean_string_append(x_264, x_263);
lean_dec(x_263);
x_266 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_266, 0, x_265);
x_267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_267, 0, x_266);
x_268 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_268, 0, x_258);
lean_ctor_set(x_268, 1, x_267);
x_269 = l_Lean_Elab_Term_throwError___rarg(x_6, x_268, x_4, x_251);
lean_dec(x_6);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
lean_dec(x_90);
lean_dec(x_11);
x_295 = l_Lean_Elab_Term_getOptions(x_4, x_251);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_299 = l_Lean_checkTraceOption(x_296, x_298);
lean_dec(x_296);
if (x_299 == 0)
{
x_270 = x_297;
goto block_294;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_inc(x_2);
x_300 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_300, 0, x_2);
lean_inc(x_4);
x_301 = l_Lean_Elab_Term_logTrace(x_298, x_6, x_300, x_4, x_297);
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
lean_dec(x_301);
x_270 = x_302;
goto block_294;
}
block_294:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_271; 
lean_dec(x_3);
x_271 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_270);
lean_dec(x_12);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_2);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_2);
x_275 = lean_ctor_get(x_271, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_271, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_277 = x_271;
} else {
 lean_dec_ref(x_271);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_8, 0);
lean_inc(x_279);
lean_dec(x_8);
lean_inc(x_4);
x_280 = l_Lean_Elab_Term_isDefEq(x_6, x_279, x_3, x_4, x_270);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
lean_dec(x_280);
x_282 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_281);
lean_dec(x_12);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_284 = x_282;
} else {
 lean_dec_ref(x_282);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_2);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_2);
x_286 = lean_ctor_get(x_282, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_282, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_288 = x_282;
} else {
 lean_dec_ref(x_282);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_290 = lean_ctor_get(x_280, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_280, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_292 = x_280;
} else {
 lean_dec_ref(x_280);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
}
}
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_387 = lean_ctor_get(x_101, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_101, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_389 = x_101;
} else {
 lean_dec_ref(x_101);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(1, 2, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set(x_390, 1, x_388);
return x_390;
}
}
}
case 1:
{
if (x_9 == 0)
{
uint8_t x_391; 
lean_dec(x_90);
lean_dec(x_16);
lean_dec(x_3);
x_391 = !lean_is_exclusive(x_1);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_392 = lean_ctor_get(x_1, 6);
lean_dec(x_392);
x_393 = lean_ctor_get(x_1, 5);
lean_dec(x_393);
x_394 = lean_ctor_get(x_1, 4);
lean_dec(x_394);
x_395 = lean_ctor_get(x_1, 3);
lean_dec(x_395);
x_396 = lean_ctor_get(x_1, 2);
lean_dec(x_396);
x_397 = lean_ctor_get(x_1, 1);
lean_dec(x_397);
x_398 = lean_ctor_get(x_1, 0);
lean_dec(x_398);
x_399 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_399, 0, x_91);
x_400 = 0;
x_401 = lean_box(0);
lean_inc(x_4);
x_402 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_399, x_400, x_401, x_4, x_17);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
lean_inc(x_4);
lean_inc(x_403);
x_405 = l_Lean_Elab_Term_isTypeFormer(x_6, x_403, x_4, x_404);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; uint8_t x_407; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_unbox(x_406);
lean_dec(x_406);
if (x_407 == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_405, 1);
lean_inc(x_408);
lean_dec(x_405);
lean_inc(x_403);
x_409 = l_Lean_mkApp(x_2, x_403);
x_410 = lean_expr_instantiate1(x_92, x_403);
lean_dec(x_403);
lean_dec(x_92);
x_2 = x_409;
x_3 = x_410;
x_5 = x_408;
goto _start;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_412 = lean_ctor_get(x_405, 1);
lean_inc(x_412);
lean_dec(x_405);
x_413 = l_Lean_Expr_mvarId_x21(x_403);
x_414 = lean_array_push(x_13, x_413);
lean_ctor_set(x_1, 6, x_414);
lean_inc(x_403);
x_415 = l_Lean_mkApp(x_2, x_403);
x_416 = lean_expr_instantiate1(x_92, x_403);
lean_dec(x_403);
lean_dec(x_92);
x_2 = x_415;
x_3 = x_416;
x_5 = x_412;
goto _start;
}
}
else
{
uint8_t x_418; 
lean_dec(x_403);
lean_free_object(x_1);
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_418 = !lean_is_exclusive(x_405);
if (x_418 == 0)
{
return x_405;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_405, 0);
x_420 = lean_ctor_get(x_405, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_405);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
else
{
lean_object* x_422; uint8_t x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_1);
x_422 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_422, 0, x_91);
x_423 = 0;
x_424 = lean_box(0);
lean_inc(x_4);
x_425 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_422, x_423, x_424, x_4, x_17);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
lean_inc(x_4);
lean_inc(x_426);
x_428 = l_Lean_Elab_Term_isTypeFormer(x_6, x_426, x_4, x_427);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; uint8_t x_430; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_unbox(x_429);
lean_dec(x_429);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
lean_dec(x_428);
x_432 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_432, 0, x_6);
lean_ctor_set(x_432, 1, x_7);
lean_ctor_set(x_432, 2, x_8);
lean_ctor_set(x_432, 3, x_10);
lean_ctor_set(x_432, 4, x_11);
lean_ctor_set(x_432, 5, x_12);
lean_ctor_set(x_432, 6, x_13);
lean_ctor_set_uint8(x_432, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_432, sizeof(void*)*7 + 1, x_14);
lean_inc(x_426);
x_433 = l_Lean_mkApp(x_2, x_426);
x_434 = lean_expr_instantiate1(x_92, x_426);
lean_dec(x_426);
lean_dec(x_92);
x_1 = x_432;
x_2 = x_433;
x_3 = x_434;
x_5 = x_431;
goto _start;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_436 = lean_ctor_get(x_428, 1);
lean_inc(x_436);
lean_dec(x_428);
x_437 = l_Lean_Expr_mvarId_x21(x_426);
x_438 = lean_array_push(x_13, x_437);
x_439 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_439, 0, x_6);
lean_ctor_set(x_439, 1, x_7);
lean_ctor_set(x_439, 2, x_8);
lean_ctor_set(x_439, 3, x_10);
lean_ctor_set(x_439, 4, x_11);
lean_ctor_set(x_439, 5, x_12);
lean_ctor_set(x_439, 6, x_438);
lean_ctor_set_uint8(x_439, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_439, sizeof(void*)*7 + 1, x_14);
lean_inc(x_426);
x_440 = l_Lean_mkApp(x_2, x_426);
x_441 = lean_expr_instantiate1(x_92, x_426);
lean_dec(x_426);
lean_dec(x_92);
x_1 = x_439;
x_2 = x_440;
x_3 = x_441;
x_5 = x_436;
goto _start;
}
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_426);
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_443 = lean_ctor_get(x_428, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_428, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_445 = x_428;
} else {
 lean_dec_ref(x_428);
 x_445 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_446 = lean_alloc_ctor(1, 2, 0);
} else {
 x_446 = x_445;
}
lean_ctor_set(x_446, 0, x_443);
lean_ctor_set(x_446, 1, x_444);
return x_446;
}
}
}
else
{
lean_object* x_447; uint8_t x_448; lean_object* x_449; uint8_t x_450; 
x_447 = lean_array_get_size(x_7);
x_448 = lean_nat_dec_lt(x_10, x_447);
lean_dec(x_447);
lean_inc(x_4);
lean_inc(x_1);
x_449 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_17);
x_450 = !lean_is_exclusive(x_1);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_451 = lean_ctor_get(x_1, 6);
lean_dec(x_451);
x_452 = lean_ctor_get(x_1, 5);
lean_dec(x_452);
x_453 = lean_ctor_get(x_1, 4);
lean_dec(x_453);
x_454 = lean_ctor_get(x_1, 3);
lean_dec(x_454);
x_455 = lean_ctor_get(x_1, 2);
lean_dec(x_455);
x_456 = lean_ctor_get(x_1, 1);
lean_dec(x_456);
x_457 = lean_ctor_get(x_1, 0);
lean_dec(x_457);
if (lean_obj_tag(x_449) == 0)
{
if (x_448 == 0)
{
lean_object* x_458; uint8_t x_459; 
lean_free_object(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
x_458 = lean_ctor_get(x_449, 1);
lean_inc(x_458);
lean_dec(x_449);
x_459 = l_Array_isEmpty___rarg(x_11);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_460 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_460, 0, x_90);
x_461 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_462 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_460);
x_463 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_464 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_464, 0, x_462);
lean_ctor_set(x_464, 1, x_463);
x_465 = x_11;
x_466 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_465);
x_467 = x_466;
x_468 = l_Array_toList___rarg(x_467);
lean_dec(x_467);
x_469 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_468);
x_470 = l_Array_HasRepr___rarg___closed__1;
x_471 = lean_string_append(x_470, x_469);
lean_dec(x_469);
x_472 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_472, 0, x_471);
x_473 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_473, 0, x_472);
x_474 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_474, 0, x_464);
lean_ctor_set(x_474, 1, x_473);
x_475 = l_Lean_Elab_Term_throwError___rarg(x_6, x_474, x_4, x_458);
lean_dec(x_6);
return x_475;
}
else
{
lean_object* x_476; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; 
lean_dec(x_90);
lean_dec(x_11);
x_503 = l_Lean_Elab_Term_getOptions(x_4, x_458);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
x_506 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_507 = l_Lean_checkTraceOption(x_504, x_506);
lean_dec(x_504);
if (x_507 == 0)
{
x_476 = x_505;
goto block_502;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_inc(x_2);
x_508 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_508, 0, x_2);
lean_inc(x_4);
x_509 = l_Lean_Elab_Term_logTrace(x_506, x_6, x_508, x_4, x_505);
x_510 = lean_ctor_get(x_509, 1);
lean_inc(x_510);
lean_dec(x_509);
x_476 = x_510;
goto block_502;
}
block_502:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_477; 
lean_dec(x_3);
x_477 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_476);
lean_dec(x_12);
if (lean_obj_tag(x_477) == 0)
{
uint8_t x_478; 
x_478 = !lean_is_exclusive(x_477);
if (x_478 == 0)
{
lean_object* x_479; 
x_479 = lean_ctor_get(x_477, 0);
lean_dec(x_479);
lean_ctor_set(x_477, 0, x_2);
return x_477;
}
else
{
lean_object* x_480; lean_object* x_481; 
x_480 = lean_ctor_get(x_477, 1);
lean_inc(x_480);
lean_dec(x_477);
x_481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_481, 0, x_2);
lean_ctor_set(x_481, 1, x_480);
return x_481;
}
}
else
{
uint8_t x_482; 
lean_dec(x_2);
x_482 = !lean_is_exclusive(x_477);
if (x_482 == 0)
{
return x_477;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_483 = lean_ctor_get(x_477, 0);
x_484 = lean_ctor_get(x_477, 1);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_477);
x_485 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
return x_485;
}
}
}
else
{
lean_object* x_486; lean_object* x_487; 
x_486 = lean_ctor_get(x_8, 0);
lean_inc(x_486);
lean_dec(x_8);
lean_inc(x_4);
x_487 = l_Lean_Elab_Term_isDefEq(x_6, x_486, x_3, x_4, x_476);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; lean_object* x_489; 
x_488 = lean_ctor_get(x_487, 1);
lean_inc(x_488);
lean_dec(x_487);
x_489 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_488);
lean_dec(x_12);
if (lean_obj_tag(x_489) == 0)
{
uint8_t x_490; 
x_490 = !lean_is_exclusive(x_489);
if (x_490 == 0)
{
lean_object* x_491; 
x_491 = lean_ctor_get(x_489, 0);
lean_dec(x_491);
lean_ctor_set(x_489, 0, x_2);
return x_489;
}
else
{
lean_object* x_492; lean_object* x_493; 
x_492 = lean_ctor_get(x_489, 1);
lean_inc(x_492);
lean_dec(x_489);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_2);
lean_ctor_set(x_493, 1, x_492);
return x_493;
}
}
else
{
uint8_t x_494; 
lean_dec(x_2);
x_494 = !lean_is_exclusive(x_489);
if (x_494 == 0)
{
return x_489;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_489, 0);
x_496 = lean_ctor_get(x_489, 1);
lean_inc(x_496);
lean_inc(x_495);
lean_dec(x_489);
x_497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_497, 0, x_495);
lean_ctor_set(x_497, 1, x_496);
return x_497;
}
}
}
else
{
uint8_t x_498; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_498 = !lean_is_exclusive(x_487);
if (x_498 == 0)
{
return x_487;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_499 = lean_ctor_get(x_487, 0);
x_500 = lean_ctor_get(x_487, 1);
lean_inc(x_500);
lean_inc(x_499);
lean_dec(x_487);
x_501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
return x_501;
}
}
}
}
}
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_90);
lean_dec(x_3);
x_511 = lean_ctor_get(x_449, 1);
lean_inc(x_511);
lean_dec(x_449);
x_512 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_513 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_512, x_91, x_4, x_511);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; lean_object* x_519; lean_object* x_520; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_516 = lean_unsigned_to_nat(1u);
x_517 = lean_nat_add(x_10, x_516);
lean_dec(x_10);
x_518 = 1;
lean_ctor_set(x_1, 3, x_517);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_518);
lean_inc(x_514);
x_519 = l_Lean_mkApp(x_2, x_514);
x_520 = lean_expr_instantiate1(x_92, x_514);
lean_dec(x_514);
lean_dec(x_92);
x_2 = x_519;
x_3 = x_520;
x_5 = x_515;
goto _start;
}
else
{
uint8_t x_522; 
lean_free_object(x_1);
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_522 = !lean_is_exclusive(x_513);
if (x_522 == 0)
{
return x_513;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = lean_ctor_get(x_513, 0);
x_524 = lean_ctor_get(x_513, 1);
lean_inc(x_524);
lean_inc(x_523);
lean_dec(x_513);
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_523);
lean_ctor_set(x_525, 1, x_524);
return x_525;
}
}
}
}
else
{
uint8_t x_526; 
lean_free_object(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_526 = !lean_is_exclusive(x_449);
if (x_526 == 0)
{
return x_449;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_527 = lean_ctor_get(x_449, 0);
x_528 = lean_ctor_get(x_449, 1);
lean_inc(x_528);
lean_inc(x_527);
lean_dec(x_449);
x_529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_529, 0, x_527);
lean_ctor_set(x_529, 1, x_528);
return x_529;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_449) == 0)
{
if (x_448 == 0)
{
lean_object* x_530; uint8_t x_531; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
x_530 = lean_ctor_get(x_449, 1);
lean_inc(x_530);
lean_dec(x_449);
x_531 = l_Array_isEmpty___rarg(x_11);
if (x_531 == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_532 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_532, 0, x_90);
x_533 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_534 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_534, 0, x_533);
lean_ctor_set(x_534, 1, x_532);
x_535 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_536 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_536, 0, x_534);
lean_ctor_set(x_536, 1, x_535);
x_537 = x_11;
x_538 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_537);
x_539 = x_538;
x_540 = l_Array_toList___rarg(x_539);
lean_dec(x_539);
x_541 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_540);
x_542 = l_Array_HasRepr___rarg___closed__1;
x_543 = lean_string_append(x_542, x_541);
lean_dec(x_541);
x_544 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_544, 0, x_543);
x_545 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_545, 0, x_544);
x_546 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_546, 0, x_536);
lean_ctor_set(x_546, 1, x_545);
x_547 = l_Lean_Elab_Term_throwError___rarg(x_6, x_546, x_4, x_530);
lean_dec(x_6);
return x_547;
}
else
{
lean_object* x_548; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; uint8_t x_577; 
lean_dec(x_90);
lean_dec(x_11);
x_573 = l_Lean_Elab_Term_getOptions(x_4, x_530);
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
x_576 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_577 = l_Lean_checkTraceOption(x_574, x_576);
lean_dec(x_574);
if (x_577 == 0)
{
x_548 = x_575;
goto block_572;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_inc(x_2);
x_578 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_578, 0, x_2);
lean_inc(x_4);
x_579 = l_Lean_Elab_Term_logTrace(x_576, x_6, x_578, x_4, x_575);
x_580 = lean_ctor_get(x_579, 1);
lean_inc(x_580);
lean_dec(x_579);
x_548 = x_580;
goto block_572;
}
block_572:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_549; 
lean_dec(x_3);
x_549 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_548);
lean_dec(x_12);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
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
 x_552 = lean_alloc_ctor(0, 2, 0);
} else {
 x_552 = x_551;
}
lean_ctor_set(x_552, 0, x_2);
lean_ctor_set(x_552, 1, x_550);
return x_552;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
lean_dec(x_2);
x_553 = lean_ctor_get(x_549, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_549, 1);
lean_inc(x_554);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_555 = x_549;
} else {
 lean_dec_ref(x_549);
 x_555 = lean_box(0);
}
if (lean_is_scalar(x_555)) {
 x_556 = lean_alloc_ctor(1, 2, 0);
} else {
 x_556 = x_555;
}
lean_ctor_set(x_556, 0, x_553);
lean_ctor_set(x_556, 1, x_554);
return x_556;
}
}
else
{
lean_object* x_557; lean_object* x_558; 
x_557 = lean_ctor_get(x_8, 0);
lean_inc(x_557);
lean_dec(x_8);
lean_inc(x_4);
x_558 = l_Lean_Elab_Term_isDefEq(x_6, x_557, x_3, x_4, x_548);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; lean_object* x_560; 
x_559 = lean_ctor_get(x_558, 1);
lean_inc(x_559);
lean_dec(x_558);
x_560 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_559);
lean_dec(x_12);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_561 = lean_ctor_get(x_560, 1);
lean_inc(x_561);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 lean_ctor_release(x_560, 1);
 x_562 = x_560;
} else {
 lean_dec_ref(x_560);
 x_562 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_563 = lean_alloc_ctor(0, 2, 0);
} else {
 x_563 = x_562;
}
lean_ctor_set(x_563, 0, x_2);
lean_ctor_set(x_563, 1, x_561);
return x_563;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
lean_dec(x_2);
x_564 = lean_ctor_get(x_560, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_560, 1);
lean_inc(x_565);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 lean_ctor_release(x_560, 1);
 x_566 = x_560;
} else {
 lean_dec_ref(x_560);
 x_566 = lean_box(0);
}
if (lean_is_scalar(x_566)) {
 x_567 = lean_alloc_ctor(1, 2, 0);
} else {
 x_567 = x_566;
}
lean_ctor_set(x_567, 0, x_564);
lean_ctor_set(x_567, 1, x_565);
return x_567;
}
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_568 = lean_ctor_get(x_558, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_558, 1);
lean_inc(x_569);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 x_570 = x_558;
} else {
 lean_dec_ref(x_558);
 x_570 = lean_box(0);
}
if (lean_is_scalar(x_570)) {
 x_571 = lean_alloc_ctor(1, 2, 0);
} else {
 x_571 = x_570;
}
lean_ctor_set(x_571, 0, x_568);
lean_ctor_set(x_571, 1, x_569);
return x_571;
}
}
}
}
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec(x_90);
lean_dec(x_3);
x_581 = lean_ctor_get(x_449, 1);
lean_inc(x_581);
lean_dec(x_449);
x_582 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_583 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_582, x_91, x_4, x_581);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; uint8_t x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
lean_dec(x_583);
x_586 = lean_unsigned_to_nat(1u);
x_587 = lean_nat_add(x_10, x_586);
lean_dec(x_10);
x_588 = 1;
x_589 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_589, 0, x_6);
lean_ctor_set(x_589, 1, x_7);
lean_ctor_set(x_589, 2, x_8);
lean_ctor_set(x_589, 3, x_587);
lean_ctor_set(x_589, 4, x_11);
lean_ctor_set(x_589, 5, x_12);
lean_ctor_set(x_589, 6, x_13);
lean_ctor_set_uint8(x_589, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_589, sizeof(void*)*7 + 1, x_588);
lean_inc(x_584);
x_590 = l_Lean_mkApp(x_2, x_584);
x_591 = lean_expr_instantiate1(x_92, x_584);
lean_dec(x_584);
lean_dec(x_92);
x_1 = x_589;
x_2 = x_590;
x_3 = x_591;
x_5 = x_585;
goto _start;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_593 = lean_ctor_get(x_583, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_583, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 x_595 = x_583;
} else {
 lean_dec_ref(x_583);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(1, 2, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_593);
lean_ctor_set(x_596, 1, x_594);
return x_596;
}
}
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_597 = lean_ctor_get(x_449, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_449, 1);
lean_inc(x_598);
if (lean_is_exclusive(x_449)) {
 lean_ctor_release(x_449, 0);
 lean_ctor_release(x_449, 1);
 x_599 = x_449;
} else {
 lean_dec_ref(x_449);
 x_599 = lean_box(0);
}
if (lean_is_scalar(x_599)) {
 x_600 = lean_alloc_ctor(1, 2, 0);
} else {
 x_600 = x_599;
}
lean_ctor_set(x_600, 0, x_597);
lean_ctor_set(x_600, 1, x_598);
return x_600;
}
}
}
}
case 2:
{
uint8_t x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; lean_object* x_605; uint8_t x_606; 
x_601 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_602 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_602, 0, x_6);
lean_ctor_set(x_602, 1, x_7);
lean_ctor_set(x_602, 2, x_8);
lean_ctor_set(x_602, 3, x_10);
lean_ctor_set(x_602, 4, x_11);
lean_ctor_set(x_602, 5, x_12);
lean_ctor_set(x_602, 6, x_13);
lean_ctor_set_uint8(x_602, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_602, sizeof(void*)*7 + 1, x_601);
x_603 = lean_array_get_size(x_7);
x_604 = lean_nat_dec_lt(x_10, x_603);
lean_dec(x_603);
lean_inc(x_4);
lean_inc(x_1);
x_605 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_17);
x_606 = !lean_is_exclusive(x_1);
if (x_606 == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_607 = lean_ctor_get(x_1, 6);
lean_dec(x_607);
x_608 = lean_ctor_get(x_1, 5);
lean_dec(x_608);
x_609 = lean_ctor_get(x_1, 4);
lean_dec(x_609);
x_610 = lean_ctor_get(x_1, 3);
lean_dec(x_610);
x_611 = lean_ctor_get(x_1, 2);
lean_dec(x_611);
x_612 = lean_ctor_get(x_1, 1);
lean_dec(x_612);
x_613 = lean_ctor_get(x_1, 0);
lean_dec(x_613);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_614; lean_object* x_615; 
x_614 = lean_ctor_get(x_605, 1);
lean_inc(x_614);
lean_dec(x_605);
if (x_604 == 0)
{
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_669; 
x_669 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; 
x_670 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; 
lean_dec(x_602);
lean_dec(x_92);
lean_dec(x_91);
x_671 = lean_box(0);
x_615 = x_671;
goto block_668;
}
else
{
lean_object* x_672; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_672 = lean_ctor_get(x_670, 0);
lean_inc(x_672);
lean_dec(x_670);
if (lean_obj_tag(x_672) == 4)
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
lean_dec(x_672);
x_674 = l_Lean_Elab_Term_getEnv___rarg(x_614);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec(x_674);
x_677 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_675, x_673);
if (lean_obj_tag(x_677) == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
lean_dec(x_602);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_678 = lean_ctor_get(x_677, 0);
lean_inc(x_678);
lean_dec(x_677);
x_679 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_679, 0, x_678);
x_680 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_680, 0, x_679);
x_681 = l_Lean_Elab_Term_throwError___rarg(x_6, x_680, x_4, x_676);
lean_dec(x_6);
return x_681;
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_682 = lean_ctor_get(x_677, 0);
lean_inc(x_682);
lean_dec(x_677);
x_683 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_676);
x_684 = lean_ctor_get(x_683, 1);
lean_inc(x_684);
lean_dec(x_683);
x_685 = l_Lean_Elab_Term_getMainModule___rarg(x_684);
x_686 = lean_ctor_get(x_685, 1);
lean_inc(x_686);
lean_dec(x_685);
x_687 = l_Lean_Syntax_getArgs(x_682);
lean_dec(x_682);
x_688 = l_Array_empty___closed__1;
x_689 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_687, x_687, x_94, x_688);
lean_dec(x_687);
x_690 = l_Lean_nullKind___closed__2;
x_691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_689);
x_692 = lean_array_push(x_688, x_691);
x_693 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_694 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_694, 0, x_693);
lean_ctor_set(x_694, 1, x_692);
x_695 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_696 = lean_array_push(x_695, x_694);
x_697 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_698 = lean_array_push(x_696, x_697);
x_699 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_700 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_698);
x_701 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_702 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_703 = lean_nat_sub(x_702, x_94);
lean_dec(x_702);
x_704 = lean_unsigned_to_nat(1u);
x_705 = lean_nat_sub(x_703, x_704);
lean_dec(x_703);
x_706 = l_Lean_Expr_getRevArg_x21___main(x_91, x_705);
lean_dec(x_91);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_707; lean_object* x_708; 
x_707 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_707, 0, x_700);
lean_inc(x_4);
lean_inc(x_2);
x_708 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_707, x_706, x_4, x_686);
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_708, 1);
lean_inc(x_710);
lean_dec(x_708);
lean_inc(x_709);
x_711 = l_Lean_mkApp(x_2, x_709);
x_712 = lean_expr_instantiate1(x_92, x_709);
lean_dec(x_709);
lean_dec(x_92);
x_1 = x_602;
x_2 = x_711;
x_3 = x_712;
x_5 = x_710;
goto _start;
}
else
{
uint8_t x_714; 
lean_dec(x_602);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_714 = !lean_is_exclusive(x_708);
if (x_714 == 0)
{
return x_708;
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_715 = lean_ctor_get(x_708, 0);
x_716 = lean_ctor_get(x_708, 1);
lean_inc(x_716);
lean_inc(x_715);
lean_dec(x_708);
x_717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_717, 0, x_715);
lean_ctor_set(x_717, 1, x_716);
return x_717;
}
}
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_718 = lean_ctor_get(x_701, 0);
lean_inc(x_718);
lean_dec(x_701);
x_719 = l_Lean_Syntax_replaceInfo___main(x_718, x_700);
x_720 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_720, 0, x_719);
lean_inc(x_4);
lean_inc(x_2);
x_721 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_720, x_706, x_4, x_686);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec(x_721);
lean_inc(x_722);
x_724 = l_Lean_mkApp(x_2, x_722);
x_725 = lean_expr_instantiate1(x_92, x_722);
lean_dec(x_722);
lean_dec(x_92);
x_1 = x_602;
x_2 = x_724;
x_3 = x_725;
x_5 = x_723;
goto _start;
}
else
{
uint8_t x_727; 
lean_dec(x_602);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_727 = !lean_is_exclusive(x_721);
if (x_727 == 0)
{
return x_721;
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_728 = lean_ctor_get(x_721, 0);
x_729 = lean_ctor_get(x_721, 1);
lean_inc(x_729);
lean_inc(x_728);
lean_dec(x_721);
x_730 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_730, 0, x_728);
lean_ctor_set(x_730, 1, x_729);
return x_730;
}
}
}
}
}
else
{
lean_object* x_731; lean_object* x_732; 
lean_dec(x_672);
lean_dec(x_602);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_731 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_732 = l_Lean_Elab_Term_throwError___rarg(x_6, x_731, x_4, x_614);
lean_dec(x_6);
return x_732;
}
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_733 = lean_ctor_get(x_669, 0);
lean_inc(x_733);
lean_dec(x_669);
lean_inc(x_733);
x_734 = l_Lean_mkApp(x_2, x_733);
x_735 = lean_expr_instantiate1(x_92, x_733);
lean_dec(x_733);
lean_dec(x_92);
x_1 = x_602;
x_2 = x_734;
x_3 = x_735;
x_5 = x_614;
goto _start;
}
}
else
{
lean_object* x_737; 
lean_dec(x_602);
lean_dec(x_92);
lean_dec(x_91);
x_737 = lean_box(0);
x_615 = x_737;
goto block_668;
}
}
else
{
lean_object* x_738; lean_object* x_739; 
lean_dec(x_602);
lean_dec(x_90);
lean_dec(x_3);
x_738 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_739 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_738, x_91, x_4, x_614);
if (lean_obj_tag(x_739) == 0)
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_739, 1);
lean_inc(x_741);
lean_dec(x_739);
x_742 = lean_unsigned_to_nat(1u);
x_743 = lean_nat_add(x_10, x_742);
lean_dec(x_10);
lean_ctor_set(x_1, 3, x_743);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_601);
lean_inc(x_740);
x_744 = l_Lean_mkApp(x_2, x_740);
x_745 = lean_expr_instantiate1(x_92, x_740);
lean_dec(x_740);
lean_dec(x_92);
x_2 = x_744;
x_3 = x_745;
x_5 = x_741;
goto _start;
}
else
{
uint8_t x_747; 
lean_free_object(x_1);
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_747 = !lean_is_exclusive(x_739);
if (x_747 == 0)
{
return x_739;
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_748 = lean_ctor_get(x_739, 0);
x_749 = lean_ctor_get(x_739, 1);
lean_inc(x_749);
lean_inc(x_748);
lean_dec(x_739);
x_750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_750, 0, x_748);
lean_ctor_set(x_750, 1, x_749);
return x_750;
}
}
}
block_668:
{
uint8_t x_616; 
lean_dec(x_615);
x_616 = l_Array_isEmpty___rarg(x_11);
if (x_616 == 0)
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_617 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_617, 0, x_90);
x_618 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_619 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_619, 0, x_618);
lean_ctor_set(x_619, 1, x_617);
x_620 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_621 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_621, 0, x_619);
lean_ctor_set(x_621, 1, x_620);
x_622 = x_11;
x_623 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_622);
x_624 = x_623;
x_625 = l_Array_toList___rarg(x_624);
lean_dec(x_624);
x_626 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_625);
x_627 = l_Array_HasRepr___rarg___closed__1;
x_628 = lean_string_append(x_627, x_626);
lean_dec(x_626);
x_629 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_629, 0, x_628);
x_630 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_630, 0, x_629);
x_631 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_631, 0, x_621);
lean_ctor_set(x_631, 1, x_630);
x_632 = l_Lean_Elab_Term_throwError___rarg(x_6, x_631, x_4, x_614);
lean_dec(x_6);
return x_632;
}
else
{
lean_object* x_633; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; uint8_t x_664; 
lean_dec(x_90);
lean_dec(x_11);
x_660 = l_Lean_Elab_Term_getOptions(x_4, x_614);
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_660, 1);
lean_inc(x_662);
lean_dec(x_660);
x_663 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_664 = l_Lean_checkTraceOption(x_661, x_663);
lean_dec(x_661);
if (x_664 == 0)
{
x_633 = x_662;
goto block_659;
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
lean_inc(x_2);
x_665 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_665, 0, x_2);
lean_inc(x_4);
x_666 = l_Lean_Elab_Term_logTrace(x_663, x_6, x_665, x_4, x_662);
x_667 = lean_ctor_get(x_666, 1);
lean_inc(x_667);
lean_dec(x_666);
x_633 = x_667;
goto block_659;
}
block_659:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_634; 
lean_dec(x_3);
x_634 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_633);
lean_dec(x_12);
if (lean_obj_tag(x_634) == 0)
{
uint8_t x_635; 
x_635 = !lean_is_exclusive(x_634);
if (x_635 == 0)
{
lean_object* x_636; 
x_636 = lean_ctor_get(x_634, 0);
lean_dec(x_636);
lean_ctor_set(x_634, 0, x_2);
return x_634;
}
else
{
lean_object* x_637; lean_object* x_638; 
x_637 = lean_ctor_get(x_634, 1);
lean_inc(x_637);
lean_dec(x_634);
x_638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_638, 0, x_2);
lean_ctor_set(x_638, 1, x_637);
return x_638;
}
}
else
{
uint8_t x_639; 
lean_dec(x_2);
x_639 = !lean_is_exclusive(x_634);
if (x_639 == 0)
{
return x_634;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_640 = lean_ctor_get(x_634, 0);
x_641 = lean_ctor_get(x_634, 1);
lean_inc(x_641);
lean_inc(x_640);
lean_dec(x_634);
x_642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_642, 0, x_640);
lean_ctor_set(x_642, 1, x_641);
return x_642;
}
}
}
else
{
lean_object* x_643; lean_object* x_644; 
x_643 = lean_ctor_get(x_8, 0);
lean_inc(x_643);
lean_dec(x_8);
lean_inc(x_4);
x_644 = l_Lean_Elab_Term_isDefEq(x_6, x_643, x_3, x_4, x_633);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; lean_object* x_646; 
x_645 = lean_ctor_get(x_644, 1);
lean_inc(x_645);
lean_dec(x_644);
x_646 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_645);
lean_dec(x_12);
if (lean_obj_tag(x_646) == 0)
{
uint8_t x_647; 
x_647 = !lean_is_exclusive(x_646);
if (x_647 == 0)
{
lean_object* x_648; 
x_648 = lean_ctor_get(x_646, 0);
lean_dec(x_648);
lean_ctor_set(x_646, 0, x_2);
return x_646;
}
else
{
lean_object* x_649; lean_object* x_650; 
x_649 = lean_ctor_get(x_646, 1);
lean_inc(x_649);
lean_dec(x_646);
x_650 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_650, 0, x_2);
lean_ctor_set(x_650, 1, x_649);
return x_650;
}
}
else
{
uint8_t x_651; 
lean_dec(x_2);
x_651 = !lean_is_exclusive(x_646);
if (x_651 == 0)
{
return x_646;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = lean_ctor_get(x_646, 0);
x_653 = lean_ctor_get(x_646, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_646);
x_654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_654, 0, x_652);
lean_ctor_set(x_654, 1, x_653);
return x_654;
}
}
}
else
{
uint8_t x_655; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_655 = !lean_is_exclusive(x_644);
if (x_655 == 0)
{
return x_644;
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_656 = lean_ctor_get(x_644, 0);
x_657 = lean_ctor_get(x_644, 1);
lean_inc(x_657);
lean_inc(x_656);
lean_dec(x_644);
x_658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_658, 0, x_656);
lean_ctor_set(x_658, 1, x_657);
return x_658;
}
}
}
}
}
}
}
else
{
uint8_t x_751; 
lean_free_object(x_1);
lean_dec(x_602);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_751 = !lean_is_exclusive(x_605);
if (x_751 == 0)
{
return x_605;
}
else
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; 
x_752 = lean_ctor_get(x_605, 0);
x_753 = lean_ctor_get(x_605, 1);
lean_inc(x_753);
lean_inc(x_752);
lean_dec(x_605);
x_754 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_754, 0, x_752);
lean_ctor_set(x_754, 1, x_753);
return x_754;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_755; lean_object* x_756; 
x_755 = lean_ctor_get(x_605, 1);
lean_inc(x_755);
lean_dec(x_605);
if (x_604 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_808; 
x_808 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_808) == 0)
{
lean_object* x_809; 
x_809 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_809) == 0)
{
lean_object* x_810; 
lean_dec(x_602);
lean_dec(x_92);
lean_dec(x_91);
x_810 = lean_box(0);
x_756 = x_810;
goto block_807;
}
else
{
lean_object* x_811; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_811 = lean_ctor_get(x_809, 0);
lean_inc(x_811);
lean_dec(x_809);
if (lean_obj_tag(x_811) == 4)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
lean_dec(x_811);
x_813 = l_Lean_Elab_Term_getEnv___rarg(x_755);
x_814 = lean_ctor_get(x_813, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_813, 1);
lean_inc(x_815);
lean_dec(x_813);
x_816 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_814, x_812);
if (lean_obj_tag(x_816) == 0)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
lean_dec(x_602);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
lean_dec(x_816);
x_818 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_818, 0, x_817);
x_819 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_819, 0, x_818);
x_820 = l_Lean_Elab_Term_throwError___rarg(x_6, x_819, x_4, x_815);
lean_dec(x_6);
return x_820;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_821 = lean_ctor_get(x_816, 0);
lean_inc(x_821);
lean_dec(x_816);
x_822 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_815);
x_823 = lean_ctor_get(x_822, 1);
lean_inc(x_823);
lean_dec(x_822);
x_824 = l_Lean_Elab_Term_getMainModule___rarg(x_823);
x_825 = lean_ctor_get(x_824, 1);
lean_inc(x_825);
lean_dec(x_824);
x_826 = l_Lean_Syntax_getArgs(x_821);
lean_dec(x_821);
x_827 = l_Array_empty___closed__1;
x_828 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_826, x_826, x_94, x_827);
lean_dec(x_826);
x_829 = l_Lean_nullKind___closed__2;
x_830 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_830, 0, x_829);
lean_ctor_set(x_830, 1, x_828);
x_831 = lean_array_push(x_827, x_830);
x_832 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_833 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_833, 0, x_832);
lean_ctor_set(x_833, 1, x_831);
x_834 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_835 = lean_array_push(x_834, x_833);
x_836 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_837 = lean_array_push(x_835, x_836);
x_838 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_839 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_839, 0, x_838);
lean_ctor_set(x_839, 1, x_837);
x_840 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_841 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_842 = lean_nat_sub(x_841, x_94);
lean_dec(x_841);
x_843 = lean_unsigned_to_nat(1u);
x_844 = lean_nat_sub(x_842, x_843);
lean_dec(x_842);
x_845 = l_Lean_Expr_getRevArg_x21___main(x_91, x_844);
lean_dec(x_91);
if (lean_obj_tag(x_840) == 0)
{
lean_object* x_846; lean_object* x_847; 
x_846 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_846, 0, x_839);
lean_inc(x_4);
lean_inc(x_2);
x_847 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_846, x_845, x_4, x_825);
if (lean_obj_tag(x_847) == 0)
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_848 = lean_ctor_get(x_847, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_847, 1);
lean_inc(x_849);
lean_dec(x_847);
lean_inc(x_848);
x_850 = l_Lean_mkApp(x_2, x_848);
x_851 = lean_expr_instantiate1(x_92, x_848);
lean_dec(x_848);
lean_dec(x_92);
x_1 = x_602;
x_2 = x_850;
x_3 = x_851;
x_5 = x_849;
goto _start;
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_602);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_853 = lean_ctor_get(x_847, 0);
lean_inc(x_853);
x_854 = lean_ctor_get(x_847, 1);
lean_inc(x_854);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 x_855 = x_847;
} else {
 lean_dec_ref(x_847);
 x_855 = lean_box(0);
}
if (lean_is_scalar(x_855)) {
 x_856 = lean_alloc_ctor(1, 2, 0);
} else {
 x_856 = x_855;
}
lean_ctor_set(x_856, 0, x_853);
lean_ctor_set(x_856, 1, x_854);
return x_856;
}
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
x_857 = lean_ctor_get(x_840, 0);
lean_inc(x_857);
lean_dec(x_840);
x_858 = l_Lean_Syntax_replaceInfo___main(x_857, x_839);
x_859 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_859, 0, x_858);
lean_inc(x_4);
lean_inc(x_2);
x_860 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_859, x_845, x_4, x_825);
if (lean_obj_tag(x_860) == 0)
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_860, 1);
lean_inc(x_862);
lean_dec(x_860);
lean_inc(x_861);
x_863 = l_Lean_mkApp(x_2, x_861);
x_864 = lean_expr_instantiate1(x_92, x_861);
lean_dec(x_861);
lean_dec(x_92);
x_1 = x_602;
x_2 = x_863;
x_3 = x_864;
x_5 = x_862;
goto _start;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
lean_dec(x_602);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_866 = lean_ctor_get(x_860, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_860, 1);
lean_inc(x_867);
if (lean_is_exclusive(x_860)) {
 lean_ctor_release(x_860, 0);
 lean_ctor_release(x_860, 1);
 x_868 = x_860;
} else {
 lean_dec_ref(x_860);
 x_868 = lean_box(0);
}
if (lean_is_scalar(x_868)) {
 x_869 = lean_alloc_ctor(1, 2, 0);
} else {
 x_869 = x_868;
}
lean_ctor_set(x_869, 0, x_866);
lean_ctor_set(x_869, 1, x_867);
return x_869;
}
}
}
}
else
{
lean_object* x_870; lean_object* x_871; 
lean_dec(x_811);
lean_dec(x_602);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_870 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_871 = l_Lean_Elab_Term_throwError___rarg(x_6, x_870, x_4, x_755);
lean_dec(x_6);
return x_871;
}
}
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_872 = lean_ctor_get(x_808, 0);
lean_inc(x_872);
lean_dec(x_808);
lean_inc(x_872);
x_873 = l_Lean_mkApp(x_2, x_872);
x_874 = lean_expr_instantiate1(x_92, x_872);
lean_dec(x_872);
lean_dec(x_92);
x_1 = x_602;
x_2 = x_873;
x_3 = x_874;
x_5 = x_755;
goto _start;
}
}
else
{
lean_object* x_876; 
lean_dec(x_602);
lean_dec(x_92);
lean_dec(x_91);
x_876 = lean_box(0);
x_756 = x_876;
goto block_807;
}
}
else
{
lean_object* x_877; lean_object* x_878; 
lean_dec(x_602);
lean_dec(x_90);
lean_dec(x_3);
x_877 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_878 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_877, x_91, x_4, x_755);
if (lean_obj_tag(x_878) == 0)
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; 
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_881 = lean_unsigned_to_nat(1u);
x_882 = lean_nat_add(x_10, x_881);
lean_dec(x_10);
x_883 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_883, 0, x_6);
lean_ctor_set(x_883, 1, x_7);
lean_ctor_set(x_883, 2, x_8);
lean_ctor_set(x_883, 3, x_882);
lean_ctor_set(x_883, 4, x_11);
lean_ctor_set(x_883, 5, x_12);
lean_ctor_set(x_883, 6, x_13);
lean_ctor_set_uint8(x_883, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_883, sizeof(void*)*7 + 1, x_601);
lean_inc(x_879);
x_884 = l_Lean_mkApp(x_2, x_879);
x_885 = lean_expr_instantiate1(x_92, x_879);
lean_dec(x_879);
lean_dec(x_92);
x_1 = x_883;
x_2 = x_884;
x_3 = x_885;
x_5 = x_880;
goto _start;
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_887 = lean_ctor_get(x_878, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_878, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 x_889 = x_878;
} else {
 lean_dec_ref(x_878);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_890 = lean_alloc_ctor(1, 2, 0);
} else {
 x_890 = x_889;
}
lean_ctor_set(x_890, 0, x_887);
lean_ctor_set(x_890, 1, x_888);
return x_890;
}
}
block_807:
{
uint8_t x_757; 
lean_dec(x_756);
x_757 = l_Array_isEmpty___rarg(x_11);
if (x_757 == 0)
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_758 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_758, 0, x_90);
x_759 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_760 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_760, 0, x_759);
lean_ctor_set(x_760, 1, x_758);
x_761 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_762 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_762, 0, x_760);
lean_ctor_set(x_762, 1, x_761);
x_763 = x_11;
x_764 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_763);
x_765 = x_764;
x_766 = l_Array_toList___rarg(x_765);
lean_dec(x_765);
x_767 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_766);
x_768 = l_Array_HasRepr___rarg___closed__1;
x_769 = lean_string_append(x_768, x_767);
lean_dec(x_767);
x_770 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_770, 0, x_769);
x_771 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_771, 0, x_770);
x_772 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_772, 0, x_762);
lean_ctor_set(x_772, 1, x_771);
x_773 = l_Lean_Elab_Term_throwError___rarg(x_6, x_772, x_4, x_755);
lean_dec(x_6);
return x_773;
}
else
{
lean_object* x_774; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; uint8_t x_803; 
lean_dec(x_90);
lean_dec(x_11);
x_799 = l_Lean_Elab_Term_getOptions(x_4, x_755);
x_800 = lean_ctor_get(x_799, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_799, 1);
lean_inc(x_801);
lean_dec(x_799);
x_802 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_803 = l_Lean_checkTraceOption(x_800, x_802);
lean_dec(x_800);
if (x_803 == 0)
{
x_774 = x_801;
goto block_798;
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; 
lean_inc(x_2);
x_804 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_804, 0, x_2);
lean_inc(x_4);
x_805 = l_Lean_Elab_Term_logTrace(x_802, x_6, x_804, x_4, x_801);
x_806 = lean_ctor_get(x_805, 1);
lean_inc(x_806);
lean_dec(x_805);
x_774 = x_806;
goto block_798;
}
block_798:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_775; 
lean_dec(x_3);
x_775 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_774);
lean_dec(x_12);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_776 = lean_ctor_get(x_775, 1);
lean_inc(x_776);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_777 = x_775;
} else {
 lean_dec_ref(x_775);
 x_777 = lean_box(0);
}
if (lean_is_scalar(x_777)) {
 x_778 = lean_alloc_ctor(0, 2, 0);
} else {
 x_778 = x_777;
}
lean_ctor_set(x_778, 0, x_2);
lean_ctor_set(x_778, 1, x_776);
return x_778;
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
lean_dec(x_2);
x_779 = lean_ctor_get(x_775, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_775, 1);
lean_inc(x_780);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_781 = x_775;
} else {
 lean_dec_ref(x_775);
 x_781 = lean_box(0);
}
if (lean_is_scalar(x_781)) {
 x_782 = lean_alloc_ctor(1, 2, 0);
} else {
 x_782 = x_781;
}
lean_ctor_set(x_782, 0, x_779);
lean_ctor_set(x_782, 1, x_780);
return x_782;
}
}
else
{
lean_object* x_783; lean_object* x_784; 
x_783 = lean_ctor_get(x_8, 0);
lean_inc(x_783);
lean_dec(x_8);
lean_inc(x_4);
x_784 = l_Lean_Elab_Term_isDefEq(x_6, x_783, x_3, x_4, x_774);
if (lean_obj_tag(x_784) == 0)
{
lean_object* x_785; lean_object* x_786; 
x_785 = lean_ctor_get(x_784, 1);
lean_inc(x_785);
lean_dec(x_784);
x_786 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_785);
lean_dec(x_12);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_787 = lean_ctor_get(x_786, 1);
lean_inc(x_787);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 x_788 = x_786;
} else {
 lean_dec_ref(x_786);
 x_788 = lean_box(0);
}
if (lean_is_scalar(x_788)) {
 x_789 = lean_alloc_ctor(0, 2, 0);
} else {
 x_789 = x_788;
}
lean_ctor_set(x_789, 0, x_2);
lean_ctor_set(x_789, 1, x_787);
return x_789;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
lean_dec(x_2);
x_790 = lean_ctor_get(x_786, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_786, 1);
lean_inc(x_791);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 x_792 = x_786;
} else {
 lean_dec_ref(x_786);
 x_792 = lean_box(0);
}
if (lean_is_scalar(x_792)) {
 x_793 = lean_alloc_ctor(1, 2, 0);
} else {
 x_793 = x_792;
}
lean_ctor_set(x_793, 0, x_790);
lean_ctor_set(x_793, 1, x_791);
return x_793;
}
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_794 = lean_ctor_get(x_784, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_784, 1);
lean_inc(x_795);
if (lean_is_exclusive(x_784)) {
 lean_ctor_release(x_784, 0);
 lean_ctor_release(x_784, 1);
 x_796 = x_784;
} else {
 lean_dec_ref(x_784);
 x_796 = lean_box(0);
}
if (lean_is_scalar(x_796)) {
 x_797 = lean_alloc_ctor(1, 2, 0);
} else {
 x_797 = x_796;
}
lean_ctor_set(x_797, 0, x_794);
lean_ctor_set(x_797, 1, x_795);
return x_797;
}
}
}
}
}
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
lean_dec(x_602);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_891 = lean_ctor_get(x_605, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_605, 1);
lean_inc(x_892);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 lean_ctor_release(x_605, 1);
 x_893 = x_605;
} else {
 lean_dec_ref(x_605);
 x_893 = lean_box(0);
}
if (lean_is_scalar(x_893)) {
 x_894 = lean_alloc_ctor(1, 2, 0);
} else {
 x_894 = x_893;
}
lean_ctor_set(x_894, 0, x_891);
lean_ctor_set(x_894, 1, x_892);
return x_894;
}
}
}
case 3:
{
if (x_9 == 0)
{
uint8_t x_895; 
lean_dec(x_90);
lean_dec(x_16);
lean_dec(x_3);
x_895 = !lean_is_exclusive(x_1);
if (x_895 == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; uint8_t x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; 
x_896 = lean_ctor_get(x_1, 6);
lean_dec(x_896);
x_897 = lean_ctor_get(x_1, 5);
lean_dec(x_897);
x_898 = lean_ctor_get(x_1, 4);
lean_dec(x_898);
x_899 = lean_ctor_get(x_1, 3);
lean_dec(x_899);
x_900 = lean_ctor_get(x_1, 2);
lean_dec(x_900);
x_901 = lean_ctor_get(x_1, 1);
lean_dec(x_901);
x_902 = lean_ctor_get(x_1, 0);
lean_dec(x_902);
x_903 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_903, 0, x_91);
x_904 = 1;
x_905 = lean_box(0);
lean_inc(x_4);
x_906 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_903, x_904, x_905, x_4, x_17);
x_907 = lean_ctor_get(x_906, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_906, 1);
lean_inc(x_908);
lean_dec(x_906);
x_909 = l_Lean_Expr_mvarId_x21(x_907);
x_910 = lean_array_push(x_12, x_909);
lean_ctor_set(x_1, 5, x_910);
lean_inc(x_907);
x_911 = l_Lean_mkApp(x_2, x_907);
x_912 = lean_expr_instantiate1(x_92, x_907);
lean_dec(x_907);
lean_dec(x_92);
x_2 = x_911;
x_3 = x_912;
x_5 = x_908;
goto _start;
}
else
{
lean_object* x_914; uint8_t x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
lean_dec(x_1);
x_914 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_914, 0, x_91);
x_915 = 1;
x_916 = lean_box(0);
lean_inc(x_4);
x_917 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_914, x_915, x_916, x_4, x_17);
x_918 = lean_ctor_get(x_917, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_917, 1);
lean_inc(x_919);
lean_dec(x_917);
x_920 = l_Lean_Expr_mvarId_x21(x_918);
x_921 = lean_array_push(x_12, x_920);
x_922 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_922, 0, x_6);
lean_ctor_set(x_922, 1, x_7);
lean_ctor_set(x_922, 2, x_8);
lean_ctor_set(x_922, 3, x_10);
lean_ctor_set(x_922, 4, x_11);
lean_ctor_set(x_922, 5, x_921);
lean_ctor_set(x_922, 6, x_13);
lean_ctor_set_uint8(x_922, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_922, sizeof(void*)*7 + 1, x_14);
lean_inc(x_918);
x_923 = l_Lean_mkApp(x_2, x_918);
x_924 = lean_expr_instantiate1(x_92, x_918);
lean_dec(x_918);
lean_dec(x_92);
x_1 = x_922;
x_2 = x_923;
x_3 = x_924;
x_5 = x_919;
goto _start;
}
}
else
{
uint8_t x_926; 
x_926 = l___private_Lean_Elab_App_9__nextArgIsHole(x_1);
if (x_926 == 0)
{
lean_object* x_927; uint8_t x_928; lean_object* x_929; uint8_t x_930; 
x_927 = lean_array_get_size(x_7);
x_928 = lean_nat_dec_lt(x_10, x_927);
lean_dec(x_927);
lean_inc(x_4);
lean_inc(x_1);
x_929 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_17);
x_930 = !lean_is_exclusive(x_1);
if (x_930 == 0)
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; 
x_931 = lean_ctor_get(x_1, 6);
lean_dec(x_931);
x_932 = lean_ctor_get(x_1, 5);
lean_dec(x_932);
x_933 = lean_ctor_get(x_1, 4);
lean_dec(x_933);
x_934 = lean_ctor_get(x_1, 3);
lean_dec(x_934);
x_935 = lean_ctor_get(x_1, 2);
lean_dec(x_935);
x_936 = lean_ctor_get(x_1, 1);
lean_dec(x_936);
x_937 = lean_ctor_get(x_1, 0);
lean_dec(x_937);
if (lean_obj_tag(x_929) == 0)
{
if (x_928 == 0)
{
lean_object* x_938; uint8_t x_939; 
lean_free_object(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
x_938 = lean_ctor_get(x_929, 1);
lean_inc(x_938);
lean_dec(x_929);
x_939 = l_Array_isEmpty___rarg(x_11);
if (x_939 == 0)
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_940 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_940, 0, x_90);
x_941 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_942 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_942, 0, x_941);
lean_ctor_set(x_942, 1, x_940);
x_943 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_944 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_944, 0, x_942);
lean_ctor_set(x_944, 1, x_943);
x_945 = x_11;
x_946 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_945);
x_947 = x_946;
x_948 = l_Array_toList___rarg(x_947);
lean_dec(x_947);
x_949 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_948);
x_950 = l_Array_HasRepr___rarg___closed__1;
x_951 = lean_string_append(x_950, x_949);
lean_dec(x_949);
x_952 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_952, 0, x_951);
x_953 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_953, 0, x_952);
x_954 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_954, 0, x_944);
lean_ctor_set(x_954, 1, x_953);
x_955 = l_Lean_Elab_Term_throwError___rarg(x_6, x_954, x_4, x_938);
lean_dec(x_6);
return x_955;
}
else
{
lean_object* x_956; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; uint8_t x_987; 
lean_dec(x_90);
lean_dec(x_11);
x_983 = l_Lean_Elab_Term_getOptions(x_4, x_938);
x_984 = lean_ctor_get(x_983, 0);
lean_inc(x_984);
x_985 = lean_ctor_get(x_983, 1);
lean_inc(x_985);
lean_dec(x_983);
x_986 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_987 = l_Lean_checkTraceOption(x_984, x_986);
lean_dec(x_984);
if (x_987 == 0)
{
x_956 = x_985;
goto block_982;
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; 
lean_inc(x_2);
x_988 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_988, 0, x_2);
lean_inc(x_4);
x_989 = l_Lean_Elab_Term_logTrace(x_986, x_6, x_988, x_4, x_985);
x_990 = lean_ctor_get(x_989, 1);
lean_inc(x_990);
lean_dec(x_989);
x_956 = x_990;
goto block_982;
}
block_982:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_957; 
lean_dec(x_3);
x_957 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_956);
lean_dec(x_12);
if (lean_obj_tag(x_957) == 0)
{
uint8_t x_958; 
x_958 = !lean_is_exclusive(x_957);
if (x_958 == 0)
{
lean_object* x_959; 
x_959 = lean_ctor_get(x_957, 0);
lean_dec(x_959);
lean_ctor_set(x_957, 0, x_2);
return x_957;
}
else
{
lean_object* x_960; lean_object* x_961; 
x_960 = lean_ctor_get(x_957, 1);
lean_inc(x_960);
lean_dec(x_957);
x_961 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_961, 0, x_2);
lean_ctor_set(x_961, 1, x_960);
return x_961;
}
}
else
{
uint8_t x_962; 
lean_dec(x_2);
x_962 = !lean_is_exclusive(x_957);
if (x_962 == 0)
{
return x_957;
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; 
x_963 = lean_ctor_get(x_957, 0);
x_964 = lean_ctor_get(x_957, 1);
lean_inc(x_964);
lean_inc(x_963);
lean_dec(x_957);
x_965 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_965, 0, x_963);
lean_ctor_set(x_965, 1, x_964);
return x_965;
}
}
}
else
{
lean_object* x_966; lean_object* x_967; 
x_966 = lean_ctor_get(x_8, 0);
lean_inc(x_966);
lean_dec(x_8);
lean_inc(x_4);
x_967 = l_Lean_Elab_Term_isDefEq(x_6, x_966, x_3, x_4, x_956);
if (lean_obj_tag(x_967) == 0)
{
lean_object* x_968; lean_object* x_969; 
x_968 = lean_ctor_get(x_967, 1);
lean_inc(x_968);
lean_dec(x_967);
x_969 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_968);
lean_dec(x_12);
if (lean_obj_tag(x_969) == 0)
{
uint8_t x_970; 
x_970 = !lean_is_exclusive(x_969);
if (x_970 == 0)
{
lean_object* x_971; 
x_971 = lean_ctor_get(x_969, 0);
lean_dec(x_971);
lean_ctor_set(x_969, 0, x_2);
return x_969;
}
else
{
lean_object* x_972; lean_object* x_973; 
x_972 = lean_ctor_get(x_969, 1);
lean_inc(x_972);
lean_dec(x_969);
x_973 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_973, 0, x_2);
lean_ctor_set(x_973, 1, x_972);
return x_973;
}
}
else
{
uint8_t x_974; 
lean_dec(x_2);
x_974 = !lean_is_exclusive(x_969);
if (x_974 == 0)
{
return x_969;
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; 
x_975 = lean_ctor_get(x_969, 0);
x_976 = lean_ctor_get(x_969, 1);
lean_inc(x_976);
lean_inc(x_975);
lean_dec(x_969);
x_977 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_977, 0, x_975);
lean_ctor_set(x_977, 1, x_976);
return x_977;
}
}
}
else
{
uint8_t x_978; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_978 = !lean_is_exclusive(x_967);
if (x_978 == 0)
{
return x_967;
}
else
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; 
x_979 = lean_ctor_get(x_967, 0);
x_980 = lean_ctor_get(x_967, 1);
lean_inc(x_980);
lean_inc(x_979);
lean_dec(x_967);
x_981 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_981, 0, x_979);
lean_ctor_set(x_981, 1, x_980);
return x_981;
}
}
}
}
}
}
else
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; 
lean_dec(x_90);
lean_dec(x_3);
x_991 = lean_ctor_get(x_929, 1);
lean_inc(x_991);
lean_dec(x_929);
x_992 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_993 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_992, x_91, x_4, x_991);
if (lean_obj_tag(x_993) == 0)
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; uint8_t x_998; lean_object* x_999; lean_object* x_1000; 
x_994 = lean_ctor_get(x_993, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_993, 1);
lean_inc(x_995);
lean_dec(x_993);
x_996 = lean_unsigned_to_nat(1u);
x_997 = lean_nat_add(x_10, x_996);
lean_dec(x_10);
x_998 = 1;
lean_ctor_set(x_1, 3, x_997);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_998);
lean_inc(x_994);
x_999 = l_Lean_mkApp(x_2, x_994);
x_1000 = lean_expr_instantiate1(x_92, x_994);
lean_dec(x_994);
lean_dec(x_92);
x_2 = x_999;
x_3 = x_1000;
x_5 = x_995;
goto _start;
}
else
{
uint8_t x_1002; 
lean_free_object(x_1);
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1002 = !lean_is_exclusive(x_993);
if (x_1002 == 0)
{
return x_993;
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
x_1003 = lean_ctor_get(x_993, 0);
x_1004 = lean_ctor_get(x_993, 1);
lean_inc(x_1004);
lean_inc(x_1003);
lean_dec(x_993);
x_1005 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1005, 0, x_1003);
lean_ctor_set(x_1005, 1, x_1004);
return x_1005;
}
}
}
}
else
{
uint8_t x_1006; 
lean_free_object(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1006 = !lean_is_exclusive(x_929);
if (x_1006 == 0)
{
return x_929;
}
else
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
x_1007 = lean_ctor_get(x_929, 0);
x_1008 = lean_ctor_get(x_929, 1);
lean_inc(x_1008);
lean_inc(x_1007);
lean_dec(x_929);
x_1009 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1009, 0, x_1007);
lean_ctor_set(x_1009, 1, x_1008);
return x_1009;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_929) == 0)
{
if (x_928 == 0)
{
lean_object* x_1010; uint8_t x_1011; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
x_1010 = lean_ctor_get(x_929, 1);
lean_inc(x_1010);
lean_dec(x_929);
x_1011 = l_Array_isEmpty___rarg(x_11);
if (x_1011 == 0)
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1012 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1012, 0, x_90);
x_1013 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1014 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1014, 0, x_1013);
lean_ctor_set(x_1014, 1, x_1012);
x_1015 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1016 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1016, 0, x_1014);
lean_ctor_set(x_1016, 1, x_1015);
x_1017 = x_11;
x_1018 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_1017);
x_1019 = x_1018;
x_1020 = l_Array_toList___rarg(x_1019);
lean_dec(x_1019);
x_1021 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1020);
x_1022 = l_Array_HasRepr___rarg___closed__1;
x_1023 = lean_string_append(x_1022, x_1021);
lean_dec(x_1021);
x_1024 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1024, 0, x_1023);
x_1025 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1025, 0, x_1024);
x_1026 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1026, 0, x_1016);
lean_ctor_set(x_1026, 1, x_1025);
x_1027 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1026, x_4, x_1010);
lean_dec(x_6);
return x_1027;
}
else
{
lean_object* x_1028; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; uint8_t x_1057; 
lean_dec(x_90);
lean_dec(x_11);
x_1053 = l_Lean_Elab_Term_getOptions(x_4, x_1010);
x_1054 = lean_ctor_get(x_1053, 0);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_1053, 1);
lean_inc(x_1055);
lean_dec(x_1053);
x_1056 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1057 = l_Lean_checkTraceOption(x_1054, x_1056);
lean_dec(x_1054);
if (x_1057 == 0)
{
x_1028 = x_1055;
goto block_1052;
}
else
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
lean_inc(x_2);
x_1058 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1058, 0, x_2);
lean_inc(x_4);
x_1059 = l_Lean_Elab_Term_logTrace(x_1056, x_6, x_1058, x_4, x_1055);
x_1060 = lean_ctor_get(x_1059, 1);
lean_inc(x_1060);
lean_dec(x_1059);
x_1028 = x_1060;
goto block_1052;
}
block_1052:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1029; 
lean_dec(x_3);
x_1029 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1028);
lean_dec(x_12);
if (lean_obj_tag(x_1029) == 0)
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1030 = lean_ctor_get(x_1029, 1);
lean_inc(x_1030);
if (lean_is_exclusive(x_1029)) {
 lean_ctor_release(x_1029, 0);
 lean_ctor_release(x_1029, 1);
 x_1031 = x_1029;
} else {
 lean_dec_ref(x_1029);
 x_1031 = lean_box(0);
}
if (lean_is_scalar(x_1031)) {
 x_1032 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1032 = x_1031;
}
lean_ctor_set(x_1032, 0, x_2);
lean_ctor_set(x_1032, 1, x_1030);
return x_1032;
}
else
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
lean_dec(x_2);
x_1033 = lean_ctor_get(x_1029, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1029, 1);
lean_inc(x_1034);
if (lean_is_exclusive(x_1029)) {
 lean_ctor_release(x_1029, 0);
 lean_ctor_release(x_1029, 1);
 x_1035 = x_1029;
} else {
 lean_dec_ref(x_1029);
 x_1035 = lean_box(0);
}
if (lean_is_scalar(x_1035)) {
 x_1036 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1036 = x_1035;
}
lean_ctor_set(x_1036, 0, x_1033);
lean_ctor_set(x_1036, 1, x_1034);
return x_1036;
}
}
else
{
lean_object* x_1037; lean_object* x_1038; 
x_1037 = lean_ctor_get(x_8, 0);
lean_inc(x_1037);
lean_dec(x_8);
lean_inc(x_4);
x_1038 = l_Lean_Elab_Term_isDefEq(x_6, x_1037, x_3, x_4, x_1028);
if (lean_obj_tag(x_1038) == 0)
{
lean_object* x_1039; lean_object* x_1040; 
x_1039 = lean_ctor_get(x_1038, 1);
lean_inc(x_1039);
lean_dec(x_1038);
x_1040 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1039);
lean_dec(x_12);
if (lean_obj_tag(x_1040) == 0)
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1041 = lean_ctor_get(x_1040, 1);
lean_inc(x_1041);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 lean_ctor_release(x_1040, 1);
 x_1042 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1042 = lean_box(0);
}
if (lean_is_scalar(x_1042)) {
 x_1043 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1043 = x_1042;
}
lean_ctor_set(x_1043, 0, x_2);
lean_ctor_set(x_1043, 1, x_1041);
return x_1043;
}
else
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
lean_dec(x_2);
x_1044 = lean_ctor_get(x_1040, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1040, 1);
lean_inc(x_1045);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 lean_ctor_release(x_1040, 1);
 x_1046 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1046 = lean_box(0);
}
if (lean_is_scalar(x_1046)) {
 x_1047 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1047 = x_1046;
}
lean_ctor_set(x_1047, 0, x_1044);
lean_ctor_set(x_1047, 1, x_1045);
return x_1047;
}
}
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1048 = lean_ctor_get(x_1038, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1038, 1);
lean_inc(x_1049);
if (lean_is_exclusive(x_1038)) {
 lean_ctor_release(x_1038, 0);
 lean_ctor_release(x_1038, 1);
 x_1050 = x_1038;
} else {
 lean_dec_ref(x_1038);
 x_1050 = lean_box(0);
}
if (lean_is_scalar(x_1050)) {
 x_1051 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1051 = x_1050;
}
lean_ctor_set(x_1051, 0, x_1048);
lean_ctor_set(x_1051, 1, x_1049);
return x_1051;
}
}
}
}
}
else
{
lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; 
lean_dec(x_90);
lean_dec(x_3);
x_1061 = lean_ctor_get(x_929, 1);
lean_inc(x_1061);
lean_dec(x_929);
x_1062 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1063 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_1062, x_91, x_4, x_1061);
if (lean_obj_tag(x_1063) == 0)
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; uint8_t x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; 
x_1064 = lean_ctor_get(x_1063, 0);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1063, 1);
lean_inc(x_1065);
lean_dec(x_1063);
x_1066 = lean_unsigned_to_nat(1u);
x_1067 = lean_nat_add(x_10, x_1066);
lean_dec(x_10);
x_1068 = 1;
x_1069 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1069, 0, x_6);
lean_ctor_set(x_1069, 1, x_7);
lean_ctor_set(x_1069, 2, x_8);
lean_ctor_set(x_1069, 3, x_1067);
lean_ctor_set(x_1069, 4, x_11);
lean_ctor_set(x_1069, 5, x_12);
lean_ctor_set(x_1069, 6, x_13);
lean_ctor_set_uint8(x_1069, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1069, sizeof(void*)*7 + 1, x_1068);
lean_inc(x_1064);
x_1070 = l_Lean_mkApp(x_2, x_1064);
x_1071 = lean_expr_instantiate1(x_92, x_1064);
lean_dec(x_1064);
lean_dec(x_92);
x_1 = x_1069;
x_2 = x_1070;
x_3 = x_1071;
x_5 = x_1065;
goto _start;
}
else
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1073 = lean_ctor_get(x_1063, 0);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_1063, 1);
lean_inc(x_1074);
if (lean_is_exclusive(x_1063)) {
 lean_ctor_release(x_1063, 0);
 lean_ctor_release(x_1063, 1);
 x_1075 = x_1063;
} else {
 lean_dec_ref(x_1063);
 x_1075 = lean_box(0);
}
if (lean_is_scalar(x_1075)) {
 x_1076 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1076 = x_1075;
}
lean_ctor_set(x_1076, 0, x_1073);
lean_ctor_set(x_1076, 1, x_1074);
return x_1076;
}
}
}
else
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1077 = lean_ctor_get(x_929, 0);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_929, 1);
lean_inc(x_1078);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 x_1079 = x_929;
} else {
 lean_dec_ref(x_929);
 x_1079 = lean_box(0);
}
if (lean_is_scalar(x_1079)) {
 x_1080 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1080 = x_1079;
}
lean_ctor_set(x_1080, 0, x_1077);
lean_ctor_set(x_1080, 1, x_1078);
return x_1080;
}
}
}
else
{
uint8_t x_1081; 
lean_dec(x_90);
lean_dec(x_16);
lean_dec(x_3);
x_1081 = !lean_is_exclusive(x_1);
if (x_1081 == 0)
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; uint8_t x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
x_1082 = lean_ctor_get(x_1, 6);
lean_dec(x_1082);
x_1083 = lean_ctor_get(x_1, 5);
lean_dec(x_1083);
x_1084 = lean_ctor_get(x_1, 4);
lean_dec(x_1084);
x_1085 = lean_ctor_get(x_1, 3);
lean_dec(x_1085);
x_1086 = lean_ctor_get(x_1, 2);
lean_dec(x_1086);
x_1087 = lean_ctor_get(x_1, 1);
lean_dec(x_1087);
x_1088 = lean_ctor_get(x_1, 0);
lean_dec(x_1088);
x_1089 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1089, 0, x_91);
x_1090 = 1;
x_1091 = lean_box(0);
lean_inc(x_4);
x_1092 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_1089, x_1090, x_1091, x_4, x_17);
x_1093 = lean_ctor_get(x_1092, 0);
lean_inc(x_1093);
x_1094 = lean_ctor_get(x_1092, 1);
lean_inc(x_1094);
lean_dec(x_1092);
x_1095 = lean_unsigned_to_nat(1u);
x_1096 = lean_nat_add(x_10, x_1095);
lean_dec(x_10);
x_1097 = l_Lean_Expr_mvarId_x21(x_1093);
x_1098 = lean_array_push(x_12, x_1097);
lean_ctor_set(x_1, 5, x_1098);
lean_ctor_set(x_1, 3, x_1096);
lean_inc(x_1093);
x_1099 = l_Lean_mkApp(x_2, x_1093);
x_1100 = lean_expr_instantiate1(x_92, x_1093);
lean_dec(x_1093);
lean_dec(x_92);
x_2 = x_1099;
x_3 = x_1100;
x_5 = x_1094;
goto _start;
}
else
{
lean_object* x_1102; uint8_t x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
lean_dec(x_1);
x_1102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1102, 0, x_91);
x_1103 = 1;
x_1104 = lean_box(0);
lean_inc(x_4);
x_1105 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_1102, x_1103, x_1104, x_4, x_17);
x_1106 = lean_ctor_get(x_1105, 0);
lean_inc(x_1106);
x_1107 = lean_ctor_get(x_1105, 1);
lean_inc(x_1107);
lean_dec(x_1105);
x_1108 = lean_unsigned_to_nat(1u);
x_1109 = lean_nat_add(x_10, x_1108);
lean_dec(x_10);
x_1110 = l_Lean_Expr_mvarId_x21(x_1106);
x_1111 = lean_array_push(x_12, x_1110);
x_1112 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1112, 0, x_6);
lean_ctor_set(x_1112, 1, x_7);
lean_ctor_set(x_1112, 2, x_8);
lean_ctor_set(x_1112, 3, x_1109);
lean_ctor_set(x_1112, 4, x_11);
lean_ctor_set(x_1112, 5, x_1111);
lean_ctor_set(x_1112, 6, x_13);
lean_ctor_set_uint8(x_1112, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1112, sizeof(void*)*7 + 1, x_14);
lean_inc(x_1106);
x_1113 = l_Lean_mkApp(x_2, x_1106);
x_1114 = lean_expr_instantiate1(x_92, x_1106);
lean_dec(x_1106);
lean_dec(x_92);
x_1 = x_1112;
x_2 = x_1113;
x_3 = x_1114;
x_5 = x_1107;
goto _start;
}
}
}
}
default: 
{
uint8_t x_1116; lean_object* x_1117; lean_object* x_1118; uint8_t x_1119; lean_object* x_1120; uint8_t x_1121; 
x_1116 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1117 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1117, 0, x_6);
lean_ctor_set(x_1117, 1, x_7);
lean_ctor_set(x_1117, 2, x_8);
lean_ctor_set(x_1117, 3, x_10);
lean_ctor_set(x_1117, 4, x_11);
lean_ctor_set(x_1117, 5, x_12);
lean_ctor_set(x_1117, 6, x_13);
lean_ctor_set_uint8(x_1117, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1117, sizeof(void*)*7 + 1, x_1116);
x_1118 = lean_array_get_size(x_7);
x_1119 = lean_nat_dec_lt(x_10, x_1118);
lean_dec(x_1118);
lean_inc(x_4);
lean_inc(x_1);
x_1120 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_17);
x_1121 = !lean_is_exclusive(x_1);
if (x_1121 == 0)
{
lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1122 = lean_ctor_get(x_1, 6);
lean_dec(x_1122);
x_1123 = lean_ctor_get(x_1, 5);
lean_dec(x_1123);
x_1124 = lean_ctor_get(x_1, 4);
lean_dec(x_1124);
x_1125 = lean_ctor_get(x_1, 3);
lean_dec(x_1125);
x_1126 = lean_ctor_get(x_1, 2);
lean_dec(x_1126);
x_1127 = lean_ctor_get(x_1, 1);
lean_dec(x_1127);
x_1128 = lean_ctor_get(x_1, 0);
lean_dec(x_1128);
if (lean_obj_tag(x_1120) == 0)
{
lean_object* x_1129; lean_object* x_1130; 
x_1129 = lean_ctor_get(x_1120, 1);
lean_inc(x_1129);
lean_dec(x_1120);
if (x_1119 == 0)
{
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1184; 
x_1184 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_1184) == 0)
{
lean_object* x_1185; 
x_1185 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_1185) == 0)
{
lean_object* x_1186; 
lean_dec(x_1117);
lean_dec(x_92);
lean_dec(x_91);
x_1186 = lean_box(0);
x_1130 = x_1186;
goto block_1183;
}
else
{
lean_object* x_1187; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1187 = lean_ctor_get(x_1185, 0);
lean_inc(x_1187);
lean_dec(x_1185);
if (lean_obj_tag(x_1187) == 4)
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
x_1188 = lean_ctor_get(x_1187, 0);
lean_inc(x_1188);
lean_dec(x_1187);
x_1189 = l_Lean_Elab_Term_getEnv___rarg(x_1129);
x_1190 = lean_ctor_get(x_1189, 0);
lean_inc(x_1190);
x_1191 = lean_ctor_get(x_1189, 1);
lean_inc(x_1191);
lean_dec(x_1189);
x_1192 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1190, x_1188);
if (lean_obj_tag(x_1192) == 0)
{
lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; 
lean_dec(x_1117);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_1193 = lean_ctor_get(x_1192, 0);
lean_inc(x_1193);
lean_dec(x_1192);
x_1194 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1194, 0, x_1193);
x_1195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1195, 0, x_1194);
x_1196 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1195, x_4, x_1191);
lean_dec(x_6);
return x_1196;
}
else
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; 
x_1197 = lean_ctor_get(x_1192, 0);
lean_inc(x_1197);
lean_dec(x_1192);
x_1198 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1191);
x_1199 = lean_ctor_get(x_1198, 1);
lean_inc(x_1199);
lean_dec(x_1198);
x_1200 = l_Lean_Elab_Term_getMainModule___rarg(x_1199);
x_1201 = lean_ctor_get(x_1200, 1);
lean_inc(x_1201);
lean_dec(x_1200);
x_1202 = l_Lean_Syntax_getArgs(x_1197);
lean_dec(x_1197);
x_1203 = l_Array_empty___closed__1;
x_1204 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1202, x_1202, x_94, x_1203);
lean_dec(x_1202);
x_1205 = l_Lean_nullKind___closed__2;
x_1206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1206, 0, x_1205);
lean_ctor_set(x_1206, 1, x_1204);
x_1207 = lean_array_push(x_1203, x_1206);
x_1208 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_1209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1209, 0, x_1208);
lean_ctor_set(x_1209, 1, x_1207);
x_1210 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1211 = lean_array_push(x_1210, x_1209);
x_1212 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1213 = lean_array_push(x_1211, x_1212);
x_1214 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1215, 0, x_1214);
lean_ctor_set(x_1215, 1, x_1213);
x_1216 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_1217 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_1218 = lean_nat_sub(x_1217, x_94);
lean_dec(x_1217);
x_1219 = lean_unsigned_to_nat(1u);
x_1220 = lean_nat_sub(x_1218, x_1219);
lean_dec(x_1218);
x_1221 = l_Lean_Expr_getRevArg_x21___main(x_91, x_1220);
lean_dec(x_91);
if (lean_obj_tag(x_1216) == 0)
{
lean_object* x_1222; lean_object* x_1223; 
x_1222 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1222, 0, x_1215);
lean_inc(x_4);
lean_inc(x_2);
x_1223 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_1222, x_1221, x_4, x_1201);
if (lean_obj_tag(x_1223) == 0)
{
lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; 
x_1224 = lean_ctor_get(x_1223, 0);
lean_inc(x_1224);
x_1225 = lean_ctor_get(x_1223, 1);
lean_inc(x_1225);
lean_dec(x_1223);
lean_inc(x_1224);
x_1226 = l_Lean_mkApp(x_2, x_1224);
x_1227 = lean_expr_instantiate1(x_92, x_1224);
lean_dec(x_1224);
lean_dec(x_92);
x_1 = x_1117;
x_2 = x_1226;
x_3 = x_1227;
x_5 = x_1225;
goto _start;
}
else
{
uint8_t x_1229; 
lean_dec(x_1117);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1229 = !lean_is_exclusive(x_1223);
if (x_1229 == 0)
{
return x_1223;
}
else
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; 
x_1230 = lean_ctor_get(x_1223, 0);
x_1231 = lean_ctor_get(x_1223, 1);
lean_inc(x_1231);
lean_inc(x_1230);
lean_dec(x_1223);
x_1232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1232, 0, x_1230);
lean_ctor_set(x_1232, 1, x_1231);
return x_1232;
}
}
}
else
{
lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
x_1233 = lean_ctor_get(x_1216, 0);
lean_inc(x_1233);
lean_dec(x_1216);
x_1234 = l_Lean_Syntax_replaceInfo___main(x_1233, x_1215);
x_1235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1235, 0, x_1234);
lean_inc(x_4);
lean_inc(x_2);
x_1236 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_1235, x_1221, x_4, x_1201);
if (lean_obj_tag(x_1236) == 0)
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; 
x_1237 = lean_ctor_get(x_1236, 0);
lean_inc(x_1237);
x_1238 = lean_ctor_get(x_1236, 1);
lean_inc(x_1238);
lean_dec(x_1236);
lean_inc(x_1237);
x_1239 = l_Lean_mkApp(x_2, x_1237);
x_1240 = lean_expr_instantiate1(x_92, x_1237);
lean_dec(x_1237);
lean_dec(x_92);
x_1 = x_1117;
x_2 = x_1239;
x_3 = x_1240;
x_5 = x_1238;
goto _start;
}
else
{
uint8_t x_1242; 
lean_dec(x_1117);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1242 = !lean_is_exclusive(x_1236);
if (x_1242 == 0)
{
return x_1236;
}
else
{
lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; 
x_1243 = lean_ctor_get(x_1236, 0);
x_1244 = lean_ctor_get(x_1236, 1);
lean_inc(x_1244);
lean_inc(x_1243);
lean_dec(x_1236);
x_1245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1245, 0, x_1243);
lean_ctor_set(x_1245, 1, x_1244);
return x_1245;
}
}
}
}
}
else
{
lean_object* x_1246; lean_object* x_1247; 
lean_dec(x_1187);
lean_dec(x_1117);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_1246 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1247 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1246, x_4, x_1129);
lean_dec(x_6);
return x_1247;
}
}
}
else
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1248 = lean_ctor_get(x_1184, 0);
lean_inc(x_1248);
lean_dec(x_1184);
lean_inc(x_1248);
x_1249 = l_Lean_mkApp(x_2, x_1248);
x_1250 = lean_expr_instantiate1(x_92, x_1248);
lean_dec(x_1248);
lean_dec(x_92);
x_1 = x_1117;
x_2 = x_1249;
x_3 = x_1250;
x_5 = x_1129;
goto _start;
}
}
else
{
lean_object* x_1252; 
lean_dec(x_1117);
lean_dec(x_92);
lean_dec(x_91);
x_1252 = lean_box(0);
x_1130 = x_1252;
goto block_1183;
}
}
else
{
lean_object* x_1253; lean_object* x_1254; 
lean_dec(x_1117);
lean_dec(x_90);
lean_dec(x_3);
x_1253 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1254 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_1253, x_91, x_4, x_1129);
if (lean_obj_tag(x_1254) == 0)
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
x_1255 = lean_ctor_get(x_1254, 0);
lean_inc(x_1255);
x_1256 = lean_ctor_get(x_1254, 1);
lean_inc(x_1256);
lean_dec(x_1254);
x_1257 = lean_unsigned_to_nat(1u);
x_1258 = lean_nat_add(x_10, x_1257);
lean_dec(x_10);
lean_ctor_set(x_1, 3, x_1258);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_1116);
lean_inc(x_1255);
x_1259 = l_Lean_mkApp(x_2, x_1255);
x_1260 = lean_expr_instantiate1(x_92, x_1255);
lean_dec(x_1255);
lean_dec(x_92);
x_2 = x_1259;
x_3 = x_1260;
x_5 = x_1256;
goto _start;
}
else
{
uint8_t x_1262; 
lean_free_object(x_1);
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1262 = !lean_is_exclusive(x_1254);
if (x_1262 == 0)
{
return x_1254;
}
else
{
lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; 
x_1263 = lean_ctor_get(x_1254, 0);
x_1264 = lean_ctor_get(x_1254, 1);
lean_inc(x_1264);
lean_inc(x_1263);
lean_dec(x_1254);
x_1265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1265, 0, x_1263);
lean_ctor_set(x_1265, 1, x_1264);
return x_1265;
}
}
}
block_1183:
{
uint8_t x_1131; 
lean_dec(x_1130);
x_1131 = l_Array_isEmpty___rarg(x_11);
if (x_1131 == 0)
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1132 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1132, 0, x_90);
x_1133 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1134 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1134, 0, x_1133);
lean_ctor_set(x_1134, 1, x_1132);
x_1135 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1136 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1136, 0, x_1134);
lean_ctor_set(x_1136, 1, x_1135);
x_1137 = x_11;
x_1138 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_1137);
x_1139 = x_1138;
x_1140 = l_Array_toList___rarg(x_1139);
lean_dec(x_1139);
x_1141 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1140);
x_1142 = l_Array_HasRepr___rarg___closed__1;
x_1143 = lean_string_append(x_1142, x_1141);
lean_dec(x_1141);
x_1144 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1144, 0, x_1143);
x_1145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1145, 0, x_1144);
x_1146 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1146, 0, x_1136);
lean_ctor_set(x_1146, 1, x_1145);
x_1147 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1146, x_4, x_1129);
lean_dec(x_6);
return x_1147;
}
else
{
lean_object* x_1148; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; uint8_t x_1179; 
lean_dec(x_90);
lean_dec(x_11);
x_1175 = l_Lean_Elab_Term_getOptions(x_4, x_1129);
x_1176 = lean_ctor_get(x_1175, 0);
lean_inc(x_1176);
x_1177 = lean_ctor_get(x_1175, 1);
lean_inc(x_1177);
lean_dec(x_1175);
x_1178 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1179 = l_Lean_checkTraceOption(x_1176, x_1178);
lean_dec(x_1176);
if (x_1179 == 0)
{
x_1148 = x_1177;
goto block_1174;
}
else
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
lean_inc(x_2);
x_1180 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1180, 0, x_2);
lean_inc(x_4);
x_1181 = l_Lean_Elab_Term_logTrace(x_1178, x_6, x_1180, x_4, x_1177);
x_1182 = lean_ctor_get(x_1181, 1);
lean_inc(x_1182);
lean_dec(x_1181);
x_1148 = x_1182;
goto block_1174;
}
block_1174:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1149; 
lean_dec(x_3);
x_1149 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1148);
lean_dec(x_12);
if (lean_obj_tag(x_1149) == 0)
{
uint8_t x_1150; 
x_1150 = !lean_is_exclusive(x_1149);
if (x_1150 == 0)
{
lean_object* x_1151; 
x_1151 = lean_ctor_get(x_1149, 0);
lean_dec(x_1151);
lean_ctor_set(x_1149, 0, x_2);
return x_1149;
}
else
{
lean_object* x_1152; lean_object* x_1153; 
x_1152 = lean_ctor_get(x_1149, 1);
lean_inc(x_1152);
lean_dec(x_1149);
x_1153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1153, 0, x_2);
lean_ctor_set(x_1153, 1, x_1152);
return x_1153;
}
}
else
{
uint8_t x_1154; 
lean_dec(x_2);
x_1154 = !lean_is_exclusive(x_1149);
if (x_1154 == 0)
{
return x_1149;
}
else
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; 
x_1155 = lean_ctor_get(x_1149, 0);
x_1156 = lean_ctor_get(x_1149, 1);
lean_inc(x_1156);
lean_inc(x_1155);
lean_dec(x_1149);
x_1157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1157, 0, x_1155);
lean_ctor_set(x_1157, 1, x_1156);
return x_1157;
}
}
}
else
{
lean_object* x_1158; lean_object* x_1159; 
x_1158 = lean_ctor_get(x_8, 0);
lean_inc(x_1158);
lean_dec(x_8);
lean_inc(x_4);
x_1159 = l_Lean_Elab_Term_isDefEq(x_6, x_1158, x_3, x_4, x_1148);
if (lean_obj_tag(x_1159) == 0)
{
lean_object* x_1160; lean_object* x_1161; 
x_1160 = lean_ctor_get(x_1159, 1);
lean_inc(x_1160);
lean_dec(x_1159);
x_1161 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1160);
lean_dec(x_12);
if (lean_obj_tag(x_1161) == 0)
{
uint8_t x_1162; 
x_1162 = !lean_is_exclusive(x_1161);
if (x_1162 == 0)
{
lean_object* x_1163; 
x_1163 = lean_ctor_get(x_1161, 0);
lean_dec(x_1163);
lean_ctor_set(x_1161, 0, x_2);
return x_1161;
}
else
{
lean_object* x_1164; lean_object* x_1165; 
x_1164 = lean_ctor_get(x_1161, 1);
lean_inc(x_1164);
lean_dec(x_1161);
x_1165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1165, 0, x_2);
lean_ctor_set(x_1165, 1, x_1164);
return x_1165;
}
}
else
{
uint8_t x_1166; 
lean_dec(x_2);
x_1166 = !lean_is_exclusive(x_1161);
if (x_1166 == 0)
{
return x_1161;
}
else
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; 
x_1167 = lean_ctor_get(x_1161, 0);
x_1168 = lean_ctor_get(x_1161, 1);
lean_inc(x_1168);
lean_inc(x_1167);
lean_dec(x_1161);
x_1169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1169, 0, x_1167);
lean_ctor_set(x_1169, 1, x_1168);
return x_1169;
}
}
}
else
{
uint8_t x_1170; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1170 = !lean_is_exclusive(x_1159);
if (x_1170 == 0)
{
return x_1159;
}
else
{
lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; 
x_1171 = lean_ctor_get(x_1159, 0);
x_1172 = lean_ctor_get(x_1159, 1);
lean_inc(x_1172);
lean_inc(x_1171);
lean_dec(x_1159);
x_1173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1173, 0, x_1171);
lean_ctor_set(x_1173, 1, x_1172);
return x_1173;
}
}
}
}
}
}
}
else
{
uint8_t x_1266; 
lean_free_object(x_1);
lean_dec(x_1117);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1266 = !lean_is_exclusive(x_1120);
if (x_1266 == 0)
{
return x_1120;
}
else
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
x_1267 = lean_ctor_get(x_1120, 0);
x_1268 = lean_ctor_get(x_1120, 1);
lean_inc(x_1268);
lean_inc(x_1267);
lean_dec(x_1120);
x_1269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1269, 0, x_1267);
lean_ctor_set(x_1269, 1, x_1268);
return x_1269;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1120) == 0)
{
lean_object* x_1270; lean_object* x_1271; 
x_1270 = lean_ctor_get(x_1120, 1);
lean_inc(x_1270);
lean_dec(x_1120);
if (x_1119 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1323; 
x_1323 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_1323) == 0)
{
lean_object* x_1324; 
x_1324 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_1324) == 0)
{
lean_object* x_1325; 
lean_dec(x_1117);
lean_dec(x_92);
lean_dec(x_91);
x_1325 = lean_box(0);
x_1271 = x_1325;
goto block_1322;
}
else
{
lean_object* x_1326; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1326 = lean_ctor_get(x_1324, 0);
lean_inc(x_1326);
lean_dec(x_1324);
if (lean_obj_tag(x_1326) == 4)
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; 
x_1327 = lean_ctor_get(x_1326, 0);
lean_inc(x_1327);
lean_dec(x_1326);
x_1328 = l_Lean_Elab_Term_getEnv___rarg(x_1270);
x_1329 = lean_ctor_get(x_1328, 0);
lean_inc(x_1329);
x_1330 = lean_ctor_get(x_1328, 1);
lean_inc(x_1330);
lean_dec(x_1328);
x_1331 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1329, x_1327);
if (lean_obj_tag(x_1331) == 0)
{
lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
lean_dec(x_1117);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_1332 = lean_ctor_get(x_1331, 0);
lean_inc(x_1332);
lean_dec(x_1331);
x_1333 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1333, 0, x_1332);
x_1334 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1334, 0, x_1333);
x_1335 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1334, x_4, x_1330);
lean_dec(x_6);
return x_1335;
}
else
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; 
x_1336 = lean_ctor_get(x_1331, 0);
lean_inc(x_1336);
lean_dec(x_1331);
x_1337 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1330);
x_1338 = lean_ctor_get(x_1337, 1);
lean_inc(x_1338);
lean_dec(x_1337);
x_1339 = l_Lean_Elab_Term_getMainModule___rarg(x_1338);
x_1340 = lean_ctor_get(x_1339, 1);
lean_inc(x_1340);
lean_dec(x_1339);
x_1341 = l_Lean_Syntax_getArgs(x_1336);
lean_dec(x_1336);
x_1342 = l_Array_empty___closed__1;
x_1343 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1341, x_1341, x_94, x_1342);
lean_dec(x_1341);
x_1344 = l_Lean_nullKind___closed__2;
x_1345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1345, 0, x_1344);
lean_ctor_set(x_1345, 1, x_1343);
x_1346 = lean_array_push(x_1342, x_1345);
x_1347 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_1348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1348, 0, x_1347);
lean_ctor_set(x_1348, 1, x_1346);
x_1349 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1350 = lean_array_push(x_1349, x_1348);
x_1351 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1352 = lean_array_push(x_1350, x_1351);
x_1353 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1354, 0, x_1353);
lean_ctor_set(x_1354, 1, x_1352);
x_1355 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_1356 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_1357 = lean_nat_sub(x_1356, x_94);
lean_dec(x_1356);
x_1358 = lean_unsigned_to_nat(1u);
x_1359 = lean_nat_sub(x_1357, x_1358);
lean_dec(x_1357);
x_1360 = l_Lean_Expr_getRevArg_x21___main(x_91, x_1359);
lean_dec(x_91);
if (lean_obj_tag(x_1355) == 0)
{
lean_object* x_1361; lean_object* x_1362; 
x_1361 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1361, 0, x_1354);
lean_inc(x_4);
lean_inc(x_2);
x_1362 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_1361, x_1360, x_4, x_1340);
if (lean_obj_tag(x_1362) == 0)
{
lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; 
x_1363 = lean_ctor_get(x_1362, 0);
lean_inc(x_1363);
x_1364 = lean_ctor_get(x_1362, 1);
lean_inc(x_1364);
lean_dec(x_1362);
lean_inc(x_1363);
x_1365 = l_Lean_mkApp(x_2, x_1363);
x_1366 = lean_expr_instantiate1(x_92, x_1363);
lean_dec(x_1363);
lean_dec(x_92);
x_1 = x_1117;
x_2 = x_1365;
x_3 = x_1366;
x_5 = x_1364;
goto _start;
}
else
{
lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; 
lean_dec(x_1117);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1368 = lean_ctor_get(x_1362, 0);
lean_inc(x_1368);
x_1369 = lean_ctor_get(x_1362, 1);
lean_inc(x_1369);
if (lean_is_exclusive(x_1362)) {
 lean_ctor_release(x_1362, 0);
 lean_ctor_release(x_1362, 1);
 x_1370 = x_1362;
} else {
 lean_dec_ref(x_1362);
 x_1370 = lean_box(0);
}
if (lean_is_scalar(x_1370)) {
 x_1371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1371 = x_1370;
}
lean_ctor_set(x_1371, 0, x_1368);
lean_ctor_set(x_1371, 1, x_1369);
return x_1371;
}
}
else
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; 
x_1372 = lean_ctor_get(x_1355, 0);
lean_inc(x_1372);
lean_dec(x_1355);
x_1373 = l_Lean_Syntax_replaceInfo___main(x_1372, x_1354);
x_1374 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1374, 0, x_1373);
lean_inc(x_4);
lean_inc(x_2);
x_1375 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_1374, x_1360, x_4, x_1340);
if (lean_obj_tag(x_1375) == 0)
{
lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; 
x_1376 = lean_ctor_get(x_1375, 0);
lean_inc(x_1376);
x_1377 = lean_ctor_get(x_1375, 1);
lean_inc(x_1377);
lean_dec(x_1375);
lean_inc(x_1376);
x_1378 = l_Lean_mkApp(x_2, x_1376);
x_1379 = lean_expr_instantiate1(x_92, x_1376);
lean_dec(x_1376);
lean_dec(x_92);
x_1 = x_1117;
x_2 = x_1378;
x_3 = x_1379;
x_5 = x_1377;
goto _start;
}
else
{
lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; 
lean_dec(x_1117);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1381 = lean_ctor_get(x_1375, 0);
lean_inc(x_1381);
x_1382 = lean_ctor_get(x_1375, 1);
lean_inc(x_1382);
if (lean_is_exclusive(x_1375)) {
 lean_ctor_release(x_1375, 0);
 lean_ctor_release(x_1375, 1);
 x_1383 = x_1375;
} else {
 lean_dec_ref(x_1375);
 x_1383 = lean_box(0);
}
if (lean_is_scalar(x_1383)) {
 x_1384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1384 = x_1383;
}
lean_ctor_set(x_1384, 0, x_1381);
lean_ctor_set(x_1384, 1, x_1382);
return x_1384;
}
}
}
}
else
{
lean_object* x_1385; lean_object* x_1386; 
lean_dec(x_1326);
lean_dec(x_1117);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_1385 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1386 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1385, x_4, x_1270);
lean_dec(x_6);
return x_1386;
}
}
}
else
{
lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1387 = lean_ctor_get(x_1323, 0);
lean_inc(x_1387);
lean_dec(x_1323);
lean_inc(x_1387);
x_1388 = l_Lean_mkApp(x_2, x_1387);
x_1389 = lean_expr_instantiate1(x_92, x_1387);
lean_dec(x_1387);
lean_dec(x_92);
x_1 = x_1117;
x_2 = x_1388;
x_3 = x_1389;
x_5 = x_1270;
goto _start;
}
}
else
{
lean_object* x_1391; 
lean_dec(x_1117);
lean_dec(x_92);
lean_dec(x_91);
x_1391 = lean_box(0);
x_1271 = x_1391;
goto block_1322;
}
}
else
{
lean_object* x_1392; lean_object* x_1393; 
lean_dec(x_1117);
lean_dec(x_90);
lean_dec(x_3);
x_1392 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1393 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_1392, x_91, x_4, x_1270);
if (lean_obj_tag(x_1393) == 0)
{
lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; 
x_1394 = lean_ctor_get(x_1393, 0);
lean_inc(x_1394);
x_1395 = lean_ctor_get(x_1393, 1);
lean_inc(x_1395);
lean_dec(x_1393);
x_1396 = lean_unsigned_to_nat(1u);
x_1397 = lean_nat_add(x_10, x_1396);
lean_dec(x_10);
x_1398 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1398, 0, x_6);
lean_ctor_set(x_1398, 1, x_7);
lean_ctor_set(x_1398, 2, x_8);
lean_ctor_set(x_1398, 3, x_1397);
lean_ctor_set(x_1398, 4, x_11);
lean_ctor_set(x_1398, 5, x_12);
lean_ctor_set(x_1398, 6, x_13);
lean_ctor_set_uint8(x_1398, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1398, sizeof(void*)*7 + 1, x_1116);
lean_inc(x_1394);
x_1399 = l_Lean_mkApp(x_2, x_1394);
x_1400 = lean_expr_instantiate1(x_92, x_1394);
lean_dec(x_1394);
lean_dec(x_92);
x_1 = x_1398;
x_2 = x_1399;
x_3 = x_1400;
x_5 = x_1395;
goto _start;
}
else
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; 
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1402 = lean_ctor_get(x_1393, 0);
lean_inc(x_1402);
x_1403 = lean_ctor_get(x_1393, 1);
lean_inc(x_1403);
if (lean_is_exclusive(x_1393)) {
 lean_ctor_release(x_1393, 0);
 lean_ctor_release(x_1393, 1);
 x_1404 = x_1393;
} else {
 lean_dec_ref(x_1393);
 x_1404 = lean_box(0);
}
if (lean_is_scalar(x_1404)) {
 x_1405 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1405 = x_1404;
}
lean_ctor_set(x_1405, 0, x_1402);
lean_ctor_set(x_1405, 1, x_1403);
return x_1405;
}
}
block_1322:
{
uint8_t x_1272; 
lean_dec(x_1271);
x_1272 = l_Array_isEmpty___rarg(x_11);
if (x_1272 == 0)
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1273 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1273, 0, x_90);
x_1274 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1275 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1275, 0, x_1274);
lean_ctor_set(x_1275, 1, x_1273);
x_1276 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1277 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1277, 0, x_1275);
lean_ctor_set(x_1277, 1, x_1276);
x_1278 = x_11;
x_1279 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_1278);
x_1280 = x_1279;
x_1281 = l_Array_toList___rarg(x_1280);
lean_dec(x_1280);
x_1282 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1281);
x_1283 = l_Array_HasRepr___rarg___closed__1;
x_1284 = lean_string_append(x_1283, x_1282);
lean_dec(x_1282);
x_1285 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1285, 0, x_1284);
x_1286 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1286, 0, x_1285);
x_1287 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1287, 0, x_1277);
lean_ctor_set(x_1287, 1, x_1286);
x_1288 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1287, x_4, x_1270);
lean_dec(x_6);
return x_1288;
}
else
{
lean_object* x_1289; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; uint8_t x_1318; 
lean_dec(x_90);
lean_dec(x_11);
x_1314 = l_Lean_Elab_Term_getOptions(x_4, x_1270);
x_1315 = lean_ctor_get(x_1314, 0);
lean_inc(x_1315);
x_1316 = lean_ctor_get(x_1314, 1);
lean_inc(x_1316);
lean_dec(x_1314);
x_1317 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1318 = l_Lean_checkTraceOption(x_1315, x_1317);
lean_dec(x_1315);
if (x_1318 == 0)
{
x_1289 = x_1316;
goto block_1313;
}
else
{
lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; 
lean_inc(x_2);
x_1319 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1319, 0, x_2);
lean_inc(x_4);
x_1320 = l_Lean_Elab_Term_logTrace(x_1317, x_6, x_1319, x_4, x_1316);
x_1321 = lean_ctor_get(x_1320, 1);
lean_inc(x_1321);
lean_dec(x_1320);
x_1289 = x_1321;
goto block_1313;
}
block_1313:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1290; 
lean_dec(x_3);
x_1290 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1289);
lean_dec(x_12);
if (lean_obj_tag(x_1290) == 0)
{
lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; 
x_1291 = lean_ctor_get(x_1290, 1);
lean_inc(x_1291);
if (lean_is_exclusive(x_1290)) {
 lean_ctor_release(x_1290, 0);
 lean_ctor_release(x_1290, 1);
 x_1292 = x_1290;
} else {
 lean_dec_ref(x_1290);
 x_1292 = lean_box(0);
}
if (lean_is_scalar(x_1292)) {
 x_1293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1293 = x_1292;
}
lean_ctor_set(x_1293, 0, x_2);
lean_ctor_set(x_1293, 1, x_1291);
return x_1293;
}
else
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; 
lean_dec(x_2);
x_1294 = lean_ctor_get(x_1290, 0);
lean_inc(x_1294);
x_1295 = lean_ctor_get(x_1290, 1);
lean_inc(x_1295);
if (lean_is_exclusive(x_1290)) {
 lean_ctor_release(x_1290, 0);
 lean_ctor_release(x_1290, 1);
 x_1296 = x_1290;
} else {
 lean_dec_ref(x_1290);
 x_1296 = lean_box(0);
}
if (lean_is_scalar(x_1296)) {
 x_1297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1297 = x_1296;
}
lean_ctor_set(x_1297, 0, x_1294);
lean_ctor_set(x_1297, 1, x_1295);
return x_1297;
}
}
else
{
lean_object* x_1298; lean_object* x_1299; 
x_1298 = lean_ctor_get(x_8, 0);
lean_inc(x_1298);
lean_dec(x_8);
lean_inc(x_4);
x_1299 = l_Lean_Elab_Term_isDefEq(x_6, x_1298, x_3, x_4, x_1289);
if (lean_obj_tag(x_1299) == 0)
{
lean_object* x_1300; lean_object* x_1301; 
x_1300 = lean_ctor_get(x_1299, 1);
lean_inc(x_1300);
lean_dec(x_1299);
x_1301 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1300);
lean_dec(x_12);
if (lean_obj_tag(x_1301) == 0)
{
lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; 
x_1302 = lean_ctor_get(x_1301, 1);
lean_inc(x_1302);
if (lean_is_exclusive(x_1301)) {
 lean_ctor_release(x_1301, 0);
 lean_ctor_release(x_1301, 1);
 x_1303 = x_1301;
} else {
 lean_dec_ref(x_1301);
 x_1303 = lean_box(0);
}
if (lean_is_scalar(x_1303)) {
 x_1304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1304 = x_1303;
}
lean_ctor_set(x_1304, 0, x_2);
lean_ctor_set(x_1304, 1, x_1302);
return x_1304;
}
else
{
lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; 
lean_dec(x_2);
x_1305 = lean_ctor_get(x_1301, 0);
lean_inc(x_1305);
x_1306 = lean_ctor_get(x_1301, 1);
lean_inc(x_1306);
if (lean_is_exclusive(x_1301)) {
 lean_ctor_release(x_1301, 0);
 lean_ctor_release(x_1301, 1);
 x_1307 = x_1301;
} else {
 lean_dec_ref(x_1301);
 x_1307 = lean_box(0);
}
if (lean_is_scalar(x_1307)) {
 x_1308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1308 = x_1307;
}
lean_ctor_set(x_1308, 0, x_1305);
lean_ctor_set(x_1308, 1, x_1306);
return x_1308;
}
}
else
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1309 = lean_ctor_get(x_1299, 0);
lean_inc(x_1309);
x_1310 = lean_ctor_get(x_1299, 1);
lean_inc(x_1310);
if (lean_is_exclusive(x_1299)) {
 lean_ctor_release(x_1299, 0);
 lean_ctor_release(x_1299, 1);
 x_1311 = x_1299;
} else {
 lean_dec_ref(x_1299);
 x_1311 = lean_box(0);
}
if (lean_is_scalar(x_1311)) {
 x_1312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1312 = x_1311;
}
lean_ctor_set(x_1312, 0, x_1309);
lean_ctor_set(x_1312, 1, x_1310);
return x_1312;
}
}
}
}
}
}
else
{
lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; 
lean_dec(x_1117);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1406 = lean_ctor_get(x_1120, 0);
lean_inc(x_1406);
x_1407 = lean_ctor_get(x_1120, 1);
lean_inc(x_1407);
if (lean_is_exclusive(x_1120)) {
 lean_ctor_release(x_1120, 0);
 lean_ctor_release(x_1120, 1);
 x_1408 = x_1120;
} else {
 lean_dec_ref(x_1120);
 x_1408 = lean_box(0);
}
if (lean_is_scalar(x_1408)) {
 x_1409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1409 = x_1408;
}
lean_ctor_set(x_1409, 0, x_1406);
lean_ctor_set(x_1409, 1, x_1407);
return x_1409;
}
}
}
}
}
else
{
lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; 
lean_dec(x_90);
lean_dec(x_3);
x_1410 = lean_ctor_get(x_95, 0);
lean_inc(x_1410);
lean_dec(x_95);
x_1411 = l_Lean_Elab_Term_NamedArg_inhabited;
x_1412 = lean_array_get(x_1411, x_11, x_1410);
x_1413 = l_Array_eraseIdx___rarg(x_11, x_1410);
lean_dec(x_1410);
x_1414 = lean_ctor_get(x_1412, 1);
lean_inc(x_1414);
lean_dec(x_1412);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1415 = l___private_Lean_Elab_App_2__elabArg(x_6, x_2, x_1414, x_91, x_4, x_17);
if (lean_obj_tag(x_1415) == 0)
{
lean_object* x_1416; lean_object* x_1417; uint8_t x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; 
x_1416 = lean_ctor_get(x_1415, 0);
lean_inc(x_1416);
x_1417 = lean_ctor_get(x_1415, 1);
lean_inc(x_1417);
lean_dec(x_1415);
x_1418 = 1;
x_1419 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1419, 0, x_6);
lean_ctor_set(x_1419, 1, x_7);
lean_ctor_set(x_1419, 2, x_8);
lean_ctor_set(x_1419, 3, x_10);
lean_ctor_set(x_1419, 4, x_1413);
lean_ctor_set(x_1419, 5, x_12);
lean_ctor_set(x_1419, 6, x_13);
lean_ctor_set_uint8(x_1419, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1419, sizeof(void*)*7 + 1, x_1418);
lean_inc(x_1416);
x_1420 = l_Lean_mkApp(x_2, x_1416);
x_1421 = lean_expr_instantiate1(x_92, x_1416);
lean_dec(x_1416);
lean_dec(x_92);
lean_inc(x_4);
x_1422 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_1417);
if (lean_obj_tag(x_1422) == 0)
{
lean_object* x_1423; 
x_1423 = lean_ctor_get(x_1422, 1);
lean_inc(x_1423);
lean_dec(x_1422);
x_1 = x_1419;
x_2 = x_1420;
x_3 = x_1421;
x_5 = x_1423;
goto _start;
}
else
{
uint8_t x_1425; 
lean_dec(x_1421);
lean_dec(x_1420);
lean_dec(x_1419);
lean_dec(x_4);
x_1425 = !lean_is_exclusive(x_1422);
if (x_1425 == 0)
{
return x_1422;
}
else
{
lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; 
x_1426 = lean_ctor_get(x_1422, 0);
x_1427 = lean_ctor_get(x_1422, 1);
lean_inc(x_1427);
lean_inc(x_1426);
lean_dec(x_1422);
x_1428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1428, 0, x_1426);
lean_ctor_set(x_1428, 1, x_1427);
return x_1428;
}
}
}
else
{
uint8_t x_1429; 
lean_dec(x_1413);
lean_dec(x_92);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1429 = !lean_is_exclusive(x_1415);
if (x_1429 == 0)
{
return x_1415;
}
else
{
lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; 
x_1430 = lean_ctor_get(x_1415, 0);
x_1431 = lean_ctor_get(x_1415, 1);
lean_inc(x_1431);
lean_inc(x_1430);
lean_dec(x_1415);
x_1432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1432, 0, x_1430);
lean_ctor_set(x_1432, 1, x_1431);
return x_1432;
}
}
}
}
else
{
lean_object* x_1433; 
lean_dec(x_13);
x_1433 = lean_box(0);
x_18 = x_1433;
goto block_89;
}
block_89:
{
uint8_t x_19; 
lean_dec(x_18);
x_19 = l_Array_isEmpty___rarg(x_11);
lean_dec(x_11);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_inc(x_4);
x_20 = l___private_Lean_Elab_App_4__tryCoeFun(x_6, x_16, x_2, x_4, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_4);
lean_inc(x_21);
x_23 = l_Lean_Elab_Term_inferType(x_6, x_21, x_4, x_22);
lean_dec(x_6);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_2 = x_21;
x_3 = x_24;
x_5 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_1);
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
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_array_get_size(x_7);
lean_dec(x_7);
x_36 = lean_nat_dec_eq(x_10, x_35);
lean_dec(x_35);
lean_dec(x_10);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_inc(x_4);
x_37 = l___private_Lean_Elab_App_4__tryCoeFun(x_6, x_16, x_2, x_4, x_17);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_4);
lean_inc(x_38);
x_40 = l_Lean_Elab_Term_inferType(x_6, x_38, x_4, x_39);
lean_dec(x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_2 = x_38;
x_3 = x_41;
x_5 = x_42;
goto _start;
}
else
{
uint8_t x_44; 
lean_dec(x_38);
lean_dec(x_4);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_37);
if (x_48 == 0)
{
return x_37;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_37, 0);
x_50 = lean_ctor_get(x_37, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_37);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_16);
lean_dec(x_1);
x_81 = l_Lean_Elab_Term_getOptions(x_4, x_17);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_85 = l_Lean_checkTraceOption(x_82, x_84);
lean_dec(x_82);
if (x_85 == 0)
{
x_52 = x_83;
goto block_80;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_inc(x_2);
x_86 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_86, 0, x_2);
lean_inc(x_4);
x_87 = l_Lean_Elab_Term_logTrace(x_84, x_6, x_86, x_4, x_83);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_52 = x_88;
goto block_80;
}
block_80:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_3);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_53, x_4, x_52);
lean_dec(x_12);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_2);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
return x_54;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_54, 0);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_54);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_8, 0);
lean_inc(x_63);
lean_dec(x_8);
lean_inc(x_4);
x_64 = l_Lean_Elab_Term_isDefEq(x_6, x_63, x_3, x_4, x_52);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_66, x_4, x_65);
lean_dec(x_12);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
lean_ctor_set(x_67, 0, x_2);
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_2);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_67);
if (x_72 == 0)
{
return x_67;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_67, 0);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_67);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_64);
if (x_76 == 0)
{
return x_64;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_64, 0);
x_78 = lean_ctor_get(x_64, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_64);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
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
uint8_t x_1434; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1434 = !lean_is_exclusive(x_15);
if (x_1434 == 0)
{
return x_15;
}
else
{
lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; 
x_1435 = lean_ctor_get(x_15, 0);
x_1436 = lean_ctor_get(x_15, 1);
lean_inc(x_1436);
lean_inc(x_1435);
lean_dec(x_15);
x_1437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1437, 0, x_1435);
lean_ctor_set(x_1437, 1, x_1436);
return x_1437;
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("args");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1;
x_2 = l___private_Lean_Elab_App_11__elabAppArgs___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__5;
x_2 = l___private_Lean_Elab_App_11__elabAppArgs___closed__6;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__7;
x_2 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__16;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__5;
x_2 = l___private_Lean_Elab_App_11__elabAppArgs___closed__9;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__10;
x_2 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_11__elabAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_2);
x_9 = l_Lean_Elab_Term_inferType(x_1, x_2, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
x_12 = l_Lean_Elab_Term_instantiateMVars(x_1, x_10, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Array_isEmpty___rarg(x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_empty___closed__1;
x_18 = 0;
lean_inc(x_4);
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_4);
lean_ctor_set(x_19, 2, x_5);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_3);
lean_ctor_set(x_19, 5, x_17);
lean_ctor_set(x_19, 6, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*7, x_6);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 1, x_18);
x_20 = l_Lean_Elab_Term_getOptions(x_7, x_14);
if (x_15 == 0)
{
lean_dec(x_4);
x_21 = x_18;
goto block_75;
}
else
{
uint8_t x_76; 
x_76 = l_Array_isEmpty___rarg(x_4);
lean_dec(x_4);
x_21 = x_76;
goto block_75;
}
block_75:
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
if (x_21 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_20, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_20, 1);
lean_inc(x_71);
lean_dec(x_20);
x_22 = x_18;
x_23 = x_70;
x_24 = x_71;
goto block_69;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_20, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_20, 1);
lean_inc(x_73);
lean_dec(x_20);
x_74 = 1;
x_22 = x_74;
x_23 = x_72;
x_24 = x_73;
goto block_69;
}
block_69:
{
lean_object* x_25; uint8_t x_26; 
x_25 = l___private_Lean_Elab_App_11__elabAppArgs___closed__2;
x_26 = l_Lean_checkTraceOption(x_23, x_25);
lean_dec(x_23);
if (x_26 == 0)
{
lean_dec(x_1);
if (x_22 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_Elab_Term_tryPostponeIfMVar(x_13, x_7, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_19, x_2, x_13, x_7, x_28);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
x_34 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_19, x_2, x_13, x_7, x_24);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_inc(x_2);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_2);
lean_inc(x_13);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_13);
if (x_6 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = l___private_Lean_Elab_App_11__elabAppArgs___closed__8;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
x_39 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
lean_inc(x_7);
x_42 = l_Lean_Elab_Term_logTrace(x_25, x_1, x_41, x_7, x_24);
lean_dec(x_1);
if (x_22 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Elab_Term_tryPostponeIfMVar(x_13, x_7, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_19, x_2, x_13, x_7, x_45);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
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
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec(x_42);
x_52 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_19, x_2, x_13, x_7, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = l___private_Lean_Elab_App_11__elabAppArgs___closed__11;
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_35);
x_55 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_36);
lean_inc(x_7);
x_58 = l_Lean_Elab_Term_logTrace(x_25, x_1, x_57, x_7, x_24);
lean_dec(x_1);
if (x_22 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Elab_Term_tryPostponeIfMVar(x_13, x_7, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_19, x_2, x_13, x_7, x_61);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
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
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
lean_dec(x_58);
x_68 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_19, x_2, x_13, x_7, x_67);
return x_68;
}
}
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_9);
if (x_77 == 0)
{
return x_9;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_9, 0);
x_79 = lean_ctor_get(x_9, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_9);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l___private_Lean_Elab_App_11__elabAppArgs(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_12__throwLValError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = l_Lean_indentExpr(x_7);
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_MessageData_ofList___closed__3;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_KernelException_toMessageData___closed__12;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = l_Lean_indentExpr(x_14);
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_Term_throwError___rarg(x_1, x_16, x_5, x_6);
return x_17;
}
}
lean_object* l___private_Lean_Elab_App_12__throwLValError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_12__throwLValError___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_12__throwLValError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure has only ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" field(s)");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, index must be greater than 0");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a valid \"field\" because environment does not contain '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__22;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__23;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("getOp");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation because environment does not contain '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__26;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_13__resolveLValAux___closed__27;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_13__resolveLValAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_13; 
x_13 = l_Lean_Expr_getAppFn___main(x_3);
if (lean_obj_tag(x_13) == 4)
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_84; 
x_84 = 0;
x_18 = x_84;
goto block_83;
}
else
{
uint8_t x_85; 
x_85 = 1;
x_18 = x_85;
goto block_83;
}
block_83:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_6;
goto block_76;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_77 = l___private_Lean_Elab_App_13__resolveLValAux___closed__18;
x_78 = l_Lean_Elab_Term_throwError___rarg(x_1, x_77, x_5, x_6);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
return x_78;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
block_76:
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Elab_Term_getEnv___rarg(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_14);
lean_inc(x_22);
x_24 = l_Lean_isStructureLike(x_22, x_14);
lean_inc(x_14);
lean_inc(x_22);
x_25 = l_Lean_getStructureFields(x_22, x_14);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_15, x_26);
lean_dec(x_15);
x_28 = lean_array_get_size(x_25);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_24 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_free_object(x_20);
lean_dec(x_22);
lean_dec(x_14);
x_30 = l___private_Lean_Elab_App_13__resolveLValAux___closed__9;
x_31 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_30, x_5, x_23);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
if (x_29 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_27);
lean_dec(x_25);
lean_free_object(x_20);
lean_dec(x_22);
lean_dec(x_14);
x_36 = l_Nat_repr(x_28);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l___private_Lean_Elab_App_13__resolveLValAux___closed__12;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l___private_Lean_Elab_App_13__resolveLValAux___closed__15;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_42, x_5, x_23);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_14);
x_44 = l_Lean_isStructure(x_22, x_14);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_25);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_14);
lean_ctor_set(x_45, 1, x_27);
lean_ctor_set(x_20, 0, x_45);
return x_20;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_array_fget(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
lean_inc(x_14);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_14);
lean_ctor_set(x_47, 1, x_14);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_20, 0, x_47);
return x_20;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_20, 0);
x_49 = lean_ctor_get(x_20, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_20);
lean_inc(x_14);
lean_inc(x_48);
x_50 = l_Lean_isStructureLike(x_48, x_14);
lean_inc(x_14);
lean_inc(x_48);
x_51 = l_Lean_getStructureFields(x_48, x_14);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_15, x_52);
lean_dec(x_15);
x_54 = lean_array_get_size(x_51);
x_55 = lean_nat_dec_lt(x_53, x_54);
if (x_50 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_14);
x_56 = l___private_Lean_Elab_App_13__resolveLValAux___closed__9;
x_57 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_56, x_5, x_49);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
if (x_55 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_14);
x_62 = l_Nat_repr(x_54);
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l___private_Lean_Elab_App_13__resolveLValAux___closed__12;
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l___private_Lean_Elab_App_13__resolveLValAux___closed__15;
x_68 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_68, x_5, x_49);
return x_69;
}
else
{
uint8_t x_70; 
lean_dec(x_54);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_14);
x_70 = l_Lean_isStructure(x_48, x_14);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_51);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_14);
lean_ctor_set(x_71, 1, x_53);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_49);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_array_fget(x_51, x_53);
lean_dec(x_53);
lean_dec(x_51);
lean_inc(x_14);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_14);
lean_ctor_set(x_74, 1, x_14);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_49);
return x_75;
}
}
}
}
}
}
}
case 1:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_13, 0);
lean_inc(x_86);
lean_dec(x_13);
x_87 = lean_ctor_get(x_4, 0);
lean_inc(x_87);
lean_dec(x_4);
x_88 = l_Lean_Elab_Term_getEnv___rarg(x_6);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_86);
lean_inc(x_90);
x_92 = l_Lean_isStructure(x_90, x_86);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_free_object(x_88);
x_93 = lean_box(0);
lean_inc(x_87);
x_94 = lean_name_mk_string(x_93, x_87);
x_95 = l_Lean_Name_append___main(x_86, x_94);
x_96 = l_Lean_Elab_Term_getCurrNamespace(x_5, x_91);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_95);
x_99 = l_Lean_Name_replacePrefix___main(x_95, x_97, x_93);
lean_dec(x_97);
x_100 = l_Lean_Elab_Term_getLCtx(x_5, x_98);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
x_104 = lean_local_ctx_find_from_user_name(x_102, x_99);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
lean_inc(x_95);
lean_inc(x_90);
x_105 = lean_environment_find(x_90, x_95);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_inc(x_95);
lean_inc(x_90);
x_106 = l_Lean_mkPrivateName(x_90, x_95);
lean_inc(x_106);
x_107 = lean_environment_find(x_90, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_106);
lean_free_object(x_100);
lean_dec(x_86);
x_108 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_108, 0, x_87);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_111 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_113 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_114, 0, x_95);
x_115 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_Elab_Term_mkConst___closed__4;
x_117 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_117, x_5, x_103);
return x_118;
}
else
{
lean_object* x_119; 
lean_dec(x_107);
lean_dec(x_95);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_86);
lean_ctor_set(x_119, 1, x_106);
lean_ctor_set(x_100, 0, x_119);
return x_100;
}
}
else
{
lean_object* x_120; 
lean_dec(x_105);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_86);
lean_ctor_set(x_120, 1, x_95);
lean_ctor_set(x_100, 0, x_120);
return x_100;
}
}
else
{
lean_object* x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; 
x_121 = lean_ctor_get(x_104, 0);
lean_inc(x_121);
lean_dec(x_104);
x_122 = l_Lean_LocalDecl_binderInfo(x_121);
x_123 = 4;
x_124 = l_Lean_BinderInfo_beq(x_122, x_123);
if (x_124 == 0)
{
lean_object* x_125; 
lean_dec(x_121);
lean_inc(x_95);
lean_inc(x_90);
x_125 = lean_environment_find(x_90, x_95);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_inc(x_95);
lean_inc(x_90);
x_126 = l_Lean_mkPrivateName(x_90, x_95);
lean_inc(x_126);
x_127 = lean_environment_find(x_90, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_126);
lean_free_object(x_100);
lean_dec(x_86);
x_128 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_128, 0, x_87);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_131 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_133 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_134, 0, x_95);
x_135 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_Elab_Term_mkConst___closed__4;
x_137 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_137, x_5, x_103);
return x_138;
}
else
{
lean_object* x_139; 
lean_dec(x_127);
lean_dec(x_95);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_139 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_139, 0, x_86);
lean_ctor_set(x_139, 1, x_126);
lean_ctor_set(x_100, 0, x_139);
return x_100;
}
}
else
{
lean_object* x_140; 
lean_dec(x_125);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_86);
lean_ctor_set(x_140, 1, x_95);
lean_ctor_set(x_100, 0, x_140);
return x_100;
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_141 = l_Lean_LocalDecl_toExpr(x_121);
lean_dec(x_121);
x_142 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_142, 0, x_86);
lean_ctor_set(x_142, 1, x_95);
lean_ctor_set(x_142, 2, x_141);
lean_ctor_set(x_100, 0, x_142);
return x_100;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_100, 0);
x_144 = lean_ctor_get(x_100, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_100);
x_145 = lean_local_ctx_find_from_user_name(x_143, x_99);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; 
lean_inc(x_95);
lean_inc(x_90);
x_146 = lean_environment_find(x_90, x_95);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_inc(x_95);
lean_inc(x_90);
x_147 = l_Lean_mkPrivateName(x_90, x_95);
lean_inc(x_147);
x_148 = lean_environment_find(x_90, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_147);
lean_dec(x_86);
x_149 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_149, 0, x_87);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_152 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_154 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_155, 0, x_95);
x_156 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Lean_Elab_Term_mkConst___closed__4;
x_158 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_158, x_5, x_144);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_148);
lean_dec(x_95);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_160 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_160, 0, x_86);
lean_ctor_set(x_160, 1, x_147);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_144);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_146);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_86);
lean_ctor_set(x_162, 1, x_95);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_144);
return x_163;
}
}
else
{
lean_object* x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; 
x_164 = lean_ctor_get(x_145, 0);
lean_inc(x_164);
lean_dec(x_145);
x_165 = l_Lean_LocalDecl_binderInfo(x_164);
x_166 = 4;
x_167 = l_Lean_BinderInfo_beq(x_165, x_166);
if (x_167 == 0)
{
lean_object* x_168; 
lean_dec(x_164);
lean_inc(x_95);
lean_inc(x_90);
x_168 = lean_environment_find(x_90, x_95);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; 
lean_inc(x_95);
lean_inc(x_90);
x_169 = l_Lean_mkPrivateName(x_90, x_95);
lean_inc(x_169);
x_170 = lean_environment_find(x_90, x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_169);
lean_dec(x_86);
x_171 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_171, 0, x_87);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_174 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
x_175 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_176 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_177, 0, x_95);
x_178 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = l_Lean_Elab_Term_mkConst___closed__4;
x_180 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_180, x_5, x_144);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_170);
lean_dec(x_95);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_182 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_182, 0, x_86);
lean_ctor_set(x_182, 1, x_169);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_144);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_168);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_184 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_184, 0, x_86);
lean_ctor_set(x_184, 1, x_95);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_144);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_186 = l_Lean_LocalDecl_toExpr(x_164);
lean_dec(x_164);
x_187 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_187, 0, x_86);
lean_ctor_set(x_187, 1, x_95);
lean_ctor_set(x_187, 2, x_186);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_144);
return x_188;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_box(0);
lean_inc(x_87);
x_190 = lean_name_mk_string(x_189, x_87);
lean_inc(x_86);
lean_inc(x_90);
x_191 = l_Lean_findField_x3f___main(x_90, x_86, x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
lean_free_object(x_88);
x_192 = l_Lean_Name_append___main(x_86, x_190);
x_193 = l_Lean_Elab_Term_getCurrNamespace(x_5, x_91);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
lean_inc(x_192);
x_196 = l_Lean_Name_replacePrefix___main(x_192, x_194, x_189);
lean_dec(x_194);
x_197 = l_Lean_Elab_Term_getLCtx(x_5, x_195);
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_197, 0);
x_200 = lean_ctor_get(x_197, 1);
x_201 = lean_local_ctx_find_from_user_name(x_199, x_196);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; 
lean_inc(x_192);
lean_inc(x_90);
x_202 = lean_environment_find(x_90, x_192);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_inc(x_192);
lean_inc(x_90);
x_203 = l_Lean_mkPrivateName(x_90, x_192);
lean_inc(x_203);
x_204 = lean_environment_find(x_90, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_203);
lean_free_object(x_197);
lean_dec(x_86);
x_205 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_205, 0, x_87);
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_207 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_208 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
x_209 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_210 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_211, 0, x_192);
x_212 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_Elab_Term_mkConst___closed__4;
x_214 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_214, x_5, x_200);
return x_215;
}
else
{
lean_object* x_216; 
lean_dec(x_204);
lean_dec(x_192);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_216 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_216, 0, x_86);
lean_ctor_set(x_216, 1, x_203);
lean_ctor_set(x_197, 0, x_216);
return x_197;
}
}
else
{
lean_object* x_217; 
lean_dec(x_202);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_217 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_217, 0, x_86);
lean_ctor_set(x_217, 1, x_192);
lean_ctor_set(x_197, 0, x_217);
return x_197;
}
}
else
{
lean_object* x_218; uint8_t x_219; uint8_t x_220; uint8_t x_221; 
x_218 = lean_ctor_get(x_201, 0);
lean_inc(x_218);
lean_dec(x_201);
x_219 = l_Lean_LocalDecl_binderInfo(x_218);
x_220 = 4;
x_221 = l_Lean_BinderInfo_beq(x_219, x_220);
if (x_221 == 0)
{
lean_object* x_222; 
lean_dec(x_218);
lean_inc(x_192);
lean_inc(x_90);
x_222 = lean_environment_find(x_90, x_192);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; 
lean_inc(x_192);
lean_inc(x_90);
x_223 = l_Lean_mkPrivateName(x_90, x_192);
lean_inc(x_223);
x_224 = lean_environment_find(x_90, x_223);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_223);
lean_free_object(x_197);
lean_dec(x_86);
x_225 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_225, 0, x_87);
x_226 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_228 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
x_229 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_230 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_231, 0, x_192);
x_232 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_Elab_Term_mkConst___closed__4;
x_234 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_234, x_5, x_200);
return x_235;
}
else
{
lean_object* x_236; 
lean_dec(x_224);
lean_dec(x_192);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_236 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_236, 0, x_86);
lean_ctor_set(x_236, 1, x_223);
lean_ctor_set(x_197, 0, x_236);
return x_197;
}
}
else
{
lean_object* x_237; 
lean_dec(x_222);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_237 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_237, 0, x_86);
lean_ctor_set(x_237, 1, x_192);
lean_ctor_set(x_197, 0, x_237);
return x_197;
}
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_238 = l_Lean_LocalDecl_toExpr(x_218);
lean_dec(x_218);
x_239 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_239, 0, x_86);
lean_ctor_set(x_239, 1, x_192);
lean_ctor_set(x_239, 2, x_238);
lean_ctor_set(x_197, 0, x_239);
return x_197;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_197, 0);
x_241 = lean_ctor_get(x_197, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_197);
x_242 = lean_local_ctx_find_from_user_name(x_240, x_196);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; 
lean_inc(x_192);
lean_inc(x_90);
x_243 = lean_environment_find(x_90, x_192);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; 
lean_inc(x_192);
lean_inc(x_90);
x_244 = l_Lean_mkPrivateName(x_90, x_192);
lean_inc(x_244);
x_245 = lean_environment_find(x_90, x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_244);
lean_dec(x_86);
x_246 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_246, 0, x_87);
x_247 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_247, 0, x_246);
x_248 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_249 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_251 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_252, 0, x_192);
x_253 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_254 = l_Lean_Elab_Term_mkConst___closed__4;
x_255 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
x_256 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_255, x_5, x_241);
return x_256;
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_245);
lean_dec(x_192);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_257 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_257, 0, x_86);
lean_ctor_set(x_257, 1, x_244);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_241);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_243);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_259 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_259, 0, x_86);
lean_ctor_set(x_259, 1, x_192);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_241);
return x_260;
}
}
else
{
lean_object* x_261; uint8_t x_262; uint8_t x_263; uint8_t x_264; 
x_261 = lean_ctor_get(x_242, 0);
lean_inc(x_261);
lean_dec(x_242);
x_262 = l_Lean_LocalDecl_binderInfo(x_261);
x_263 = 4;
x_264 = l_Lean_BinderInfo_beq(x_262, x_263);
if (x_264 == 0)
{
lean_object* x_265; 
lean_dec(x_261);
lean_inc(x_192);
lean_inc(x_90);
x_265 = lean_environment_find(x_90, x_192);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; 
lean_inc(x_192);
lean_inc(x_90);
x_266 = l_Lean_mkPrivateName(x_90, x_192);
lean_inc(x_266);
x_267 = lean_environment_find(x_90, x_266);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_266);
lean_dec(x_86);
x_268 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_268, 0, x_87);
x_269 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_269, 0, x_268);
x_270 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_271 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_269);
x_272 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_273 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_274 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_274, 0, x_192);
x_275 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
x_276 = l_Lean_Elab_Term_mkConst___closed__4;
x_277 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
x_278 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_277, x_5, x_241);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_267);
lean_dec(x_192);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_279 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_279, 0, x_86);
lean_ctor_set(x_279, 1, x_266);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_241);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_265);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_281 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_281, 0, x_86);
lean_ctor_set(x_281, 1, x_192);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_241);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_283 = l_Lean_LocalDecl_toExpr(x_261);
lean_dec(x_261);
x_284 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_284, 0, x_86);
lean_ctor_set(x_284, 1, x_192);
lean_ctor_set(x_284, 2, x_283);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_241);
return x_285;
}
}
}
}
else
{
lean_object* x_286; lean_object* x_287; 
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_286 = lean_ctor_get(x_191, 0);
lean_inc(x_286);
lean_dec(x_191);
x_287 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_86);
lean_ctor_set(x_287, 2, x_190);
lean_ctor_set(x_88, 0, x_287);
return x_88;
}
}
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_288 = lean_ctor_get(x_88, 0);
x_289 = lean_ctor_get(x_88, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_88);
lean_inc(x_86);
lean_inc(x_288);
x_290 = l_Lean_isStructure(x_288, x_86);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_291 = lean_box(0);
lean_inc(x_87);
x_292 = lean_name_mk_string(x_291, x_87);
x_293 = l_Lean_Name_append___main(x_86, x_292);
x_294 = l_Lean_Elab_Term_getCurrNamespace(x_5, x_289);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
lean_inc(x_293);
x_297 = l_Lean_Name_replacePrefix___main(x_293, x_295, x_291);
lean_dec(x_295);
x_298 = l_Lean_Elab_Term_getLCtx(x_5, x_296);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_301 = x_298;
} else {
 lean_dec_ref(x_298);
 x_301 = lean_box(0);
}
x_302 = lean_local_ctx_find_from_user_name(x_299, x_297);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; 
lean_inc(x_293);
lean_inc(x_288);
x_303 = lean_environment_find(x_288, x_293);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; 
lean_inc(x_293);
lean_inc(x_288);
x_304 = l_Lean_mkPrivateName(x_288, x_293);
lean_inc(x_304);
x_305 = lean_environment_find(x_288, x_304);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_304);
lean_dec(x_301);
lean_dec(x_86);
x_306 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_306, 0, x_87);
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_306);
x_308 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_309 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_307);
x_310 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_311 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_312, 0, x_293);
x_313 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
x_314 = l_Lean_Elab_Term_mkConst___closed__4;
x_315 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
x_316 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_315, x_5, x_300);
return x_316;
}
else
{
lean_object* x_317; lean_object* x_318; 
lean_dec(x_305);
lean_dec(x_293);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_317 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_317, 0, x_86);
lean_ctor_set(x_317, 1, x_304);
if (lean_is_scalar(x_301)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_301;
}
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_300);
return x_318;
}
}
else
{
lean_object* x_319; lean_object* x_320; 
lean_dec(x_303);
lean_dec(x_288);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_319 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_319, 0, x_86);
lean_ctor_set(x_319, 1, x_293);
if (lean_is_scalar(x_301)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_301;
}
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_300);
return x_320;
}
}
else
{
lean_object* x_321; uint8_t x_322; uint8_t x_323; uint8_t x_324; 
x_321 = lean_ctor_get(x_302, 0);
lean_inc(x_321);
lean_dec(x_302);
x_322 = l_Lean_LocalDecl_binderInfo(x_321);
x_323 = 4;
x_324 = l_Lean_BinderInfo_beq(x_322, x_323);
if (x_324 == 0)
{
lean_object* x_325; 
lean_dec(x_321);
lean_inc(x_293);
lean_inc(x_288);
x_325 = lean_environment_find(x_288, x_293);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; 
lean_inc(x_293);
lean_inc(x_288);
x_326 = l_Lean_mkPrivateName(x_288, x_293);
lean_inc(x_326);
x_327 = lean_environment_find(x_288, x_326);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_326);
lean_dec(x_301);
lean_dec(x_86);
x_328 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_328, 0, x_87);
x_329 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_329, 0, x_328);
x_330 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_331 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_329);
x_332 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_333 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_334, 0, x_293);
x_335 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
x_336 = l_Lean_Elab_Term_mkConst___closed__4;
x_337 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
x_338 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_337, x_5, x_300);
return x_338;
}
else
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_327);
lean_dec(x_293);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_339 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_339, 0, x_86);
lean_ctor_set(x_339, 1, x_326);
if (lean_is_scalar(x_301)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_301;
}
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_300);
return x_340;
}
}
else
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_325);
lean_dec(x_288);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_341 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_341, 0, x_86);
lean_ctor_set(x_341, 1, x_293);
if (lean_is_scalar(x_301)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_301;
}
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_300);
return x_342;
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_288);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_343 = l_Lean_LocalDecl_toExpr(x_321);
lean_dec(x_321);
x_344 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_344, 0, x_86);
lean_ctor_set(x_344, 1, x_293);
lean_ctor_set(x_344, 2, x_343);
if (lean_is_scalar(x_301)) {
 x_345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_345 = x_301;
}
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_300);
return x_345;
}
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_box(0);
lean_inc(x_87);
x_347 = lean_name_mk_string(x_346, x_87);
lean_inc(x_86);
lean_inc(x_288);
x_348 = l_Lean_findField_x3f___main(x_288, x_86, x_347);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_349 = l_Lean_Name_append___main(x_86, x_347);
x_350 = l_Lean_Elab_Term_getCurrNamespace(x_5, x_289);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
lean_inc(x_349);
x_353 = l_Lean_Name_replacePrefix___main(x_349, x_351, x_346);
lean_dec(x_351);
x_354 = l_Lean_Elab_Term_getLCtx(x_5, x_352);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_357 = x_354;
} else {
 lean_dec_ref(x_354);
 x_357 = lean_box(0);
}
x_358 = lean_local_ctx_find_from_user_name(x_355, x_353);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; 
lean_inc(x_349);
lean_inc(x_288);
x_359 = lean_environment_find(x_288, x_349);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; 
lean_inc(x_349);
lean_inc(x_288);
x_360 = l_Lean_mkPrivateName(x_288, x_349);
lean_inc(x_360);
x_361 = lean_environment_find(x_288, x_360);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_360);
lean_dec(x_357);
lean_dec(x_86);
x_362 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_362, 0, x_87);
x_363 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_363, 0, x_362);
x_364 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_365 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_363);
x_366 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_367 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
x_368 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_368, 0, x_349);
x_369 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
x_370 = l_Lean_Elab_Term_mkConst___closed__4;
x_371 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
x_372 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_371, x_5, x_356);
return x_372;
}
else
{
lean_object* x_373; lean_object* x_374; 
lean_dec(x_361);
lean_dec(x_349);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_373 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_373, 0, x_86);
lean_ctor_set(x_373, 1, x_360);
if (lean_is_scalar(x_357)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_357;
}
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_356);
return x_374;
}
}
else
{
lean_object* x_375; lean_object* x_376; 
lean_dec(x_359);
lean_dec(x_288);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_375 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_375, 0, x_86);
lean_ctor_set(x_375, 1, x_349);
if (lean_is_scalar(x_357)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_357;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_356);
return x_376;
}
}
else
{
lean_object* x_377; uint8_t x_378; uint8_t x_379; uint8_t x_380; 
x_377 = lean_ctor_get(x_358, 0);
lean_inc(x_377);
lean_dec(x_358);
x_378 = l_Lean_LocalDecl_binderInfo(x_377);
x_379 = 4;
x_380 = l_Lean_BinderInfo_beq(x_378, x_379);
if (x_380 == 0)
{
lean_object* x_381; 
lean_dec(x_377);
lean_inc(x_349);
lean_inc(x_288);
x_381 = lean_environment_find(x_288, x_349);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; 
lean_inc(x_349);
lean_inc(x_288);
x_382 = l_Lean_mkPrivateName(x_288, x_349);
lean_inc(x_382);
x_383 = lean_environment_find(x_288, x_382);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_382);
lean_dec(x_357);
lean_dec(x_86);
x_384 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_384, 0, x_87);
x_385 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_385, 0, x_384);
x_386 = l___private_Lean_Elab_App_13__resolveLValAux___closed__21;
x_387 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_385);
x_388 = l___private_Lean_Elab_App_13__resolveLValAux___closed__24;
x_389 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_390, 0, x_349);
x_391 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
x_392 = l_Lean_Elab_Term_mkConst___closed__4;
x_393 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
x_394 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_393, x_5, x_356);
return x_394;
}
else
{
lean_object* x_395; lean_object* x_396; 
lean_dec(x_383);
lean_dec(x_349);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_395 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_395, 0, x_86);
lean_ctor_set(x_395, 1, x_382);
if (lean_is_scalar(x_357)) {
 x_396 = lean_alloc_ctor(0, 2, 0);
} else {
 x_396 = x_357;
}
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_356);
return x_396;
}
}
else
{
lean_object* x_397; lean_object* x_398; 
lean_dec(x_381);
lean_dec(x_288);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_397 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_397, 0, x_86);
lean_ctor_set(x_397, 1, x_349);
if (lean_is_scalar(x_357)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_357;
}
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_356);
return x_398;
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_288);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_399 = l_Lean_LocalDecl_toExpr(x_377);
lean_dec(x_377);
x_400 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_400, 0, x_86);
lean_ctor_set(x_400, 1, x_349);
lean_ctor_set(x_400, 2, x_399);
if (lean_is_scalar(x_357)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_357;
}
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_356);
return x_401;
}
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_288);
lean_dec(x_87);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_402 = lean_ctor_get(x_348, 0);
lean_inc(x_402);
lean_dec(x_348);
x_403 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_86);
lean_ctor_set(x_403, 2, x_347);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_289);
return x_404;
}
}
}
}
default: 
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; 
x_405 = lean_ctor_get(x_13, 0);
lean_inc(x_405);
lean_dec(x_13);
x_406 = lean_ctor_get(x_4, 0);
lean_inc(x_406);
lean_dec(x_4);
x_407 = l_Lean_Elab_Term_getEnv___rarg(x_6);
x_408 = !lean_is_exclusive(x_407);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_409 = lean_ctor_get(x_407, 0);
x_410 = lean_ctor_get(x_407, 1);
x_411 = l___private_Lean_Elab_App_13__resolveLValAux___closed__25;
x_412 = lean_name_mk_string(x_405, x_411);
lean_inc(x_412);
x_413 = lean_environment_find(x_409, x_412);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_free_object(x_407);
lean_dec(x_406);
x_414 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_414, 0, x_412);
x_415 = l___private_Lean_Elab_App_13__resolveLValAux___closed__28;
x_416 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_414);
x_417 = l_Lean_Elab_Term_mkConst___closed__4;
x_418 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
x_419 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_418, x_5, x_410);
return x_419;
}
else
{
lean_object* x_420; 
lean_dec(x_413);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_420 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_420, 0, x_412);
lean_ctor_set(x_420, 1, x_406);
lean_ctor_set(x_407, 0, x_420);
return x_407;
}
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_421 = lean_ctor_get(x_407, 0);
x_422 = lean_ctor_get(x_407, 1);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_407);
x_423 = l___private_Lean_Elab_App_13__resolveLValAux___closed__25;
x_424 = lean_name_mk_string(x_405, x_423);
lean_inc(x_424);
x_425 = lean_environment_find(x_421, x_424);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_406);
x_426 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_426, 0, x_424);
x_427 = l___private_Lean_Elab_App_13__resolveLValAux___closed__28;
x_428 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_426);
x_429 = l_Lean_Elab_Term_mkConst___closed__4;
x_430 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_429);
x_431 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_430, x_5, x_422);
return x_431;
}
else
{
lean_object* x_432; lean_object* x_433; 
lean_dec(x_425);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_432 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_432, 0, x_424);
lean_ctor_set(x_432, 1, x_406);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_422);
return x_433;
}
}
}
}
}
else
{
lean_object* x_434; 
lean_dec(x_13);
x_434 = lean_box(0);
x_7 = x_434;
goto block_12;
}
block_12:
{
lean_dec(x_7);
if (lean_obj_tag(x_4) == 2)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = l___private_Lean_Elab_App_13__resolveLValAux___closed__6;
x_9 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_8, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = l___private_Lean_Elab_App_13__resolveLValAux___closed__3;
x_11 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_10, x_5, x_6);
return x_11;
}
}
}
}
lean_object* l___private_Lean_Elab_App_13__resolveLValAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_App_13__resolveLValAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_14__resolveLValLoop___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_1);
x_14 = l_PersistentArray_push___rarg(x_13, x_1);
lean_ctor_set(x_5, 2, x_14);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_5, 2);
x_19 = lean_ctor_get(x_5, 3);
x_20 = lean_ctor_get(x_5, 4);
x_21 = lean_ctor_get(x_5, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_1);
x_22 = l_PersistentArray_push___rarg(x_18, x_1);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_21);
x_3 = x_11;
x_5 = x_23;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_App_14__resolveLValLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
x_8 = l_Lean_Elab_Term_whnfCore(x_1, x_4, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Term_tryPostponeIfMVar(x_9, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_2);
x_13 = l___private_Lean_Elab_App_13__resolveLValAux(x_1, x_2, x_9, x_3, x_6, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_6);
x_18 = l_Lean_Elab_Term_unfoldDefinition_x3f(x_1, x_9, x_6, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Array_forMAux___main___at___private_Lean_Elab_App_14__resolveLValLoop___main___spec__1(x_17, x_5, x_21, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_14);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_14);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_array_push(x_5, x_17);
x_4 = x_28;
x_5 = x_29;
x_7 = x_27;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_13, 0);
lean_dec(x_36);
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_14);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
return x_11;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_8);
if (x_43 == 0)
{
return x_8;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_8, 0);
x_45 = lean_ctor_get(x_8, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_8);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_14__resolveLValLoop___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at___private_Lean_Elab_App_14__resolveLValLoop___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Lean_Elab_App_14__resolveLValLoop___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_App_14__resolveLValLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_App_14__resolveLValLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_App_14__resolveLValLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Elab_App_14__resolveLValLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_App_14__resolveLValLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_App_15__resolveLVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_2);
x_6 = l_Lean_Elab_Term_inferType(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Array_empty___closed__1;
x_10 = l___private_Lean_Elab_App_14__resolveLValLoop___main(x_1, x_2, x_3, x_7, x_9, x_4, x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l___private_Lean_Elab_App_15__resolveLVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_App_15__resolveLVal(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("self");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
lean_inc(x_4);
x_10 = l_Lean_Elab_Term_mkConst(x_1, x_7, x_9, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_mkOptionalNode___closed__2;
x_17 = lean_array_push(x_16, x_15);
x_18 = lean_box(0);
x_19 = l_Array_empty___closed__1;
x_20 = 0;
lean_inc(x_4);
lean_inc(x_1);
x_21 = l___private_Lean_Elab_App_11__elabAppArgs(x_1, x_11, x_17, x_19, x_18, x_20, x_4, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_2 = x_22;
x_3 = x_8;
x_5 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* _init_l___private_Lean_Elab_App_16__mkBaseProjections___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to access field in parent structure");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_16__mkBaseProjections___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_16__mkBaseProjections___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_16__mkBaseProjections___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_16__mkBaseProjections___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_16__mkBaseProjections(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Elab_Term_getEnv___rarg(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_getPathToBaseStructure_x3f(x_8, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = l___private_Lean_Elab_App_16__mkBaseProjections___closed__3;
x_12 = l_Lean_Elab_Term_throwError___rarg(x_1, x_11, x_5, x_9);
lean_dec(x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1(x_1, x_4, x_13, x_5, x_9);
return x_14;
}
}
}
lean_object* l___private_Lean_Elab_App_16__mkBaseProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_App_16__mkBaseProjections(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_17__addLValArg___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, function '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_17__addLValArg___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_17__addLValArg___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not have explicit argument with type (");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_17__addLValArg___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_17__addLValArg___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ...)");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_17__addLValArg___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_17__addLValArg___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, insufficient number of arguments for '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_17__addLValArg___main___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_17__addLValArg___main___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_17__addLValArg___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
if (lean_obj_tag(x_8) == 7)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint8_t x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
x_25 = lean_ctor_get(x_8, 2);
x_26 = lean_ctor_get_uint64(x_8, sizeof(void*)*3);
x_27 = (uint8_t)((x_26 << 24) >> 61);
x_28 = l_Lean_BinderInfo_isExplicit(x_27);
if (x_28 == 0)
{
x_8 = x_25;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_17__addLValArg___main___spec__1(x_23, x_7, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Expr_consumeMData___main(x_24);
x_33 = l_Lean_Expr_isAppOf(x_32, x_2);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_array_get_size(x_5);
x_35 = lean_nat_dec_lt(x_6, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_36 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_36, 0, x_3);
x_37 = l___private_Lean_Elab_App_17__addLValArg___main___closed__12;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Elab_Term_mkConst___closed__4;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Elab_Term_throwError___rarg(x_1, x_40, x_9, x_10);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_6, x_42);
lean_dec(x_6);
x_6 = x_43;
x_8 = x_25;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_4);
x_46 = l_Array_insertAt___rarg(x_5, x_6, x_45);
lean_dec(x_6);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_10);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
lean_dec(x_31);
x_49 = l_Array_eraseIdx___rarg(x_7, x_48);
lean_dec(x_48);
x_7 = x_49;
x_8 = x_25;
goto _start;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_51 = lean_box(0);
x_11 = x_51;
goto block_22;
}
block_22:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_3);
x_13 = l___private_Lean_Elab_App_17__addLValArg___main___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l___private_Lean_Elab_App_17__addLValArg___main___closed__6;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Lean_Elab_App_17__addLValArg___main___closed__9;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Term_throwError___rarg(x_1, x_20, x_9, x_10);
return x_21;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_17__addLValArg___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_17__addLValArg___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_17__addLValArg___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_17__addLValArg___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_17__addLValArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_17__addLValArg___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_17__addLValArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_17__addLValArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("idx");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_11__elabAppArgs(x_1, x_6, x_2, x_3, x_4, x_5, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
lean_inc(x_8);
lean_inc(x_6);
x_13 = l___private_Lean_Elab_App_15__resolveLVal(x_1, x_6, x_11, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 2);
lean_inc(x_18);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_1);
x_19 = l___private_Lean_Elab_App_16__mkBaseProjections(x_1, x_16, x_17, x_6, x_8, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Name_append___main(x_16, x_18);
lean_dec(x_16);
x_23 = lean_box(0);
lean_inc(x_8);
x_24 = l_Lean_Elab_Term_mkConst(x_1, x_22, x_23, x_8, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_List_isEmpty___rarg(x_12);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_20);
x_29 = l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_mkOptionalNode___closed__2;
x_32 = lean_array_push(x_31, x_30);
x_33 = lean_box(0);
x_34 = l_Array_empty___closed__1;
x_35 = 0;
lean_inc(x_8);
lean_inc(x_1);
x_36 = l___private_Lean_Elab_App_11__elabAppArgs(x_1, x_25, x_32, x_34, x_33, x_35, x_8, x_26);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_6 = x_37;
x_7 = x_12;
x_9 = x_38;
goto _start;
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_12);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_20);
x_45 = l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
lean_inc(x_8);
x_47 = l_Lean_Elab_Term_addNamedArg(x_1, x_2, x_46, x_8, x_26);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l___private_Lean_Elab_App_11__elabAppArgs(x_1, x_25, x_48, x_3, x_4, x_5, x_8, x_49);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
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
}
else
{
uint8_t x_55; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_24);
if (x_55 == 0)
{
return x_24;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_24, 0);
x_57 = lean_ctor_get(x_24, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_24);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_19);
if (x_59 == 0)
{
return x_19;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_19, 0);
x_61 = lean_ctor_get(x_19, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_19);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
case 1:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_13, 1);
lean_inc(x_63);
lean_dec(x_13);
x_64 = lean_ctor_get(x_14, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_14, 1);
lean_inc(x_65);
lean_dec(x_14);
x_66 = l_Lean_mkProj(x_64, x_65, x_6);
x_6 = x_66;
x_7 = x_12;
x_9 = x_63;
goto _start;
}
case 2:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_13, 1);
lean_inc(x_68);
lean_dec(x_13);
x_69 = lean_ctor_get(x_14, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_14, 1);
lean_inc(x_70);
lean_dec(x_14);
x_71 = lean_box(0);
lean_inc(x_8);
lean_inc(x_70);
x_72 = l_Lean_Elab_Term_mkConst(x_1, x_70, x_71, x_8, x_68);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_List_isEmpty___rarg(x_12);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
lean_dec(x_70);
lean_dec(x_69);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_6);
x_77 = l_Lean_mkOptionalNode___closed__2;
x_78 = lean_array_push(x_77, x_76);
x_79 = lean_box(0);
x_80 = l_Array_empty___closed__1;
x_81 = 0;
lean_inc(x_8);
lean_inc(x_1);
x_82 = l___private_Lean_Elab_App_11__elabAppArgs(x_1, x_73, x_80, x_78, x_79, x_81, x_8, x_74);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_6 = x_83;
x_7 = x_12;
x_9 = x_84;
goto _start;
}
else
{
uint8_t x_86; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_82);
if (x_86 == 0)
{
return x_82;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_82, 0);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_82);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; 
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_73);
x_90 = l_Lean_Elab_Term_inferType(x_1, x_73, x_8, x_74);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_2);
x_94 = l___private_Lean_Elab_App_17__addLValArg___main(x_1, x_69, x_70, x_6, x_3, x_93, x_2, x_91, x_8, x_92);
lean_dec(x_91);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l___private_Lean_Elab_App_11__elabAppArgs(x_1, x_73, x_2, x_95, x_4, x_5, x_8, x_96);
return x_97;
}
else
{
uint8_t x_98; 
lean_dec(x_73);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_94);
if (x_98 == 0)
{
return x_94;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_94, 0);
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_94);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_90);
if (x_102 == 0)
{
return x_90;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_90, 0);
x_104 = lean_ctor_get(x_90, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_90);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_72);
if (x_106 == 0)
{
return x_72;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_72, 0);
x_108 = lean_ctor_get(x_72, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_72);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
case 3:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_110 = lean_ctor_get(x_13, 1);
lean_inc(x_110);
lean_dec(x_13);
x_111 = lean_ctor_get(x_14, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_14, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_14, 2);
lean_inc(x_113);
lean_dec(x_14);
x_114 = l_List_isEmpty___rarg(x_12);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; 
lean_dec(x_112);
lean_dec(x_111);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_6);
x_116 = l_Lean_mkOptionalNode___closed__2;
x_117 = lean_array_push(x_116, x_115);
x_118 = lean_box(0);
x_119 = l_Array_empty___closed__1;
x_120 = 0;
lean_inc(x_8);
lean_inc(x_1);
x_121 = l___private_Lean_Elab_App_11__elabAppArgs(x_1, x_113, x_119, x_117, x_118, x_120, x_8, x_110);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_6 = x_122;
x_7 = x_12;
x_9 = x_123;
goto _start;
}
else
{
uint8_t x_125; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_121);
if (x_125 == 0)
{
return x_121;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_121, 0);
x_127 = lean_ctor_get(x_121, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_121);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; 
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_113);
x_129 = l_Lean_Elab_Term_inferType(x_1, x_113, x_8, x_110);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_2);
x_133 = l___private_Lean_Elab_App_17__addLValArg___main(x_1, x_111, x_112, x_6, x_3, x_132, x_2, x_130, x_8, x_131);
lean_dec(x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l___private_Lean_Elab_App_11__elabAppArgs(x_1, x_113, x_2, x_134, x_4, x_5, x_8, x_135);
return x_136;
}
else
{
uint8_t x_137; 
lean_dec(x_113);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_133);
if (x_137 == 0)
{
return x_133;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_133, 0);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_133);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_129);
if (x_141 == 0)
{
return x_129;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_129, 0);
x_143 = lean_ctor_get(x_129, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_129);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
}
default: 
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_13, 1);
lean_inc(x_145);
lean_dec(x_13);
x_146 = lean_ctor_get(x_14, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_14, 1);
lean_inc(x_147);
lean_dec(x_14);
x_148 = lean_box(0);
lean_inc(x_8);
x_149 = l_Lean_Elab_Term_mkConst(x_1, x_146, x_148, x_8, x_145);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = l_List_isEmpty___rarg(x_12);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; 
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_6);
x_154 = l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_147);
x_157 = l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = l_Lean_mkAppStx___closed__9;
x_160 = lean_array_push(x_159, x_155);
x_161 = lean_array_push(x_160, x_158);
x_162 = lean_box(0);
x_163 = l_Array_empty___closed__1;
x_164 = 0;
lean_inc(x_8);
lean_inc(x_1);
x_165 = l___private_Lean_Elab_App_11__elabAppArgs(x_1, x_150, x_161, x_163, x_162, x_164, x_8, x_151);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_6 = x_166;
x_7 = x_12;
x_9 = x_167;
goto _start;
}
else
{
uint8_t x_169; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_165);
if (x_169 == 0)
{
return x_165;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_165, 0);
x_171 = lean_ctor_get(x_165, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_165);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_12);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_6);
x_174 = l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
lean_inc(x_8);
x_176 = l_Lean_Elab_Term_addNamedArg(x_1, x_2, x_175, x_8, x_151);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_147);
x_180 = l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
lean_inc(x_8);
x_182 = l_Lean_Elab_Term_addNamedArg(x_1, x_177, x_181, x_8, x_178);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l___private_Lean_Elab_App_11__elabAppArgs(x_1, x_150, x_183, x_3, x_4, x_5, x_8, x_184);
return x_185;
}
else
{
uint8_t x_186; 
lean_dec(x_150);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_dec(x_150);
lean_dec(x_147);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_dec(x_147);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_149);
if (x_194 == 0)
{
return x_149;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_149, 0);
x_196 = lean_ctor_get(x_149, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_149);
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
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_13);
if (x_198 == 0)
{
return x_13;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_13, 0);
x_200 = lean_ctor_get(x_13, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_13);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l___private_Lean_Elab_App_18__elabAppLValsAux___main(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_18__elabAppLValsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l___private_Lean_Elab_App_18__elabAppLValsAux(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__elabAppLVals___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of field notation with `@` modifier");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__elabAppLVals___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_19__elabAppLVals___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__elabAppLVals___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_19__elabAppLVals___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_19__elabAppLVals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_List_isEmpty___rarg(x_3);
if (x_10 == 0)
{
if (x_7 == 0)
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_18__elabAppLValsAux___main(x_1, x_4, x_5, x_6, x_7, x_2, x_3, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = l___private_Lean_Elab_App_19__elabAppLVals___closed__3;
x_13 = l_Lean_Elab_Term_throwError___rarg(x_1, x_12, x_8, x_9);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; 
x_18 = l___private_Lean_Elab_App_18__elabAppLValsAux___main(x_1, x_4, x_5, x_6, x_7, x_2, x_3, x_8, x_9);
return x_18;
}
}
}
lean_object* l___private_Lean_Elab_App_19__elabAppLVals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l___private_Lean_Elab_App_19__elabAppLVals(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUniv___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_3);
x_12 = lean_array_fget(x_2, x_11);
x_13 = l_Lean_Elab_Term_elabLevel(x_12, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_5);
x_3 = x_11;
x_4 = lean_box(0);
x_5 = x_16;
x_7 = x_15;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_11);
lean_dec(x_5);
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
else
{
lean_object* x_22; 
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_empty___closed__1;
x_11 = l_Array_foldlStepMAux___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(x_8, x_7, x_9, x_10);
lean_dec(x_7);
x_12 = lean_array_get_size(x_11);
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUniv___spec__1(x_1, x_11, x_12, lean_box(0), x_6, x_2, x_3);
lean_dec(x_11);
return x_13;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUniv___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUniv___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUniv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_elabExplicitUniv(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__1(lean_object* x_1) {
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_List_map___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__1(x_15);
lean_inc(x_2);
x_17 = l_List_append___rarg(x_16, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l___private_Lean_Elab_App_19__elabAppLVals(x_1, x_14, x_17, x_3, x_4, x_5, x_6, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_array_push(x_7, x_18);
x_7 = x_20;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_push(x_7, x_24);
x_7 = x_25;
x_8 = x_13;
goto _start;
}
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_27);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set(x_18, 0, x_31);
x_32 = lean_array_push(x_7, x_18);
x_7 = x_32;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_array_push(x_7, x_36);
x_7 = x_37;
x_8 = x_13;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_18, 0);
lean_dec(x_40);
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_18, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_18, 0);
lean_dec(x_45);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_46; 
lean_dec(x_18);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_27);
lean_ctor_set(x_46, 1, x_10);
return x_46;
}
}
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_List_map___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__1(x_15);
lean_inc(x_2);
x_17 = l_List_append___rarg(x_16, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l___private_Lean_Elab_App_19__elabAppLVals(x_1, x_14, x_17, x_3, x_4, x_5, x_6, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_array_push(x_7, x_18);
x_7 = x_20;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_array_push(x_7, x_24);
x_7 = x_25;
x_8 = x_13;
goto _start;
}
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_27);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set(x_18, 0, x_31);
x_32 = lean_array_push(x_7, x_18);
x_7 = x_32;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_array_push(x_7, x_36);
x_7 = x_37;
x_8 = x_13;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_18, 0);
lean_dec(x_40);
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_18, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_18, 0);
lean_dec(x_45);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_46; 
lean_dec(x_18);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_27);
lean_ctor_set(x_46, 1, x_10);
return x_46;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_20__elabAppFnId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_inc(x_10);
x_14 = l_Lean_Elab_Term_resolveName(x_2, x_12, x_13, x_3, x_10, x_11);
lean_dec(x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_List_lengthAux___main___rarg(x_15, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
lean_ctor_set_uint8(x_10, sizeof(void*)*10 + 1, x_22);
x_23 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_15, x_10, x_16);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_15, x_10, x_16);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
x_27 = lean_ctor_get(x_10, 2);
x_28 = lean_ctor_get(x_10, 3);
x_29 = lean_ctor_get(x_10, 4);
x_30 = lean_ctor_get(x_10, 5);
x_31 = lean_ctor_get(x_10, 6);
x_32 = lean_ctor_get(x_10, 7);
x_33 = lean_ctor_get(x_10, 8);
x_34 = lean_ctor_get(x_10, 9);
x_35 = lean_ctor_get_uint8(x_10, sizeof(void*)*10);
x_36 = lean_ctor_get_uint8(x_10, sizeof(void*)*10 + 1);
x_37 = lean_ctor_get_uint8(x_10, sizeof(void*)*10 + 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_List_lengthAux___main___rarg(x_15, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_dec_eq(x_39, x_40);
lean_dec(x_39);
if (x_41 == 0)
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_42 = 0;
x_43 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_43, 0, x_25);
lean_ctor_set(x_43, 1, x_26);
lean_ctor_set(x_43, 2, x_27);
lean_ctor_set(x_43, 3, x_28);
lean_ctor_set(x_43, 4, x_29);
lean_ctor_set(x_43, 5, x_30);
lean_ctor_set(x_43, 6, x_31);
lean_ctor_set(x_43, 7, x_32);
lean_ctor_set(x_43, 8, x_33);
lean_ctor_set(x_43, 9, x_34);
lean_ctor_set_uint8(x_43, sizeof(void*)*10, x_35);
lean_ctor_set_uint8(x_43, sizeof(void*)*10 + 1, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*10 + 2, x_37);
x_44 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_15, x_43, x_16);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_27);
lean_ctor_set(x_45, 3, x_28);
lean_ctor_set(x_45, 4, x_29);
lean_ctor_set(x_45, 5, x_30);
lean_ctor_set(x_45, 6, x_31);
lean_ctor_set(x_45, 7, x_32);
lean_ctor_set(x_45, 8, x_33);
lean_ctor_set(x_45, 9, x_34);
lean_ctor_set_uint8(x_45, sizeof(void*)*10, x_35);
lean_ctor_set_uint8(x_45, sizeof(void*)*10 + 1, x_36);
lean_ctor_set_uint8(x_45, sizeof(void*)*10 + 2, x_37);
x_46 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_15, x_45, x_16);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_14);
if (x_47 == 0)
{
return x_14;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_14, 0);
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_14);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_11);
return x_51;
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__2(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_List_foldlM___main___at___private_Lean_Elab_App_20__elabAppFnId___spec__3(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_20__elabAppFnId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_8);
lean_dec(x_8);
x_13 = l___private_Lean_Elab_App_20__elabAppFnId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__1(lean_object* x_1) {
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_System_FilePath_dirName___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_List_map___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__1(x_5);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_System_FilePath_dirName___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_10);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_List_map___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__1(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_8);
x_14 = lean_nat_dec_lt(x_9, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_8, x_9);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_9, x_17);
lean_dec(x_9);
lean_inc(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_19 = l___private_Lean_Elab_App_21__elabAppFn___main(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_9 = x_18;
x_10 = x_20;
x_12 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* l___private_Lean_Elab_App_21__elabAppFn___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Syntax_isIdent(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_2);
x_12 = l_Lean_Syntax_getKind(x_2);
x_13 = l_Lean_choiceKind;
x_14 = lean_name_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_285; lean_object* x_393; uint8_t x_394; 
x_393 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
lean_inc(x_2);
x_394 = l_Lean_Syntax_isOfKind(x_2, x_393);
if (x_394 == 0)
{
uint8_t x_395; 
x_395 = 0;
x_285 = x_395;
goto block_392;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; 
x_396 = l_Lean_Syntax_getArgs(x_2);
x_397 = lean_array_get_size(x_396);
lean_dec(x_396);
x_398 = lean_unsigned_to_nat(3u);
x_399 = lean_nat_dec_eq(x_397, x_398);
lean_dec(x_397);
x_285 = x_399;
goto block_392;
}
block_284:
{
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_270; uint8_t x_271; 
x_270 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_2);
x_271 = l_Lean_Syntax_isOfKind(x_2, x_270);
if (x_271 == 0)
{
uint8_t x_272; 
x_272 = 0;
x_16 = x_272;
goto block_269;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_273 = l_Lean_Syntax_getArgs(x_2);
x_274 = lean_array_get_size(x_273);
lean_dec(x_273);
x_275 = lean_unsigned_to_nat(2u);
x_276 = lean_nat_dec_eq(x_274, x_275);
lean_dec(x_274);
x_16 = x_276;
goto block_269;
}
block_269:
{
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_inc(x_2);
x_18 = l_Lean_Syntax_isOfKind(x_2, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_box(0);
x_20 = 1;
lean_inc(x_10);
lean_inc(x_9);
x_21 = l_Lean_Elab_Term_elabTermAux___main(x_19, x_20, x_20, x_2, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l___private_Lean_Elab_App_19__elabAppLVals(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_9, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_array_push(x_8, x_25);
lean_ctor_set(x_21, 1, x_10);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_push(x_8, x_30);
lean_ctor_set(x_21, 1, x_10);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_32);
x_34 = !lean_is_exclusive(x_25);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
lean_ctor_set(x_25, 0, x_36);
x_37 = lean_array_push(x_8, x_25);
lean_ctor_set(x_21, 1, x_10);
lean_ctor_set(x_21, 0, x_37);
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_array_push(x_8, x_40);
lean_ctor_set(x_21, 1, x_10);
lean_ctor_set(x_21, 0, x_41);
return x_21;
}
}
else
{
uint8_t x_42; 
lean_free_object(x_21);
lean_dec(x_10);
lean_dec(x_8);
x_42 = !lean_is_exclusive(x_25);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_25, 0);
lean_dec(x_43);
return x_25;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_25, 1);
lean_inc(x_44);
lean_dec(x_25);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_free_object(x_21);
lean_dec(x_8);
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_25, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_25, 0);
lean_dec(x_48);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
lean_object* x_49; 
lean_dec(x_25);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_32);
lean_ctor_set(x_49, 1, x_10);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_21);
x_52 = l___private_Lean_Elab_App_19__elabAppLVals(x_1, x_50, x_3, x_4, x_5, x_6, x_7, x_9, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_array_push(x_8, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_10);
return x_58;
}
else
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_59);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_62 = x_52;
} else {
 lean_dec_ref(x_52);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
x_65 = lean_array_push(x_8, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_10);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_10);
lean_dec(x_8);
x_67 = lean_ctor_get(x_52, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_68 = x_52;
} else {
 lean_dec_ref(x_52);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_59);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_8);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_70 = x_52;
} else {
 lean_dec_ref(x_52);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_10);
return x_71;
}
}
}
}
else
{
lean_object* x_72; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = lean_ctor_get(x_21, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
lean_dec(x_72);
x_74 = !lean_is_exclusive(x_21);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_21, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
lean_dec(x_73);
lean_ctor_set(x_21, 0, x_76);
x_77 = lean_array_push(x_8, x_21);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_10);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_21, 1);
lean_inc(x_79);
lean_dec(x_21);
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
lean_dec(x_73);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_array_push(x_8, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_10);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_10);
lean_dec(x_8);
x_84 = !lean_is_exclusive(x_21);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_21, 0);
lean_dec(x_85);
return x_21;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_21, 1);
lean_inc(x_86);
lean_dec(x_21);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_8);
x_88 = !lean_is_exclusive(x_21);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_21, 1);
lean_dec(x_89);
x_90 = lean_ctor_get(x_21, 0);
lean_dec(x_90);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
else
{
lean_object* x_91; 
lean_dec(x_21);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_72);
lean_ctor_set(x_91, 1, x_10);
return x_91;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = l_Lean_Syntax_getArgs(x_2);
x_93 = lean_array_get_size(x_92);
lean_dec(x_92);
x_94 = lean_unsigned_to_nat(2u);
x_95 = lean_nat_dec_eq(x_93, x_94);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_96 = lean_box(0);
x_97 = 1;
lean_inc(x_10);
lean_inc(x_9);
x_98 = l_Lean_Elab_Term_elabTermAux___main(x_96, x_97, x_97, x_2, x_9, x_10);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_ctor_get(x_98, 1);
x_102 = l___private_Lean_Elab_App_19__elabAppLVals(x_1, x_100, x_3, x_4, x_5, x_6, x_7, x_9, x_101);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_array_push(x_8, x_102);
lean_ctor_set(x_98, 1, x_10);
lean_ctor_set(x_98, 0, x_104);
return x_98;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_102, 0);
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_102);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_array_push(x_8, x_107);
lean_ctor_set(x_98, 1, x_10);
lean_ctor_set(x_98, 0, x_108);
return x_98;
}
}
else
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_102, 0);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
lean_dec(x_109);
x_111 = !lean_is_exclusive(x_102);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_102, 0);
lean_dec(x_112);
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
lean_dec(x_110);
lean_ctor_set(x_102, 0, x_113);
x_114 = lean_array_push(x_8, x_102);
lean_ctor_set(x_98, 1, x_10);
lean_ctor_set(x_98, 0, x_114);
return x_98;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_102, 1);
lean_inc(x_115);
lean_dec(x_102);
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
lean_dec(x_110);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = lean_array_push(x_8, x_117);
lean_ctor_set(x_98, 1, x_10);
lean_ctor_set(x_98, 0, x_118);
return x_98;
}
}
else
{
uint8_t x_119; 
lean_free_object(x_98);
lean_dec(x_10);
lean_dec(x_8);
x_119 = !lean_is_exclusive(x_102);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_102, 0);
lean_dec(x_120);
return x_102;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_102, 1);
lean_inc(x_121);
lean_dec(x_102);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_109);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_98);
lean_dec(x_8);
x_123 = !lean_is_exclusive(x_102);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_102, 1);
lean_dec(x_124);
x_125 = lean_ctor_get(x_102, 0);
lean_dec(x_125);
lean_ctor_set(x_102, 1, x_10);
return x_102;
}
else
{
lean_object* x_126; 
lean_dec(x_102);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_109);
lean_ctor_set(x_126, 1, x_10);
return x_126;
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_98, 0);
x_128 = lean_ctor_get(x_98, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_98);
x_129 = l___private_Lean_Elab_App_19__elabAppLVals(x_1, x_127, x_3, x_4, x_5, x_6, x_7, x_9, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
x_134 = lean_array_push(x_8, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_10);
return x_135;
}
else
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_129, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_136);
x_138 = lean_ctor_get(x_129, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_139 = x_129;
} else {
 lean_dec_ref(x_129);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_137, 0);
lean_inc(x_140);
lean_dec(x_137);
if (lean_is_scalar(x_139)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_139;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_138);
x_142 = lean_array_push(x_8, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_10);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_10);
lean_dec(x_8);
x_144 = lean_ctor_get(x_129, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_145 = x_129;
} else {
 lean_dec_ref(x_129);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_136);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_8);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_147 = x_129;
} else {
 lean_dec_ref(x_129);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_136);
lean_ctor_set(x_148, 1, x_10);
return x_148;
}
}
}
}
else
{
lean_object* x_149; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_149 = lean_ctor_get(x_98, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
uint8_t x_151; 
lean_dec(x_149);
x_151 = !lean_is_exclusive(x_98);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_98, 0);
lean_dec(x_152);
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
lean_dec(x_150);
lean_ctor_set(x_98, 0, x_153);
x_154 = lean_array_push(x_8, x_98);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_10);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_98, 1);
lean_inc(x_156);
lean_dec(x_98);
x_157 = lean_ctor_get(x_150, 0);
lean_inc(x_157);
lean_dec(x_150);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
x_159 = lean_array_push(x_8, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_10);
return x_160;
}
}
else
{
uint8_t x_161; 
lean_dec(x_10);
lean_dec(x_8);
x_161 = !lean_is_exclusive(x_98);
if (x_161 == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_98, 0);
lean_dec(x_162);
return x_98;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_98, 1);
lean_inc(x_163);
lean_dec(x_98);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_149);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_8);
x_165 = !lean_is_exclusive(x_98);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_98, 1);
lean_dec(x_166);
x_167 = lean_ctor_get(x_98, 0);
lean_dec(x_167);
lean_ctor_set(x_98, 1, x_10);
return x_98;
}
else
{
lean_object* x_168; 
lean_dec(x_98);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_149);
lean_ctor_set(x_168, 1, x_10);
return x_168;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_169 = lean_unsigned_to_nat(1u);
x_170 = l_Lean_Syntax_getArg(x_2, x_169);
lean_dec(x_2);
x_171 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_170);
x_172 = l_Lean_Syntax_isOfKind(x_170, x_171);
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec(x_170);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_173 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_10);
return x_173;
}
else
{
uint8_t x_174; 
x_174 = 1;
x_2 = x_170;
x_7 = x_174;
goto _start;
}
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_176 = lean_unsigned_to_nat(0u);
x_177 = l_Lean_Syntax_getArg(x_2, x_176);
x_178 = l_Lean_identKind___closed__2;
lean_inc(x_177);
x_179 = l_Lean_Syntax_isOfKind(x_177, x_178);
if (x_179 == 0)
{
lean_object* x_180; uint8_t x_181; lean_object* x_182; 
lean_dec(x_177);
x_180 = lean_box(0);
x_181 = 1;
lean_inc(x_10);
lean_inc(x_9);
x_182 = l_Lean_Elab_Term_elabTermAux___main(x_180, x_181, x_181, x_2, x_9, x_10);
if (lean_obj_tag(x_182) == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_182, 0);
x_185 = lean_ctor_get(x_182, 1);
x_186 = l___private_Lean_Elab_App_19__elabAppLVals(x_1, x_184, x_3, x_4, x_5, x_6, x_7, x_9, x_185);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_array_push(x_8, x_186);
lean_ctor_set(x_182, 1, x_10);
lean_ctor_set(x_182, 0, x_188);
return x_182;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_186, 0);
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_186);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_array_push(x_8, x_191);
lean_ctor_set(x_182, 1, x_10);
lean_ctor_set(x_182, 0, x_192);
return x_182;
}
}
else
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_186, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
lean_dec(x_193);
x_195 = !lean_is_exclusive(x_186);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_186, 0);
lean_dec(x_196);
x_197 = lean_ctor_get(x_194, 0);
lean_inc(x_197);
lean_dec(x_194);
lean_ctor_set(x_186, 0, x_197);
x_198 = lean_array_push(x_8, x_186);
lean_ctor_set(x_182, 1, x_10);
lean_ctor_set(x_182, 0, x_198);
return x_182;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_ctor_get(x_186, 1);
lean_inc(x_199);
lean_dec(x_186);
x_200 = lean_ctor_get(x_194, 0);
lean_inc(x_200);
lean_dec(x_194);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
x_202 = lean_array_push(x_8, x_201);
lean_ctor_set(x_182, 1, x_10);
lean_ctor_set(x_182, 0, x_202);
return x_182;
}
}
else
{
uint8_t x_203; 
lean_free_object(x_182);
lean_dec(x_10);
lean_dec(x_8);
x_203 = !lean_is_exclusive(x_186);
if (x_203 == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_186, 0);
lean_dec(x_204);
return x_186;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_186, 1);
lean_inc(x_205);
lean_dec(x_186);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_193);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
uint8_t x_207; 
lean_free_object(x_182);
lean_dec(x_8);
x_207 = !lean_is_exclusive(x_186);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_186, 1);
lean_dec(x_208);
x_209 = lean_ctor_get(x_186, 0);
lean_dec(x_209);
lean_ctor_set(x_186, 1, x_10);
return x_186;
}
else
{
lean_object* x_210; 
lean_dec(x_186);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_193);
lean_ctor_set(x_210, 1, x_10);
return x_210;
}
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_182, 0);
x_212 = lean_ctor_get(x_182, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_182);
x_213 = l___private_Lean_Elab_App_19__elabAppLVals(x_1, x_211, x_3, x_4, x_5, x_6, x_7, x_9, x_212);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_216 = x_213;
} else {
 lean_dec_ref(x_213);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
x_218 = lean_array_push(x_8, x_217);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_10);
return x_219;
}
else
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_213, 0);
lean_inc(x_220);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_220);
x_222 = lean_ctor_get(x_213, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_223 = x_213;
} else {
 lean_dec_ref(x_213);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_221, 0);
lean_inc(x_224);
lean_dec(x_221);
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_222);
x_226 = lean_array_push(x_8, x_225);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_10);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_10);
lean_dec(x_8);
x_228 = lean_ctor_get(x_213, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_229 = x_213;
} else {
 lean_dec_ref(x_213);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_220);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_8);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_231 = x_213;
} else {
 lean_dec_ref(x_213);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_220);
lean_ctor_set(x_232, 1, x_10);
return x_232;
}
}
}
}
else
{
lean_object* x_233; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_233 = lean_ctor_get(x_182, 0);
lean_inc(x_233);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
if (lean_obj_tag(x_234) == 0)
{
uint8_t x_235; 
lean_dec(x_233);
x_235 = !lean_is_exclusive(x_182);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_236 = lean_ctor_get(x_182, 0);
lean_dec(x_236);
x_237 = lean_ctor_get(x_234, 0);
lean_inc(x_237);
lean_dec(x_234);
lean_ctor_set(x_182, 0, x_237);
x_238 = lean_array_push(x_8, x_182);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_10);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_240 = lean_ctor_get(x_182, 1);
lean_inc(x_240);
lean_dec(x_182);
x_241 = lean_ctor_get(x_234, 0);
lean_inc(x_241);
lean_dec(x_234);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_240);
x_243 = lean_array_push(x_8, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_10);
return x_244;
}
}
else
{
uint8_t x_245; 
lean_dec(x_10);
lean_dec(x_8);
x_245 = !lean_is_exclusive(x_182);
if (x_245 == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_182, 0);
lean_dec(x_246);
return x_182;
}
else
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_182, 1);
lean_inc(x_247);
lean_dec(x_182);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_233);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_8);
x_249 = !lean_is_exclusive(x_182);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_182, 1);
lean_dec(x_250);
x_251 = lean_ctor_get(x_182, 0);
lean_dec(x_251);
lean_ctor_set(x_182, 1, x_10);
return x_182;
}
else
{
lean_object* x_252; 
lean_dec(x_182);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_233);
lean_ctor_set(x_252, 1, x_10);
return x_252;
}
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_253 = lean_unsigned_to_nat(1u);
x_254 = l_Lean_Syntax_getArg(x_2, x_253);
lean_dec(x_2);
x_255 = l_Lean_Syntax_getArgs(x_254);
lean_dec(x_254);
x_256 = l_Array_isEmpty___rarg(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = l_Lean_Syntax_inhabited;
x_258 = lean_array_get(x_257, x_255, x_176);
lean_dec(x_255);
x_259 = l_Lean_Elab_Term_elabExplicitUniv(x_258, x_9, x_10);
lean_dec(x_258);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = l___private_Lean_Elab_App_20__elabAppFnId(x_1, x_177, x_260, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_261);
return x_262;
}
else
{
uint8_t x_263; 
lean_dec(x_177);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_263 = !lean_is_exclusive(x_259);
if (x_263 == 0)
{
return x_259;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_259, 0);
x_265 = lean_ctor_get(x_259, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_259);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
else
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_255);
x_267 = lean_box(0);
x_268 = l___private_Lean_Elab_App_20__elabAppFnId(x_1, x_177, x_267, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_268;
}
}
}
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_277 = lean_unsigned_to_nat(0u);
x_278 = l_Lean_Syntax_getArg(x_2, x_277);
x_279 = lean_unsigned_to_nat(2u);
x_280 = l_Lean_Syntax_getArg(x_2, x_279);
lean_dec(x_2);
x_281 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_281, 0, x_280);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_3);
x_2 = x_278;
x_3 = x_282;
goto _start;
}
}
block_392:
{
if (x_285 == 0)
{
lean_object* x_286; uint8_t x_287; 
x_286 = l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
lean_inc(x_2);
x_287 = l_Lean_Syntax_isOfKind(x_2, x_286);
if (x_287 == 0)
{
uint8_t x_288; 
x_288 = 0;
x_15 = x_288;
goto block_284;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_289 = l_Lean_Syntax_getArgs(x_2);
x_290 = lean_array_get_size(x_289);
lean_dec(x_289);
x_291 = lean_unsigned_to_nat(4u);
x_292 = lean_nat_dec_eq(x_290, x_291);
lean_dec(x_290);
x_15 = x_292;
goto block_284;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_293 = lean_unsigned_to_nat(0u);
x_294 = l_Lean_Syntax_getArg(x_2, x_293);
x_295 = lean_unsigned_to_nat(2u);
x_296 = l_Lean_Syntax_getArg(x_2, x_295);
x_297 = l_Lean_fieldIdxKind___closed__2;
lean_inc(x_296);
x_298 = l_Lean_Syntax_isOfKind(x_296, x_297);
if (x_298 == 0)
{
lean_object* x_299; uint8_t x_300; 
x_299 = l_Lean_identKind___closed__2;
lean_inc(x_296);
x_300 = l_Lean_Syntax_isOfKind(x_296, x_299);
if (x_300 == 0)
{
lean_object* x_301; uint8_t x_302; lean_object* x_303; 
lean_dec(x_296);
lean_dec(x_294);
x_301 = lean_box(0);
x_302 = 1;
lean_inc(x_10);
lean_inc(x_9);
x_303 = l_Lean_Elab_Term_elabTermAux___main(x_301, x_302, x_302, x_2, x_9, x_10);
if (lean_obj_tag(x_303) == 0)
{
uint8_t x_304; 
x_304 = !lean_is_exclusive(x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_303, 0);
x_306 = lean_ctor_get(x_303, 1);
x_307 = l___private_Lean_Elab_App_19__elabAppLVals(x_1, x_305, x_3, x_4, x_5, x_6, x_7, x_9, x_306);
if (lean_obj_tag(x_307) == 0)
{
uint8_t x_308; 
x_308 = !lean_is_exclusive(x_307);
if (x_308 == 0)
{
lean_object* x_309; 
x_309 = lean_array_push(x_8, x_307);
lean_ctor_set(x_303, 1, x_10);
lean_ctor_set(x_303, 0, x_309);
return x_303;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_310 = lean_ctor_get(x_307, 0);
x_311 = lean_ctor_get(x_307, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_307);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_array_push(x_8, x_312);
lean_ctor_set(x_303, 1, x_10);
lean_ctor_set(x_303, 0, x_313);
return x_303;
}
}
else
{
lean_object* x_314; 
x_314 = lean_ctor_get(x_307, 0);
lean_inc(x_314);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
if (lean_obj_tag(x_315) == 0)
{
uint8_t x_316; 
lean_dec(x_314);
x_316 = !lean_is_exclusive(x_307);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_307, 0);
lean_dec(x_317);
x_318 = lean_ctor_get(x_315, 0);
lean_inc(x_318);
lean_dec(x_315);
lean_ctor_set(x_307, 0, x_318);
x_319 = lean_array_push(x_8, x_307);
lean_ctor_set(x_303, 1, x_10);
lean_ctor_set(x_303, 0, x_319);
return x_303;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_320 = lean_ctor_get(x_307, 1);
lean_inc(x_320);
lean_dec(x_307);
x_321 = lean_ctor_get(x_315, 0);
lean_inc(x_321);
lean_dec(x_315);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_320);
x_323 = lean_array_push(x_8, x_322);
lean_ctor_set(x_303, 1, x_10);
lean_ctor_set(x_303, 0, x_323);
return x_303;
}
}
else
{
uint8_t x_324; 
lean_free_object(x_303);
lean_dec(x_10);
lean_dec(x_8);
x_324 = !lean_is_exclusive(x_307);
if (x_324 == 0)
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_307, 0);
lean_dec(x_325);
return x_307;
}
else
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_ctor_get(x_307, 1);
lean_inc(x_326);
lean_dec(x_307);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_314);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
else
{
uint8_t x_328; 
lean_free_object(x_303);
lean_dec(x_8);
x_328 = !lean_is_exclusive(x_307);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_307, 1);
lean_dec(x_329);
x_330 = lean_ctor_get(x_307, 0);
lean_dec(x_330);
lean_ctor_set(x_307, 1, x_10);
return x_307;
}
else
{
lean_object* x_331; 
lean_dec(x_307);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_314);
lean_ctor_set(x_331, 1, x_10);
return x_331;
}
}
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_303, 0);
x_333 = lean_ctor_get(x_303, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_303);
x_334 = l___private_Lean_Elab_App_19__elabAppLVals(x_1, x_332, x_3, x_4, x_5, x_6, x_7, x_9, x_333);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_337 = x_334;
} else {
 lean_dec_ref(x_334);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
x_339 = lean_array_push(x_8, x_338);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_10);
return x_340;
}
else
{
lean_object* x_341; 
x_341 = lean_ctor_get(x_334, 0);
lean_inc(x_341);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_341);
x_343 = lean_ctor_get(x_334, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_344 = x_334;
} else {
 lean_dec_ref(x_334);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_342, 0);
lean_inc(x_345);
lean_dec(x_342);
if (lean_is_scalar(x_344)) {
 x_346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_346 = x_344;
}
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_343);
x_347 = lean_array_push(x_8, x_346);
x_348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_10);
return x_348;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_10);
lean_dec(x_8);
x_349 = lean_ctor_get(x_334, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_350 = x_334;
} else {
 lean_dec_ref(x_334);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(1, 2, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_341);
lean_ctor_set(x_351, 1, x_349);
return x_351;
}
}
else
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_8);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_352 = x_334;
} else {
 lean_dec_ref(x_334);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_341);
lean_ctor_set(x_353, 1, x_10);
return x_353;
}
}
}
}
else
{
lean_object* x_354; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_354 = lean_ctor_get(x_303, 0);
lean_inc(x_354);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
if (lean_obj_tag(x_355) == 0)
{
uint8_t x_356; 
lean_dec(x_354);
x_356 = !lean_is_exclusive(x_303);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_357 = lean_ctor_get(x_303, 0);
lean_dec(x_357);
x_358 = lean_ctor_get(x_355, 0);
lean_inc(x_358);
lean_dec(x_355);
lean_ctor_set(x_303, 0, x_358);
x_359 = lean_array_push(x_8, x_303);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_10);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_361 = lean_ctor_get(x_303, 1);
lean_inc(x_361);
lean_dec(x_303);
x_362 = lean_ctor_get(x_355, 0);
lean_inc(x_362);
lean_dec(x_355);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_361);
x_364 = lean_array_push(x_8, x_363);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_10);
return x_365;
}
}
else
{
uint8_t x_366; 
lean_dec(x_10);
lean_dec(x_8);
x_366 = !lean_is_exclusive(x_303);
if (x_366 == 0)
{
lean_object* x_367; 
x_367 = lean_ctor_get(x_303, 0);
lean_dec(x_367);
return x_303;
}
else
{
lean_object* x_368; lean_object* x_369; 
x_368 = lean_ctor_get(x_303, 1);
lean_inc(x_368);
lean_dec(x_303);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_354);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
}
else
{
uint8_t x_370; 
lean_dec(x_8);
x_370 = !lean_is_exclusive(x_303);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; 
x_371 = lean_ctor_get(x_303, 1);
lean_dec(x_371);
x_372 = lean_ctor_get(x_303, 0);
lean_dec(x_372);
lean_ctor_set(x_303, 1, x_10);
return x_303;
}
else
{
lean_object* x_373; 
lean_dec(x_303);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_354);
lean_ctor_set(x_373, 1, x_10);
return x_373;
}
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_2);
x_374 = l_Lean_Syntax_getId(x_296);
lean_dec(x_296);
x_375 = l_Lean_Name_eraseMacroScopes(x_374);
lean_dec(x_374);
x_376 = l_Lean_Name_components(x_375);
x_377 = l_List_map___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__1(x_376);
x_378 = l_List_append___rarg(x_377, x_3);
x_2 = x_294;
x_3 = x_378;
goto _start;
}
}
else
{
lean_object* x_380; lean_object* x_381; 
lean_dec(x_2);
x_380 = l_Lean_fieldIdxKind;
x_381 = l_Lean_Syntax_isNatLitAux(x_380, x_296);
lean_dec(x_296);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_382 = l_Nat_Inhabited;
x_383 = l_Option_get_x21___rarg___closed__3;
x_384 = lean_panic_fn(x_382, x_383);
x_385 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_385, 0, x_384);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_3);
x_2 = x_294;
x_3 = x_386;
goto _start;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = lean_ctor_get(x_381, 0);
lean_inc(x_388);
lean_dec(x_381);
x_389 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_389, 0, x_388);
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_3);
x_2 = x_294;
x_3 = x_390;
goto _start;
}
}
}
}
}
else
{
lean_object* x_400; uint8_t x_401; 
x_400 = l_Lean_Syntax_getArgs(x_2);
x_401 = !lean_is_exclusive(x_9);
if (x_401 == 0)
{
uint8_t x_402; lean_object* x_403; lean_object* x_404; 
x_402 = 0;
lean_ctor_set_uint8(x_9, sizeof(void*)*10 + 1, x_402);
x_403 = lean_unsigned_to_nat(0u);
x_404 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_400, x_403, x_8, x_9, x_10);
lean_dec(x_400);
lean_dec(x_2);
return x_404;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; uint8_t x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_405 = lean_ctor_get(x_9, 0);
x_406 = lean_ctor_get(x_9, 1);
x_407 = lean_ctor_get(x_9, 2);
x_408 = lean_ctor_get(x_9, 3);
x_409 = lean_ctor_get(x_9, 4);
x_410 = lean_ctor_get(x_9, 5);
x_411 = lean_ctor_get(x_9, 6);
x_412 = lean_ctor_get(x_9, 7);
x_413 = lean_ctor_get(x_9, 8);
x_414 = lean_ctor_get(x_9, 9);
x_415 = lean_ctor_get_uint8(x_9, sizeof(void*)*10);
x_416 = lean_ctor_get_uint8(x_9, sizeof(void*)*10 + 2);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc(x_411);
lean_inc(x_410);
lean_inc(x_409);
lean_inc(x_408);
lean_inc(x_407);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_9);
x_417 = 0;
x_418 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_418, 0, x_405);
lean_ctor_set(x_418, 1, x_406);
lean_ctor_set(x_418, 2, x_407);
lean_ctor_set(x_418, 3, x_408);
lean_ctor_set(x_418, 4, x_409);
lean_ctor_set(x_418, 5, x_410);
lean_ctor_set(x_418, 6, x_411);
lean_ctor_set(x_418, 7, x_412);
lean_ctor_set(x_418, 8, x_413);
lean_ctor_set(x_418, 9, x_414);
lean_ctor_set_uint8(x_418, sizeof(void*)*10, x_415);
lean_ctor_set_uint8(x_418, sizeof(void*)*10 + 1, x_417);
lean_ctor_set_uint8(x_418, sizeof(void*)*10 + 2, x_416);
x_419 = lean_unsigned_to_nat(0u);
x_420 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_400, x_419, x_8, x_418, x_10);
lean_dec(x_400);
lean_dec(x_2);
return x_420;
}
}
}
else
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_box(0);
x_422 = l___private_Lean_Elab_App_20__elabAppFnId(x_1, x_2, x_421, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_422;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_21__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_2);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_21__elabAppFn___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l___private_Lean_Elab_App_21__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_21__elabAppFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_21__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_21__elabAppFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l___private_Lean_Elab_App_21__elabAppFn(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_22__getSuccess___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_Array_shrink___main___rarg(x_1, x_3);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_array_fget(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_7);
x_8 = lean_nat_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_11 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_fswap(x_1, x_2, x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_16 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
x_1 = x_13;
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_2 = x_19;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_App_22__getSuccess(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_filterAux___main___at___private_Lean_Elab_App_22__getSuccess___spec__1(x_1, x_2, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_getPosition___at___private_Lean_Elab_App_23__toMessageData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_FileMap_toPosition(x_4, x_5);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_FileMap_toPosition(x_8, x_9);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
lean_object* _init_l___private_Lean_Elab_App_23__toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Syntax_6__formatInfo___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_23__toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = l_Lean_Elab_getPos___at_Lean_Elab_Term_throwError___spec__2(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = l_Lean_Elab_getPosition___at___private_Lean_Elab_App_23__toMessageData___spec__1(x_8, x_3, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = l_Lean_Position_DecidableEq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = l_Nat_repr(x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l___private_Lean_Elab_App_23__toMessageData___closed__1;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = l_Nat_repr(x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_ctor_get(x_1, 4);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_9, 0, x_28);
return x_9;
}
else
{
lean_object* x_29; 
lean_dec(x_12);
x_29 = lean_ctor_get(x_1, 4);
lean_inc(x_29);
lean_dec(x_1);
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
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = l_Lean_Position_DecidableEq(x_30, x_32);
lean_dec(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = l_Nat_repr(x_34);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l___private_Lean_Elab_App_23__toMessageData___closed__1;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = l_Nat_repr(x_40);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_ctor_get(x_1, 4);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_31);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_32);
x_50 = lean_ctor_get(x_1, 4);
lean_inc(x_50);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_31);
return x_51;
}
}
}
}
lean_object* l___private_Lean_Elab_App_23__toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_App_23__toMessageData(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_24__mergeFailures___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = x_3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_3, x_2, x_11);
x_13 = x_10;
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
x_14 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__1;
x_15 = l_unreachable_x21___rarg(x_14);
lean_inc(x_4);
x_16 = lean_apply_2(x_15, x_4, x_5);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
x_21 = x_17;
x_22 = lean_array_fset(x_12, x_2, x_21);
lean_dec(x_2);
x_2 = x_20;
x_3 = x_22;
x_5 = x_18;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_13, 0);
lean_inc(x_28);
lean_dec(x_13);
lean_inc(x_4);
x_29 = l___private_Lean_Elab_App_23__toMessageData(x_28, x_1, x_4, x_5);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_2, x_32);
x_34 = x_30;
x_35 = lean_array_fset(x_12, x_2, x_34);
lean_dec(x_2);
x_2 = x_33;
x_3 = x_35;
x_5 = x_31;
goto _start;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("overloaded, errors ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_24__mergeFailures___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = x_1;
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_App_24__mergeFailures___spec__1___boxed), 5, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_5);
x_8 = x_7;
lean_inc(x_3);
x_9 = lean_apply_2(x_8, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_MessageData_ofArray(x_10);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_Term_throwError___rarg(x_2, x_14, x_3, x_11);
lean_dec(x_2);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l___private_Lean_Elab_App_24__mergeFailures(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_24__mergeFailures___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_24__mergeFailures___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Lean_Elab_App_24__mergeFailures___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_25__elabAppAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = x_4;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_4, x_3, x_9);
x_11 = x_8;
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_2);
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_1);
lean_ctor_set(x_19, 3, x_2);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_16);
x_21 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = x_21;
x_23 = lean_array_fset(x_10, x_3, x_22);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
x_25 = l_Lean_MessageData_Inhabited;
x_26 = l_unreachable_x21___rarg(x_25);
x_27 = x_26;
x_28 = lean_array_fset(x_10, x_3, x_27);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_28;
goto _start;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_App_25__elabAppAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous, possible interpretations ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_25__elabAppAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_25__elabAppAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_25__elabAppAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_25__elabAppAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_25__elabAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_2);
x_11 = l___private_Lean_Elab_App_21__elabAppFn___main(x_1, x_2, x_8, x_3, x_4, x_5, x_9, x_10, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
x_18 = l_Array_filterAux___main___at___private_Lean_Elab_App_22__getSuccess___spec__1(x_12, x_17, x_17);
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_eq(x_19, x_15);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = lean_nat_dec_lt(x_15, x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
x_22 = l___private_Lean_Elab_App_24__mergeFailures___rarg(x_12, x_2, x_6, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_12);
x_23 = l_Lean_Elab_Term_getLCtx(x_6, x_13);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Term_getOptions(x_6, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = x_18;
x_30 = l_Array_umapMAux___main___at___private_Lean_Elab_App_25__elabAppAux___spec__1(x_24, x_27, x_17, x_29);
x_31 = x_30;
x_32 = l_Lean_MessageData_ofArray(x_31);
lean_dec(x_31);
x_33 = l___private_Lean_Elab_App_25__elabAppAux___closed__3;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Elab_Term_throwError___rarg(x_2, x_34, x_6, x_28);
lean_dec(x_2);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_2);
x_36 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_37 = lean_array_get(x_36, x_18, x_17);
lean_dec(x_18);
x_38 = l_Lean_Elab_Term_applyResult(x_37, x_6, x_13);
lean_dec(x_13);
lean_dec(x_6);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
x_39 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_array_get(x_39, x_12, x_40);
lean_dec(x_12);
x_42 = l_Lean_Elab_Term_applyResult(x_41, x_6, x_13);
lean_dec(x_13);
lean_dec(x_6);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_6);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
return x_11;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_26__expandApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_16 = l_Lean_Syntax_getKind(x_10);
x_17 = l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
x_18 = lean_name_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_10);
x_20 = lean_array_push(x_15, x_19);
lean_ctor_set(x_4, 1, x_20);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = l_Lean_Syntax_getArg(x_10, x_11);
x_23 = l_Lean_Syntax_getId(x_22);
lean_dec(x_22);
x_24 = l_Lean_Name_eraseMacroScopes(x_23);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(3u);
x_26 = l_Lean_Syntax_getArg(x_10, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_5);
x_29 = l_Lean_Elab_Term_addNamedArg(x_10, x_14, x_28, x_5, x_6);
lean_dec(x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_ctor_set(x_4, 0, x_30);
x_3 = x_12;
x_6 = x_31;
goto _start;
}
else
{
uint8_t x_33; 
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_4, 0);
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_4);
lean_inc(x_10);
x_39 = l_Lean_Syntax_getKind(x_10);
x_40 = l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
x_41 = lean_name_eq(x_39, x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_10);
x_43 = lean_array_push(x_38, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
x_3 = x_12;
x_4 = x_44;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = l_Lean_Syntax_getArg(x_10, x_11);
x_47 = l_Lean_Syntax_getId(x_46);
lean_dec(x_46);
x_48 = l_Lean_Name_eraseMacroScopes(x_47);
lean_dec(x_47);
x_49 = lean_unsigned_to_nat(3u);
x_50 = l_Lean_Syntax_getArg(x_10, x_49);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_5);
x_53 = l_Lean_Elab_Term_addNamedArg(x_10, x_37, x_52, x_5, x_6);
lean_dec(x_10);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_38);
x_3 = x_12;
x_4 = x_56;
x_6 = x_55;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_38);
lean_dec(x_12);
lean_dec(x_5);
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_60 = x_53;
} else {
 lean_dec_ref(x_53);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
}
}
lean_object* _init_l___private_Lean_Elab_App_26__expandApp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_26__expandApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = l___private_Lean_Elab_App_26__expandApp___closed__1;
x_10 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_26__expandApp___spec__1(x_1, x_8, x_4, x_9, x_2, x_3);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_5);
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_26__expandApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_26__expandApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_App_26__expandApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_App_26__expandApp(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Lean_Elab_App_26__expandApp(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l___private_Lean_Elab_App_25__elabAppAux(x_1, x_9, x_10, x_11, x_2, x_3, x_8);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabApp), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_mkAppStx___closed__8;
x_4 = l___regBuiltin_Lean_Elab_Term_elabApp___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Array_empty___closed__1;
lean_inc(x_1);
x_6 = l___private_Lean_Elab_App_25__elabAppAux(x_1, x_1, x_5, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_elabId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabId), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_mkTermIdFromIdent___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabId___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_inc(x_1);
x_55 = l_Lean_Syntax_isOfKind(x_1, x_54);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = 0;
x_5 = x_56;
goto block_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = l_Lean_Syntax_getArgs(x_1);
x_58 = lean_array_get_size(x_57);
lean_dec(x_57);
x_59 = lean_unsigned_to_nat(2u);
x_60 = lean_nat_dec_eq(x_58, x_59);
lean_dec(x_58);
x_5 = x_60;
goto block_53;
}
block_53:
{
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_43; uint8_t x_44; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_43 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_8);
x_44 = l_Lean_Syntax_isOfKind(x_8, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_1);
x_45 = l_Lean_Parser_Term_paren___elambda__1___closed__1;
lean_inc(x_8);
x_46 = l_Lean_Syntax_isOfKind(x_8, x_45);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = 0;
x_9 = x_47;
goto block_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = l_Lean_Syntax_getArgs(x_8);
x_49 = lean_array_get_size(x_48);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(3u);
x_51 = lean_nat_dec_eq(x_49, x_50);
lean_dec(x_49);
x_9 = x_51;
goto block_42;
}
}
else
{
lean_object* x_52; 
lean_dec(x_8);
x_52 = l_Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4);
return x_52;
}
block_42:
{
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = 1;
x_11 = 0;
x_12 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_10, x_11, x_8, x_3, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Syntax_getArg(x_8, x_7);
x_14 = l_Lean_nullKind___closed__2;
lean_inc(x_13);
x_15 = l_Lean_Syntax_isOfKind(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
lean_dec(x_13);
x_16 = 1;
x_17 = 0;
x_18 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_16, x_17, x_8, x_3, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = l_Lean_Syntax_getArgs(x_13);
x_20 = lean_array_get_size(x_19);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
uint8_t x_23; uint8_t x_24; lean_object* x_25; 
lean_dec(x_13);
x_23 = 1;
x_24 = 0;
x_25 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_23, x_24, x_8, x_3, x_4);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Syntax_getArg(x_13, x_26);
x_28 = l_Lean_Syntax_getArg(x_13, x_7);
lean_dec(x_13);
lean_inc(x_28);
x_29 = l_Lean_Syntax_isOfKind(x_28, x_14);
if (x_29 == 0)
{
uint8_t x_30; uint8_t x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_27);
x_30 = 1;
x_31 = 0;
x_32 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_30, x_31, x_8, x_3, x_4);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_34 = lean_array_get_size(x_33);
lean_dec(x_33);
x_35 = lean_nat_dec_eq(x_34, x_26);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; uint8_t x_37; lean_object* x_38; 
lean_dec(x_27);
x_36 = 1;
x_37 = 0;
x_38 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_36, x_37, x_8, x_3, x_4);
return x_38;
}
else
{
uint8_t x_39; uint8_t x_40; lean_object* x_41; 
lean_dec(x_8);
x_39 = 1;
x_40 = 0;
x_41 = l_Lean_Elab_Term_elabTermAux___main(x_2, x_39, x_40, x_27, x_3, x_4);
return x_41;
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
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabExplicit), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabChoice), 4, 0);
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
lean_object* l_Lean_Elab_Term_elabProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabProj), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrayRef), 4, 0);
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
lean_object* l_Lean_Elab_Term_elabRawIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabRawIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabRawIdent), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_identKind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabRawIdent___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_27__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* initialize_Lean_Util_FindMVar(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_App(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_FindMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_Arg_inhabited___closed__1 = _init_l_Lean_Elab_Term_Arg_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Arg_inhabited___closed__1);
l_Lean_Elab_Term_Arg_inhabited = _init_l_Lean_Elab_Term_Arg_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_Arg_inhabited);
l_Lean_Elab_Term_NamedArg_inhabited___closed__1 = _init_l_Lean_Elab_Term_NamedArg_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_NamedArg_inhabited___closed__1);
l_Lean_Elab_Term_NamedArg_inhabited = _init_l_Lean_Elab_Term_NamedArg_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_NamedArg_inhabited);
l_Lean_Elab_Term_addNamedArg___closed__1 = _init_l_Lean_Elab_Term_addNamedArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__1);
l_Lean_Elab_Term_addNamedArg___closed__2 = _init_l_Lean_Elab_Term_addNamedArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__2);
l_Lean_Elab_Term_addNamedArg___closed__3 = _init_l_Lean_Elab_Term_addNamedArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__3);
l_Lean_Elab_Term_addNamedArg___closed__4 = _init_l_Lean_Elab_Term_addNamedArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__4);
l_Lean_Elab_Term_addNamedArg___closed__5 = _init_l_Lean_Elab_Term_addNamedArg___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__5);
l_Lean_Elab_Term_addNamedArg___closed__6 = _init_l_Lean_Elab_Term_addNamedArg___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__6);
l___private_Lean_Elab_App_4__tryCoeFun___closed__1 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__1);
l___private_Lean_Elab_App_4__tryCoeFun___closed__2 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__2);
l___private_Lean_Elab_App_4__tryCoeFun___closed__3 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__3);
l___private_Lean_Elab_App_4__tryCoeFun___closed__4 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__4);
l___private_Lean_Elab_App_4__tryCoeFun___closed__5 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__5);
l___private_Lean_Elab_App_4__tryCoeFun___closed__6 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__6);
l___private_Lean_Elab_App_4__tryCoeFun___closed__7 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__7);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__2 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__2);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__4 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__4);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__7 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__7);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__8 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__8);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__10 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__10);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__11 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__11);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__13 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__13);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__14 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__14();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__14);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16);
l___private_Lean_Elab_App_11__elabAppArgs___closed__1 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__1);
l___private_Lean_Elab_App_11__elabAppArgs___closed__2 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__2);
l___private_Lean_Elab_App_11__elabAppArgs___closed__3 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__3);
l___private_Lean_Elab_App_11__elabAppArgs___closed__4 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__4);
l___private_Lean_Elab_App_11__elabAppArgs___closed__5 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__5);
l___private_Lean_Elab_App_11__elabAppArgs___closed__6 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__6);
l___private_Lean_Elab_App_11__elabAppArgs___closed__7 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__7);
l___private_Lean_Elab_App_11__elabAppArgs___closed__8 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__8);
l___private_Lean_Elab_App_11__elabAppArgs___closed__9 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__9);
l___private_Lean_Elab_App_11__elabAppArgs___closed__10 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__10);
l___private_Lean_Elab_App_11__elabAppArgs___closed__11 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__11);
l___private_Lean_Elab_App_13__resolveLValAux___closed__1 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__1);
l___private_Lean_Elab_App_13__resolveLValAux___closed__2 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__2);
l___private_Lean_Elab_App_13__resolveLValAux___closed__3 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__3);
l___private_Lean_Elab_App_13__resolveLValAux___closed__4 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__4);
l___private_Lean_Elab_App_13__resolveLValAux___closed__5 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__5);
l___private_Lean_Elab_App_13__resolveLValAux___closed__6 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__6);
l___private_Lean_Elab_App_13__resolveLValAux___closed__7 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__7);
l___private_Lean_Elab_App_13__resolveLValAux___closed__8 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__8);
l___private_Lean_Elab_App_13__resolveLValAux___closed__9 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__9);
l___private_Lean_Elab_App_13__resolveLValAux___closed__10 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__10);
l___private_Lean_Elab_App_13__resolveLValAux___closed__11 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__11);
l___private_Lean_Elab_App_13__resolveLValAux___closed__12 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__12);
l___private_Lean_Elab_App_13__resolveLValAux___closed__13 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__13();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__13);
l___private_Lean_Elab_App_13__resolveLValAux___closed__14 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__14();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__14);
l___private_Lean_Elab_App_13__resolveLValAux___closed__15 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__15();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__15);
l___private_Lean_Elab_App_13__resolveLValAux___closed__16 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__16();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__16);
l___private_Lean_Elab_App_13__resolveLValAux___closed__17 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__17();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__17);
l___private_Lean_Elab_App_13__resolveLValAux___closed__18 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__18();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__18);
l___private_Lean_Elab_App_13__resolveLValAux___closed__19 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__19();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__19);
l___private_Lean_Elab_App_13__resolveLValAux___closed__20 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__20();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__20);
l___private_Lean_Elab_App_13__resolveLValAux___closed__21 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__21();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__21);
l___private_Lean_Elab_App_13__resolveLValAux___closed__22 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__22();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__22);
l___private_Lean_Elab_App_13__resolveLValAux___closed__23 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__23();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__23);
l___private_Lean_Elab_App_13__resolveLValAux___closed__24 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__24();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__24);
l___private_Lean_Elab_App_13__resolveLValAux___closed__25 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__25();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__25);
l___private_Lean_Elab_App_13__resolveLValAux___closed__26 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__26();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__26);
l___private_Lean_Elab_App_13__resolveLValAux___closed__27 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__27();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__27);
l___private_Lean_Elab_App_13__resolveLValAux___closed__28 = _init_l___private_Lean_Elab_App_13__resolveLValAux___closed__28();
lean_mark_persistent(l___private_Lean_Elab_App_13__resolveLValAux___closed__28);
l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__1 = _init_l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__1);
l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2 = _init_l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2);
l___private_Lean_Elab_App_16__mkBaseProjections___closed__1 = _init_l___private_Lean_Elab_App_16__mkBaseProjections___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_16__mkBaseProjections___closed__1);
l___private_Lean_Elab_App_16__mkBaseProjections___closed__2 = _init_l___private_Lean_Elab_App_16__mkBaseProjections___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_16__mkBaseProjections___closed__2);
l___private_Lean_Elab_App_16__mkBaseProjections___closed__3 = _init_l___private_Lean_Elab_App_16__mkBaseProjections___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_16__mkBaseProjections___closed__3);
l___private_Lean_Elab_App_17__addLValArg___main___closed__1 = _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_17__addLValArg___main___closed__1);
l___private_Lean_Elab_App_17__addLValArg___main___closed__2 = _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_17__addLValArg___main___closed__2);
l___private_Lean_Elab_App_17__addLValArg___main___closed__3 = _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_17__addLValArg___main___closed__3);
l___private_Lean_Elab_App_17__addLValArg___main___closed__4 = _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_17__addLValArg___main___closed__4);
l___private_Lean_Elab_App_17__addLValArg___main___closed__5 = _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_17__addLValArg___main___closed__5);
l___private_Lean_Elab_App_17__addLValArg___main___closed__6 = _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_17__addLValArg___main___closed__6);
l___private_Lean_Elab_App_17__addLValArg___main___closed__7 = _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_17__addLValArg___main___closed__7);
l___private_Lean_Elab_App_17__addLValArg___main___closed__8 = _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_17__addLValArg___main___closed__8);
l___private_Lean_Elab_App_17__addLValArg___main___closed__9 = _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_17__addLValArg___main___closed__9);
l___private_Lean_Elab_App_17__addLValArg___main___closed__10 = _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_17__addLValArg___main___closed__10);
l___private_Lean_Elab_App_17__addLValArg___main___closed__11 = _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_17__addLValArg___main___closed__11);
l___private_Lean_Elab_App_17__addLValArg___main___closed__12 = _init_l___private_Lean_Elab_App_17__addLValArg___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_17__addLValArg___main___closed__12);
l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__1 = _init_l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__1);
l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2 = _init_l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2);
l___private_Lean_Elab_App_19__elabAppLVals___closed__1 = _init_l___private_Lean_Elab_App_19__elabAppLVals___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_19__elabAppLVals___closed__1);
l___private_Lean_Elab_App_19__elabAppLVals___closed__2 = _init_l___private_Lean_Elab_App_19__elabAppLVals___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_19__elabAppLVals___closed__2);
l___private_Lean_Elab_App_19__elabAppLVals___closed__3 = _init_l___private_Lean_Elab_App_19__elabAppLVals___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_19__elabAppLVals___closed__3);
l___private_Lean_Elab_App_23__toMessageData___closed__1 = _init_l___private_Lean_Elab_App_23__toMessageData___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_23__toMessageData___closed__1);
l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__1 = _init_l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__1);
l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__2 = _init_l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__2);
l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__3 = _init_l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_24__mergeFailures___rarg___closed__3);
l___private_Lean_Elab_App_25__elabAppAux___closed__1 = _init_l___private_Lean_Elab_App_25__elabAppAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_25__elabAppAux___closed__1);
l___private_Lean_Elab_App_25__elabAppAux___closed__2 = _init_l___private_Lean_Elab_App_25__elabAppAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_25__elabAppAux___closed__2);
l___private_Lean_Elab_App_25__elabAppAux___closed__3 = _init_l___private_Lean_Elab_App_25__elabAppAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_25__elabAppAux___closed__3);
l___private_Lean_Elab_App_26__expandApp___closed__1 = _init_l___private_Lean_Elab_App_26__expandApp___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_26__expandApp___closed__1);
l___regBuiltin_Lean_Elab_Term_elabApp___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabApp___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabApp___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabApp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabId___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabId___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabId___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabId(lean_io_mk_world());
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
l___regBuiltin_Lean_Elab_Term_elabRawIdent___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabRawIdent___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabRawIdent___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabRawIdent(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_App_27__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
