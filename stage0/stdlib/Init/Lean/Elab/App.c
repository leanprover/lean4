// Lean compiler output
// Module: Init.Lean.Elab.App
// Imports: Init.Lean.Util.FindMVar Init.Lean.Elab.Term Init.Lean.Elab.Binders
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
lean_object* l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__7;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__5;
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabSortApp(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_14__resolveLValLoop___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_14__resolveLValLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__10;
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__5;
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
lean_object* l___private_Init_Lean_Elab_App_24__mergeFailures(lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__8;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__4;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUniv___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind___closed__2;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elab_App_9__nextArgIsHole(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__2;
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__12;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_26__expandApp(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elab_App_21__elabAppFn___main___spec__1(lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_24__mergeFailures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_12__throwLValError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__20;
lean_object* l___private_Init_Lean_Elab_App_26__expandApp___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_26__expandApp___closed__1;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp___closed__1;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elab_App_6__hasTypeMVar(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__10;
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_17__addLValArg___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_24__mergeFailures___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__10;
lean_object* l___private_Init_Lean_Elab_App_14__resolveLValLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp(lean_object*);
extern lean_object* l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__1;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___boxed(lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__7;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_23__toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_19__elabAppLVals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_23__toMessageData___closed__1;
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__11;
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__11;
extern lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_25__elabAppAux___closed__3;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabId(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_19__elabAppLVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__6;
lean_object* l___private_Init_Lean_Elab_App_23__toMessageData___closed__2;
extern lean_object* l_Lean_Parser_Term_sort___elambda__1___closed__2;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabSortApp___closed__1;
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef(lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited;
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__4;
lean_object* l___private_Init_Lean_Elab_App_20__elabAppFnId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___private_Init_Lean_Elab_App_15__resolveLVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawIdent(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_12__throwLValError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l___private_Init_Lean_Elab_App_8__propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_repr___main___closed__13;
extern lean_object* l_Lean_Parser_Term_proj___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__9;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_5__getForallBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_26__expandApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__1;
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__17;
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName___rarg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__3;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__8;
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_App_23__toMessageData___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
extern lean_object* l_Lean_MessageData_Inhabited;
extern lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7;
lean_object* l_Array_filterAux___main___at___private_Init_Lean_Elab_App_22__getSuccess___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabId(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_15__resolveLVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__26;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__1;
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_App_20__elabAppFnId___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__3;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l_Lean_Syntax_replaceInfo___main(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkConst___closed__4;
lean_object* l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__2;
lean_object* l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__12;
lean_object* l_Lean_Elab_Term_Arg_hasToString(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_21__elabAppFn___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__19;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_26__expandApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__11;
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_5__getForallBody(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__1;
lean_object* l_List_map___main___at___private_Init_Lean_Elab_App_20__elabAppFnId___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabAtom(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__6;
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_18__elabAppLValsAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__23;
lean_object* l_Lean_Elab_Term_elabApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__1;
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_1__ensureArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_6__hasTypeMVar___boxed(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_25__elabAppAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_27__regTraceClasses(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_elabChoice(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_contains___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_21__elabAppFn___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__2;
lean_object* l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__2;
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_24__mergeFailures___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_App_14__resolveLValLoop___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_TermElabResult_inhabited;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
extern lean_object* l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
lean_object* l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_App_23__toMessageData___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__8;
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__7;
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_20__elabAppFnId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__10;
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabProj(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_25__elabAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__4;
lean_object* l_Lean_MessageData_ofArray(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_3__mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_App_14__resolveLValLoop___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__4;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__25;
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___main(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__6;
lean_object* l___private_Init_Lean_Elab_App_2__elabArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_21__elabAppFn___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__2;
extern lean_object* l_Lean_Meta_Exception_mkAppTypeMismatchMessage___closed__8;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___private_Init_Lean_Elab_App_22__getSuccess(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__4;
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__13;
lean_object* l___private_Init_Lean_Elab_App_25__elabAppAux___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__5;
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Elab_Term_elabSortApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_25__elabAppAux___closed__1;
lean_object* l_Lean_mkLevelSucc(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__9;
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabSortApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__27;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Elab_Term_registerSyntheticMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__14;
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__5;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__3;
extern lean_object* l_Lean_Parser_Term_paren___elambda__1___closed__1;
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_5__getForallBody___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__5;
lean_object* l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__5;
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_throwError___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabId___closed__1;
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__9;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__13;
lean_object* l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
lean_object* l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__1;
lean_object* l_Lean_Elab_Term_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__3;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__1;
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
lean_object* l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__3;
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_16__mkBaseProjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__3;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1;
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__8;
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__2;
lean_object* l___private_Init_Lean_Elab_App_16__mkBaseProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__15;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__18;
lean_object* l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__1;
lean_object* l_Lean_Elab_Term_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__5;
lean_object* l___private_Init_Lean_Elab_App_4__tryCoeFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData___main(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_23__toMessageData(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__1;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_9__nextArgIsHole___boxed(lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_5__getForallBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24;
lean_object* l___private_Init_Lean_Elab_App_14__resolveLValLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__7;
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_App_20__elabAppFnId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabRawIdent___closed__1;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__16;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__2;
extern lean_object* l_Lean_Meta_Exception_toStr___closed__6;
uint8_t l_Lean_Position_DecidableEq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__7;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
extern lean_object* l___private_Init_Lean_Elab_Util_4__regTraceClasses___closed__1;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyResult(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__2;
lean_object* l_Lean_Elab_Term_elabRawIdent(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_4__tryCoeFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_21__elabAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_17__addLValArg___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_12__throwLValError(lean_object*);
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__22;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__1;
lean_object* l___private_Init_Lean_Elab_App_18__elabAppLValsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__1;
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__11;
uint8_t l_Array_contains___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_repr___main___closed__16;
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__3;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__14;
lean_object* l_Lean_Elab_Term_ensureHasTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__28;
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__6;
lean_object* l___private_Init_Lean_Elab_App_21__elabAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_sortApp___elambda__1___closed__2;
lean_object* l_Lean_Name_components(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUniv___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__4;
lean_object* l_Lean_Elab_Term_elabFunCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_3__mkArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_21__elabAppFn___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__3;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_formatStxAux___main(x_3, x_4, x_2);
x_6 = l_Lean_Options_empty;
x_7 = l_Lean_Format_pretty(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_expr_dbg_to_string(x_8);
lean_dec(x_8);
return x_9;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_formatStxAux___main(x_11, x_12, x_10);
x_14 = l_Lean_Options_empty;
x_15 = l_Lean_Format_pretty(x_13, x_14);
x_16 = lean_string_append(x_8, x_15);
lean_dec(x_15);
x_17 = l_Option_HasRepr___rarg___closed__3;
x_18 = lean_string_append(x_16, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_expr_dbg_to_string(x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_8, x_20);
lean_dec(x_20);
x_22 = l_Option_HasRepr___rarg___closed__3;
x_23 = lean_string_append(x_21, x_22);
return x_23;
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(x_2, x_3, x_2, x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_array_push(x_2, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_2);
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
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_2, x_3);
lean_inc(x_4);
lean_inc(x_10);
x_11 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_10, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(0);
lean_inc(x_1);
x_16 = l_Lean_Elab_Term_registerSyntheticMVar(x_1, x_10, x_15, x_4, x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_3 = x_19;
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_3 = x_23;
x_5 = x_21;
goto _start;
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
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
lean_object* l___private_Init_Lean_Elab_App_1__ensureArgType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Init_Lean_Elab_App_2__elabArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_10 = l_Lean_Elab_Term_elabTerm(x_7, x_8, x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Init_Lean_Elab_App_1__ensureArgType(x_1, x_2, x_11, x_4, x_5, x_12);
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
x_19 = l___private_Init_Lean_Elab_App_1__ensureArgType(x_1, x_2, x_18, x_4, x_5, x_6);
return x_19;
}
}
}
lean_object* l___private_Init_Lean_Elab_App_3__mkArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Init_Lean_Elab_App_3__mkArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_App_3__mkArrow(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeFun");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toStr___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeFun");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__4;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_App_4__tryCoeFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l___private_Init_Lean_Elab_App_3__mkArrow(x_2, x_9, x_4, x_8);
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
x_25 = l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__2;
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
x_84 = l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__7;
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
x_74 = l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__4;
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
x_40 = l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__4;
x_41 = l_Lean_Elab_Term_throwError___rarg(x_1, x_40, x_4, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_4);
x_42 = l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__6;
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
lean_object* l___private_Init_Lean_Elab_App_4__tryCoeFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_App_4__tryCoeFun(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_5__getForallBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_Lean_Elab_App_5__getForallBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_5__getForallBody___main___spec__1(x_4, x_2, x_8);
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
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_5__getForallBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_5__getForallBody___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_App_5__getForallBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_App_5__getForallBody___main(x_1, x_2, x_3);
return x_4;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t l_Array_contains___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__2(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_Array_contains___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__1(x_5, x_4);
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
x_13 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__3(x_1, x_8, x_3);
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
x_21 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__3(x_1, x_16, x_3);
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
x_29 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__3(x_1, x_24, x_3);
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
x_44 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__3(x_1, x_32, x_3);
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
x_39 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__3(x_1, x_33, x_35);
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
uint8_t l___private_Init_Lean_Elab_App_6__hasTypeMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__3(x_1, x_2, x_3);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_contains___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_App_6__hasTypeMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Elab_App_6__hasTypeMVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_Array_contains___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__1(x_5, x_4);
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
x_13 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_8, x_3);
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
x_21 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_16, x_3);
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
x_29 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_24, x_3);
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
x_44 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_32, x_3);
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
x_39 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_33, x_35);
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
uint8_t l___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_2, x_3);
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
lean_object* l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_App_8__propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_18 = l___private_Init_Lean_Elab_App_5__getForallBody___main(x_16, x_17, x_2);
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
x_23 = l___private_Init_Lean_Elab_App_6__hasTypeMVar(x_1, x_21);
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
x_26 = l___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar(x_1, x_21);
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
uint8_t l___private_Init_Lean_Elab_App_9__nextArgIsHole(lean_object* x_1) {
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
lean_object* l___private_Init_Lean_Elab_App_9__nextArgIsHole___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_App_9__nextArgIsHole(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_array_fget(x_2, x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_fset(x_2, x_1, x_6);
x_8 = x_5;
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = x_9;
x_13 = lean_array_fset(x_7, x_1, x_12);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Lean_mkAppStx___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalize");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__1;
x_2 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit parameter '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is missing, unused named arguments ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid autoParam, argument must be a constant");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("begin");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__13;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__14;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_95 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_90, x_11, x_94);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = (uint8_t)((x_93 << 24) >> 61);
switch (x_96) {
case 0:
{
lean_object* x_97; uint8_t x_98; 
lean_inc(x_4);
lean_inc(x_1);
x_97 = l___private_Init_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_17);
x_98 = !lean_is_exclusive(x_1);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_1, 6);
lean_dec(x_99);
x_100 = lean_ctor_get(x_1, 5);
lean_dec(x_100);
x_101 = lean_ctor_get(x_1, 4);
lean_dec(x_101);
x_102 = lean_ctor_get(x_1, 3);
lean_dec(x_102);
x_103 = lean_ctor_get(x_1, 2);
lean_dec(x_103);
x_104 = lean_ctor_get(x_1, 1);
lean_dec(x_104);
x_105 = lean_ctor_get(x_1, 0);
lean_dec(x_105);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_106; uint8_t x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_97, 1);
lean_inc(x_106);
lean_dec(x_97);
x_107 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_107);
x_108 = lean_array_get_size(x_7);
x_109 = lean_nat_dec_lt(x_10, x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_110; 
x_110 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
x_111 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
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
x_114 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_115 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_117 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = x_11;
x_119 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_118);
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
x_128 = l_Lean_Elab_Term_throwError___rarg(x_6, x_127, x_4, x_106);
lean_dec(x_6);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
lean_dec(x_90);
lean_dec(x_11);
x_156 = l_Lean_Elab_Term_getOptions(x_4, x_106);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
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
else
{
lean_object* x_164; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_164 = lean_ctor_get(x_111, 0);
lean_inc(x_164);
lean_dec(x_111);
if (lean_obj_tag(x_164) == 4)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec(x_164);
x_166 = l_Lean_Elab_Term_getEnv___rarg(x_106);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l___private_Init_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_167, x_165);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_171, 0, x_170);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = l_Lean_Elab_Term_throwError___rarg(x_6, x_172, x_4, x_168);
lean_dec(x_6);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_174 = lean_ctor_get(x_169, 0);
lean_inc(x_174);
lean_dec(x_169);
x_175 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_168);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_177 = l_Lean_Elab_Term_getMainModule___rarg(x_176);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_179 = l_Lean_Syntax_getArgs(x_174);
lean_dec(x_174);
x_180 = l_Array_empty___closed__1;
x_181 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_179, x_179, x_94, x_180);
lean_dec(x_179);
x_182 = l_Lean_nullKind___closed__2;
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
x_184 = lean_array_push(x_180, x_183);
x_185 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_188 = lean_array_push(x_187, x_186);
x_189 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_190 = lean_array_push(x_188, x_189);
x_191 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
x_193 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_194 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_195 = lean_nat_sub(x_194, x_94);
lean_dec(x_194);
x_196 = lean_unsigned_to_nat(1u);
x_197 = lean_nat_sub(x_195, x_196);
lean_dec(x_195);
x_198 = l_Lean_Expr_getRevArg_x21___main(x_91, x_197);
lean_dec(x_91);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_199, 0, x_192);
lean_inc(x_4);
lean_inc(x_2);
x_200 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_199, x_198, x_4, x_178);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
lean_inc(x_201);
x_203 = l_Lean_mkApp(x_2, x_201);
x_204 = lean_expr_instantiate1(x_92, x_201);
lean_dec(x_201);
lean_dec(x_92);
x_2 = x_203;
x_3 = x_204;
x_5 = x_202;
goto _start;
}
else
{
uint8_t x_206; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_206 = !lean_is_exclusive(x_200);
if (x_206 == 0)
{
return x_200;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_200, 0);
x_208 = lean_ctor_get(x_200, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_200);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_193, 0);
lean_inc(x_210);
lean_dec(x_193);
x_211 = l_Lean_Syntax_replaceInfo___main(x_210, x_192);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_211);
lean_inc(x_4);
lean_inc(x_2);
x_213 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_212, x_198, x_4, x_178);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
lean_inc(x_214);
x_216 = l_Lean_mkApp(x_2, x_214);
x_217 = lean_expr_instantiate1(x_92, x_214);
lean_dec(x_214);
lean_dec(x_92);
x_2 = x_216;
x_3 = x_217;
x_5 = x_215;
goto _start;
}
else
{
uint8_t x_219; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_219 = !lean_is_exclusive(x_213);
if (x_219 == 0)
{
return x_213;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_213, 0);
x_221 = lean_ctor_get(x_213, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_213);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_164);
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_223 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_224 = l_Lean_Elab_Term_throwError___rarg(x_6, x_223, x_4, x_106);
lean_dec(x_6);
return x_224;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_225 = lean_ctor_get(x_110, 0);
lean_inc(x_225);
lean_dec(x_110);
lean_inc(x_225);
x_226 = l_Lean_mkApp(x_2, x_225);
x_227 = lean_expr_instantiate1(x_92, x_225);
lean_dec(x_225);
lean_dec(x_92);
x_2 = x_226;
x_3 = x_227;
x_5 = x_106;
goto _start;
}
}
else
{
uint8_t x_229; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
x_229 = l_Array_isEmpty___rarg(x_11);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_230 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_230, 0, x_90);
x_231 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_232 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
x_233 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_234 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = x_11;
x_236 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_235);
x_237 = x_236;
x_238 = l_Array_toList___rarg(x_237);
lean_dec(x_237);
x_239 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_238);
x_240 = l_Array_HasRepr___rarg___closed__1;
x_241 = lean_string_append(x_240, x_239);
lean_dec(x_239);
x_242 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_242, 0, x_241);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_242);
x_244 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_244, 0, x_234);
lean_ctor_set(x_244, 1, x_243);
x_245 = l_Lean_Elab_Term_throwError___rarg(x_6, x_244, x_4, x_106);
lean_dec(x_6);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
lean_dec(x_90);
lean_dec(x_11);
x_273 = l_Lean_Elab_Term_getOptions(x_4, x_106);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_277 = l_Lean_checkTraceOption(x_274, x_276);
lean_dec(x_274);
if (x_277 == 0)
{
x_246 = x_275;
goto block_272;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_inc(x_2);
x_278 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_278, 0, x_2);
x_279 = l_Lean_Elab_Term_logTrace(x_276, x_6, x_278, x_4, x_275);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_246 = x_280;
goto block_272;
}
block_272:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_247; 
lean_dec(x_3);
x_247 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_246);
lean_dec(x_12);
if (lean_obj_tag(x_247) == 0)
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_247);
if (x_248 == 0)
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_247, 0);
lean_dec(x_249);
lean_ctor_set(x_247, 0, x_2);
return x_247;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
lean_dec(x_247);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_2);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
else
{
uint8_t x_252; 
lean_dec(x_2);
x_252 = !lean_is_exclusive(x_247);
if (x_252 == 0)
{
return x_247;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_247, 0);
x_254 = lean_ctor_get(x_247, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_247);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
else
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_8, 0);
lean_inc(x_256);
lean_dec(x_8);
lean_inc(x_4);
x_257 = l_Lean_Elab_Term_isDefEq(x_6, x_256, x_3, x_4, x_246);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
lean_dec(x_257);
x_259 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_258);
lean_dec(x_12);
if (lean_obj_tag(x_259) == 0)
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_259, 0);
lean_dec(x_261);
lean_ctor_set(x_259, 0, x_2);
return x_259;
}
else
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_259, 1);
lean_inc(x_262);
lean_dec(x_259);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_2);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
else
{
uint8_t x_264; 
lean_dec(x_2);
x_264 = !lean_is_exclusive(x_259);
if (x_264 == 0)
{
return x_259;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_259, 0);
x_266 = lean_ctor_get(x_259, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_259);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
else
{
uint8_t x_268; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_268 = !lean_is_exclusive(x_257);
if (x_268 == 0)
{
return x_257;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_257, 0);
x_270 = lean_ctor_get(x_257, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_257);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
}
}
}
}
else
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_1);
lean_dec(x_90);
lean_dec(x_3);
x_281 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_282 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_281, x_91, x_4, x_106);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = lean_unsigned_to_nat(1u);
x_286 = lean_nat_add(x_10, x_285);
lean_dec(x_10);
x_287 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_287, 0, x_6);
lean_ctor_set(x_287, 1, x_7);
lean_ctor_set(x_287, 2, x_8);
lean_ctor_set(x_287, 3, x_286);
lean_ctor_set(x_287, 4, x_11);
lean_ctor_set(x_287, 5, x_12);
lean_ctor_set(x_287, 6, x_13);
lean_ctor_set_uint8(x_287, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_287, sizeof(void*)*7 + 1, x_107);
lean_inc(x_283);
x_288 = l_Lean_mkApp(x_2, x_283);
x_289 = lean_expr_instantiate1(x_92, x_283);
lean_dec(x_283);
lean_dec(x_92);
x_1 = x_287;
x_2 = x_288;
x_3 = x_289;
x_5 = x_284;
goto _start;
}
else
{
uint8_t x_291; 
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
x_291 = !lean_is_exclusive(x_282);
if (x_291 == 0)
{
return x_282;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_282, 0);
x_293 = lean_ctor_get(x_282, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_282);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
}
}
else
{
uint8_t x_295; 
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
x_295 = !lean_is_exclusive(x_97);
if (x_295 == 0)
{
return x_97;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_97, 0);
x_297 = lean_ctor_get(x_97, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_97);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_299; uint8_t x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_299 = lean_ctor_get(x_97, 1);
lean_inc(x_299);
lean_dec(x_97);
x_300 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_301 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_301, 0, x_6);
lean_ctor_set(x_301, 1, x_7);
lean_ctor_set(x_301, 2, x_8);
lean_ctor_set(x_301, 3, x_10);
lean_ctor_set(x_301, 4, x_11);
lean_ctor_set(x_301, 5, x_12);
lean_ctor_set(x_301, 6, x_13);
lean_ctor_set_uint8(x_301, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_301, sizeof(void*)*7 + 1, x_300);
x_302 = lean_array_get_size(x_7);
x_303 = lean_nat_dec_lt(x_10, x_302);
lean_dec(x_302);
if (x_303 == 0)
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
uint8_t x_306; 
lean_dec(x_301);
lean_dec(x_92);
lean_dec(x_91);
x_306 = l_Array_isEmpty___rarg(x_11);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_307 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_307, 0, x_90);
x_308 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_309 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_307);
x_310 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_311 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_312 = x_11;
x_313 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_312);
x_314 = x_313;
x_315 = l_Array_toList___rarg(x_314);
lean_dec(x_314);
x_316 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_315);
x_317 = l_Array_HasRepr___rarg___closed__1;
x_318 = lean_string_append(x_317, x_316);
lean_dec(x_316);
x_319 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_319, 0, x_318);
x_320 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_320, 0, x_319);
x_321 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_321, 0, x_311);
lean_ctor_set(x_321, 1, x_320);
x_322 = l_Lean_Elab_Term_throwError___rarg(x_6, x_321, x_4, x_299);
lean_dec(x_6);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; 
lean_dec(x_90);
lean_dec(x_11);
x_348 = l_Lean_Elab_Term_getOptions(x_4, x_299);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_352 = l_Lean_checkTraceOption(x_349, x_351);
lean_dec(x_349);
if (x_352 == 0)
{
x_323 = x_350;
goto block_347;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_inc(x_2);
x_353 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_353, 0, x_2);
x_354 = l_Lean_Elab_Term_logTrace(x_351, x_6, x_353, x_4, x_350);
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
lean_dec(x_354);
x_323 = x_355;
goto block_347;
}
block_347:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_324; 
lean_dec(x_3);
x_324 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_323);
lean_dec(x_12);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_324, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_326 = x_324;
} else {
 lean_dec_ref(x_324);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_2);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_2);
x_328 = lean_ctor_get(x_324, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_324, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_330 = x_324;
} else {
 lean_dec_ref(x_324);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_329);
return x_331;
}
}
else
{
lean_object* x_332; lean_object* x_333; 
x_332 = lean_ctor_get(x_8, 0);
lean_inc(x_332);
lean_dec(x_8);
lean_inc(x_4);
x_333 = l_Lean_Elab_Term_isDefEq(x_6, x_332, x_3, x_4, x_323);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
lean_dec(x_333);
x_335 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_334);
lean_dec(x_12);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_335, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_337 = x_335;
} else {
 lean_dec_ref(x_335);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_2);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_2);
x_339 = lean_ctor_get(x_335, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_335, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_341 = x_335;
} else {
 lean_dec_ref(x_335);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_339);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_343 = lean_ctor_get(x_333, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_333, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_345 = x_333;
} else {
 lean_dec_ref(x_333);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_344);
return x_346;
}
}
}
}
}
else
{
lean_object* x_356; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_356 = lean_ctor_get(x_305, 0);
lean_inc(x_356);
lean_dec(x_305);
if (lean_obj_tag(x_356) == 4)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
lean_dec(x_356);
x_358 = l_Lean_Elab_Term_getEnv___rarg(x_299);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_361 = l___private_Init_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_359, x_357);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_301);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
lean_dec(x_361);
x_363 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_363, 0, x_362);
x_364 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_364, 0, x_363);
x_365 = l_Lean_Elab_Term_throwError___rarg(x_6, x_364, x_4, x_360);
lean_dec(x_6);
return x_365;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_366 = lean_ctor_get(x_361, 0);
lean_inc(x_366);
lean_dec(x_361);
x_367 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_360);
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
lean_dec(x_367);
x_369 = l_Lean_Elab_Term_getMainModule___rarg(x_368);
x_370 = lean_ctor_get(x_369, 1);
lean_inc(x_370);
lean_dec(x_369);
x_371 = l_Lean_Syntax_getArgs(x_366);
lean_dec(x_366);
x_372 = l_Array_empty___closed__1;
x_373 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_371, x_371, x_94, x_372);
lean_dec(x_371);
x_374 = l_Lean_nullKind___closed__2;
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_373);
x_376 = lean_array_push(x_372, x_375);
x_377 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_376);
x_379 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_380 = lean_array_push(x_379, x_378);
x_381 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_382 = lean_array_push(x_380, x_381);
x_383 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_382);
x_385 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_386 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_387 = lean_nat_sub(x_386, x_94);
lean_dec(x_386);
x_388 = lean_unsigned_to_nat(1u);
x_389 = lean_nat_sub(x_387, x_388);
lean_dec(x_387);
x_390 = l_Lean_Expr_getRevArg_x21___main(x_91, x_389);
lean_dec(x_91);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_391, 0, x_384);
lean_inc(x_4);
lean_inc(x_2);
x_392 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_391, x_390, x_4, x_370);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
lean_inc(x_393);
x_395 = l_Lean_mkApp(x_2, x_393);
x_396 = lean_expr_instantiate1(x_92, x_393);
lean_dec(x_393);
lean_dec(x_92);
x_1 = x_301;
x_2 = x_395;
x_3 = x_396;
x_5 = x_394;
goto _start;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_301);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_398 = lean_ctor_get(x_392, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_392, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_400 = x_392;
} else {
 lean_dec_ref(x_392);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_398);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_402 = lean_ctor_get(x_385, 0);
lean_inc(x_402);
lean_dec(x_385);
x_403 = l_Lean_Syntax_replaceInfo___main(x_402, x_384);
x_404 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_404, 0, x_403);
lean_inc(x_4);
lean_inc(x_2);
x_405 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_404, x_390, x_4, x_370);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
lean_inc(x_406);
x_408 = l_Lean_mkApp(x_2, x_406);
x_409 = lean_expr_instantiate1(x_92, x_406);
lean_dec(x_406);
lean_dec(x_92);
x_1 = x_301;
x_2 = x_408;
x_3 = x_409;
x_5 = x_407;
goto _start;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_301);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_411 = lean_ctor_get(x_405, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_405, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_413 = x_405;
} else {
 lean_dec_ref(x_405);
 x_413 = lean_box(0);
}
if (lean_is_scalar(x_413)) {
 x_414 = lean_alloc_ctor(1, 2, 0);
} else {
 x_414 = x_413;
}
lean_ctor_set(x_414, 0, x_411);
lean_ctor_set(x_414, 1, x_412);
return x_414;
}
}
}
}
else
{
lean_object* x_415; lean_object* x_416; 
lean_dec(x_356);
lean_dec(x_301);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_415 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_416 = l_Lean_Elab_Term_throwError___rarg(x_6, x_415, x_4, x_299);
lean_dec(x_6);
return x_416;
}
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_417 = lean_ctor_get(x_304, 0);
lean_inc(x_417);
lean_dec(x_304);
lean_inc(x_417);
x_418 = l_Lean_mkApp(x_2, x_417);
x_419 = lean_expr_instantiate1(x_92, x_417);
lean_dec(x_417);
lean_dec(x_92);
x_1 = x_301;
x_2 = x_418;
x_3 = x_419;
x_5 = x_299;
goto _start;
}
}
else
{
uint8_t x_421; 
lean_dec(x_301);
lean_dec(x_92);
lean_dec(x_91);
x_421 = l_Array_isEmpty___rarg(x_11);
if (x_421 == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_422 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_422, 0, x_90);
x_423 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_424 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_422);
x_425 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_426 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
x_427 = x_11;
x_428 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_427);
x_429 = x_428;
x_430 = l_Array_toList___rarg(x_429);
lean_dec(x_429);
x_431 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_430);
x_432 = l_Array_HasRepr___rarg___closed__1;
x_433 = lean_string_append(x_432, x_431);
lean_dec(x_431);
x_434 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_434, 0, x_433);
x_435 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_435, 0, x_434);
x_436 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_436, 0, x_426);
lean_ctor_set(x_436, 1, x_435);
x_437 = l_Lean_Elab_Term_throwError___rarg(x_6, x_436, x_4, x_299);
lean_dec(x_6);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; 
lean_dec(x_90);
lean_dec(x_11);
x_463 = l_Lean_Elab_Term_getOptions(x_4, x_299);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
x_466 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_467 = l_Lean_checkTraceOption(x_464, x_466);
lean_dec(x_464);
if (x_467 == 0)
{
x_438 = x_465;
goto block_462;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_inc(x_2);
x_468 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_468, 0, x_2);
x_469 = l_Lean_Elab_Term_logTrace(x_466, x_6, x_468, x_4, x_465);
x_470 = lean_ctor_get(x_469, 1);
lean_inc(x_470);
lean_dec(x_469);
x_438 = x_470;
goto block_462;
}
block_462:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_439; 
lean_dec(x_3);
x_439 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_438);
lean_dec(x_12);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_439, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_441 = x_439;
} else {
 lean_dec_ref(x_439);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_2);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_2);
x_443 = lean_ctor_get(x_439, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_439, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_445 = x_439;
} else {
 lean_dec_ref(x_439);
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
else
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_8, 0);
lean_inc(x_447);
lean_dec(x_8);
lean_inc(x_4);
x_448 = l_Lean_Elab_Term_isDefEq(x_6, x_447, x_3, x_4, x_438);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_ctor_get(x_448, 1);
lean_inc(x_449);
lean_dec(x_448);
x_450 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_449);
lean_dec(x_12);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_452 = x_450;
} else {
 lean_dec_ref(x_450);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(0, 2, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_2);
lean_ctor_set(x_453, 1, x_451);
return x_453;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_2);
x_454 = lean_ctor_get(x_450, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_450, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_456 = x_450;
} else {
 lean_dec_ref(x_450);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(1, 2, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_454);
lean_ctor_set(x_457, 1, x_455);
return x_457;
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_458 = lean_ctor_get(x_448, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_448, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 x_460 = x_448;
} else {
 lean_dec_ref(x_448);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(1, 2, 0);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_458);
lean_ctor_set(x_461, 1, x_459);
return x_461;
}
}
}
}
}
}
else
{
lean_object* x_471; lean_object* x_472; 
lean_dec(x_301);
lean_dec(x_90);
lean_dec(x_3);
x_471 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_472 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_471, x_91, x_4, x_299);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
lean_dec(x_472);
x_475 = lean_unsigned_to_nat(1u);
x_476 = lean_nat_add(x_10, x_475);
lean_dec(x_10);
x_477 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_477, 0, x_6);
lean_ctor_set(x_477, 1, x_7);
lean_ctor_set(x_477, 2, x_8);
lean_ctor_set(x_477, 3, x_476);
lean_ctor_set(x_477, 4, x_11);
lean_ctor_set(x_477, 5, x_12);
lean_ctor_set(x_477, 6, x_13);
lean_ctor_set_uint8(x_477, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_477, sizeof(void*)*7 + 1, x_300);
lean_inc(x_473);
x_478 = l_Lean_mkApp(x_2, x_473);
x_479 = lean_expr_instantiate1(x_92, x_473);
lean_dec(x_473);
lean_dec(x_92);
x_1 = x_477;
x_2 = x_478;
x_3 = x_479;
x_5 = x_474;
goto _start;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
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
x_481 = lean_ctor_get(x_472, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_472, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_483 = x_472;
} else {
 lean_dec_ref(x_472);
 x_483 = lean_box(0);
}
if (lean_is_scalar(x_483)) {
 x_484 = lean_alloc_ctor(1, 2, 0);
} else {
 x_484 = x_483;
}
lean_ctor_set(x_484, 0, x_481);
lean_ctor_set(x_484, 1, x_482);
return x_484;
}
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
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
x_485 = lean_ctor_get(x_97, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_97, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_487 = x_97;
} else {
 lean_dec_ref(x_97);
 x_487 = lean_box(0);
}
if (lean_is_scalar(x_487)) {
 x_488 = lean_alloc_ctor(1, 2, 0);
} else {
 x_488 = x_487;
}
lean_ctor_set(x_488, 0, x_485);
lean_ctor_set(x_488, 1, x_486);
return x_488;
}
}
}
case 1:
{
if (x_9 == 0)
{
uint8_t x_489; 
lean_dec(x_90);
lean_dec(x_16);
lean_dec(x_3);
x_489 = !lean_is_exclusive(x_1);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_490 = lean_ctor_get(x_1, 6);
lean_dec(x_490);
x_491 = lean_ctor_get(x_1, 5);
lean_dec(x_491);
x_492 = lean_ctor_get(x_1, 4);
lean_dec(x_492);
x_493 = lean_ctor_get(x_1, 3);
lean_dec(x_493);
x_494 = lean_ctor_get(x_1, 2);
lean_dec(x_494);
x_495 = lean_ctor_get(x_1, 1);
lean_dec(x_495);
x_496 = lean_ctor_get(x_1, 0);
lean_dec(x_496);
x_497 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_497, 0, x_91);
x_498 = 0;
x_499 = lean_box(0);
lean_inc(x_4);
x_500 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_497, x_498, x_499, x_4, x_17);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
lean_inc(x_4);
lean_inc(x_501);
x_503 = l_Lean_Elab_Term_isTypeFormer(x_6, x_501, x_4, x_502);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; uint8_t x_505; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_unbox(x_504);
lean_dec(x_504);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_506 = lean_ctor_get(x_503, 1);
lean_inc(x_506);
lean_dec(x_503);
lean_inc(x_501);
x_507 = l_Lean_mkApp(x_2, x_501);
x_508 = lean_expr_instantiate1(x_92, x_501);
lean_dec(x_501);
lean_dec(x_92);
x_2 = x_507;
x_3 = x_508;
x_5 = x_506;
goto _start;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_510 = lean_ctor_get(x_503, 1);
lean_inc(x_510);
lean_dec(x_503);
x_511 = l_Lean_Expr_mvarId_x21(x_501);
x_512 = lean_array_push(x_13, x_511);
lean_ctor_set(x_1, 6, x_512);
lean_inc(x_501);
x_513 = l_Lean_mkApp(x_2, x_501);
x_514 = lean_expr_instantiate1(x_92, x_501);
lean_dec(x_501);
lean_dec(x_92);
x_2 = x_513;
x_3 = x_514;
x_5 = x_510;
goto _start;
}
}
else
{
uint8_t x_516; 
lean_dec(x_501);
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
x_516 = !lean_is_exclusive(x_503);
if (x_516 == 0)
{
return x_503;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_503, 0);
x_518 = lean_ctor_get(x_503, 1);
lean_inc(x_518);
lean_inc(x_517);
lean_dec(x_503);
x_519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_518);
return x_519;
}
}
}
else
{
lean_object* x_520; uint8_t x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
lean_dec(x_1);
x_520 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_520, 0, x_91);
x_521 = 0;
x_522 = lean_box(0);
lean_inc(x_4);
x_523 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_520, x_521, x_522, x_4, x_17);
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 1);
lean_inc(x_525);
lean_dec(x_523);
lean_inc(x_4);
lean_inc(x_524);
x_526 = l_Lean_Elab_Term_isTypeFormer(x_6, x_524, x_4, x_525);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; uint8_t x_528; 
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
x_528 = lean_unbox(x_527);
lean_dec(x_527);
if (x_528 == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_529 = lean_ctor_get(x_526, 1);
lean_inc(x_529);
lean_dec(x_526);
x_530 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_530, 0, x_6);
lean_ctor_set(x_530, 1, x_7);
lean_ctor_set(x_530, 2, x_8);
lean_ctor_set(x_530, 3, x_10);
lean_ctor_set(x_530, 4, x_11);
lean_ctor_set(x_530, 5, x_12);
lean_ctor_set(x_530, 6, x_13);
lean_ctor_set_uint8(x_530, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_530, sizeof(void*)*7 + 1, x_14);
lean_inc(x_524);
x_531 = l_Lean_mkApp(x_2, x_524);
x_532 = lean_expr_instantiate1(x_92, x_524);
lean_dec(x_524);
lean_dec(x_92);
x_1 = x_530;
x_2 = x_531;
x_3 = x_532;
x_5 = x_529;
goto _start;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_534 = lean_ctor_get(x_526, 1);
lean_inc(x_534);
lean_dec(x_526);
x_535 = l_Lean_Expr_mvarId_x21(x_524);
x_536 = lean_array_push(x_13, x_535);
x_537 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_537, 0, x_6);
lean_ctor_set(x_537, 1, x_7);
lean_ctor_set(x_537, 2, x_8);
lean_ctor_set(x_537, 3, x_10);
lean_ctor_set(x_537, 4, x_11);
lean_ctor_set(x_537, 5, x_12);
lean_ctor_set(x_537, 6, x_536);
lean_ctor_set_uint8(x_537, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_537, sizeof(void*)*7 + 1, x_14);
lean_inc(x_524);
x_538 = l_Lean_mkApp(x_2, x_524);
x_539 = lean_expr_instantiate1(x_92, x_524);
lean_dec(x_524);
lean_dec(x_92);
x_1 = x_537;
x_2 = x_538;
x_3 = x_539;
x_5 = x_534;
goto _start;
}
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
lean_dec(x_524);
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
x_541 = lean_ctor_get(x_526, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_526, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_543 = x_526;
} else {
 lean_dec_ref(x_526);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(1, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_541);
lean_ctor_set(x_544, 1, x_542);
return x_544;
}
}
}
else
{
lean_object* x_545; uint8_t x_546; 
lean_inc(x_4);
lean_inc(x_1);
x_545 = l___private_Init_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_17);
x_546 = !lean_is_exclusive(x_1);
if (x_546 == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_547 = lean_ctor_get(x_1, 6);
lean_dec(x_547);
x_548 = lean_ctor_get(x_1, 5);
lean_dec(x_548);
x_549 = lean_ctor_get(x_1, 4);
lean_dec(x_549);
x_550 = lean_ctor_get(x_1, 3);
lean_dec(x_550);
x_551 = lean_ctor_get(x_1, 2);
lean_dec(x_551);
x_552 = lean_ctor_get(x_1, 1);
lean_dec(x_552);
x_553 = lean_ctor_get(x_1, 0);
lean_dec(x_553);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_554; lean_object* x_555; uint8_t x_556; 
x_554 = lean_ctor_get(x_545, 1);
lean_inc(x_554);
lean_dec(x_545);
x_555 = lean_array_get_size(x_7);
x_556 = lean_nat_dec_lt(x_10, x_555);
lean_dec(x_555);
if (x_556 == 0)
{
uint8_t x_557; 
lean_free_object(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
x_557 = l_Array_isEmpty___rarg(x_11);
if (x_557 == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_558 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_558, 0, x_90);
x_559 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_560 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_560, 0, x_559);
lean_ctor_set(x_560, 1, x_558);
x_561 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_562 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_562, 0, x_560);
lean_ctor_set(x_562, 1, x_561);
x_563 = x_11;
x_564 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_563);
x_565 = x_564;
x_566 = l_Array_toList___rarg(x_565);
lean_dec(x_565);
x_567 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_566);
x_568 = l_Array_HasRepr___rarg___closed__1;
x_569 = lean_string_append(x_568, x_567);
lean_dec(x_567);
x_570 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_570, 0, x_569);
x_571 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_571, 0, x_570);
x_572 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_572, 0, x_562);
lean_ctor_set(x_572, 1, x_571);
x_573 = l_Lean_Elab_Term_throwError___rarg(x_6, x_572, x_4, x_554);
lean_dec(x_6);
return x_573;
}
else
{
lean_object* x_574; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; uint8_t x_605; 
lean_dec(x_90);
lean_dec(x_11);
x_601 = l_Lean_Elab_Term_getOptions(x_4, x_554);
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
lean_dec(x_601);
x_604 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_605 = l_Lean_checkTraceOption(x_602, x_604);
lean_dec(x_602);
if (x_605 == 0)
{
x_574 = x_603;
goto block_600;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
lean_inc(x_2);
x_606 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_606, 0, x_2);
x_607 = l_Lean_Elab_Term_logTrace(x_604, x_6, x_606, x_4, x_603);
x_608 = lean_ctor_get(x_607, 1);
lean_inc(x_608);
lean_dec(x_607);
x_574 = x_608;
goto block_600;
}
block_600:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_575; 
lean_dec(x_3);
x_575 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_574);
lean_dec(x_12);
if (lean_obj_tag(x_575) == 0)
{
uint8_t x_576; 
x_576 = !lean_is_exclusive(x_575);
if (x_576 == 0)
{
lean_object* x_577; 
x_577 = lean_ctor_get(x_575, 0);
lean_dec(x_577);
lean_ctor_set(x_575, 0, x_2);
return x_575;
}
else
{
lean_object* x_578; lean_object* x_579; 
x_578 = lean_ctor_get(x_575, 1);
lean_inc(x_578);
lean_dec(x_575);
x_579 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_579, 0, x_2);
lean_ctor_set(x_579, 1, x_578);
return x_579;
}
}
else
{
uint8_t x_580; 
lean_dec(x_2);
x_580 = !lean_is_exclusive(x_575);
if (x_580 == 0)
{
return x_575;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_581 = lean_ctor_get(x_575, 0);
x_582 = lean_ctor_get(x_575, 1);
lean_inc(x_582);
lean_inc(x_581);
lean_dec(x_575);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_581);
lean_ctor_set(x_583, 1, x_582);
return x_583;
}
}
}
else
{
lean_object* x_584; lean_object* x_585; 
x_584 = lean_ctor_get(x_8, 0);
lean_inc(x_584);
lean_dec(x_8);
lean_inc(x_4);
x_585 = l_Lean_Elab_Term_isDefEq(x_6, x_584, x_3, x_4, x_574);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; lean_object* x_587; 
x_586 = lean_ctor_get(x_585, 1);
lean_inc(x_586);
lean_dec(x_585);
x_587 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_586);
lean_dec(x_12);
if (lean_obj_tag(x_587) == 0)
{
uint8_t x_588; 
x_588 = !lean_is_exclusive(x_587);
if (x_588 == 0)
{
lean_object* x_589; 
x_589 = lean_ctor_get(x_587, 0);
lean_dec(x_589);
lean_ctor_set(x_587, 0, x_2);
return x_587;
}
else
{
lean_object* x_590; lean_object* x_591; 
x_590 = lean_ctor_get(x_587, 1);
lean_inc(x_590);
lean_dec(x_587);
x_591 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_591, 0, x_2);
lean_ctor_set(x_591, 1, x_590);
return x_591;
}
}
else
{
uint8_t x_592; 
lean_dec(x_2);
x_592 = !lean_is_exclusive(x_587);
if (x_592 == 0)
{
return x_587;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_593 = lean_ctor_get(x_587, 0);
x_594 = lean_ctor_get(x_587, 1);
lean_inc(x_594);
lean_inc(x_593);
lean_dec(x_587);
x_595 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_595, 0, x_593);
lean_ctor_set(x_595, 1, x_594);
return x_595;
}
}
}
else
{
uint8_t x_596; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_596 = !lean_is_exclusive(x_585);
if (x_596 == 0)
{
return x_585;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_585, 0);
x_598 = lean_ctor_get(x_585, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_585);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
}
}
}
}
else
{
lean_object* x_609; lean_object* x_610; 
lean_dec(x_90);
lean_dec(x_3);
x_609 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_610 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_609, x_91, x_4, x_554);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; lean_object* x_616; lean_object* x_617; 
x_611 = lean_ctor_get(x_610, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_610, 1);
lean_inc(x_612);
lean_dec(x_610);
x_613 = lean_unsigned_to_nat(1u);
x_614 = lean_nat_add(x_10, x_613);
lean_dec(x_10);
x_615 = 1;
lean_ctor_set(x_1, 3, x_614);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_615);
lean_inc(x_611);
x_616 = l_Lean_mkApp(x_2, x_611);
x_617 = lean_expr_instantiate1(x_92, x_611);
lean_dec(x_611);
lean_dec(x_92);
x_2 = x_616;
x_3 = x_617;
x_5 = x_612;
goto _start;
}
else
{
uint8_t x_619; 
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
x_619 = !lean_is_exclusive(x_610);
if (x_619 == 0)
{
return x_610;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_ctor_get(x_610, 0);
x_621 = lean_ctor_get(x_610, 1);
lean_inc(x_621);
lean_inc(x_620);
lean_dec(x_610);
x_622 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_622, 0, x_620);
lean_ctor_set(x_622, 1, x_621);
return x_622;
}
}
}
}
else
{
uint8_t x_623; 
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
x_623 = !lean_is_exclusive(x_545);
if (x_623 == 0)
{
return x_545;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_624 = lean_ctor_get(x_545, 0);
x_625 = lean_ctor_get(x_545, 1);
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_545);
x_626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_626, 0, x_624);
lean_ctor_set(x_626, 1, x_625);
return x_626;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_627; lean_object* x_628; uint8_t x_629; 
x_627 = lean_ctor_get(x_545, 1);
lean_inc(x_627);
lean_dec(x_545);
x_628 = lean_array_get_size(x_7);
x_629 = lean_nat_dec_lt(x_10, x_628);
lean_dec(x_628);
if (x_629 == 0)
{
uint8_t x_630; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
x_630 = l_Array_isEmpty___rarg(x_11);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_631 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_631, 0, x_90);
x_632 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_633 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_633, 0, x_632);
lean_ctor_set(x_633, 1, x_631);
x_634 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_635 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_634);
x_636 = x_11;
x_637 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_636);
x_638 = x_637;
x_639 = l_Array_toList___rarg(x_638);
lean_dec(x_638);
x_640 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_639);
x_641 = l_Array_HasRepr___rarg___closed__1;
x_642 = lean_string_append(x_641, x_640);
lean_dec(x_640);
x_643 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_643, 0, x_642);
x_644 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_644, 0, x_643);
x_645 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_645, 0, x_635);
lean_ctor_set(x_645, 1, x_644);
x_646 = l_Lean_Elab_Term_throwError___rarg(x_6, x_645, x_4, x_627);
lean_dec(x_6);
return x_646;
}
else
{
lean_object* x_647; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; 
lean_dec(x_90);
lean_dec(x_11);
x_672 = l_Lean_Elab_Term_getOptions(x_4, x_627);
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
lean_dec(x_672);
x_675 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_676 = l_Lean_checkTraceOption(x_673, x_675);
lean_dec(x_673);
if (x_676 == 0)
{
x_647 = x_674;
goto block_671;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
lean_inc(x_2);
x_677 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_677, 0, x_2);
x_678 = l_Lean_Elab_Term_logTrace(x_675, x_6, x_677, x_4, x_674);
x_679 = lean_ctor_get(x_678, 1);
lean_inc(x_679);
lean_dec(x_678);
x_647 = x_679;
goto block_671;
}
block_671:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_648; 
lean_dec(x_3);
x_648 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_647);
lean_dec(x_12);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_649 = lean_ctor_get(x_648, 1);
lean_inc(x_649);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_650 = x_648;
} else {
 lean_dec_ref(x_648);
 x_650 = lean_box(0);
}
if (lean_is_scalar(x_650)) {
 x_651 = lean_alloc_ctor(0, 2, 0);
} else {
 x_651 = x_650;
}
lean_ctor_set(x_651, 0, x_2);
lean_ctor_set(x_651, 1, x_649);
return x_651;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec(x_2);
x_652 = lean_ctor_get(x_648, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_648, 1);
lean_inc(x_653);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_654 = x_648;
} else {
 lean_dec_ref(x_648);
 x_654 = lean_box(0);
}
if (lean_is_scalar(x_654)) {
 x_655 = lean_alloc_ctor(1, 2, 0);
} else {
 x_655 = x_654;
}
lean_ctor_set(x_655, 0, x_652);
lean_ctor_set(x_655, 1, x_653);
return x_655;
}
}
else
{
lean_object* x_656; lean_object* x_657; 
x_656 = lean_ctor_get(x_8, 0);
lean_inc(x_656);
lean_dec(x_8);
lean_inc(x_4);
x_657 = l_Lean_Elab_Term_isDefEq(x_6, x_656, x_3, x_4, x_647);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; lean_object* x_659; 
x_658 = lean_ctor_get(x_657, 1);
lean_inc(x_658);
lean_dec(x_657);
x_659 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_658);
lean_dec(x_12);
if (lean_obj_tag(x_659) == 0)
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; 
x_660 = lean_ctor_get(x_659, 1);
lean_inc(x_660);
if (lean_is_exclusive(x_659)) {
 lean_ctor_release(x_659, 0);
 lean_ctor_release(x_659, 1);
 x_661 = x_659;
} else {
 lean_dec_ref(x_659);
 x_661 = lean_box(0);
}
if (lean_is_scalar(x_661)) {
 x_662 = lean_alloc_ctor(0, 2, 0);
} else {
 x_662 = x_661;
}
lean_ctor_set(x_662, 0, x_2);
lean_ctor_set(x_662, 1, x_660);
return x_662;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
lean_dec(x_2);
x_663 = lean_ctor_get(x_659, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_659, 1);
lean_inc(x_664);
if (lean_is_exclusive(x_659)) {
 lean_ctor_release(x_659, 0);
 lean_ctor_release(x_659, 1);
 x_665 = x_659;
} else {
 lean_dec_ref(x_659);
 x_665 = lean_box(0);
}
if (lean_is_scalar(x_665)) {
 x_666 = lean_alloc_ctor(1, 2, 0);
} else {
 x_666 = x_665;
}
lean_ctor_set(x_666, 0, x_663);
lean_ctor_set(x_666, 1, x_664);
return x_666;
}
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_667 = lean_ctor_get(x_657, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_657, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 x_669 = x_657;
} else {
 lean_dec_ref(x_657);
 x_669 = lean_box(0);
}
if (lean_is_scalar(x_669)) {
 x_670 = lean_alloc_ctor(1, 2, 0);
} else {
 x_670 = x_669;
}
lean_ctor_set(x_670, 0, x_667);
lean_ctor_set(x_670, 1, x_668);
return x_670;
}
}
}
}
}
else
{
lean_object* x_680; lean_object* x_681; 
lean_dec(x_90);
lean_dec(x_3);
x_680 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_681 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_680, x_91, x_4, x_627);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; uint8_t x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
lean_dec(x_681);
x_684 = lean_unsigned_to_nat(1u);
x_685 = lean_nat_add(x_10, x_684);
lean_dec(x_10);
x_686 = 1;
x_687 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_687, 0, x_6);
lean_ctor_set(x_687, 1, x_7);
lean_ctor_set(x_687, 2, x_8);
lean_ctor_set(x_687, 3, x_685);
lean_ctor_set(x_687, 4, x_11);
lean_ctor_set(x_687, 5, x_12);
lean_ctor_set(x_687, 6, x_13);
lean_ctor_set_uint8(x_687, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_687, sizeof(void*)*7 + 1, x_686);
lean_inc(x_682);
x_688 = l_Lean_mkApp(x_2, x_682);
x_689 = lean_expr_instantiate1(x_92, x_682);
lean_dec(x_682);
lean_dec(x_92);
x_1 = x_687;
x_2 = x_688;
x_3 = x_689;
x_5 = x_683;
goto _start;
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
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
x_691 = lean_ctor_get(x_681, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_681, 1);
lean_inc(x_692);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_693 = x_681;
} else {
 lean_dec_ref(x_681);
 x_693 = lean_box(0);
}
if (lean_is_scalar(x_693)) {
 x_694 = lean_alloc_ctor(1, 2, 0);
} else {
 x_694 = x_693;
}
lean_ctor_set(x_694, 0, x_691);
lean_ctor_set(x_694, 1, x_692);
return x_694;
}
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
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
x_695 = lean_ctor_get(x_545, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_545, 1);
lean_inc(x_696);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_697 = x_545;
} else {
 lean_dec_ref(x_545);
 x_697 = lean_box(0);
}
if (lean_is_scalar(x_697)) {
 x_698 = lean_alloc_ctor(1, 2, 0);
} else {
 x_698 = x_697;
}
lean_ctor_set(x_698, 0, x_695);
lean_ctor_set(x_698, 1, x_696);
return x_698;
}
}
}
}
case 2:
{
lean_object* x_699; uint8_t x_700; 
lean_inc(x_4);
lean_inc(x_1);
x_699 = l___private_Init_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_17);
x_700 = !lean_is_exclusive(x_1);
if (x_700 == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_701 = lean_ctor_get(x_1, 6);
lean_dec(x_701);
x_702 = lean_ctor_get(x_1, 5);
lean_dec(x_702);
x_703 = lean_ctor_get(x_1, 4);
lean_dec(x_703);
x_704 = lean_ctor_get(x_1, 3);
lean_dec(x_704);
x_705 = lean_ctor_get(x_1, 2);
lean_dec(x_705);
x_706 = lean_ctor_get(x_1, 1);
lean_dec(x_706);
x_707 = lean_ctor_get(x_1, 0);
lean_dec(x_707);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_708; uint8_t x_709; lean_object* x_710; uint8_t x_711; 
x_708 = lean_ctor_get(x_699, 1);
lean_inc(x_708);
lean_dec(x_699);
x_709 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_709);
x_710 = lean_array_get_size(x_7);
x_711 = lean_nat_dec_lt(x_10, x_710);
lean_dec(x_710);
if (x_711 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_712; 
x_712 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; 
x_713 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_713) == 0)
{
uint8_t x_714; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
x_714 = l_Array_isEmpty___rarg(x_11);
if (x_714 == 0)
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_715 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_715, 0, x_90);
x_716 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_717 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_717, 0, x_716);
lean_ctor_set(x_717, 1, x_715);
x_718 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_719 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_719, 0, x_717);
lean_ctor_set(x_719, 1, x_718);
x_720 = x_11;
x_721 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_720);
x_722 = x_721;
x_723 = l_Array_toList___rarg(x_722);
lean_dec(x_722);
x_724 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_723);
x_725 = l_Array_HasRepr___rarg___closed__1;
x_726 = lean_string_append(x_725, x_724);
lean_dec(x_724);
x_727 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_727, 0, x_726);
x_728 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_728, 0, x_727);
x_729 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_729, 0, x_719);
lean_ctor_set(x_729, 1, x_728);
x_730 = l_Lean_Elab_Term_throwError___rarg(x_6, x_729, x_4, x_708);
lean_dec(x_6);
return x_730;
}
else
{
lean_object* x_731; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; uint8_t x_762; 
lean_dec(x_90);
lean_dec(x_11);
x_758 = l_Lean_Elab_Term_getOptions(x_4, x_708);
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec(x_758);
x_761 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_762 = l_Lean_checkTraceOption(x_759, x_761);
lean_dec(x_759);
if (x_762 == 0)
{
x_731 = x_760;
goto block_757;
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; 
lean_inc(x_2);
x_763 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_763, 0, x_2);
x_764 = l_Lean_Elab_Term_logTrace(x_761, x_6, x_763, x_4, x_760);
x_765 = lean_ctor_get(x_764, 1);
lean_inc(x_765);
lean_dec(x_764);
x_731 = x_765;
goto block_757;
}
block_757:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_732; 
lean_dec(x_3);
x_732 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_731);
lean_dec(x_12);
if (lean_obj_tag(x_732) == 0)
{
uint8_t x_733; 
x_733 = !lean_is_exclusive(x_732);
if (x_733 == 0)
{
lean_object* x_734; 
x_734 = lean_ctor_get(x_732, 0);
lean_dec(x_734);
lean_ctor_set(x_732, 0, x_2);
return x_732;
}
else
{
lean_object* x_735; lean_object* x_736; 
x_735 = lean_ctor_get(x_732, 1);
lean_inc(x_735);
lean_dec(x_732);
x_736 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_736, 0, x_2);
lean_ctor_set(x_736, 1, x_735);
return x_736;
}
}
else
{
uint8_t x_737; 
lean_dec(x_2);
x_737 = !lean_is_exclusive(x_732);
if (x_737 == 0)
{
return x_732;
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_738 = lean_ctor_get(x_732, 0);
x_739 = lean_ctor_get(x_732, 1);
lean_inc(x_739);
lean_inc(x_738);
lean_dec(x_732);
x_740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_740, 0, x_738);
lean_ctor_set(x_740, 1, x_739);
return x_740;
}
}
}
else
{
lean_object* x_741; lean_object* x_742; 
x_741 = lean_ctor_get(x_8, 0);
lean_inc(x_741);
lean_dec(x_8);
lean_inc(x_4);
x_742 = l_Lean_Elab_Term_isDefEq(x_6, x_741, x_3, x_4, x_731);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; lean_object* x_744; 
x_743 = lean_ctor_get(x_742, 1);
lean_inc(x_743);
lean_dec(x_742);
x_744 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_743);
lean_dec(x_12);
if (lean_obj_tag(x_744) == 0)
{
uint8_t x_745; 
x_745 = !lean_is_exclusive(x_744);
if (x_745 == 0)
{
lean_object* x_746; 
x_746 = lean_ctor_get(x_744, 0);
lean_dec(x_746);
lean_ctor_set(x_744, 0, x_2);
return x_744;
}
else
{
lean_object* x_747; lean_object* x_748; 
x_747 = lean_ctor_get(x_744, 1);
lean_inc(x_747);
lean_dec(x_744);
x_748 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_748, 0, x_2);
lean_ctor_set(x_748, 1, x_747);
return x_748;
}
}
else
{
uint8_t x_749; 
lean_dec(x_2);
x_749 = !lean_is_exclusive(x_744);
if (x_749 == 0)
{
return x_744;
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_750 = lean_ctor_get(x_744, 0);
x_751 = lean_ctor_get(x_744, 1);
lean_inc(x_751);
lean_inc(x_750);
lean_dec(x_744);
x_752 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_752, 0, x_750);
lean_ctor_set(x_752, 1, x_751);
return x_752;
}
}
}
else
{
uint8_t x_753; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_753 = !lean_is_exclusive(x_742);
if (x_753 == 0)
{
return x_742;
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_754 = lean_ctor_get(x_742, 0);
x_755 = lean_ctor_get(x_742, 1);
lean_inc(x_755);
lean_inc(x_754);
lean_dec(x_742);
x_756 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_756, 0, x_754);
lean_ctor_set(x_756, 1, x_755);
return x_756;
}
}
}
}
}
}
else
{
lean_object* x_766; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_766 = lean_ctor_get(x_713, 0);
lean_inc(x_766);
lean_dec(x_713);
if (lean_obj_tag(x_766) == 4)
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; 
x_767 = lean_ctor_get(x_766, 0);
lean_inc(x_767);
lean_dec(x_766);
x_768 = l_Lean_Elab_Term_getEnv___rarg(x_708);
x_769 = lean_ctor_get(x_768, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_768, 1);
lean_inc(x_770);
lean_dec(x_768);
x_771 = l___private_Init_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_769, x_767);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
lean_dec(x_771);
x_773 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_773, 0, x_772);
x_774 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_774, 0, x_773);
x_775 = l_Lean_Elab_Term_throwError___rarg(x_6, x_774, x_4, x_770);
lean_dec(x_6);
return x_775;
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; 
x_776 = lean_ctor_get(x_771, 0);
lean_inc(x_776);
lean_dec(x_771);
x_777 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_770);
x_778 = lean_ctor_get(x_777, 1);
lean_inc(x_778);
lean_dec(x_777);
x_779 = l_Lean_Elab_Term_getMainModule___rarg(x_778);
x_780 = lean_ctor_get(x_779, 1);
lean_inc(x_780);
lean_dec(x_779);
x_781 = l_Lean_Syntax_getArgs(x_776);
lean_dec(x_776);
x_782 = l_Array_empty___closed__1;
x_783 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_781, x_781, x_94, x_782);
lean_dec(x_781);
x_784 = l_Lean_nullKind___closed__2;
x_785 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_785, 0, x_784);
lean_ctor_set(x_785, 1, x_783);
x_786 = lean_array_push(x_782, x_785);
x_787 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_787);
lean_ctor_set(x_788, 1, x_786);
x_789 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_790 = lean_array_push(x_789, x_788);
x_791 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_792 = lean_array_push(x_790, x_791);
x_793 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_794 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_794, 0, x_793);
lean_ctor_set(x_794, 1, x_792);
x_795 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_796 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_797 = lean_nat_sub(x_796, x_94);
lean_dec(x_796);
x_798 = lean_unsigned_to_nat(1u);
x_799 = lean_nat_sub(x_797, x_798);
lean_dec(x_797);
x_800 = l_Lean_Expr_getRevArg_x21___main(x_91, x_799);
lean_dec(x_91);
if (lean_obj_tag(x_795) == 0)
{
lean_object* x_801; lean_object* x_802; 
x_801 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_801, 0, x_794);
lean_inc(x_4);
lean_inc(x_2);
x_802 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_801, x_800, x_4, x_780);
if (lean_obj_tag(x_802) == 0)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_802, 1);
lean_inc(x_804);
lean_dec(x_802);
lean_inc(x_803);
x_805 = l_Lean_mkApp(x_2, x_803);
x_806 = lean_expr_instantiate1(x_92, x_803);
lean_dec(x_803);
lean_dec(x_92);
x_2 = x_805;
x_3 = x_806;
x_5 = x_804;
goto _start;
}
else
{
uint8_t x_808; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_808 = !lean_is_exclusive(x_802);
if (x_808 == 0)
{
return x_802;
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_809 = lean_ctor_get(x_802, 0);
x_810 = lean_ctor_get(x_802, 1);
lean_inc(x_810);
lean_inc(x_809);
lean_dec(x_802);
x_811 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_811, 0, x_809);
lean_ctor_set(x_811, 1, x_810);
return x_811;
}
}
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_812 = lean_ctor_get(x_795, 0);
lean_inc(x_812);
lean_dec(x_795);
x_813 = l_Lean_Syntax_replaceInfo___main(x_812, x_794);
x_814 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_814, 0, x_813);
lean_inc(x_4);
lean_inc(x_2);
x_815 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_814, x_800, x_4, x_780);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_815, 1);
lean_inc(x_817);
lean_dec(x_815);
lean_inc(x_816);
x_818 = l_Lean_mkApp(x_2, x_816);
x_819 = lean_expr_instantiate1(x_92, x_816);
lean_dec(x_816);
lean_dec(x_92);
x_2 = x_818;
x_3 = x_819;
x_5 = x_817;
goto _start;
}
else
{
uint8_t x_821; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_821 = !lean_is_exclusive(x_815);
if (x_821 == 0)
{
return x_815;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_822 = lean_ctor_get(x_815, 0);
x_823 = lean_ctor_get(x_815, 1);
lean_inc(x_823);
lean_inc(x_822);
lean_dec(x_815);
x_824 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_824, 0, x_822);
lean_ctor_set(x_824, 1, x_823);
return x_824;
}
}
}
}
}
else
{
lean_object* x_825; lean_object* x_826; 
lean_dec(x_766);
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_825 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_826 = l_Lean_Elab_Term_throwError___rarg(x_6, x_825, x_4, x_708);
lean_dec(x_6);
return x_826;
}
}
}
else
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_827 = lean_ctor_get(x_712, 0);
lean_inc(x_827);
lean_dec(x_712);
lean_inc(x_827);
x_828 = l_Lean_mkApp(x_2, x_827);
x_829 = lean_expr_instantiate1(x_92, x_827);
lean_dec(x_827);
lean_dec(x_92);
x_2 = x_828;
x_3 = x_829;
x_5 = x_708;
goto _start;
}
}
else
{
uint8_t x_831; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
x_831 = l_Array_isEmpty___rarg(x_11);
if (x_831 == 0)
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_832 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_832, 0, x_90);
x_833 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_834 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_834, 0, x_833);
lean_ctor_set(x_834, 1, x_832);
x_835 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_836 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_836, 0, x_834);
lean_ctor_set(x_836, 1, x_835);
x_837 = x_11;
x_838 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_837);
x_839 = x_838;
x_840 = l_Array_toList___rarg(x_839);
lean_dec(x_839);
x_841 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_840);
x_842 = l_Array_HasRepr___rarg___closed__1;
x_843 = lean_string_append(x_842, x_841);
lean_dec(x_841);
x_844 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_844, 0, x_843);
x_845 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_845, 0, x_844);
x_846 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_846, 0, x_836);
lean_ctor_set(x_846, 1, x_845);
x_847 = l_Lean_Elab_Term_throwError___rarg(x_6, x_846, x_4, x_708);
lean_dec(x_6);
return x_847;
}
else
{
lean_object* x_848; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; uint8_t x_879; 
lean_dec(x_90);
lean_dec(x_11);
x_875 = l_Lean_Elab_Term_getOptions(x_4, x_708);
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
lean_dec(x_875);
x_878 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_879 = l_Lean_checkTraceOption(x_876, x_878);
lean_dec(x_876);
if (x_879 == 0)
{
x_848 = x_877;
goto block_874;
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; 
lean_inc(x_2);
x_880 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_880, 0, x_2);
x_881 = l_Lean_Elab_Term_logTrace(x_878, x_6, x_880, x_4, x_877);
x_882 = lean_ctor_get(x_881, 1);
lean_inc(x_882);
lean_dec(x_881);
x_848 = x_882;
goto block_874;
}
block_874:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_849; 
lean_dec(x_3);
x_849 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_848);
lean_dec(x_12);
if (lean_obj_tag(x_849) == 0)
{
uint8_t x_850; 
x_850 = !lean_is_exclusive(x_849);
if (x_850 == 0)
{
lean_object* x_851; 
x_851 = lean_ctor_get(x_849, 0);
lean_dec(x_851);
lean_ctor_set(x_849, 0, x_2);
return x_849;
}
else
{
lean_object* x_852; lean_object* x_853; 
x_852 = lean_ctor_get(x_849, 1);
lean_inc(x_852);
lean_dec(x_849);
x_853 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_853, 0, x_2);
lean_ctor_set(x_853, 1, x_852);
return x_853;
}
}
else
{
uint8_t x_854; 
lean_dec(x_2);
x_854 = !lean_is_exclusive(x_849);
if (x_854 == 0)
{
return x_849;
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; 
x_855 = lean_ctor_get(x_849, 0);
x_856 = lean_ctor_get(x_849, 1);
lean_inc(x_856);
lean_inc(x_855);
lean_dec(x_849);
x_857 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_857, 0, x_855);
lean_ctor_set(x_857, 1, x_856);
return x_857;
}
}
}
else
{
lean_object* x_858; lean_object* x_859; 
x_858 = lean_ctor_get(x_8, 0);
lean_inc(x_858);
lean_dec(x_8);
lean_inc(x_4);
x_859 = l_Lean_Elab_Term_isDefEq(x_6, x_858, x_3, x_4, x_848);
if (lean_obj_tag(x_859) == 0)
{
lean_object* x_860; lean_object* x_861; 
x_860 = lean_ctor_get(x_859, 1);
lean_inc(x_860);
lean_dec(x_859);
x_861 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_860);
lean_dec(x_12);
if (lean_obj_tag(x_861) == 0)
{
uint8_t x_862; 
x_862 = !lean_is_exclusive(x_861);
if (x_862 == 0)
{
lean_object* x_863; 
x_863 = lean_ctor_get(x_861, 0);
lean_dec(x_863);
lean_ctor_set(x_861, 0, x_2);
return x_861;
}
else
{
lean_object* x_864; lean_object* x_865; 
x_864 = lean_ctor_get(x_861, 1);
lean_inc(x_864);
lean_dec(x_861);
x_865 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_865, 0, x_2);
lean_ctor_set(x_865, 1, x_864);
return x_865;
}
}
else
{
uint8_t x_866; 
lean_dec(x_2);
x_866 = !lean_is_exclusive(x_861);
if (x_866 == 0)
{
return x_861;
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_867 = lean_ctor_get(x_861, 0);
x_868 = lean_ctor_get(x_861, 1);
lean_inc(x_868);
lean_inc(x_867);
lean_dec(x_861);
x_869 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_869, 0, x_867);
lean_ctor_set(x_869, 1, x_868);
return x_869;
}
}
}
else
{
uint8_t x_870; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_870 = !lean_is_exclusive(x_859);
if (x_870 == 0)
{
return x_859;
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_871 = lean_ctor_get(x_859, 0);
x_872 = lean_ctor_get(x_859, 1);
lean_inc(x_872);
lean_inc(x_871);
lean_dec(x_859);
x_873 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_873, 0, x_871);
lean_ctor_set(x_873, 1, x_872);
return x_873;
}
}
}
}
}
}
}
else
{
lean_object* x_883; lean_object* x_884; 
lean_dec(x_1);
lean_dec(x_90);
lean_dec(x_3);
x_883 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_884 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_883, x_91, x_4, x_708);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; 
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
lean_dec(x_884);
x_887 = lean_unsigned_to_nat(1u);
x_888 = lean_nat_add(x_10, x_887);
lean_dec(x_10);
x_889 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_889, 0, x_6);
lean_ctor_set(x_889, 1, x_7);
lean_ctor_set(x_889, 2, x_8);
lean_ctor_set(x_889, 3, x_888);
lean_ctor_set(x_889, 4, x_11);
lean_ctor_set(x_889, 5, x_12);
lean_ctor_set(x_889, 6, x_13);
lean_ctor_set_uint8(x_889, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_889, sizeof(void*)*7 + 1, x_709);
lean_inc(x_885);
x_890 = l_Lean_mkApp(x_2, x_885);
x_891 = lean_expr_instantiate1(x_92, x_885);
lean_dec(x_885);
lean_dec(x_92);
x_1 = x_889;
x_2 = x_890;
x_3 = x_891;
x_5 = x_886;
goto _start;
}
else
{
uint8_t x_893; 
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
x_893 = !lean_is_exclusive(x_884);
if (x_893 == 0)
{
return x_884;
}
else
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; 
x_894 = lean_ctor_get(x_884, 0);
x_895 = lean_ctor_get(x_884, 1);
lean_inc(x_895);
lean_inc(x_894);
lean_dec(x_884);
x_896 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_896, 0, x_894);
lean_ctor_set(x_896, 1, x_895);
return x_896;
}
}
}
}
else
{
uint8_t x_897; 
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
x_897 = !lean_is_exclusive(x_699);
if (x_897 == 0)
{
return x_699;
}
else
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_898 = lean_ctor_get(x_699, 0);
x_899 = lean_ctor_get(x_699, 1);
lean_inc(x_899);
lean_inc(x_898);
lean_dec(x_699);
x_900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_900, 0, x_898);
lean_ctor_set(x_900, 1, x_899);
return x_900;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_901; uint8_t x_902; lean_object* x_903; lean_object* x_904; uint8_t x_905; 
x_901 = lean_ctor_get(x_699, 1);
lean_inc(x_901);
lean_dec(x_699);
x_902 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_903 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_903, 0, x_6);
lean_ctor_set(x_903, 1, x_7);
lean_ctor_set(x_903, 2, x_8);
lean_ctor_set(x_903, 3, x_10);
lean_ctor_set(x_903, 4, x_11);
lean_ctor_set(x_903, 5, x_12);
lean_ctor_set(x_903, 6, x_13);
lean_ctor_set_uint8(x_903, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_903, sizeof(void*)*7 + 1, x_902);
x_904 = lean_array_get_size(x_7);
x_905 = lean_nat_dec_lt(x_10, x_904);
lean_dec(x_904);
if (x_905 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_906; 
x_906 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_906) == 0)
{
lean_object* x_907; 
x_907 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_907) == 0)
{
uint8_t x_908; 
lean_dec(x_903);
lean_dec(x_92);
lean_dec(x_91);
x_908 = l_Array_isEmpty___rarg(x_11);
if (x_908 == 0)
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_909 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_909, 0, x_90);
x_910 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_911 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_911, 0, x_910);
lean_ctor_set(x_911, 1, x_909);
x_912 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_913 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_913, 0, x_911);
lean_ctor_set(x_913, 1, x_912);
x_914 = x_11;
x_915 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_914);
x_916 = x_915;
x_917 = l_Array_toList___rarg(x_916);
lean_dec(x_916);
x_918 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_917);
x_919 = l_Array_HasRepr___rarg___closed__1;
x_920 = lean_string_append(x_919, x_918);
lean_dec(x_918);
x_921 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_921, 0, x_920);
x_922 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_922, 0, x_921);
x_923 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_923, 0, x_913);
lean_ctor_set(x_923, 1, x_922);
x_924 = l_Lean_Elab_Term_throwError___rarg(x_6, x_923, x_4, x_901);
lean_dec(x_6);
return x_924;
}
else
{
lean_object* x_925; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; uint8_t x_954; 
lean_dec(x_90);
lean_dec(x_11);
x_950 = l_Lean_Elab_Term_getOptions(x_4, x_901);
x_951 = lean_ctor_get(x_950, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_950, 1);
lean_inc(x_952);
lean_dec(x_950);
x_953 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_954 = l_Lean_checkTraceOption(x_951, x_953);
lean_dec(x_951);
if (x_954 == 0)
{
x_925 = x_952;
goto block_949;
}
else
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; 
lean_inc(x_2);
x_955 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_955, 0, x_2);
x_956 = l_Lean_Elab_Term_logTrace(x_953, x_6, x_955, x_4, x_952);
x_957 = lean_ctor_get(x_956, 1);
lean_inc(x_957);
lean_dec(x_956);
x_925 = x_957;
goto block_949;
}
block_949:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_926; 
lean_dec(x_3);
x_926 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_925);
lean_dec(x_12);
if (lean_obj_tag(x_926) == 0)
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; 
x_927 = lean_ctor_get(x_926, 1);
lean_inc(x_927);
if (lean_is_exclusive(x_926)) {
 lean_ctor_release(x_926, 0);
 lean_ctor_release(x_926, 1);
 x_928 = x_926;
} else {
 lean_dec_ref(x_926);
 x_928 = lean_box(0);
}
if (lean_is_scalar(x_928)) {
 x_929 = lean_alloc_ctor(0, 2, 0);
} else {
 x_929 = x_928;
}
lean_ctor_set(x_929, 0, x_2);
lean_ctor_set(x_929, 1, x_927);
return x_929;
}
else
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; 
lean_dec(x_2);
x_930 = lean_ctor_get(x_926, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_926, 1);
lean_inc(x_931);
if (lean_is_exclusive(x_926)) {
 lean_ctor_release(x_926, 0);
 lean_ctor_release(x_926, 1);
 x_932 = x_926;
} else {
 lean_dec_ref(x_926);
 x_932 = lean_box(0);
}
if (lean_is_scalar(x_932)) {
 x_933 = lean_alloc_ctor(1, 2, 0);
} else {
 x_933 = x_932;
}
lean_ctor_set(x_933, 0, x_930);
lean_ctor_set(x_933, 1, x_931);
return x_933;
}
}
else
{
lean_object* x_934; lean_object* x_935; 
x_934 = lean_ctor_get(x_8, 0);
lean_inc(x_934);
lean_dec(x_8);
lean_inc(x_4);
x_935 = l_Lean_Elab_Term_isDefEq(x_6, x_934, x_3, x_4, x_925);
if (lean_obj_tag(x_935) == 0)
{
lean_object* x_936; lean_object* x_937; 
x_936 = lean_ctor_get(x_935, 1);
lean_inc(x_936);
lean_dec(x_935);
x_937 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_936);
lean_dec(x_12);
if (lean_obj_tag(x_937) == 0)
{
lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_938 = lean_ctor_get(x_937, 1);
lean_inc(x_938);
if (lean_is_exclusive(x_937)) {
 lean_ctor_release(x_937, 0);
 lean_ctor_release(x_937, 1);
 x_939 = x_937;
} else {
 lean_dec_ref(x_937);
 x_939 = lean_box(0);
}
if (lean_is_scalar(x_939)) {
 x_940 = lean_alloc_ctor(0, 2, 0);
} else {
 x_940 = x_939;
}
lean_ctor_set(x_940, 0, x_2);
lean_ctor_set(x_940, 1, x_938);
return x_940;
}
else
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; 
lean_dec(x_2);
x_941 = lean_ctor_get(x_937, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_937, 1);
lean_inc(x_942);
if (lean_is_exclusive(x_937)) {
 lean_ctor_release(x_937, 0);
 lean_ctor_release(x_937, 1);
 x_943 = x_937;
} else {
 lean_dec_ref(x_937);
 x_943 = lean_box(0);
}
if (lean_is_scalar(x_943)) {
 x_944 = lean_alloc_ctor(1, 2, 0);
} else {
 x_944 = x_943;
}
lean_ctor_set(x_944, 0, x_941);
lean_ctor_set(x_944, 1, x_942);
return x_944;
}
}
else
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_945 = lean_ctor_get(x_935, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_935, 1);
lean_inc(x_946);
if (lean_is_exclusive(x_935)) {
 lean_ctor_release(x_935, 0);
 lean_ctor_release(x_935, 1);
 x_947 = x_935;
} else {
 lean_dec_ref(x_935);
 x_947 = lean_box(0);
}
if (lean_is_scalar(x_947)) {
 x_948 = lean_alloc_ctor(1, 2, 0);
} else {
 x_948 = x_947;
}
lean_ctor_set(x_948, 0, x_945);
lean_ctor_set(x_948, 1, x_946);
return x_948;
}
}
}
}
}
else
{
lean_object* x_958; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_958 = lean_ctor_get(x_907, 0);
lean_inc(x_958);
lean_dec(x_907);
if (lean_obj_tag(x_958) == 4)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; 
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
lean_dec(x_958);
x_960 = l_Lean_Elab_Term_getEnv___rarg(x_901);
x_961 = lean_ctor_get(x_960, 0);
lean_inc(x_961);
x_962 = lean_ctor_get(x_960, 1);
lean_inc(x_962);
lean_dec(x_960);
x_963 = l___private_Init_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_961, x_959);
if (lean_obj_tag(x_963) == 0)
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; 
lean_dec(x_903);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
lean_dec(x_963);
x_965 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_965, 0, x_964);
x_966 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_966, 0, x_965);
x_967 = l_Lean_Elab_Term_throwError___rarg(x_6, x_966, x_4, x_962);
lean_dec(x_6);
return x_967;
}
else
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_968 = lean_ctor_get(x_963, 0);
lean_inc(x_968);
lean_dec(x_963);
x_969 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_962);
x_970 = lean_ctor_get(x_969, 1);
lean_inc(x_970);
lean_dec(x_969);
x_971 = l_Lean_Elab_Term_getMainModule___rarg(x_970);
x_972 = lean_ctor_get(x_971, 1);
lean_inc(x_972);
lean_dec(x_971);
x_973 = l_Lean_Syntax_getArgs(x_968);
lean_dec(x_968);
x_974 = l_Array_empty___closed__1;
x_975 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_973, x_973, x_94, x_974);
lean_dec(x_973);
x_976 = l_Lean_nullKind___closed__2;
x_977 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_977, 0, x_976);
lean_ctor_set(x_977, 1, x_975);
x_978 = lean_array_push(x_974, x_977);
x_979 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_980 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_980, 0, x_979);
lean_ctor_set(x_980, 1, x_978);
x_981 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_982 = lean_array_push(x_981, x_980);
x_983 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_984 = lean_array_push(x_982, x_983);
x_985 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_986 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_986, 0, x_985);
lean_ctor_set(x_986, 1, x_984);
x_987 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_988 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_989 = lean_nat_sub(x_988, x_94);
lean_dec(x_988);
x_990 = lean_unsigned_to_nat(1u);
x_991 = lean_nat_sub(x_989, x_990);
lean_dec(x_989);
x_992 = l_Lean_Expr_getRevArg_x21___main(x_91, x_991);
lean_dec(x_91);
if (lean_obj_tag(x_987) == 0)
{
lean_object* x_993; lean_object* x_994; 
x_993 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_993, 0, x_986);
lean_inc(x_4);
lean_inc(x_2);
x_994 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_993, x_992, x_4, x_972);
if (lean_obj_tag(x_994) == 0)
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_995 = lean_ctor_get(x_994, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_994, 1);
lean_inc(x_996);
lean_dec(x_994);
lean_inc(x_995);
x_997 = l_Lean_mkApp(x_2, x_995);
x_998 = lean_expr_instantiate1(x_92, x_995);
lean_dec(x_995);
lean_dec(x_92);
x_1 = x_903;
x_2 = x_997;
x_3 = x_998;
x_5 = x_996;
goto _start;
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; 
lean_dec(x_903);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1000 = lean_ctor_get(x_994, 0);
lean_inc(x_1000);
x_1001 = lean_ctor_get(x_994, 1);
lean_inc(x_1001);
if (lean_is_exclusive(x_994)) {
 lean_ctor_release(x_994, 0);
 lean_ctor_release(x_994, 1);
 x_1002 = x_994;
} else {
 lean_dec_ref(x_994);
 x_1002 = lean_box(0);
}
if (lean_is_scalar(x_1002)) {
 x_1003 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1003 = x_1002;
}
lean_ctor_set(x_1003, 0, x_1000);
lean_ctor_set(x_1003, 1, x_1001);
return x_1003;
}
}
else
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; 
x_1004 = lean_ctor_get(x_987, 0);
lean_inc(x_1004);
lean_dec(x_987);
x_1005 = l_Lean_Syntax_replaceInfo___main(x_1004, x_986);
x_1006 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1006, 0, x_1005);
lean_inc(x_4);
lean_inc(x_2);
x_1007 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1006, x_992, x_4, x_972);
if (lean_obj_tag(x_1007) == 0)
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
x_1008 = lean_ctor_get(x_1007, 0);
lean_inc(x_1008);
x_1009 = lean_ctor_get(x_1007, 1);
lean_inc(x_1009);
lean_dec(x_1007);
lean_inc(x_1008);
x_1010 = l_Lean_mkApp(x_2, x_1008);
x_1011 = lean_expr_instantiate1(x_92, x_1008);
lean_dec(x_1008);
lean_dec(x_92);
x_1 = x_903;
x_2 = x_1010;
x_3 = x_1011;
x_5 = x_1009;
goto _start;
}
else
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
lean_dec(x_903);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1013 = lean_ctor_get(x_1007, 0);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_1007, 1);
lean_inc(x_1014);
if (lean_is_exclusive(x_1007)) {
 lean_ctor_release(x_1007, 0);
 lean_ctor_release(x_1007, 1);
 x_1015 = x_1007;
} else {
 lean_dec_ref(x_1007);
 x_1015 = lean_box(0);
}
if (lean_is_scalar(x_1015)) {
 x_1016 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1016 = x_1015;
}
lean_ctor_set(x_1016, 0, x_1013);
lean_ctor_set(x_1016, 1, x_1014);
return x_1016;
}
}
}
}
else
{
lean_object* x_1017; lean_object* x_1018; 
lean_dec(x_958);
lean_dec(x_903);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_1017 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1018 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1017, x_4, x_901);
lean_dec(x_6);
return x_1018;
}
}
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1019 = lean_ctor_get(x_906, 0);
lean_inc(x_1019);
lean_dec(x_906);
lean_inc(x_1019);
x_1020 = l_Lean_mkApp(x_2, x_1019);
x_1021 = lean_expr_instantiate1(x_92, x_1019);
lean_dec(x_1019);
lean_dec(x_92);
x_1 = x_903;
x_2 = x_1020;
x_3 = x_1021;
x_5 = x_901;
goto _start;
}
}
else
{
uint8_t x_1023; 
lean_dec(x_903);
lean_dec(x_92);
lean_dec(x_91);
x_1023 = l_Array_isEmpty___rarg(x_11);
if (x_1023 == 0)
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1024 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1024, 0, x_90);
x_1025 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1026 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1026, 0, x_1025);
lean_ctor_set(x_1026, 1, x_1024);
x_1027 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1028 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1028, 0, x_1026);
lean_ctor_set(x_1028, 1, x_1027);
x_1029 = x_11;
x_1030 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_1029);
x_1031 = x_1030;
x_1032 = l_Array_toList___rarg(x_1031);
lean_dec(x_1031);
x_1033 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1032);
x_1034 = l_Array_HasRepr___rarg___closed__1;
x_1035 = lean_string_append(x_1034, x_1033);
lean_dec(x_1033);
x_1036 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1036, 0, x_1035);
x_1037 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1037, 0, x_1036);
x_1038 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1038, 0, x_1028);
lean_ctor_set(x_1038, 1, x_1037);
x_1039 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1038, x_4, x_901);
lean_dec(x_6);
return x_1039;
}
else
{
lean_object* x_1040; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; uint8_t x_1069; 
lean_dec(x_90);
lean_dec(x_11);
x_1065 = l_Lean_Elab_Term_getOptions(x_4, x_901);
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1065, 1);
lean_inc(x_1067);
lean_dec(x_1065);
x_1068 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1069 = l_Lean_checkTraceOption(x_1066, x_1068);
lean_dec(x_1066);
if (x_1069 == 0)
{
x_1040 = x_1067;
goto block_1064;
}
else
{
lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
lean_inc(x_2);
x_1070 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1070, 0, x_2);
x_1071 = l_Lean_Elab_Term_logTrace(x_1068, x_6, x_1070, x_4, x_1067);
x_1072 = lean_ctor_get(x_1071, 1);
lean_inc(x_1072);
lean_dec(x_1071);
x_1040 = x_1072;
goto block_1064;
}
block_1064:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1041; 
lean_dec(x_3);
x_1041 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1040);
lean_dec(x_12);
if (lean_obj_tag(x_1041) == 0)
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
x_1042 = lean_ctor_get(x_1041, 1);
lean_inc(x_1042);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1043 = x_1041;
} else {
 lean_dec_ref(x_1041);
 x_1043 = lean_box(0);
}
if (lean_is_scalar(x_1043)) {
 x_1044 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1044 = x_1043;
}
lean_ctor_set(x_1044, 0, x_2);
lean_ctor_set(x_1044, 1, x_1042);
return x_1044;
}
else
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; 
lean_dec(x_2);
x_1045 = lean_ctor_get(x_1041, 0);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1041, 1);
lean_inc(x_1046);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1047 = x_1041;
} else {
 lean_dec_ref(x_1041);
 x_1047 = lean_box(0);
}
if (lean_is_scalar(x_1047)) {
 x_1048 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1048 = x_1047;
}
lean_ctor_set(x_1048, 0, x_1045);
lean_ctor_set(x_1048, 1, x_1046);
return x_1048;
}
}
else
{
lean_object* x_1049; lean_object* x_1050; 
x_1049 = lean_ctor_get(x_8, 0);
lean_inc(x_1049);
lean_dec(x_8);
lean_inc(x_4);
x_1050 = l_Lean_Elab_Term_isDefEq(x_6, x_1049, x_3, x_4, x_1040);
if (lean_obj_tag(x_1050) == 0)
{
lean_object* x_1051; lean_object* x_1052; 
x_1051 = lean_ctor_get(x_1050, 1);
lean_inc(x_1051);
lean_dec(x_1050);
x_1052 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1051);
lean_dec(x_12);
if (lean_obj_tag(x_1052) == 0)
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
x_1053 = lean_ctor_get(x_1052, 1);
lean_inc(x_1053);
if (lean_is_exclusive(x_1052)) {
 lean_ctor_release(x_1052, 0);
 lean_ctor_release(x_1052, 1);
 x_1054 = x_1052;
} else {
 lean_dec_ref(x_1052);
 x_1054 = lean_box(0);
}
if (lean_is_scalar(x_1054)) {
 x_1055 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1055 = x_1054;
}
lean_ctor_set(x_1055, 0, x_2);
lean_ctor_set(x_1055, 1, x_1053);
return x_1055;
}
else
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
lean_dec(x_2);
x_1056 = lean_ctor_get(x_1052, 0);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1052, 1);
lean_inc(x_1057);
if (lean_is_exclusive(x_1052)) {
 lean_ctor_release(x_1052, 0);
 lean_ctor_release(x_1052, 1);
 x_1058 = x_1052;
} else {
 lean_dec_ref(x_1052);
 x_1058 = lean_box(0);
}
if (lean_is_scalar(x_1058)) {
 x_1059 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1059 = x_1058;
}
lean_ctor_set(x_1059, 0, x_1056);
lean_ctor_set(x_1059, 1, x_1057);
return x_1059;
}
}
else
{
lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1060 = lean_ctor_get(x_1050, 0);
lean_inc(x_1060);
x_1061 = lean_ctor_get(x_1050, 1);
lean_inc(x_1061);
if (lean_is_exclusive(x_1050)) {
 lean_ctor_release(x_1050, 0);
 lean_ctor_release(x_1050, 1);
 x_1062 = x_1050;
} else {
 lean_dec_ref(x_1050);
 x_1062 = lean_box(0);
}
if (lean_is_scalar(x_1062)) {
 x_1063 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1063 = x_1062;
}
lean_ctor_set(x_1063, 0, x_1060);
lean_ctor_set(x_1063, 1, x_1061);
return x_1063;
}
}
}
}
}
}
else
{
lean_object* x_1073; lean_object* x_1074; 
lean_dec(x_903);
lean_dec(x_90);
lean_dec(x_3);
x_1073 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1074 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1073, x_91, x_4, x_901);
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
x_1075 = lean_ctor_get(x_1074, 0);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_1074, 1);
lean_inc(x_1076);
lean_dec(x_1074);
x_1077 = lean_unsigned_to_nat(1u);
x_1078 = lean_nat_add(x_10, x_1077);
lean_dec(x_10);
x_1079 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1079, 0, x_6);
lean_ctor_set(x_1079, 1, x_7);
lean_ctor_set(x_1079, 2, x_8);
lean_ctor_set(x_1079, 3, x_1078);
lean_ctor_set(x_1079, 4, x_11);
lean_ctor_set(x_1079, 5, x_12);
lean_ctor_set(x_1079, 6, x_13);
lean_ctor_set_uint8(x_1079, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1079, sizeof(void*)*7 + 1, x_902);
lean_inc(x_1075);
x_1080 = l_Lean_mkApp(x_2, x_1075);
x_1081 = lean_expr_instantiate1(x_92, x_1075);
lean_dec(x_1075);
lean_dec(x_92);
x_1 = x_1079;
x_2 = x_1080;
x_3 = x_1081;
x_5 = x_1076;
goto _start;
}
else
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
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
x_1083 = lean_ctor_get(x_1074, 0);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1074, 1);
lean_inc(x_1084);
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 lean_ctor_release(x_1074, 1);
 x_1085 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1085 = lean_box(0);
}
if (lean_is_scalar(x_1085)) {
 x_1086 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1086 = x_1085;
}
lean_ctor_set(x_1086, 0, x_1083);
lean_ctor_set(x_1086, 1, x_1084);
return x_1086;
}
}
}
else
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; 
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
x_1087 = lean_ctor_get(x_699, 0);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_699, 1);
lean_inc(x_1088);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 x_1089 = x_699;
} else {
 lean_dec_ref(x_699);
 x_1089 = lean_box(0);
}
if (lean_is_scalar(x_1089)) {
 x_1090 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1090 = x_1089;
}
lean_ctor_set(x_1090, 0, x_1087);
lean_ctor_set(x_1090, 1, x_1088);
return x_1090;
}
}
}
case 3:
{
if (x_9 == 0)
{
uint8_t x_1091; 
lean_dec(x_90);
lean_dec(x_16);
lean_dec(x_3);
x_1091 = !lean_is_exclusive(x_1);
if (x_1091 == 0)
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; uint8_t x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
x_1092 = lean_ctor_get(x_1, 6);
lean_dec(x_1092);
x_1093 = lean_ctor_get(x_1, 5);
lean_dec(x_1093);
x_1094 = lean_ctor_get(x_1, 4);
lean_dec(x_1094);
x_1095 = lean_ctor_get(x_1, 3);
lean_dec(x_1095);
x_1096 = lean_ctor_get(x_1, 2);
lean_dec(x_1096);
x_1097 = lean_ctor_get(x_1, 1);
lean_dec(x_1097);
x_1098 = lean_ctor_get(x_1, 0);
lean_dec(x_1098);
x_1099 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1099, 0, x_91);
x_1100 = 1;
x_1101 = lean_box(0);
lean_inc(x_4);
x_1102 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_1099, x_1100, x_1101, x_4, x_17);
x_1103 = lean_ctor_get(x_1102, 0);
lean_inc(x_1103);
x_1104 = lean_ctor_get(x_1102, 1);
lean_inc(x_1104);
lean_dec(x_1102);
x_1105 = l_Lean_Expr_mvarId_x21(x_1103);
x_1106 = lean_array_push(x_12, x_1105);
lean_ctor_set(x_1, 5, x_1106);
lean_inc(x_1103);
x_1107 = l_Lean_mkApp(x_2, x_1103);
x_1108 = lean_expr_instantiate1(x_92, x_1103);
lean_dec(x_1103);
lean_dec(x_92);
x_2 = x_1107;
x_3 = x_1108;
x_5 = x_1104;
goto _start;
}
else
{
lean_object* x_1110; uint8_t x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; 
lean_dec(x_1);
x_1110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1110, 0, x_91);
x_1111 = 1;
x_1112 = lean_box(0);
lean_inc(x_4);
x_1113 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_1110, x_1111, x_1112, x_4, x_17);
x_1114 = lean_ctor_get(x_1113, 0);
lean_inc(x_1114);
x_1115 = lean_ctor_get(x_1113, 1);
lean_inc(x_1115);
lean_dec(x_1113);
x_1116 = l_Lean_Expr_mvarId_x21(x_1114);
x_1117 = lean_array_push(x_12, x_1116);
x_1118 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1118, 0, x_6);
lean_ctor_set(x_1118, 1, x_7);
lean_ctor_set(x_1118, 2, x_8);
lean_ctor_set(x_1118, 3, x_10);
lean_ctor_set(x_1118, 4, x_11);
lean_ctor_set(x_1118, 5, x_1117);
lean_ctor_set(x_1118, 6, x_13);
lean_ctor_set_uint8(x_1118, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1118, sizeof(void*)*7 + 1, x_14);
lean_inc(x_1114);
x_1119 = l_Lean_mkApp(x_2, x_1114);
x_1120 = lean_expr_instantiate1(x_92, x_1114);
lean_dec(x_1114);
lean_dec(x_92);
x_1 = x_1118;
x_2 = x_1119;
x_3 = x_1120;
x_5 = x_1115;
goto _start;
}
}
else
{
uint8_t x_1122; 
x_1122 = l___private_Init_Lean_Elab_App_9__nextArgIsHole(x_1);
if (x_1122 == 0)
{
lean_object* x_1123; uint8_t x_1124; 
lean_inc(x_4);
lean_inc(x_1);
x_1123 = l___private_Init_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_17);
x_1124 = !lean_is_exclusive(x_1);
if (x_1124 == 0)
{
lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
x_1125 = lean_ctor_get(x_1, 6);
lean_dec(x_1125);
x_1126 = lean_ctor_get(x_1, 5);
lean_dec(x_1126);
x_1127 = lean_ctor_get(x_1, 4);
lean_dec(x_1127);
x_1128 = lean_ctor_get(x_1, 3);
lean_dec(x_1128);
x_1129 = lean_ctor_get(x_1, 2);
lean_dec(x_1129);
x_1130 = lean_ctor_get(x_1, 1);
lean_dec(x_1130);
x_1131 = lean_ctor_get(x_1, 0);
lean_dec(x_1131);
if (lean_obj_tag(x_1123) == 0)
{
lean_object* x_1132; lean_object* x_1133; uint8_t x_1134; 
x_1132 = lean_ctor_get(x_1123, 1);
lean_inc(x_1132);
lean_dec(x_1123);
x_1133 = lean_array_get_size(x_7);
x_1134 = lean_nat_dec_lt(x_10, x_1133);
lean_dec(x_1133);
if (x_1134 == 0)
{
uint8_t x_1135; 
lean_free_object(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
x_1135 = l_Array_isEmpty___rarg(x_11);
if (x_1135 == 0)
{
lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1136 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1136, 0, x_90);
x_1137 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1138 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1138, 0, x_1137);
lean_ctor_set(x_1138, 1, x_1136);
x_1139 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1140 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1140, 0, x_1138);
lean_ctor_set(x_1140, 1, x_1139);
x_1141 = x_11;
x_1142 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_1141);
x_1143 = x_1142;
x_1144 = l_Array_toList___rarg(x_1143);
lean_dec(x_1143);
x_1145 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1144);
x_1146 = l_Array_HasRepr___rarg___closed__1;
x_1147 = lean_string_append(x_1146, x_1145);
lean_dec(x_1145);
x_1148 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1148, 0, x_1147);
x_1149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1149, 0, x_1148);
x_1150 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1150, 0, x_1140);
lean_ctor_set(x_1150, 1, x_1149);
x_1151 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1150, x_4, x_1132);
lean_dec(x_6);
return x_1151;
}
else
{
lean_object* x_1152; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; uint8_t x_1183; 
lean_dec(x_90);
lean_dec(x_11);
x_1179 = l_Lean_Elab_Term_getOptions(x_4, x_1132);
x_1180 = lean_ctor_get(x_1179, 0);
lean_inc(x_1180);
x_1181 = lean_ctor_get(x_1179, 1);
lean_inc(x_1181);
lean_dec(x_1179);
x_1182 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1183 = l_Lean_checkTraceOption(x_1180, x_1182);
lean_dec(x_1180);
if (x_1183 == 0)
{
x_1152 = x_1181;
goto block_1178;
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
lean_inc(x_2);
x_1184 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1184, 0, x_2);
x_1185 = l_Lean_Elab_Term_logTrace(x_1182, x_6, x_1184, x_4, x_1181);
x_1186 = lean_ctor_get(x_1185, 1);
lean_inc(x_1186);
lean_dec(x_1185);
x_1152 = x_1186;
goto block_1178;
}
block_1178:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1153; 
lean_dec(x_3);
x_1153 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1152);
lean_dec(x_12);
if (lean_obj_tag(x_1153) == 0)
{
uint8_t x_1154; 
x_1154 = !lean_is_exclusive(x_1153);
if (x_1154 == 0)
{
lean_object* x_1155; 
x_1155 = lean_ctor_get(x_1153, 0);
lean_dec(x_1155);
lean_ctor_set(x_1153, 0, x_2);
return x_1153;
}
else
{
lean_object* x_1156; lean_object* x_1157; 
x_1156 = lean_ctor_get(x_1153, 1);
lean_inc(x_1156);
lean_dec(x_1153);
x_1157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1157, 0, x_2);
lean_ctor_set(x_1157, 1, x_1156);
return x_1157;
}
}
else
{
uint8_t x_1158; 
lean_dec(x_2);
x_1158 = !lean_is_exclusive(x_1153);
if (x_1158 == 0)
{
return x_1153;
}
else
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
x_1159 = lean_ctor_get(x_1153, 0);
x_1160 = lean_ctor_get(x_1153, 1);
lean_inc(x_1160);
lean_inc(x_1159);
lean_dec(x_1153);
x_1161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1161, 0, x_1159);
lean_ctor_set(x_1161, 1, x_1160);
return x_1161;
}
}
}
else
{
lean_object* x_1162; lean_object* x_1163; 
x_1162 = lean_ctor_get(x_8, 0);
lean_inc(x_1162);
lean_dec(x_8);
lean_inc(x_4);
x_1163 = l_Lean_Elab_Term_isDefEq(x_6, x_1162, x_3, x_4, x_1152);
if (lean_obj_tag(x_1163) == 0)
{
lean_object* x_1164; lean_object* x_1165; 
x_1164 = lean_ctor_get(x_1163, 1);
lean_inc(x_1164);
lean_dec(x_1163);
x_1165 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1164);
lean_dec(x_12);
if (lean_obj_tag(x_1165) == 0)
{
uint8_t x_1166; 
x_1166 = !lean_is_exclusive(x_1165);
if (x_1166 == 0)
{
lean_object* x_1167; 
x_1167 = lean_ctor_get(x_1165, 0);
lean_dec(x_1167);
lean_ctor_set(x_1165, 0, x_2);
return x_1165;
}
else
{
lean_object* x_1168; lean_object* x_1169; 
x_1168 = lean_ctor_get(x_1165, 1);
lean_inc(x_1168);
lean_dec(x_1165);
x_1169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1169, 0, x_2);
lean_ctor_set(x_1169, 1, x_1168);
return x_1169;
}
}
else
{
uint8_t x_1170; 
lean_dec(x_2);
x_1170 = !lean_is_exclusive(x_1165);
if (x_1170 == 0)
{
return x_1165;
}
else
{
lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; 
x_1171 = lean_ctor_get(x_1165, 0);
x_1172 = lean_ctor_get(x_1165, 1);
lean_inc(x_1172);
lean_inc(x_1171);
lean_dec(x_1165);
x_1173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1173, 0, x_1171);
lean_ctor_set(x_1173, 1, x_1172);
return x_1173;
}
}
}
else
{
uint8_t x_1174; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1174 = !lean_is_exclusive(x_1163);
if (x_1174 == 0)
{
return x_1163;
}
else
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; 
x_1175 = lean_ctor_get(x_1163, 0);
x_1176 = lean_ctor_get(x_1163, 1);
lean_inc(x_1176);
lean_inc(x_1175);
lean_dec(x_1163);
x_1177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1177, 0, x_1175);
lean_ctor_set(x_1177, 1, x_1176);
return x_1177;
}
}
}
}
}
}
else
{
lean_object* x_1187; lean_object* x_1188; 
lean_dec(x_90);
lean_dec(x_3);
x_1187 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1188 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1187, x_91, x_4, x_1132);
if (lean_obj_tag(x_1188) == 0)
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; uint8_t x_1193; lean_object* x_1194; lean_object* x_1195; 
x_1189 = lean_ctor_get(x_1188, 0);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1188, 1);
lean_inc(x_1190);
lean_dec(x_1188);
x_1191 = lean_unsigned_to_nat(1u);
x_1192 = lean_nat_add(x_10, x_1191);
lean_dec(x_10);
x_1193 = 1;
lean_ctor_set(x_1, 3, x_1192);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_1193);
lean_inc(x_1189);
x_1194 = l_Lean_mkApp(x_2, x_1189);
x_1195 = lean_expr_instantiate1(x_92, x_1189);
lean_dec(x_1189);
lean_dec(x_92);
x_2 = x_1194;
x_3 = x_1195;
x_5 = x_1190;
goto _start;
}
else
{
uint8_t x_1197; 
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
x_1197 = !lean_is_exclusive(x_1188);
if (x_1197 == 0)
{
return x_1188;
}
else
{
lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; 
x_1198 = lean_ctor_get(x_1188, 0);
x_1199 = lean_ctor_get(x_1188, 1);
lean_inc(x_1199);
lean_inc(x_1198);
lean_dec(x_1188);
x_1200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1200, 0, x_1198);
lean_ctor_set(x_1200, 1, x_1199);
return x_1200;
}
}
}
}
else
{
uint8_t x_1201; 
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
x_1201 = !lean_is_exclusive(x_1123);
if (x_1201 == 0)
{
return x_1123;
}
else
{
lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; 
x_1202 = lean_ctor_get(x_1123, 0);
x_1203 = lean_ctor_get(x_1123, 1);
lean_inc(x_1203);
lean_inc(x_1202);
lean_dec(x_1123);
x_1204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1204, 0, x_1202);
lean_ctor_set(x_1204, 1, x_1203);
return x_1204;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1123) == 0)
{
lean_object* x_1205; lean_object* x_1206; uint8_t x_1207; 
x_1205 = lean_ctor_get(x_1123, 1);
lean_inc(x_1205);
lean_dec(x_1123);
x_1206 = lean_array_get_size(x_7);
x_1207 = lean_nat_dec_lt(x_10, x_1206);
lean_dec(x_1206);
if (x_1207 == 0)
{
uint8_t x_1208; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
x_1208 = l_Array_isEmpty___rarg(x_11);
if (x_1208 == 0)
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1209 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1209, 0, x_90);
x_1210 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1211 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1211, 0, x_1210);
lean_ctor_set(x_1211, 1, x_1209);
x_1212 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1213 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1213, 0, x_1211);
lean_ctor_set(x_1213, 1, x_1212);
x_1214 = x_11;
x_1215 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_1214);
x_1216 = x_1215;
x_1217 = l_Array_toList___rarg(x_1216);
lean_dec(x_1216);
x_1218 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1217);
x_1219 = l_Array_HasRepr___rarg___closed__1;
x_1220 = lean_string_append(x_1219, x_1218);
lean_dec(x_1218);
x_1221 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1221, 0, x_1220);
x_1222 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1222, 0, x_1221);
x_1223 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1223, 0, x_1213);
lean_ctor_set(x_1223, 1, x_1222);
x_1224 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1223, x_4, x_1205);
lean_dec(x_6);
return x_1224;
}
else
{
lean_object* x_1225; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; uint8_t x_1254; 
lean_dec(x_90);
lean_dec(x_11);
x_1250 = l_Lean_Elab_Term_getOptions(x_4, x_1205);
x_1251 = lean_ctor_get(x_1250, 0);
lean_inc(x_1251);
x_1252 = lean_ctor_get(x_1250, 1);
lean_inc(x_1252);
lean_dec(x_1250);
x_1253 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1254 = l_Lean_checkTraceOption(x_1251, x_1253);
lean_dec(x_1251);
if (x_1254 == 0)
{
x_1225 = x_1252;
goto block_1249;
}
else
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; 
lean_inc(x_2);
x_1255 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1255, 0, x_2);
x_1256 = l_Lean_Elab_Term_logTrace(x_1253, x_6, x_1255, x_4, x_1252);
x_1257 = lean_ctor_get(x_1256, 1);
lean_inc(x_1257);
lean_dec(x_1256);
x_1225 = x_1257;
goto block_1249;
}
block_1249:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1226; 
lean_dec(x_3);
x_1226 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1225);
lean_dec(x_12);
if (lean_obj_tag(x_1226) == 0)
{
lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; 
x_1227 = lean_ctor_get(x_1226, 1);
lean_inc(x_1227);
if (lean_is_exclusive(x_1226)) {
 lean_ctor_release(x_1226, 0);
 lean_ctor_release(x_1226, 1);
 x_1228 = x_1226;
} else {
 lean_dec_ref(x_1226);
 x_1228 = lean_box(0);
}
if (lean_is_scalar(x_1228)) {
 x_1229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1229 = x_1228;
}
lean_ctor_set(x_1229, 0, x_2);
lean_ctor_set(x_1229, 1, x_1227);
return x_1229;
}
else
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; 
lean_dec(x_2);
x_1230 = lean_ctor_get(x_1226, 0);
lean_inc(x_1230);
x_1231 = lean_ctor_get(x_1226, 1);
lean_inc(x_1231);
if (lean_is_exclusive(x_1226)) {
 lean_ctor_release(x_1226, 0);
 lean_ctor_release(x_1226, 1);
 x_1232 = x_1226;
} else {
 lean_dec_ref(x_1226);
 x_1232 = lean_box(0);
}
if (lean_is_scalar(x_1232)) {
 x_1233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1233 = x_1232;
}
lean_ctor_set(x_1233, 0, x_1230);
lean_ctor_set(x_1233, 1, x_1231);
return x_1233;
}
}
else
{
lean_object* x_1234; lean_object* x_1235; 
x_1234 = lean_ctor_get(x_8, 0);
lean_inc(x_1234);
lean_dec(x_8);
lean_inc(x_4);
x_1235 = l_Lean_Elab_Term_isDefEq(x_6, x_1234, x_3, x_4, x_1225);
if (lean_obj_tag(x_1235) == 0)
{
lean_object* x_1236; lean_object* x_1237; 
x_1236 = lean_ctor_get(x_1235, 1);
lean_inc(x_1236);
lean_dec(x_1235);
x_1237 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1236);
lean_dec(x_12);
if (lean_obj_tag(x_1237) == 0)
{
lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; 
x_1238 = lean_ctor_get(x_1237, 1);
lean_inc(x_1238);
if (lean_is_exclusive(x_1237)) {
 lean_ctor_release(x_1237, 0);
 lean_ctor_release(x_1237, 1);
 x_1239 = x_1237;
} else {
 lean_dec_ref(x_1237);
 x_1239 = lean_box(0);
}
if (lean_is_scalar(x_1239)) {
 x_1240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1240 = x_1239;
}
lean_ctor_set(x_1240, 0, x_2);
lean_ctor_set(x_1240, 1, x_1238);
return x_1240;
}
else
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; 
lean_dec(x_2);
x_1241 = lean_ctor_get(x_1237, 0);
lean_inc(x_1241);
x_1242 = lean_ctor_get(x_1237, 1);
lean_inc(x_1242);
if (lean_is_exclusive(x_1237)) {
 lean_ctor_release(x_1237, 0);
 lean_ctor_release(x_1237, 1);
 x_1243 = x_1237;
} else {
 lean_dec_ref(x_1237);
 x_1243 = lean_box(0);
}
if (lean_is_scalar(x_1243)) {
 x_1244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1244 = x_1243;
}
lean_ctor_set(x_1244, 0, x_1241);
lean_ctor_set(x_1244, 1, x_1242);
return x_1244;
}
}
else
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1245 = lean_ctor_get(x_1235, 0);
lean_inc(x_1245);
x_1246 = lean_ctor_get(x_1235, 1);
lean_inc(x_1246);
if (lean_is_exclusive(x_1235)) {
 lean_ctor_release(x_1235, 0);
 lean_ctor_release(x_1235, 1);
 x_1247 = x_1235;
} else {
 lean_dec_ref(x_1235);
 x_1247 = lean_box(0);
}
if (lean_is_scalar(x_1247)) {
 x_1248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1248 = x_1247;
}
lean_ctor_set(x_1248, 0, x_1245);
lean_ctor_set(x_1248, 1, x_1246);
return x_1248;
}
}
}
}
}
else
{
lean_object* x_1258; lean_object* x_1259; 
lean_dec(x_90);
lean_dec(x_3);
x_1258 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1259 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1258, x_91, x_4, x_1205);
if (lean_obj_tag(x_1259) == 0)
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; uint8_t x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1260 = lean_ctor_get(x_1259, 0);
lean_inc(x_1260);
x_1261 = lean_ctor_get(x_1259, 1);
lean_inc(x_1261);
lean_dec(x_1259);
x_1262 = lean_unsigned_to_nat(1u);
x_1263 = lean_nat_add(x_10, x_1262);
lean_dec(x_10);
x_1264 = 1;
x_1265 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1265, 0, x_6);
lean_ctor_set(x_1265, 1, x_7);
lean_ctor_set(x_1265, 2, x_8);
lean_ctor_set(x_1265, 3, x_1263);
lean_ctor_set(x_1265, 4, x_11);
lean_ctor_set(x_1265, 5, x_12);
lean_ctor_set(x_1265, 6, x_13);
lean_ctor_set_uint8(x_1265, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1265, sizeof(void*)*7 + 1, x_1264);
lean_inc(x_1260);
x_1266 = l_Lean_mkApp(x_2, x_1260);
x_1267 = lean_expr_instantiate1(x_92, x_1260);
lean_dec(x_1260);
lean_dec(x_92);
x_1 = x_1265;
x_2 = x_1266;
x_3 = x_1267;
x_5 = x_1261;
goto _start;
}
else
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
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
x_1269 = lean_ctor_get(x_1259, 0);
lean_inc(x_1269);
x_1270 = lean_ctor_get(x_1259, 1);
lean_inc(x_1270);
if (lean_is_exclusive(x_1259)) {
 lean_ctor_release(x_1259, 0);
 lean_ctor_release(x_1259, 1);
 x_1271 = x_1259;
} else {
 lean_dec_ref(x_1259);
 x_1271 = lean_box(0);
}
if (lean_is_scalar(x_1271)) {
 x_1272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1272 = x_1271;
}
lean_ctor_set(x_1272, 0, x_1269);
lean_ctor_set(x_1272, 1, x_1270);
return x_1272;
}
}
}
else
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; 
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
x_1273 = lean_ctor_get(x_1123, 0);
lean_inc(x_1273);
x_1274 = lean_ctor_get(x_1123, 1);
lean_inc(x_1274);
if (lean_is_exclusive(x_1123)) {
 lean_ctor_release(x_1123, 0);
 lean_ctor_release(x_1123, 1);
 x_1275 = x_1123;
} else {
 lean_dec_ref(x_1123);
 x_1275 = lean_box(0);
}
if (lean_is_scalar(x_1275)) {
 x_1276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1276 = x_1275;
}
lean_ctor_set(x_1276, 0, x_1273);
lean_ctor_set(x_1276, 1, x_1274);
return x_1276;
}
}
}
else
{
uint8_t x_1277; 
lean_dec(x_90);
lean_dec(x_16);
lean_dec(x_3);
x_1277 = !lean_is_exclusive(x_1);
if (x_1277 == 0)
{
lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; uint8_t x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; 
x_1278 = lean_ctor_get(x_1, 6);
lean_dec(x_1278);
x_1279 = lean_ctor_get(x_1, 5);
lean_dec(x_1279);
x_1280 = lean_ctor_get(x_1, 4);
lean_dec(x_1280);
x_1281 = lean_ctor_get(x_1, 3);
lean_dec(x_1281);
x_1282 = lean_ctor_get(x_1, 2);
lean_dec(x_1282);
x_1283 = lean_ctor_get(x_1, 1);
lean_dec(x_1283);
x_1284 = lean_ctor_get(x_1, 0);
lean_dec(x_1284);
x_1285 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1285, 0, x_91);
x_1286 = 1;
x_1287 = lean_box(0);
lean_inc(x_4);
x_1288 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_1285, x_1286, x_1287, x_4, x_17);
x_1289 = lean_ctor_get(x_1288, 0);
lean_inc(x_1289);
x_1290 = lean_ctor_get(x_1288, 1);
lean_inc(x_1290);
lean_dec(x_1288);
x_1291 = lean_unsigned_to_nat(1u);
x_1292 = lean_nat_add(x_10, x_1291);
lean_dec(x_10);
x_1293 = l_Lean_Expr_mvarId_x21(x_1289);
x_1294 = lean_array_push(x_12, x_1293);
lean_ctor_set(x_1, 5, x_1294);
lean_ctor_set(x_1, 3, x_1292);
lean_inc(x_1289);
x_1295 = l_Lean_mkApp(x_2, x_1289);
x_1296 = lean_expr_instantiate1(x_92, x_1289);
lean_dec(x_1289);
lean_dec(x_92);
x_2 = x_1295;
x_3 = x_1296;
x_5 = x_1290;
goto _start;
}
else
{
lean_object* x_1298; uint8_t x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; 
lean_dec(x_1);
x_1298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1298, 0, x_91);
x_1299 = 1;
x_1300 = lean_box(0);
lean_inc(x_4);
x_1301 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_1298, x_1299, x_1300, x_4, x_17);
x_1302 = lean_ctor_get(x_1301, 0);
lean_inc(x_1302);
x_1303 = lean_ctor_get(x_1301, 1);
lean_inc(x_1303);
lean_dec(x_1301);
x_1304 = lean_unsigned_to_nat(1u);
x_1305 = lean_nat_add(x_10, x_1304);
lean_dec(x_10);
x_1306 = l_Lean_Expr_mvarId_x21(x_1302);
x_1307 = lean_array_push(x_12, x_1306);
x_1308 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1308, 0, x_6);
lean_ctor_set(x_1308, 1, x_7);
lean_ctor_set(x_1308, 2, x_8);
lean_ctor_set(x_1308, 3, x_1305);
lean_ctor_set(x_1308, 4, x_11);
lean_ctor_set(x_1308, 5, x_1307);
lean_ctor_set(x_1308, 6, x_13);
lean_ctor_set_uint8(x_1308, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1308, sizeof(void*)*7 + 1, x_14);
lean_inc(x_1302);
x_1309 = l_Lean_mkApp(x_2, x_1302);
x_1310 = lean_expr_instantiate1(x_92, x_1302);
lean_dec(x_1302);
lean_dec(x_92);
x_1 = x_1308;
x_2 = x_1309;
x_3 = x_1310;
x_5 = x_1303;
goto _start;
}
}
}
}
default: 
{
lean_object* x_1312; uint8_t x_1313; 
lean_inc(x_4);
lean_inc(x_1);
x_1312 = l___private_Init_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_17);
x_1313 = !lean_is_exclusive(x_1);
if (x_1313 == 0)
{
lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; 
x_1314 = lean_ctor_get(x_1, 6);
lean_dec(x_1314);
x_1315 = lean_ctor_get(x_1, 5);
lean_dec(x_1315);
x_1316 = lean_ctor_get(x_1, 4);
lean_dec(x_1316);
x_1317 = lean_ctor_get(x_1, 3);
lean_dec(x_1317);
x_1318 = lean_ctor_get(x_1, 2);
lean_dec(x_1318);
x_1319 = lean_ctor_get(x_1, 1);
lean_dec(x_1319);
x_1320 = lean_ctor_get(x_1, 0);
lean_dec(x_1320);
if (lean_obj_tag(x_1312) == 0)
{
lean_object* x_1321; uint8_t x_1322; lean_object* x_1323; uint8_t x_1324; 
x_1321 = lean_ctor_get(x_1312, 1);
lean_inc(x_1321);
lean_dec(x_1312);
x_1322 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_1322);
x_1323 = lean_array_get_size(x_7);
x_1324 = lean_nat_dec_lt(x_10, x_1323);
lean_dec(x_1323);
if (x_1324 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1325; 
x_1325 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_1325) == 0)
{
lean_object* x_1326; 
x_1326 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_1326) == 0)
{
uint8_t x_1327; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
x_1327 = l_Array_isEmpty___rarg(x_11);
if (x_1327 == 0)
{
lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1328 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1328, 0, x_90);
x_1329 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1330 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1330, 0, x_1329);
lean_ctor_set(x_1330, 1, x_1328);
x_1331 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1332 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1332, 0, x_1330);
lean_ctor_set(x_1332, 1, x_1331);
x_1333 = x_11;
x_1334 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_1333);
x_1335 = x_1334;
x_1336 = l_Array_toList___rarg(x_1335);
lean_dec(x_1335);
x_1337 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1336);
x_1338 = l_Array_HasRepr___rarg___closed__1;
x_1339 = lean_string_append(x_1338, x_1337);
lean_dec(x_1337);
x_1340 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1340, 0, x_1339);
x_1341 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1341, 0, x_1340);
x_1342 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1342, 0, x_1332);
lean_ctor_set(x_1342, 1, x_1341);
x_1343 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1342, x_4, x_1321);
lean_dec(x_6);
return x_1343;
}
else
{
lean_object* x_1344; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; uint8_t x_1375; 
lean_dec(x_90);
lean_dec(x_11);
x_1371 = l_Lean_Elab_Term_getOptions(x_4, x_1321);
x_1372 = lean_ctor_get(x_1371, 0);
lean_inc(x_1372);
x_1373 = lean_ctor_get(x_1371, 1);
lean_inc(x_1373);
lean_dec(x_1371);
x_1374 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1375 = l_Lean_checkTraceOption(x_1372, x_1374);
lean_dec(x_1372);
if (x_1375 == 0)
{
x_1344 = x_1373;
goto block_1370;
}
else
{
lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; 
lean_inc(x_2);
x_1376 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1376, 0, x_2);
x_1377 = l_Lean_Elab_Term_logTrace(x_1374, x_6, x_1376, x_4, x_1373);
x_1378 = lean_ctor_get(x_1377, 1);
lean_inc(x_1378);
lean_dec(x_1377);
x_1344 = x_1378;
goto block_1370;
}
block_1370:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1345; 
lean_dec(x_3);
x_1345 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1344);
lean_dec(x_12);
if (lean_obj_tag(x_1345) == 0)
{
uint8_t x_1346; 
x_1346 = !lean_is_exclusive(x_1345);
if (x_1346 == 0)
{
lean_object* x_1347; 
x_1347 = lean_ctor_get(x_1345, 0);
lean_dec(x_1347);
lean_ctor_set(x_1345, 0, x_2);
return x_1345;
}
else
{
lean_object* x_1348; lean_object* x_1349; 
x_1348 = lean_ctor_get(x_1345, 1);
lean_inc(x_1348);
lean_dec(x_1345);
x_1349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1349, 0, x_2);
lean_ctor_set(x_1349, 1, x_1348);
return x_1349;
}
}
else
{
uint8_t x_1350; 
lean_dec(x_2);
x_1350 = !lean_is_exclusive(x_1345);
if (x_1350 == 0)
{
return x_1345;
}
else
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; 
x_1351 = lean_ctor_get(x_1345, 0);
x_1352 = lean_ctor_get(x_1345, 1);
lean_inc(x_1352);
lean_inc(x_1351);
lean_dec(x_1345);
x_1353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1353, 0, x_1351);
lean_ctor_set(x_1353, 1, x_1352);
return x_1353;
}
}
}
else
{
lean_object* x_1354; lean_object* x_1355; 
x_1354 = lean_ctor_get(x_8, 0);
lean_inc(x_1354);
lean_dec(x_8);
lean_inc(x_4);
x_1355 = l_Lean_Elab_Term_isDefEq(x_6, x_1354, x_3, x_4, x_1344);
if (lean_obj_tag(x_1355) == 0)
{
lean_object* x_1356; lean_object* x_1357; 
x_1356 = lean_ctor_get(x_1355, 1);
lean_inc(x_1356);
lean_dec(x_1355);
x_1357 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1356);
lean_dec(x_12);
if (lean_obj_tag(x_1357) == 0)
{
uint8_t x_1358; 
x_1358 = !lean_is_exclusive(x_1357);
if (x_1358 == 0)
{
lean_object* x_1359; 
x_1359 = lean_ctor_get(x_1357, 0);
lean_dec(x_1359);
lean_ctor_set(x_1357, 0, x_2);
return x_1357;
}
else
{
lean_object* x_1360; lean_object* x_1361; 
x_1360 = lean_ctor_get(x_1357, 1);
lean_inc(x_1360);
lean_dec(x_1357);
x_1361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1361, 0, x_2);
lean_ctor_set(x_1361, 1, x_1360);
return x_1361;
}
}
else
{
uint8_t x_1362; 
lean_dec(x_2);
x_1362 = !lean_is_exclusive(x_1357);
if (x_1362 == 0)
{
return x_1357;
}
else
{
lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; 
x_1363 = lean_ctor_get(x_1357, 0);
x_1364 = lean_ctor_get(x_1357, 1);
lean_inc(x_1364);
lean_inc(x_1363);
lean_dec(x_1357);
x_1365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1365, 0, x_1363);
lean_ctor_set(x_1365, 1, x_1364);
return x_1365;
}
}
}
else
{
uint8_t x_1366; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1366 = !lean_is_exclusive(x_1355);
if (x_1366 == 0)
{
return x_1355;
}
else
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; 
x_1367 = lean_ctor_get(x_1355, 0);
x_1368 = lean_ctor_get(x_1355, 1);
lean_inc(x_1368);
lean_inc(x_1367);
lean_dec(x_1355);
x_1369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1369, 0, x_1367);
lean_ctor_set(x_1369, 1, x_1368);
return x_1369;
}
}
}
}
}
}
else
{
lean_object* x_1379; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1379 = lean_ctor_get(x_1326, 0);
lean_inc(x_1379);
lean_dec(x_1326);
if (lean_obj_tag(x_1379) == 4)
{
lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; 
x_1380 = lean_ctor_get(x_1379, 0);
lean_inc(x_1380);
lean_dec(x_1379);
x_1381 = l_Lean_Elab_Term_getEnv___rarg(x_1321);
x_1382 = lean_ctor_get(x_1381, 0);
lean_inc(x_1382);
x_1383 = lean_ctor_get(x_1381, 1);
lean_inc(x_1383);
lean_dec(x_1381);
x_1384 = l___private_Init_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1382, x_1380);
if (lean_obj_tag(x_1384) == 0)
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_1385 = lean_ctor_get(x_1384, 0);
lean_inc(x_1385);
lean_dec(x_1384);
x_1386 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1386, 0, x_1385);
x_1387 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1387, 0, x_1386);
x_1388 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1387, x_4, x_1383);
lean_dec(x_6);
return x_1388;
}
else
{
lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; 
x_1389 = lean_ctor_get(x_1384, 0);
lean_inc(x_1389);
lean_dec(x_1384);
x_1390 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1383);
x_1391 = lean_ctor_get(x_1390, 1);
lean_inc(x_1391);
lean_dec(x_1390);
x_1392 = l_Lean_Elab_Term_getMainModule___rarg(x_1391);
x_1393 = lean_ctor_get(x_1392, 1);
lean_inc(x_1393);
lean_dec(x_1392);
x_1394 = l_Lean_Syntax_getArgs(x_1389);
lean_dec(x_1389);
x_1395 = l_Array_empty___closed__1;
x_1396 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1394, x_1394, x_94, x_1395);
lean_dec(x_1394);
x_1397 = l_Lean_nullKind___closed__2;
x_1398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1398, 0, x_1397);
lean_ctor_set(x_1398, 1, x_1396);
x_1399 = lean_array_push(x_1395, x_1398);
x_1400 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_1401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1401, 0, x_1400);
lean_ctor_set(x_1401, 1, x_1399);
x_1402 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1403 = lean_array_push(x_1402, x_1401);
x_1404 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1405 = lean_array_push(x_1403, x_1404);
x_1406 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1407, 0, x_1406);
lean_ctor_set(x_1407, 1, x_1405);
x_1408 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_1409 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_1410 = lean_nat_sub(x_1409, x_94);
lean_dec(x_1409);
x_1411 = lean_unsigned_to_nat(1u);
x_1412 = lean_nat_sub(x_1410, x_1411);
lean_dec(x_1410);
x_1413 = l_Lean_Expr_getRevArg_x21___main(x_91, x_1412);
lean_dec(x_91);
if (lean_obj_tag(x_1408) == 0)
{
lean_object* x_1414; lean_object* x_1415; 
x_1414 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1414, 0, x_1407);
lean_inc(x_4);
lean_inc(x_2);
x_1415 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1414, x_1413, x_4, x_1393);
if (lean_obj_tag(x_1415) == 0)
{
lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; 
x_1416 = lean_ctor_get(x_1415, 0);
lean_inc(x_1416);
x_1417 = lean_ctor_get(x_1415, 1);
lean_inc(x_1417);
lean_dec(x_1415);
lean_inc(x_1416);
x_1418 = l_Lean_mkApp(x_2, x_1416);
x_1419 = lean_expr_instantiate1(x_92, x_1416);
lean_dec(x_1416);
lean_dec(x_92);
x_2 = x_1418;
x_3 = x_1419;
x_5 = x_1417;
goto _start;
}
else
{
uint8_t x_1421; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1421 = !lean_is_exclusive(x_1415);
if (x_1421 == 0)
{
return x_1415;
}
else
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; 
x_1422 = lean_ctor_get(x_1415, 0);
x_1423 = lean_ctor_get(x_1415, 1);
lean_inc(x_1423);
lean_inc(x_1422);
lean_dec(x_1415);
x_1424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1424, 0, x_1422);
lean_ctor_set(x_1424, 1, x_1423);
return x_1424;
}
}
}
else
{
lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; 
x_1425 = lean_ctor_get(x_1408, 0);
lean_inc(x_1425);
lean_dec(x_1408);
x_1426 = l_Lean_Syntax_replaceInfo___main(x_1425, x_1407);
x_1427 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1427, 0, x_1426);
lean_inc(x_4);
lean_inc(x_2);
x_1428 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1427, x_1413, x_4, x_1393);
if (lean_obj_tag(x_1428) == 0)
{
lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; 
x_1429 = lean_ctor_get(x_1428, 0);
lean_inc(x_1429);
x_1430 = lean_ctor_get(x_1428, 1);
lean_inc(x_1430);
lean_dec(x_1428);
lean_inc(x_1429);
x_1431 = l_Lean_mkApp(x_2, x_1429);
x_1432 = lean_expr_instantiate1(x_92, x_1429);
lean_dec(x_1429);
lean_dec(x_92);
x_2 = x_1431;
x_3 = x_1432;
x_5 = x_1430;
goto _start;
}
else
{
uint8_t x_1434; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1434 = !lean_is_exclusive(x_1428);
if (x_1434 == 0)
{
return x_1428;
}
else
{
lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; 
x_1435 = lean_ctor_get(x_1428, 0);
x_1436 = lean_ctor_get(x_1428, 1);
lean_inc(x_1436);
lean_inc(x_1435);
lean_dec(x_1428);
x_1437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1437, 0, x_1435);
lean_ctor_set(x_1437, 1, x_1436);
return x_1437;
}
}
}
}
}
else
{
lean_object* x_1438; lean_object* x_1439; 
lean_dec(x_1379);
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_1438 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1439 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1438, x_4, x_1321);
lean_dec(x_6);
return x_1439;
}
}
}
else
{
lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1440 = lean_ctor_get(x_1325, 0);
lean_inc(x_1440);
lean_dec(x_1325);
lean_inc(x_1440);
x_1441 = l_Lean_mkApp(x_2, x_1440);
x_1442 = lean_expr_instantiate1(x_92, x_1440);
lean_dec(x_1440);
lean_dec(x_92);
x_2 = x_1441;
x_3 = x_1442;
x_5 = x_1321;
goto _start;
}
}
else
{
uint8_t x_1444; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
x_1444 = l_Array_isEmpty___rarg(x_11);
if (x_1444 == 0)
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1445 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1445, 0, x_90);
x_1446 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1447 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1447, 0, x_1446);
lean_ctor_set(x_1447, 1, x_1445);
x_1448 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1449 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1449, 0, x_1447);
lean_ctor_set(x_1449, 1, x_1448);
x_1450 = x_11;
x_1451 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_1450);
x_1452 = x_1451;
x_1453 = l_Array_toList___rarg(x_1452);
lean_dec(x_1452);
x_1454 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1453);
x_1455 = l_Array_HasRepr___rarg___closed__1;
x_1456 = lean_string_append(x_1455, x_1454);
lean_dec(x_1454);
x_1457 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1457, 0, x_1456);
x_1458 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1458, 0, x_1457);
x_1459 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1459, 0, x_1449);
lean_ctor_set(x_1459, 1, x_1458);
x_1460 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1459, x_4, x_1321);
lean_dec(x_6);
return x_1460;
}
else
{
lean_object* x_1461; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; uint8_t x_1492; 
lean_dec(x_90);
lean_dec(x_11);
x_1488 = l_Lean_Elab_Term_getOptions(x_4, x_1321);
x_1489 = lean_ctor_get(x_1488, 0);
lean_inc(x_1489);
x_1490 = lean_ctor_get(x_1488, 1);
lean_inc(x_1490);
lean_dec(x_1488);
x_1491 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1492 = l_Lean_checkTraceOption(x_1489, x_1491);
lean_dec(x_1489);
if (x_1492 == 0)
{
x_1461 = x_1490;
goto block_1487;
}
else
{
lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; 
lean_inc(x_2);
x_1493 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1493, 0, x_2);
x_1494 = l_Lean_Elab_Term_logTrace(x_1491, x_6, x_1493, x_4, x_1490);
x_1495 = lean_ctor_get(x_1494, 1);
lean_inc(x_1495);
lean_dec(x_1494);
x_1461 = x_1495;
goto block_1487;
}
block_1487:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1462; 
lean_dec(x_3);
x_1462 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1461);
lean_dec(x_12);
if (lean_obj_tag(x_1462) == 0)
{
uint8_t x_1463; 
x_1463 = !lean_is_exclusive(x_1462);
if (x_1463 == 0)
{
lean_object* x_1464; 
x_1464 = lean_ctor_get(x_1462, 0);
lean_dec(x_1464);
lean_ctor_set(x_1462, 0, x_2);
return x_1462;
}
else
{
lean_object* x_1465; lean_object* x_1466; 
x_1465 = lean_ctor_get(x_1462, 1);
lean_inc(x_1465);
lean_dec(x_1462);
x_1466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1466, 0, x_2);
lean_ctor_set(x_1466, 1, x_1465);
return x_1466;
}
}
else
{
uint8_t x_1467; 
lean_dec(x_2);
x_1467 = !lean_is_exclusive(x_1462);
if (x_1467 == 0)
{
return x_1462;
}
else
{
lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; 
x_1468 = lean_ctor_get(x_1462, 0);
x_1469 = lean_ctor_get(x_1462, 1);
lean_inc(x_1469);
lean_inc(x_1468);
lean_dec(x_1462);
x_1470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1470, 0, x_1468);
lean_ctor_set(x_1470, 1, x_1469);
return x_1470;
}
}
}
else
{
lean_object* x_1471; lean_object* x_1472; 
x_1471 = lean_ctor_get(x_8, 0);
lean_inc(x_1471);
lean_dec(x_8);
lean_inc(x_4);
x_1472 = l_Lean_Elab_Term_isDefEq(x_6, x_1471, x_3, x_4, x_1461);
if (lean_obj_tag(x_1472) == 0)
{
lean_object* x_1473; lean_object* x_1474; 
x_1473 = lean_ctor_get(x_1472, 1);
lean_inc(x_1473);
lean_dec(x_1472);
x_1474 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1473);
lean_dec(x_12);
if (lean_obj_tag(x_1474) == 0)
{
uint8_t x_1475; 
x_1475 = !lean_is_exclusive(x_1474);
if (x_1475 == 0)
{
lean_object* x_1476; 
x_1476 = lean_ctor_get(x_1474, 0);
lean_dec(x_1476);
lean_ctor_set(x_1474, 0, x_2);
return x_1474;
}
else
{
lean_object* x_1477; lean_object* x_1478; 
x_1477 = lean_ctor_get(x_1474, 1);
lean_inc(x_1477);
lean_dec(x_1474);
x_1478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1478, 0, x_2);
lean_ctor_set(x_1478, 1, x_1477);
return x_1478;
}
}
else
{
uint8_t x_1479; 
lean_dec(x_2);
x_1479 = !lean_is_exclusive(x_1474);
if (x_1479 == 0)
{
return x_1474;
}
else
{
lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; 
x_1480 = lean_ctor_get(x_1474, 0);
x_1481 = lean_ctor_get(x_1474, 1);
lean_inc(x_1481);
lean_inc(x_1480);
lean_dec(x_1474);
x_1482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1482, 0, x_1480);
lean_ctor_set(x_1482, 1, x_1481);
return x_1482;
}
}
}
else
{
uint8_t x_1483; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1483 = !lean_is_exclusive(x_1472);
if (x_1483 == 0)
{
return x_1472;
}
else
{
lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; 
x_1484 = lean_ctor_get(x_1472, 0);
x_1485 = lean_ctor_get(x_1472, 1);
lean_inc(x_1485);
lean_inc(x_1484);
lean_dec(x_1472);
x_1486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1486, 0, x_1484);
lean_ctor_set(x_1486, 1, x_1485);
return x_1486;
}
}
}
}
}
}
}
else
{
lean_object* x_1496; lean_object* x_1497; 
lean_dec(x_1);
lean_dec(x_90);
lean_dec(x_3);
x_1496 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1497 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1496, x_91, x_4, x_1321);
if (lean_obj_tag(x_1497) == 0)
{
lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; 
x_1498 = lean_ctor_get(x_1497, 0);
lean_inc(x_1498);
x_1499 = lean_ctor_get(x_1497, 1);
lean_inc(x_1499);
lean_dec(x_1497);
x_1500 = lean_unsigned_to_nat(1u);
x_1501 = lean_nat_add(x_10, x_1500);
lean_dec(x_10);
x_1502 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1502, 0, x_6);
lean_ctor_set(x_1502, 1, x_7);
lean_ctor_set(x_1502, 2, x_8);
lean_ctor_set(x_1502, 3, x_1501);
lean_ctor_set(x_1502, 4, x_11);
lean_ctor_set(x_1502, 5, x_12);
lean_ctor_set(x_1502, 6, x_13);
lean_ctor_set_uint8(x_1502, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1502, sizeof(void*)*7 + 1, x_1322);
lean_inc(x_1498);
x_1503 = l_Lean_mkApp(x_2, x_1498);
x_1504 = lean_expr_instantiate1(x_92, x_1498);
lean_dec(x_1498);
lean_dec(x_92);
x_1 = x_1502;
x_2 = x_1503;
x_3 = x_1504;
x_5 = x_1499;
goto _start;
}
else
{
uint8_t x_1506; 
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
x_1506 = !lean_is_exclusive(x_1497);
if (x_1506 == 0)
{
return x_1497;
}
else
{
lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; 
x_1507 = lean_ctor_get(x_1497, 0);
x_1508 = lean_ctor_get(x_1497, 1);
lean_inc(x_1508);
lean_inc(x_1507);
lean_dec(x_1497);
x_1509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1509, 0, x_1507);
lean_ctor_set(x_1509, 1, x_1508);
return x_1509;
}
}
}
}
else
{
uint8_t x_1510; 
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
x_1510 = !lean_is_exclusive(x_1312);
if (x_1510 == 0)
{
return x_1312;
}
else
{
lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; 
x_1511 = lean_ctor_get(x_1312, 0);
x_1512 = lean_ctor_get(x_1312, 1);
lean_inc(x_1512);
lean_inc(x_1511);
lean_dec(x_1312);
x_1513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1513, 0, x_1511);
lean_ctor_set(x_1513, 1, x_1512);
return x_1513;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1312) == 0)
{
lean_object* x_1514; uint8_t x_1515; lean_object* x_1516; lean_object* x_1517; uint8_t x_1518; 
x_1514 = lean_ctor_get(x_1312, 1);
lean_inc(x_1514);
lean_dec(x_1312);
x_1515 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1516 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1516, 0, x_6);
lean_ctor_set(x_1516, 1, x_7);
lean_ctor_set(x_1516, 2, x_8);
lean_ctor_set(x_1516, 3, x_10);
lean_ctor_set(x_1516, 4, x_11);
lean_ctor_set(x_1516, 5, x_12);
lean_ctor_set(x_1516, 6, x_13);
lean_ctor_set_uint8(x_1516, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1516, sizeof(void*)*7 + 1, x_1515);
x_1517 = lean_array_get_size(x_7);
x_1518 = lean_nat_dec_lt(x_10, x_1517);
lean_dec(x_1517);
if (x_1518 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1519; 
x_1519 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_1519) == 0)
{
lean_object* x_1520; 
x_1520 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_1520) == 0)
{
uint8_t x_1521; 
lean_dec(x_1516);
lean_dec(x_92);
lean_dec(x_91);
x_1521 = l_Array_isEmpty___rarg(x_11);
if (x_1521 == 0)
{
lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1522 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1522, 0, x_90);
x_1523 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1524 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1524, 0, x_1523);
lean_ctor_set(x_1524, 1, x_1522);
x_1525 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1526 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1526, 0, x_1524);
lean_ctor_set(x_1526, 1, x_1525);
x_1527 = x_11;
x_1528 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_1527);
x_1529 = x_1528;
x_1530 = l_Array_toList___rarg(x_1529);
lean_dec(x_1529);
x_1531 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1530);
x_1532 = l_Array_HasRepr___rarg___closed__1;
x_1533 = lean_string_append(x_1532, x_1531);
lean_dec(x_1531);
x_1534 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1534, 0, x_1533);
x_1535 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1535, 0, x_1534);
x_1536 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1536, 0, x_1526);
lean_ctor_set(x_1536, 1, x_1535);
x_1537 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1536, x_4, x_1514);
lean_dec(x_6);
return x_1537;
}
else
{
lean_object* x_1538; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; uint8_t x_1567; 
lean_dec(x_90);
lean_dec(x_11);
x_1563 = l_Lean_Elab_Term_getOptions(x_4, x_1514);
x_1564 = lean_ctor_get(x_1563, 0);
lean_inc(x_1564);
x_1565 = lean_ctor_get(x_1563, 1);
lean_inc(x_1565);
lean_dec(x_1563);
x_1566 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1567 = l_Lean_checkTraceOption(x_1564, x_1566);
lean_dec(x_1564);
if (x_1567 == 0)
{
x_1538 = x_1565;
goto block_1562;
}
else
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; 
lean_inc(x_2);
x_1568 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1568, 0, x_2);
x_1569 = l_Lean_Elab_Term_logTrace(x_1566, x_6, x_1568, x_4, x_1565);
x_1570 = lean_ctor_get(x_1569, 1);
lean_inc(x_1570);
lean_dec(x_1569);
x_1538 = x_1570;
goto block_1562;
}
block_1562:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1539; 
lean_dec(x_3);
x_1539 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1538);
lean_dec(x_12);
if (lean_obj_tag(x_1539) == 0)
{
lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; 
x_1540 = lean_ctor_get(x_1539, 1);
lean_inc(x_1540);
if (lean_is_exclusive(x_1539)) {
 lean_ctor_release(x_1539, 0);
 lean_ctor_release(x_1539, 1);
 x_1541 = x_1539;
} else {
 lean_dec_ref(x_1539);
 x_1541 = lean_box(0);
}
if (lean_is_scalar(x_1541)) {
 x_1542 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1542 = x_1541;
}
lean_ctor_set(x_1542, 0, x_2);
lean_ctor_set(x_1542, 1, x_1540);
return x_1542;
}
else
{
lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; 
lean_dec(x_2);
x_1543 = lean_ctor_get(x_1539, 0);
lean_inc(x_1543);
x_1544 = lean_ctor_get(x_1539, 1);
lean_inc(x_1544);
if (lean_is_exclusive(x_1539)) {
 lean_ctor_release(x_1539, 0);
 lean_ctor_release(x_1539, 1);
 x_1545 = x_1539;
} else {
 lean_dec_ref(x_1539);
 x_1545 = lean_box(0);
}
if (lean_is_scalar(x_1545)) {
 x_1546 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1546 = x_1545;
}
lean_ctor_set(x_1546, 0, x_1543);
lean_ctor_set(x_1546, 1, x_1544);
return x_1546;
}
}
else
{
lean_object* x_1547; lean_object* x_1548; 
x_1547 = lean_ctor_get(x_8, 0);
lean_inc(x_1547);
lean_dec(x_8);
lean_inc(x_4);
x_1548 = l_Lean_Elab_Term_isDefEq(x_6, x_1547, x_3, x_4, x_1538);
if (lean_obj_tag(x_1548) == 0)
{
lean_object* x_1549; lean_object* x_1550; 
x_1549 = lean_ctor_get(x_1548, 1);
lean_inc(x_1549);
lean_dec(x_1548);
x_1550 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1549);
lean_dec(x_12);
if (lean_obj_tag(x_1550) == 0)
{
lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; 
x_1551 = lean_ctor_get(x_1550, 1);
lean_inc(x_1551);
if (lean_is_exclusive(x_1550)) {
 lean_ctor_release(x_1550, 0);
 lean_ctor_release(x_1550, 1);
 x_1552 = x_1550;
} else {
 lean_dec_ref(x_1550);
 x_1552 = lean_box(0);
}
if (lean_is_scalar(x_1552)) {
 x_1553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1553 = x_1552;
}
lean_ctor_set(x_1553, 0, x_2);
lean_ctor_set(x_1553, 1, x_1551);
return x_1553;
}
else
{
lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; 
lean_dec(x_2);
x_1554 = lean_ctor_get(x_1550, 0);
lean_inc(x_1554);
x_1555 = lean_ctor_get(x_1550, 1);
lean_inc(x_1555);
if (lean_is_exclusive(x_1550)) {
 lean_ctor_release(x_1550, 0);
 lean_ctor_release(x_1550, 1);
 x_1556 = x_1550;
} else {
 lean_dec_ref(x_1550);
 x_1556 = lean_box(0);
}
if (lean_is_scalar(x_1556)) {
 x_1557 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1557 = x_1556;
}
lean_ctor_set(x_1557, 0, x_1554);
lean_ctor_set(x_1557, 1, x_1555);
return x_1557;
}
}
else
{
lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1558 = lean_ctor_get(x_1548, 0);
lean_inc(x_1558);
x_1559 = lean_ctor_get(x_1548, 1);
lean_inc(x_1559);
if (lean_is_exclusive(x_1548)) {
 lean_ctor_release(x_1548, 0);
 lean_ctor_release(x_1548, 1);
 x_1560 = x_1548;
} else {
 lean_dec_ref(x_1548);
 x_1560 = lean_box(0);
}
if (lean_is_scalar(x_1560)) {
 x_1561 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1561 = x_1560;
}
lean_ctor_set(x_1561, 0, x_1558);
lean_ctor_set(x_1561, 1, x_1559);
return x_1561;
}
}
}
}
}
else
{
lean_object* x_1571; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1571 = lean_ctor_get(x_1520, 0);
lean_inc(x_1571);
lean_dec(x_1520);
if (lean_obj_tag(x_1571) == 4)
{
lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; 
x_1572 = lean_ctor_get(x_1571, 0);
lean_inc(x_1572);
lean_dec(x_1571);
x_1573 = l_Lean_Elab_Term_getEnv___rarg(x_1514);
x_1574 = lean_ctor_get(x_1573, 0);
lean_inc(x_1574);
x_1575 = lean_ctor_get(x_1573, 1);
lean_inc(x_1575);
lean_dec(x_1573);
x_1576 = l___private_Init_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1574, x_1572);
if (lean_obj_tag(x_1576) == 0)
{
lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; 
lean_dec(x_1516);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_1577 = lean_ctor_get(x_1576, 0);
lean_inc(x_1577);
lean_dec(x_1576);
x_1578 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1578, 0, x_1577);
x_1579 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1579, 0, x_1578);
x_1580 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1579, x_4, x_1575);
lean_dec(x_6);
return x_1580;
}
else
{
lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; 
x_1581 = lean_ctor_get(x_1576, 0);
lean_inc(x_1581);
lean_dec(x_1576);
x_1582 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1575);
x_1583 = lean_ctor_get(x_1582, 1);
lean_inc(x_1583);
lean_dec(x_1582);
x_1584 = l_Lean_Elab_Term_getMainModule___rarg(x_1583);
x_1585 = lean_ctor_get(x_1584, 1);
lean_inc(x_1585);
lean_dec(x_1584);
x_1586 = l_Lean_Syntax_getArgs(x_1581);
lean_dec(x_1581);
x_1587 = l_Array_empty___closed__1;
x_1588 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1586, x_1586, x_94, x_1587);
lean_dec(x_1586);
x_1589 = l_Lean_nullKind___closed__2;
x_1590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1590, 0, x_1589);
lean_ctor_set(x_1590, 1, x_1588);
x_1591 = lean_array_push(x_1587, x_1590);
x_1592 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_1593 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1593, 0, x_1592);
lean_ctor_set(x_1593, 1, x_1591);
x_1594 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1595 = lean_array_push(x_1594, x_1593);
x_1596 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1597 = lean_array_push(x_1595, x_1596);
x_1598 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1599, 0, x_1598);
lean_ctor_set(x_1599, 1, x_1597);
x_1600 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_1601 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_1602 = lean_nat_sub(x_1601, x_94);
lean_dec(x_1601);
x_1603 = lean_unsigned_to_nat(1u);
x_1604 = lean_nat_sub(x_1602, x_1603);
lean_dec(x_1602);
x_1605 = l_Lean_Expr_getRevArg_x21___main(x_91, x_1604);
lean_dec(x_91);
if (lean_obj_tag(x_1600) == 0)
{
lean_object* x_1606; lean_object* x_1607; 
x_1606 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1606, 0, x_1599);
lean_inc(x_4);
lean_inc(x_2);
x_1607 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1606, x_1605, x_4, x_1585);
if (lean_obj_tag(x_1607) == 0)
{
lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; 
x_1608 = lean_ctor_get(x_1607, 0);
lean_inc(x_1608);
x_1609 = lean_ctor_get(x_1607, 1);
lean_inc(x_1609);
lean_dec(x_1607);
lean_inc(x_1608);
x_1610 = l_Lean_mkApp(x_2, x_1608);
x_1611 = lean_expr_instantiate1(x_92, x_1608);
lean_dec(x_1608);
lean_dec(x_92);
x_1 = x_1516;
x_2 = x_1610;
x_3 = x_1611;
x_5 = x_1609;
goto _start;
}
else
{
lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; 
lean_dec(x_1516);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1613 = lean_ctor_get(x_1607, 0);
lean_inc(x_1613);
x_1614 = lean_ctor_get(x_1607, 1);
lean_inc(x_1614);
if (lean_is_exclusive(x_1607)) {
 lean_ctor_release(x_1607, 0);
 lean_ctor_release(x_1607, 1);
 x_1615 = x_1607;
} else {
 lean_dec_ref(x_1607);
 x_1615 = lean_box(0);
}
if (lean_is_scalar(x_1615)) {
 x_1616 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1616 = x_1615;
}
lean_ctor_set(x_1616, 0, x_1613);
lean_ctor_set(x_1616, 1, x_1614);
return x_1616;
}
}
else
{
lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; 
x_1617 = lean_ctor_get(x_1600, 0);
lean_inc(x_1617);
lean_dec(x_1600);
x_1618 = l_Lean_Syntax_replaceInfo___main(x_1617, x_1599);
x_1619 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1619, 0, x_1618);
lean_inc(x_4);
lean_inc(x_2);
x_1620 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1619, x_1605, x_4, x_1585);
if (lean_obj_tag(x_1620) == 0)
{
lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; 
x_1621 = lean_ctor_get(x_1620, 0);
lean_inc(x_1621);
x_1622 = lean_ctor_get(x_1620, 1);
lean_inc(x_1622);
lean_dec(x_1620);
lean_inc(x_1621);
x_1623 = l_Lean_mkApp(x_2, x_1621);
x_1624 = lean_expr_instantiate1(x_92, x_1621);
lean_dec(x_1621);
lean_dec(x_92);
x_1 = x_1516;
x_2 = x_1623;
x_3 = x_1624;
x_5 = x_1622;
goto _start;
}
else
{
lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; 
lean_dec(x_1516);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1626 = lean_ctor_get(x_1620, 0);
lean_inc(x_1626);
x_1627 = lean_ctor_get(x_1620, 1);
lean_inc(x_1627);
if (lean_is_exclusive(x_1620)) {
 lean_ctor_release(x_1620, 0);
 lean_ctor_release(x_1620, 1);
 x_1628 = x_1620;
} else {
 lean_dec_ref(x_1620);
 x_1628 = lean_box(0);
}
if (lean_is_scalar(x_1628)) {
 x_1629 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1629 = x_1628;
}
lean_ctor_set(x_1629, 0, x_1626);
lean_ctor_set(x_1629, 1, x_1627);
return x_1629;
}
}
}
}
else
{
lean_object* x_1630; lean_object* x_1631; 
lean_dec(x_1571);
lean_dec(x_1516);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_1630 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1631 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1630, x_4, x_1514);
lean_dec(x_6);
return x_1631;
}
}
}
else
{
lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1632 = lean_ctor_get(x_1519, 0);
lean_inc(x_1632);
lean_dec(x_1519);
lean_inc(x_1632);
x_1633 = l_Lean_mkApp(x_2, x_1632);
x_1634 = lean_expr_instantiate1(x_92, x_1632);
lean_dec(x_1632);
lean_dec(x_92);
x_1 = x_1516;
x_2 = x_1633;
x_3 = x_1634;
x_5 = x_1514;
goto _start;
}
}
else
{
uint8_t x_1636; 
lean_dec(x_1516);
lean_dec(x_92);
lean_dec(x_91);
x_1636 = l_Array_isEmpty___rarg(x_11);
if (x_1636 == 0)
{
lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1637 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1637, 0, x_90);
x_1638 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1639 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1639, 0, x_1638);
lean_ctor_set(x_1639, 1, x_1637);
x_1640 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1641 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1641, 0, x_1639);
lean_ctor_set(x_1641, 1, x_1640);
x_1642 = x_11;
x_1643 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_1642);
x_1644 = x_1643;
x_1645 = l_Array_toList___rarg(x_1644);
lean_dec(x_1644);
x_1646 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1645);
x_1647 = l_Array_HasRepr___rarg___closed__1;
x_1648 = lean_string_append(x_1647, x_1646);
lean_dec(x_1646);
x_1649 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1649, 0, x_1648);
x_1650 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1650, 0, x_1649);
x_1651 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1651, 0, x_1641);
lean_ctor_set(x_1651, 1, x_1650);
x_1652 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1651, x_4, x_1514);
lean_dec(x_6);
return x_1652;
}
else
{
lean_object* x_1653; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; uint8_t x_1682; 
lean_dec(x_90);
lean_dec(x_11);
x_1678 = l_Lean_Elab_Term_getOptions(x_4, x_1514);
x_1679 = lean_ctor_get(x_1678, 0);
lean_inc(x_1679);
x_1680 = lean_ctor_get(x_1678, 1);
lean_inc(x_1680);
lean_dec(x_1678);
x_1681 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1682 = l_Lean_checkTraceOption(x_1679, x_1681);
lean_dec(x_1679);
if (x_1682 == 0)
{
x_1653 = x_1680;
goto block_1677;
}
else
{
lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; 
lean_inc(x_2);
x_1683 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1683, 0, x_2);
x_1684 = l_Lean_Elab_Term_logTrace(x_1681, x_6, x_1683, x_4, x_1680);
x_1685 = lean_ctor_get(x_1684, 1);
lean_inc(x_1685);
lean_dec(x_1684);
x_1653 = x_1685;
goto block_1677;
}
block_1677:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1654; 
lean_dec(x_3);
x_1654 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1653);
lean_dec(x_12);
if (lean_obj_tag(x_1654) == 0)
{
lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; 
x_1655 = lean_ctor_get(x_1654, 1);
lean_inc(x_1655);
if (lean_is_exclusive(x_1654)) {
 lean_ctor_release(x_1654, 0);
 lean_ctor_release(x_1654, 1);
 x_1656 = x_1654;
} else {
 lean_dec_ref(x_1654);
 x_1656 = lean_box(0);
}
if (lean_is_scalar(x_1656)) {
 x_1657 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1657 = x_1656;
}
lean_ctor_set(x_1657, 0, x_2);
lean_ctor_set(x_1657, 1, x_1655);
return x_1657;
}
else
{
lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; 
lean_dec(x_2);
x_1658 = lean_ctor_get(x_1654, 0);
lean_inc(x_1658);
x_1659 = lean_ctor_get(x_1654, 1);
lean_inc(x_1659);
if (lean_is_exclusive(x_1654)) {
 lean_ctor_release(x_1654, 0);
 lean_ctor_release(x_1654, 1);
 x_1660 = x_1654;
} else {
 lean_dec_ref(x_1654);
 x_1660 = lean_box(0);
}
if (lean_is_scalar(x_1660)) {
 x_1661 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1661 = x_1660;
}
lean_ctor_set(x_1661, 0, x_1658);
lean_ctor_set(x_1661, 1, x_1659);
return x_1661;
}
}
else
{
lean_object* x_1662; lean_object* x_1663; 
x_1662 = lean_ctor_get(x_8, 0);
lean_inc(x_1662);
lean_dec(x_8);
lean_inc(x_4);
x_1663 = l_Lean_Elab_Term_isDefEq(x_6, x_1662, x_3, x_4, x_1653);
if (lean_obj_tag(x_1663) == 0)
{
lean_object* x_1664; lean_object* x_1665; 
x_1664 = lean_ctor_get(x_1663, 1);
lean_inc(x_1664);
lean_dec(x_1663);
x_1665 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1664);
lean_dec(x_12);
if (lean_obj_tag(x_1665) == 0)
{
lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; 
x_1666 = lean_ctor_get(x_1665, 1);
lean_inc(x_1666);
if (lean_is_exclusive(x_1665)) {
 lean_ctor_release(x_1665, 0);
 lean_ctor_release(x_1665, 1);
 x_1667 = x_1665;
} else {
 lean_dec_ref(x_1665);
 x_1667 = lean_box(0);
}
if (lean_is_scalar(x_1667)) {
 x_1668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1668 = x_1667;
}
lean_ctor_set(x_1668, 0, x_2);
lean_ctor_set(x_1668, 1, x_1666);
return x_1668;
}
else
{
lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; 
lean_dec(x_2);
x_1669 = lean_ctor_get(x_1665, 0);
lean_inc(x_1669);
x_1670 = lean_ctor_get(x_1665, 1);
lean_inc(x_1670);
if (lean_is_exclusive(x_1665)) {
 lean_ctor_release(x_1665, 0);
 lean_ctor_release(x_1665, 1);
 x_1671 = x_1665;
} else {
 lean_dec_ref(x_1665);
 x_1671 = lean_box(0);
}
if (lean_is_scalar(x_1671)) {
 x_1672 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1672 = x_1671;
}
lean_ctor_set(x_1672, 0, x_1669);
lean_ctor_set(x_1672, 1, x_1670);
return x_1672;
}
}
else
{
lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1673 = lean_ctor_get(x_1663, 0);
lean_inc(x_1673);
x_1674 = lean_ctor_get(x_1663, 1);
lean_inc(x_1674);
if (lean_is_exclusive(x_1663)) {
 lean_ctor_release(x_1663, 0);
 lean_ctor_release(x_1663, 1);
 x_1675 = x_1663;
} else {
 lean_dec_ref(x_1663);
 x_1675 = lean_box(0);
}
if (lean_is_scalar(x_1675)) {
 x_1676 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1676 = x_1675;
}
lean_ctor_set(x_1676, 0, x_1673);
lean_ctor_set(x_1676, 1, x_1674);
return x_1676;
}
}
}
}
}
}
else
{
lean_object* x_1686; lean_object* x_1687; 
lean_dec(x_1516);
lean_dec(x_90);
lean_dec(x_3);
x_1686 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1687 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1686, x_91, x_4, x_1514);
if (lean_obj_tag(x_1687) == 0)
{
lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; 
x_1688 = lean_ctor_get(x_1687, 0);
lean_inc(x_1688);
x_1689 = lean_ctor_get(x_1687, 1);
lean_inc(x_1689);
lean_dec(x_1687);
x_1690 = lean_unsigned_to_nat(1u);
x_1691 = lean_nat_add(x_10, x_1690);
lean_dec(x_10);
x_1692 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1692, 0, x_6);
lean_ctor_set(x_1692, 1, x_7);
lean_ctor_set(x_1692, 2, x_8);
lean_ctor_set(x_1692, 3, x_1691);
lean_ctor_set(x_1692, 4, x_11);
lean_ctor_set(x_1692, 5, x_12);
lean_ctor_set(x_1692, 6, x_13);
lean_ctor_set_uint8(x_1692, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1692, sizeof(void*)*7 + 1, x_1515);
lean_inc(x_1688);
x_1693 = l_Lean_mkApp(x_2, x_1688);
x_1694 = lean_expr_instantiate1(x_92, x_1688);
lean_dec(x_1688);
lean_dec(x_92);
x_1 = x_1692;
x_2 = x_1693;
x_3 = x_1694;
x_5 = x_1689;
goto _start;
}
else
{
lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; 
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
x_1696 = lean_ctor_get(x_1687, 0);
lean_inc(x_1696);
x_1697 = lean_ctor_get(x_1687, 1);
lean_inc(x_1697);
if (lean_is_exclusive(x_1687)) {
 lean_ctor_release(x_1687, 0);
 lean_ctor_release(x_1687, 1);
 x_1698 = x_1687;
} else {
 lean_dec_ref(x_1687);
 x_1698 = lean_box(0);
}
if (lean_is_scalar(x_1698)) {
 x_1699 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1699 = x_1698;
}
lean_ctor_set(x_1699, 0, x_1696);
lean_ctor_set(x_1699, 1, x_1697);
return x_1699;
}
}
}
else
{
lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; 
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
x_1700 = lean_ctor_get(x_1312, 0);
lean_inc(x_1700);
x_1701 = lean_ctor_get(x_1312, 1);
lean_inc(x_1701);
if (lean_is_exclusive(x_1312)) {
 lean_ctor_release(x_1312, 0);
 lean_ctor_release(x_1312, 1);
 x_1702 = x_1312;
} else {
 lean_dec_ref(x_1312);
 x_1702 = lean_box(0);
}
if (lean_is_scalar(x_1702)) {
 x_1703 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1703 = x_1702;
}
lean_ctor_set(x_1703, 0, x_1700);
lean_ctor_set(x_1703, 1, x_1701);
return x_1703;
}
}
}
}
}
else
{
lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; 
lean_dec(x_90);
lean_dec(x_3);
x_1704 = lean_ctor_get(x_95, 0);
lean_inc(x_1704);
lean_dec(x_95);
x_1705 = l_Lean_Elab_Term_NamedArg_inhabited;
x_1706 = lean_array_get(x_1705, x_11, x_1704);
x_1707 = l_Array_eraseIdx___rarg(x_11, x_1704);
lean_dec(x_1704);
x_1708 = lean_ctor_get(x_1706, 1);
lean_inc(x_1708);
lean_dec(x_1706);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1709 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1708, x_91, x_4, x_17);
if (lean_obj_tag(x_1709) == 0)
{
lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; uint8_t x_1713; 
x_1710 = lean_ctor_get(x_1709, 0);
lean_inc(x_1710);
x_1711 = lean_ctor_get(x_1709, 1);
lean_inc(x_1711);
lean_dec(x_1709);
lean_inc(x_4);
lean_inc(x_1);
x_1712 = l___private_Init_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_1711);
x_1713 = !lean_is_exclusive(x_1);
if (x_1713 == 0)
{
lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; 
x_1714 = lean_ctor_get(x_1, 6);
lean_dec(x_1714);
x_1715 = lean_ctor_get(x_1, 5);
lean_dec(x_1715);
x_1716 = lean_ctor_get(x_1, 4);
lean_dec(x_1716);
x_1717 = lean_ctor_get(x_1, 3);
lean_dec(x_1717);
x_1718 = lean_ctor_get(x_1, 2);
lean_dec(x_1718);
x_1719 = lean_ctor_get(x_1, 1);
lean_dec(x_1719);
x_1720 = lean_ctor_get(x_1, 0);
lean_dec(x_1720);
if (lean_obj_tag(x_1712) == 0)
{
lean_object* x_1721; uint8_t x_1722; lean_object* x_1723; lean_object* x_1724; 
x_1721 = lean_ctor_get(x_1712, 1);
lean_inc(x_1721);
lean_dec(x_1712);
x_1722 = 1;
lean_ctor_set(x_1, 4, x_1707);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 1, x_1722);
lean_inc(x_1710);
x_1723 = l_Lean_mkApp(x_2, x_1710);
x_1724 = lean_expr_instantiate1(x_92, x_1710);
lean_dec(x_1710);
lean_dec(x_92);
x_2 = x_1723;
x_3 = x_1724;
x_5 = x_1721;
goto _start;
}
else
{
uint8_t x_1726; 
lean_free_object(x_1);
lean_dec(x_1710);
lean_dec(x_1707);
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1726 = !lean_is_exclusive(x_1712);
if (x_1726 == 0)
{
return x_1712;
}
else
{
lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; 
x_1727 = lean_ctor_get(x_1712, 0);
x_1728 = lean_ctor_get(x_1712, 1);
lean_inc(x_1728);
lean_inc(x_1727);
lean_dec(x_1712);
x_1729 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1729, 0, x_1727);
lean_ctor_set(x_1729, 1, x_1728);
return x_1729;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1712) == 0)
{
lean_object* x_1730; uint8_t x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; 
x_1730 = lean_ctor_get(x_1712, 1);
lean_inc(x_1730);
lean_dec(x_1712);
x_1731 = 1;
x_1732 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_1732, 0, x_6);
lean_ctor_set(x_1732, 1, x_7);
lean_ctor_set(x_1732, 2, x_8);
lean_ctor_set(x_1732, 3, x_10);
lean_ctor_set(x_1732, 4, x_1707);
lean_ctor_set(x_1732, 5, x_12);
lean_ctor_set(x_1732, 6, x_13);
lean_ctor_set_uint8(x_1732, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_1732, sizeof(void*)*7 + 1, x_1731);
lean_inc(x_1710);
x_1733 = l_Lean_mkApp(x_2, x_1710);
x_1734 = lean_expr_instantiate1(x_92, x_1710);
lean_dec(x_1710);
lean_dec(x_92);
x_1 = x_1732;
x_2 = x_1733;
x_3 = x_1734;
x_5 = x_1730;
goto _start;
}
else
{
lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; 
lean_dec(x_1710);
lean_dec(x_1707);
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1736 = lean_ctor_get(x_1712, 0);
lean_inc(x_1736);
x_1737 = lean_ctor_get(x_1712, 1);
lean_inc(x_1737);
if (lean_is_exclusive(x_1712)) {
 lean_ctor_release(x_1712, 0);
 lean_ctor_release(x_1712, 1);
 x_1738 = x_1712;
} else {
 lean_dec_ref(x_1712);
 x_1738 = lean_box(0);
}
if (lean_is_scalar(x_1738)) {
 x_1739 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1739 = x_1738;
}
lean_ctor_set(x_1739, 0, x_1736);
lean_ctor_set(x_1739, 1, x_1737);
return x_1739;
}
}
}
else
{
uint8_t x_1740; 
lean_dec(x_1707);
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
x_1740 = !lean_is_exclusive(x_1709);
if (x_1740 == 0)
{
return x_1709;
}
else
{
lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; 
x_1741 = lean_ctor_get(x_1709, 0);
x_1742 = lean_ctor_get(x_1709, 1);
lean_inc(x_1742);
lean_inc(x_1741);
lean_dec(x_1709);
x_1743 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1743, 0, x_1741);
lean_ctor_set(x_1743, 1, x_1742);
return x_1743;
}
}
}
}
else
{
lean_object* x_1744; 
lean_dec(x_13);
x_1744 = lean_box(0);
x_18 = x_1744;
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
x_20 = l___private_Init_Lean_Elab_App_4__tryCoeFun(x_6, x_16, x_2, x_4, x_17);
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
x_37 = l___private_Init_Lean_Elab_App_4__tryCoeFun(x_6, x_16, x_2, x_4, x_17);
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
x_84 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
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
uint8_t x_1745; 
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
x_1745 = !lean_is_exclusive(x_15);
if (x_1745 == 0)
{
return x_15;
}
else
{
lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; 
x_1746 = lean_ctor_get(x_15, 0);
x_1747 = lean_ctor_get(x_15, 1);
lean_inc(x_1747);
lean_inc(x_1746);
lean_dec(x_15);
x_1748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1748, 0, x_1746);
lean_ctor_set(x_1748, 1, x_1747);
return x_1748;
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("args");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__1;
x_2 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit: ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__5;
x_2 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__6;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__7;
x_2 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__16;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__5;
x_2 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__9;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__10;
x_2 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_2);
x_9 = l_Lean_Elab_Term_inferType(x_1, x_2, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
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
x_46 = l_Lean_Elab_Term_getOptions(x_7, x_14);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__2;
x_50 = l_Lean_checkTraceOption(x_47, x_49);
lean_dec(x_47);
if (x_50 == 0)
{
x_15 = x_48;
goto block_45;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_inc(x_2);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_2);
lean_inc(x_13);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_13);
if (x_6 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__8;
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
x_55 = l___private_Init_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
x_58 = l_Lean_Elab_Term_logTrace(x_49, x_1, x_57, x_7, x_48);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_15 = x_59;
goto block_45;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__11;
x_61 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_51);
x_62 = l___private_Init_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_52);
x_65 = l_Lean_Elab_Term_logTrace(x_49, x_1, x_64, x_7, x_48);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_15 = x_66;
goto block_45;
}
}
block_45:
{
uint8_t x_16; 
x_16 = l_Array_isEmpty___rarg(x_3);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Term_tryPostponeIfMVar(x_13, x_7, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_empty___closed__1;
x_21 = 0;
x_22 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_22, 2, x_5);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_3);
lean_ctor_set(x_22, 5, x_20);
lean_ctor_set(x_22, 6, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*7, x_6);
lean_ctor_set_uint8(x_22, sizeof(void*)*7 + 1, x_21);
x_23 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main(x_22, x_2, x_13, x_7, x_18);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = l_Array_isEmpty___rarg(x_4);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = l_Lean_Elab_Term_tryPostponeIfMVar(x_13, x_7, x_15);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Array_empty___closed__1;
x_33 = 0;
x_34 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_4);
lean_ctor_set(x_34, 2, x_5);
lean_ctor_set(x_34, 3, x_31);
lean_ctor_set(x_34, 4, x_3);
lean_ctor_set(x_34, 5, x_32);
lean_ctor_set(x_34, 6, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*7, x_6);
lean_ctor_set_uint8(x_34, sizeof(void*)*7 + 1, x_33);
x_35 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main(x_34, x_2, x_13, x_7, x_30);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Array_empty___closed__1;
x_42 = 0;
x_43 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_4);
lean_ctor_set(x_43, 2, x_5);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_3);
lean_ctor_set(x_43, 5, x_41);
lean_ctor_set(x_43, 6, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*7, x_6);
lean_ctor_set_uint8(x_43, sizeof(void*)*7 + 1, x_42);
x_44 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main(x_43, x_2, x_13, x_7, x_15);
return x_44;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_9);
if (x_67 == 0)
{
return x_9;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_9, 0);
x_69 = lean_ctor_get(x_9, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_9);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Lean_Elab_App_11__elabAppArgs(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Init_Lean_Elab_App_12__throwLValError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = l_Lean_Meta_Exception_mkAppTypeMismatchMessage___closed__8;
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
lean_object* l___private_Init_Lean_Elab_App_12__throwLValError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_App_12__throwLValError___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_App_12__throwLValError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure has only ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" field(s)");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure expected");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, index must be greater than 0");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a valid \"field\" because environment does not contain '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__22;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__23;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("getOp");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation because environment does not contain '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__26;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__27;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_13; 
x_13 = l_Lean_Expr_getAppFn___main(x_3);
if (lean_obj_tag(x_13) == 4)
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_43; 
x_18 = l_Lean_Elab_Term_getEnv___rarg(x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_19);
x_43 = l_Lean_isStructureLike(x_19, x_14);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
x_44 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__15;
x_45 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_44, x_5, x_20);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
x_22 = x_20;
goto block_42;
}
block_42:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_inc(x_14);
lean_inc(x_19);
x_23 = l_Lean_getStructureFields(x_19, x_14);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_15, x_24);
lean_dec(x_15);
x_26 = lean_array_get_size(x_23);
x_27 = lean_nat_dec_lt(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_14);
x_28 = l_Nat_repr(x_26);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__9;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__12;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_34, x_5, x_22);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_26);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_14);
x_36 = l_Lean_isStructure(x_19, x_14);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_14);
lean_ctor_set(x_37, 1, x_25);
if (lean_is_scalar(x_21)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_21;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_22);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_array_fget(x_23, x_25);
lean_dec(x_25);
lean_dec(x_23);
lean_inc(x_14);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_14);
lean_ctor_set(x_40, 1, x_14);
lean_ctor_set(x_40, 2, x_39);
if (lean_is_scalar(x_21)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_21;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_22);
return x_41;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_50 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__18;
x_51 = l_Lean_Elab_Term_throwError___rarg(x_1, x_50, x_5, x_6);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
case 1:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_13, 0);
lean_inc(x_56);
lean_dec(x_13);
x_57 = lean_ctor_get(x_4, 0);
lean_inc(x_57);
lean_dec(x_4);
x_58 = l_Lean_Elab_Term_getEnv___rarg(x_6);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_56);
lean_inc(x_60);
x_62 = l_Lean_isStructure(x_60, x_56);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_free_object(x_58);
x_63 = lean_box(0);
lean_inc(x_57);
x_64 = lean_name_mk_string(x_63, x_57);
x_65 = l_Lean_Name_append___main(x_56, x_64);
x_66 = l_Lean_Elab_Term_getCurrNamespace(x_5, x_61);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_65);
x_69 = l_Lean_Name_replacePrefix___main(x_65, x_67, x_63);
lean_dec(x_67);
x_70 = l_Lean_Elab_Term_getLCtx(x_5, x_68);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_70, 1);
x_74 = lean_local_ctx_find_from_user_name(x_72, x_69);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
lean_inc(x_65);
x_75 = lean_environment_find(x_60, x_65);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_free_object(x_70);
lean_dec(x_56);
x_76 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_76, 0, x_57);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21;
x_79 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24;
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_82, 0, x_65);
x_83 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Elab_Term_mkConst___closed__4;
x_85 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_85, x_5, x_73);
return x_86;
}
else
{
lean_object* x_87; 
lean_dec(x_75);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_56);
lean_ctor_set(x_87, 1, x_65);
lean_ctor_set(x_70, 0, x_87);
return x_70;
}
}
else
{
lean_object* x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_74, 0);
lean_inc(x_88);
lean_dec(x_74);
x_89 = l_Lean_LocalDecl_binderInfo(x_88);
x_90 = 4;
x_91 = l_Lean_BinderInfo_beq(x_89, x_90);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_88);
lean_inc(x_65);
x_92 = lean_environment_find(x_60, x_65);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_free_object(x_70);
lean_dec(x_56);
x_93 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_93, 0, x_57);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21;
x_96 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24;
x_98 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_99, 0, x_65);
x_100 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_Elab_Term_mkConst___closed__4;
x_102 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_102, x_5, x_73);
return x_103;
}
else
{
lean_object* x_104; 
lean_dec(x_92);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_56);
lean_ctor_set(x_104, 1, x_65);
lean_ctor_set(x_70, 0, x_104);
return x_70;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_105 = l_Lean_LocalDecl_toExpr(x_88);
lean_dec(x_88);
x_106 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_106, 0, x_56);
lean_ctor_set(x_106, 1, x_65);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_70, 0, x_106);
return x_70;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_70, 0);
x_108 = lean_ctor_get(x_70, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_70);
x_109 = lean_local_ctx_find_from_user_name(x_107, x_69);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
lean_inc(x_65);
x_110 = lean_environment_find(x_60, x_65);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_56);
x_111 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_111, 0, x_57);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21;
x_114 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24;
x_116 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_117, 0, x_65);
x_118 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_Elab_Term_mkConst___closed__4;
x_120 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_120, x_5, x_108);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_110);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_122 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_122, 0, x_56);
lean_ctor_set(x_122, 1, x_65);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_108);
return x_123;
}
}
else
{
lean_object* x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_109, 0);
lean_inc(x_124);
lean_dec(x_109);
x_125 = l_Lean_LocalDecl_binderInfo(x_124);
x_126 = 4;
x_127 = l_Lean_BinderInfo_beq(x_125, x_126);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_124);
lean_inc(x_65);
x_128 = lean_environment_find(x_60, x_65);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_56);
x_129 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_129, 0, x_57);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21;
x_132 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24;
x_134 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_135, 0, x_65);
x_136 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_Elab_Term_mkConst___closed__4;
x_138 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_138, x_5, x_108);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_128);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_56);
lean_ctor_set(x_140, 1, x_65);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_108);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_142 = l_Lean_LocalDecl_toExpr(x_124);
lean_dec(x_124);
x_143 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_143, 0, x_56);
lean_ctor_set(x_143, 1, x_65);
lean_ctor_set(x_143, 2, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_108);
return x_144;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_box(0);
lean_inc(x_57);
x_146 = lean_name_mk_string(x_145, x_57);
lean_inc(x_56);
lean_inc(x_60);
x_147 = l_Lean_findField_x3f___main(x_60, x_56, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
lean_free_object(x_58);
x_148 = l_Lean_Name_append___main(x_56, x_146);
x_149 = l_Lean_Elab_Term_getCurrNamespace(x_5, x_61);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
lean_inc(x_148);
x_152 = l_Lean_Name_replacePrefix___main(x_148, x_150, x_145);
lean_dec(x_150);
x_153 = l_Lean_Elab_Term_getLCtx(x_5, x_151);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_153, 0);
x_156 = lean_ctor_get(x_153, 1);
x_157 = lean_local_ctx_find_from_user_name(x_155, x_152);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
lean_inc(x_148);
x_158 = lean_environment_find(x_60, x_148);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_free_object(x_153);
lean_dec(x_56);
x_159 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_159, 0, x_57);
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_161 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21;
x_162 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24;
x_164 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_165, 0, x_148);
x_166 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_Elab_Term_mkConst___closed__4;
x_168 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_168, x_5, x_156);
return x_169;
}
else
{
lean_object* x_170; 
lean_dec(x_158);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_56);
lean_ctor_set(x_170, 1, x_148);
lean_ctor_set(x_153, 0, x_170);
return x_153;
}
}
else
{
lean_object* x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; 
x_171 = lean_ctor_get(x_157, 0);
lean_inc(x_171);
lean_dec(x_157);
x_172 = l_Lean_LocalDecl_binderInfo(x_171);
x_173 = 4;
x_174 = l_Lean_BinderInfo_beq(x_172, x_173);
if (x_174 == 0)
{
lean_object* x_175; 
lean_dec(x_171);
lean_inc(x_148);
x_175 = lean_environment_find(x_60, x_148);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_free_object(x_153);
lean_dec(x_56);
x_176 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_176, 0, x_57);
x_177 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_177, 0, x_176);
x_178 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21;
x_179 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
x_180 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24;
x_181 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_182, 0, x_148);
x_183 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_Elab_Term_mkConst___closed__4;
x_185 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_185, x_5, x_156);
return x_186;
}
else
{
lean_object* x_187; 
lean_dec(x_175);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_187 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_187, 0, x_56);
lean_ctor_set(x_187, 1, x_148);
lean_ctor_set(x_153, 0, x_187);
return x_153;
}
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_188 = l_Lean_LocalDecl_toExpr(x_171);
lean_dec(x_171);
x_189 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_189, 0, x_56);
lean_ctor_set(x_189, 1, x_148);
lean_ctor_set(x_189, 2, x_188);
lean_ctor_set(x_153, 0, x_189);
return x_153;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_153, 0);
x_191 = lean_ctor_get(x_153, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_153);
x_192 = lean_local_ctx_find_from_user_name(x_190, x_152);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
lean_inc(x_148);
x_193 = lean_environment_find(x_60, x_148);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_56);
x_194 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_194, 0, x_57);
x_195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_196 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21;
x_197 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
x_198 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24;
x_199 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_200, 0, x_148);
x_201 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_Elab_Term_mkConst___closed__4;
x_203 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_203, x_5, x_191);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_193);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_56);
lean_ctor_set(x_205, 1, x_148);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_191);
return x_206;
}
}
else
{
lean_object* x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; 
x_207 = lean_ctor_get(x_192, 0);
lean_inc(x_207);
lean_dec(x_192);
x_208 = l_Lean_LocalDecl_binderInfo(x_207);
x_209 = 4;
x_210 = l_Lean_BinderInfo_beq(x_208, x_209);
if (x_210 == 0)
{
lean_object* x_211; 
lean_dec(x_207);
lean_inc(x_148);
x_211 = lean_environment_find(x_60, x_148);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_56);
x_212 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_212, 0, x_57);
x_213 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21;
x_215 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_213);
x_216 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24;
x_217 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_218, 0, x_148);
x_219 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Lean_Elab_Term_mkConst___closed__4;
x_221 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_222 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_221, x_5, x_191);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_211);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_223 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_223, 0, x_56);
lean_ctor_set(x_223, 1, x_148);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_191);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_225 = l_Lean_LocalDecl_toExpr(x_207);
lean_dec(x_207);
x_226 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_226, 0, x_56);
lean_ctor_set(x_226, 1, x_148);
lean_ctor_set(x_226, 2, x_225);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_191);
return x_227;
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_228 = lean_ctor_get(x_147, 0);
lean_inc(x_228);
lean_dec(x_147);
x_229 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_56);
lean_ctor_set(x_229, 2, x_146);
lean_ctor_set(x_58, 0, x_229);
return x_58;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_230 = lean_ctor_get(x_58, 0);
x_231 = lean_ctor_get(x_58, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_58);
lean_inc(x_56);
lean_inc(x_230);
x_232 = l_Lean_isStructure(x_230, x_56);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_233 = lean_box(0);
lean_inc(x_57);
x_234 = lean_name_mk_string(x_233, x_57);
x_235 = l_Lean_Name_append___main(x_56, x_234);
x_236 = l_Lean_Elab_Term_getCurrNamespace(x_5, x_231);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
lean_inc(x_235);
x_239 = l_Lean_Name_replacePrefix___main(x_235, x_237, x_233);
lean_dec(x_237);
x_240 = l_Lean_Elab_Term_getLCtx(x_5, x_238);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_243 = x_240;
} else {
 lean_dec_ref(x_240);
 x_243 = lean_box(0);
}
x_244 = lean_local_ctx_find_from_user_name(x_241, x_239);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; 
lean_inc(x_235);
x_245 = lean_environment_find(x_230, x_235);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_243);
lean_dec(x_56);
x_246 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_246, 0, x_57);
x_247 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_247, 0, x_246);
x_248 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21;
x_249 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24;
x_251 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_252, 0, x_235);
x_253 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_254 = l_Lean_Elab_Term_mkConst___closed__4;
x_255 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
x_256 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_255, x_5, x_242);
return x_256;
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_245);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_257 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_257, 0, x_56);
lean_ctor_set(x_257, 1, x_235);
if (lean_is_scalar(x_243)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_243;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_242);
return x_258;
}
}
else
{
lean_object* x_259; uint8_t x_260; uint8_t x_261; uint8_t x_262; 
x_259 = lean_ctor_get(x_244, 0);
lean_inc(x_259);
lean_dec(x_244);
x_260 = l_Lean_LocalDecl_binderInfo(x_259);
x_261 = 4;
x_262 = l_Lean_BinderInfo_beq(x_260, x_261);
if (x_262 == 0)
{
lean_object* x_263; 
lean_dec(x_259);
lean_inc(x_235);
x_263 = lean_environment_find(x_230, x_235);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_243);
lean_dec(x_56);
x_264 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_264, 0, x_57);
x_265 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_265, 0, x_264);
x_266 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21;
x_267 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
x_268 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24;
x_269 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_270, 0, x_235);
x_271 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
x_272 = l_Lean_Elab_Term_mkConst___closed__4;
x_273 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_274 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_273, x_5, x_242);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_263);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_275 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_275, 0, x_56);
lean_ctor_set(x_275, 1, x_235);
if (lean_is_scalar(x_243)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_243;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_242);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_230);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_277 = l_Lean_LocalDecl_toExpr(x_259);
lean_dec(x_259);
x_278 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_278, 0, x_56);
lean_ctor_set(x_278, 1, x_235);
lean_ctor_set(x_278, 2, x_277);
if (lean_is_scalar(x_243)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_243;
}
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_242);
return x_279;
}
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_box(0);
lean_inc(x_57);
x_281 = lean_name_mk_string(x_280, x_57);
lean_inc(x_56);
lean_inc(x_230);
x_282 = l_Lean_findField_x3f___main(x_230, x_56, x_281);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_283 = l_Lean_Name_append___main(x_56, x_281);
x_284 = l_Lean_Elab_Term_getCurrNamespace(x_5, x_231);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
lean_inc(x_283);
x_287 = l_Lean_Name_replacePrefix___main(x_283, x_285, x_280);
lean_dec(x_285);
x_288 = l_Lean_Elab_Term_getLCtx(x_5, x_286);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_291 = x_288;
} else {
 lean_dec_ref(x_288);
 x_291 = lean_box(0);
}
x_292 = lean_local_ctx_find_from_user_name(x_289, x_287);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; 
lean_inc(x_283);
x_293 = lean_environment_find(x_230, x_283);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_291);
lean_dec(x_56);
x_294 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_294, 0, x_57);
x_295 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_295, 0, x_294);
x_296 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21;
x_297 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_295);
x_298 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24;
x_299 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_300, 0, x_283);
x_301 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = l_Lean_Elab_Term_mkConst___closed__4;
x_303 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
x_304 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_303, x_5, x_290);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_293);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_305 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_305, 0, x_56);
lean_ctor_set(x_305, 1, x_283);
if (lean_is_scalar(x_291)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_291;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_290);
return x_306;
}
}
else
{
lean_object* x_307; uint8_t x_308; uint8_t x_309; uint8_t x_310; 
x_307 = lean_ctor_get(x_292, 0);
lean_inc(x_307);
lean_dec(x_292);
x_308 = l_Lean_LocalDecl_binderInfo(x_307);
x_309 = 4;
x_310 = l_Lean_BinderInfo_beq(x_308, x_309);
if (x_310 == 0)
{
lean_object* x_311; 
lean_dec(x_307);
lean_inc(x_283);
x_311 = lean_environment_find(x_230, x_283);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_291);
lean_dec(x_56);
x_312 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_312, 0, x_57);
x_313 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_313, 0, x_312);
x_314 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21;
x_315 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
x_316 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24;
x_317 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_318, 0, x_283);
x_319 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
x_320 = l_Lean_Elab_Term_mkConst___closed__4;
x_321 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
x_322 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_321, x_5, x_290);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; 
lean_dec(x_311);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_323 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_323, 0, x_56);
lean_ctor_set(x_323, 1, x_283);
if (lean_is_scalar(x_291)) {
 x_324 = lean_alloc_ctor(0, 2, 0);
} else {
 x_324 = x_291;
}
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_290);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_230);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_325 = l_Lean_LocalDecl_toExpr(x_307);
lean_dec(x_307);
x_326 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_326, 0, x_56);
lean_ctor_set(x_326, 1, x_283);
lean_ctor_set(x_326, 2, x_325);
if (lean_is_scalar(x_291)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_291;
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_290);
return x_327;
}
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_230);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_328 = lean_ctor_get(x_282, 0);
lean_inc(x_328);
lean_dec(x_282);
x_329 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_56);
lean_ctor_set(x_329, 2, x_281);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_231);
return x_330;
}
}
}
}
default: 
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_331 = lean_ctor_get(x_13, 0);
lean_inc(x_331);
lean_dec(x_13);
x_332 = lean_ctor_get(x_4, 0);
lean_inc(x_332);
lean_dec(x_4);
x_333 = l_Lean_Elab_Term_getEnv___rarg(x_6);
x_334 = !lean_is_exclusive(x_333);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_335 = lean_ctor_get(x_333, 0);
x_336 = lean_ctor_get(x_333, 1);
x_337 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__25;
x_338 = lean_name_mk_string(x_331, x_337);
lean_inc(x_338);
x_339 = lean_environment_find(x_335, x_338);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_free_object(x_333);
lean_dec(x_332);
x_340 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_340, 0, x_338);
x_341 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__28;
x_342 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_340);
x_343 = l_Lean_Elab_Term_mkConst___closed__4;
x_344 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
x_345 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_344, x_5, x_336);
return x_345;
}
else
{
lean_object* x_346; 
lean_dec(x_339);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_346 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_346, 0, x_338);
lean_ctor_set(x_346, 1, x_332);
lean_ctor_set(x_333, 0, x_346);
return x_333;
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_347 = lean_ctor_get(x_333, 0);
x_348 = lean_ctor_get(x_333, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_333);
x_349 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__25;
x_350 = lean_name_mk_string(x_331, x_349);
lean_inc(x_350);
x_351 = lean_environment_find(x_347, x_350);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_332);
x_352 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_352, 0, x_350);
x_353 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__28;
x_354 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_352);
x_355 = l_Lean_Elab_Term_mkConst___closed__4;
x_356 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
x_357 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_356, x_5, x_348);
return x_357;
}
else
{
lean_object* x_358; lean_object* x_359; 
lean_dec(x_351);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_358 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_358, 0, x_350);
lean_ctor_set(x_358, 1, x_332);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_348);
return x_359;
}
}
}
}
}
else
{
lean_object* x_360; 
lean_dec(x_13);
x_360 = lean_box(0);
x_7 = x_360;
goto block_12;
}
block_12:
{
lean_dec(x_7);
if (lean_obj_tag(x_4) == 2)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__6;
x_9 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_8, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__3;
x_11 = l___private_Init_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_10, x_5, x_6);
return x_11;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_App_13__resolveLValAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_App_14__resolveLValLoop___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_5, 2);
lean_inc(x_1);
x_12 = l_PersistentArray_push___rarg(x_11, x_1);
lean_ctor_set(x_5, 2, x_12);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
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
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_3, x_24);
lean_dec(x_3);
x_3 = x_25;
x_5 = x_23;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_App_14__resolveLValLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_13 = l___private_Init_Lean_Elab_App_13__resolveLValAux(x_1, x_2, x_9, x_3, x_6, x_12);
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
x_22 = l_Array_forMAux___main___at___private_Init_Lean_Elab_App_14__resolveLValLoop___main___spec__1(x_17, x_5, x_21, x_6, x_20);
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
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_App_14__resolveLValLoop___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at___private_Init_Lean_Elab_App_14__resolveLValLoop___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_App_14__resolveLValLoop___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_App_14__resolveLValLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_App_14__resolveLValLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_App_14__resolveLValLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_App_14__resolveLValLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_App_14__resolveLValLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_App_15__resolveLVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l___private_Init_Lean_Elab_App_14__resolveLValLoop___main(x_1, x_2, x_3, x_7, x_9, x_4, x_8);
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
lean_object* l___private_Init_Lean_Elab_App_15__resolveLVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_App_15__resolveLVal(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("self");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_14 = l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
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
x_21 = l___private_Init_Lean_Elab_App_11__elabAppArgs(x_1, x_11, x_17, x_19, x_18, x_20, x_4, x_12);
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
lean_object* _init_l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to access field in parent structure");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_App_16__mkBaseProjections(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__3;
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
x_14 = l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1(x_1, x_4, x_13, x_5, x_9);
return x_14;
}
}
}
lean_object* l___private_Init_Lean_Elab_App_16__mkBaseProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Elab_App_16__mkBaseProjections(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_17__addLValArg___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, function '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not have explicit argument with type (");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ...)");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, insufficient number of arguments for '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_31 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_17__addLValArg___main___spec__1(x_23, x_7, x_30);
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
x_37 = l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__12;
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
x_13 = l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__6;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__9;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_Term_throwError___rarg(x_1, x_20, x_9, x_10);
return x_21;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_17__addLValArg___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_17__addLValArg___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Elab_App_17__addLValArg___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Elab_App_17__addLValArg___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Elab_App_17__addLValArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("idx");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Elab_App_11__elabAppArgs(x_1, x_6, x_2, x_3, x_4, x_5, x_8, x_9);
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
x_13 = l___private_Init_Lean_Elab_App_15__resolveLVal(x_1, x_6, x_11, x_8, x_9);
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
x_19 = l___private_Init_Lean_Elab_App_16__mkBaseProjections(x_1, x_16, x_17, x_6, x_8, x_15);
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
x_29 = l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
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
x_36 = l___private_Init_Lean_Elab_App_11__elabAppArgs(x_1, x_25, x_32, x_34, x_33, x_35, x_8, x_26);
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
x_45 = l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
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
x_50 = l___private_Init_Lean_Elab_App_11__elabAppArgs(x_1, x_25, x_48, x_3, x_4, x_5, x_8, x_49);
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
x_82 = l___private_Init_Lean_Elab_App_11__elabAppArgs(x_1, x_73, x_80, x_78, x_79, x_81, x_8, x_74);
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
x_94 = l___private_Init_Lean_Elab_App_17__addLValArg___main(x_1, x_69, x_70, x_6, x_3, x_93, x_2, x_91, x_8, x_92);
lean_dec(x_91);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = l___private_Init_Lean_Elab_App_11__elabAppArgs(x_1, x_73, x_2, x_95, x_4, x_5, x_8, x_96);
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
x_121 = l___private_Init_Lean_Elab_App_11__elabAppArgs(x_1, x_113, x_119, x_117, x_118, x_120, x_8, x_110);
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
x_133 = l___private_Init_Lean_Elab_App_17__addLValArg___main(x_1, x_111, x_112, x_6, x_3, x_132, x_2, x_130, x_8, x_131);
lean_dec(x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l___private_Init_Lean_Elab_App_11__elabAppArgs(x_1, x_113, x_2, x_134, x_4, x_5, x_8, x_135);
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
x_154 = l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_147);
x_157 = l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
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
x_165 = l___private_Init_Lean_Elab_App_11__elabAppArgs(x_1, x_150, x_161, x_163, x_162, x_164, x_8, x_151);
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
x_174 = l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2;
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
x_180 = l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
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
x_185 = l___private_Init_Lean_Elab_App_11__elabAppArgs(x_1, x_150, x_183, x_3, x_4, x_5, x_8, x_184);
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
lean_object* l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_App_18__elabAppLValsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Init_Lean_Elab_App_18__elabAppLValsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Lean_Elab_App_18__elabAppLValsAux(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of field notation with `@` modifier");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_App_19__elabAppLVals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_List_isEmpty___rarg(x_3);
if (x_10 == 0)
{
if (x_7 == 0)
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main(x_1, x_4, x_5, x_6, x_7, x_2, x_3, x_8, x_9);
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
x_12 = l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__3;
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
x_18 = l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main(x_1, x_4, x_5, x_6, x_7, x_2, x_3, x_8, x_9);
return x_18;
}
}
}
lean_object* l___private_Init_Lean_Elab_App_19__elabAppLVals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8, x_9);
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
lean_object* l_List_map___main___at___private_Init_Lean_Elab_App_20__elabAppFnId___spec__1(lean_object* x_1) {
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
x_7 = l_List_map___main___at___private_Init_Lean_Elab_App_20__elabAppFnId___spec__1(x_5);
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
x_11 = l_List_map___main___at___private_Init_Lean_Elab_App_20__elabAppFnId___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_App_20__elabAppFnId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_16 = l_List_map___main___at___private_Init_Lean_Elab_App_20__elabAppFnId___spec__1(x_15);
lean_inc(x_2);
x_17 = l_List_append___rarg(x_16, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_14, x_17, x_3, x_4, x_5, x_6, x_9, x_10);
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
lean_object* l___private_Init_Lean_Elab_App_20__elabAppFnId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_foldlM___main___at___private_Init_Lean_Elab_App_20__elabAppFnId___spec__2(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_15, x_10, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_11);
return x_22;
}
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_App_20__elabAppFnId___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_List_foldlM___main___at___private_Init_Lean_Elab_App_20__elabAppFnId___spec__2(x_1, x_2, x_3, x_4, x_5, x_11, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l___private_Init_Lean_Elab_App_20__elabAppFnId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_8);
lean_dec(x_8);
x_13 = l___private_Init_Lean_Elab_App_20__elabAppFnId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elab_App_21__elabAppFn___main___spec__1(lean_object* x_1) {
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
x_9 = l_List_map___main___at___private_Init_Lean_Elab_App_21__elabAppFn___main___spec__1(x_5);
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
x_15 = l_List_map___main___at___private_Init_Lean_Elab_App_21__elabAppFn___main___spec__1(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_21__elabAppFn___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_19 = l___private_Init_Lean_Elab_App_21__elabAppFn___main(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12);
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
lean_object* l___private_Init_Lean_Elab_App_21__elabAppFn___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
uint8_t x_15; uint8_t x_287; lean_object* x_397; uint8_t x_398; 
x_397 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
lean_inc(x_2);
x_398 = l_Lean_Syntax_isOfKind(x_2, x_397);
if (x_398 == 0)
{
uint8_t x_399; 
x_399 = 0;
x_287 = x_399;
goto block_396;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; 
x_400 = l_Lean_Syntax_getArgs(x_2);
x_401 = lean_array_get_size(x_400);
lean_dec(x_400);
x_402 = lean_unsigned_to_nat(3u);
x_403 = lean_nat_dec_eq(x_401, x_402);
lean_dec(x_401);
x_287 = x_403;
goto block_396;
}
block_286:
{
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_170; lean_object* x_272; uint8_t x_273; 
x_272 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_2);
x_273 = l_Lean_Syntax_isOfKind(x_2, x_272);
if (x_273 == 0)
{
uint8_t x_274; 
x_274 = 0;
x_170 = x_274;
goto block_271;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_275 = l_Lean_Syntax_getArgs(x_2);
x_276 = lean_array_get_size(x_275);
lean_dec(x_275);
x_277 = lean_unsigned_to_nat(2u);
x_278 = lean_nat_dec_eq(x_276, x_277);
lean_dec(x_276);
x_170 = x_278;
goto block_271;
}
block_169:
{
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_box(0);
x_18 = 1;
lean_inc(x_10);
lean_inc(x_9);
x_19 = l_Lean_Elab_Term_elabTerm(x_2, x_17, x_18, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_array_push(x_8, x_23);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_push(x_8, x_28);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 0, x_29);
return x_19;
}
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_30);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
lean_ctor_set(x_23, 0, x_34);
x_35 = lean_array_push(x_8, x_23);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_dec(x_23);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_array_push(x_8, x_38);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 0, x_39);
return x_19;
}
}
else
{
uint8_t x_40; 
lean_free_object(x_19);
lean_dec(x_10);
lean_dec(x_8);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_23, 0);
lean_dec(x_41);
return x_23;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_dec(x_23);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_30);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_free_object(x_19);
lean_dec(x_8);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_23, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_23, 0);
lean_dec(x_46);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
else
{
lean_object* x_47; 
lean_dec(x_23);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_30);
lean_ctor_set(x_47, 1, x_10);
return x_47;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 0);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_19);
x_50 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_48, x_3, x_4, x_5, x_6, x_7, x_9, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_array_push(x_8, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_10);
return x_56;
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_57);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_60 = x_50;
} else {
 lean_dec_ref(x_50);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
lean_dec(x_58);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
x_63 = lean_array_push(x_8, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_10);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_10);
lean_dec(x_8);
x_65 = lean_ctor_get(x_50, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_66 = x_50;
} else {
 lean_dec_ref(x_50);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_8);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_68 = x_50;
} else {
 lean_dec_ref(x_50);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_57);
lean_ctor_set(x_69, 1, x_10);
return x_69;
}
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_70 = lean_ctor_get(x_19, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
lean_dec(x_70);
x_72 = !lean_is_exclusive(x_19);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_19, 0);
lean_dec(x_73);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
lean_dec(x_71);
lean_ctor_set(x_19, 0, x_74);
x_75 = lean_array_push(x_8, x_19);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_10);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_19, 1);
lean_inc(x_77);
lean_dec(x_19);
x_78 = lean_ctor_get(x_71, 0);
lean_inc(x_78);
lean_dec(x_71);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_array_push(x_8, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_10);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_10);
lean_dec(x_8);
x_82 = !lean_is_exclusive(x_19);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_19, 0);
lean_dec(x_83);
return x_19;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_19, 1);
lean_inc(x_84);
lean_dec(x_19);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_70);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_8);
x_86 = !lean_is_exclusive(x_19);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_19, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_19, 0);
lean_dec(x_88);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_89; 
lean_dec(x_19);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_70);
lean_ctor_set(x_89, 1, x_10);
return x_89;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_unsigned_to_nat(1u);
x_91 = l_Lean_Syntax_getArg(x_2, x_90);
x_92 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_91);
x_93 = l_Lean_Syntax_isOfKind(x_91, x_92);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; lean_object* x_96; 
lean_dec(x_91);
x_94 = lean_box(0);
x_95 = 1;
lean_inc(x_10);
lean_inc(x_9);
x_96 = l_Lean_Elab_Term_elabTerm(x_2, x_94, x_95, x_9, x_10);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
x_100 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_98, x_3, x_4, x_5, x_6, x_7, x_9, x_99);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_array_push(x_8, x_100);
lean_ctor_set(x_96, 1, x_10);
lean_ctor_set(x_96, 0, x_102);
return x_96;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_100, 0);
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_100);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_array_push(x_8, x_105);
lean_ctor_set(x_96, 1, x_10);
lean_ctor_set(x_96, 0, x_106);
return x_96;
}
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_100, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
lean_dec(x_107);
x_109 = !lean_is_exclusive(x_100);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_100, 0);
lean_dec(x_110);
x_111 = lean_ctor_get(x_108, 0);
lean_inc(x_111);
lean_dec(x_108);
lean_ctor_set(x_100, 0, x_111);
x_112 = lean_array_push(x_8, x_100);
lean_ctor_set(x_96, 1, x_10);
lean_ctor_set(x_96, 0, x_112);
return x_96;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_100, 1);
lean_inc(x_113);
lean_dec(x_100);
x_114 = lean_ctor_get(x_108, 0);
lean_inc(x_114);
lean_dec(x_108);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = lean_array_push(x_8, x_115);
lean_ctor_set(x_96, 1, x_10);
lean_ctor_set(x_96, 0, x_116);
return x_96;
}
}
else
{
uint8_t x_117; 
lean_free_object(x_96);
lean_dec(x_10);
lean_dec(x_8);
x_117 = !lean_is_exclusive(x_100);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_100, 0);
lean_dec(x_118);
return x_100;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_100, 1);
lean_inc(x_119);
lean_dec(x_100);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_107);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_free_object(x_96);
lean_dec(x_8);
x_121 = !lean_is_exclusive(x_100);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_100, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_100, 0);
lean_dec(x_123);
lean_ctor_set(x_100, 1, x_10);
return x_100;
}
else
{
lean_object* x_124; 
lean_dec(x_100);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_107);
lean_ctor_set(x_124, 1, x_10);
return x_124;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_96, 0);
x_126 = lean_ctor_get(x_96, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_96);
x_127 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_125, x_3, x_4, x_5, x_6, x_7, x_9, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_array_push(x_8, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_10);
return x_133;
}
else
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_127, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_134);
x_136 = lean_ctor_get(x_127, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_137 = x_127;
} else {
 lean_dec_ref(x_127);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
lean_dec(x_135);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
x_140 = lean_array_push(x_8, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_10);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_10);
lean_dec(x_8);
x_142 = lean_ctor_get(x_127, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_143 = x_127;
} else {
 lean_dec_ref(x_127);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_134);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_8);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_145 = x_127;
} else {
 lean_dec_ref(x_127);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_134);
lean_ctor_set(x_146, 1, x_10);
return x_146;
}
}
}
}
else
{
lean_object* x_147; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_147 = lean_ctor_get(x_96, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
lean_dec(x_147);
x_149 = !lean_is_exclusive(x_96);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_96, 0);
lean_dec(x_150);
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
lean_dec(x_148);
lean_ctor_set(x_96, 0, x_151);
x_152 = lean_array_push(x_8, x_96);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_10);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_96, 1);
lean_inc(x_154);
lean_dec(x_96);
x_155 = lean_ctor_get(x_148, 0);
lean_inc(x_155);
lean_dec(x_148);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = lean_array_push(x_8, x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_10);
return x_158;
}
}
else
{
uint8_t x_159; 
lean_dec(x_10);
lean_dec(x_8);
x_159 = !lean_is_exclusive(x_96);
if (x_159 == 0)
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_96, 0);
lean_dec(x_160);
return x_96;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_96, 1);
lean_inc(x_161);
lean_dec(x_96);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_147);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_8);
x_163 = !lean_is_exclusive(x_96);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_96, 1);
lean_dec(x_164);
x_165 = lean_ctor_get(x_96, 0);
lean_dec(x_165);
lean_ctor_set(x_96, 1, x_10);
return x_96;
}
else
{
lean_object* x_166; 
lean_dec(x_96);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_147);
lean_ctor_set(x_166, 1, x_10);
return x_166;
}
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_2);
x_167 = 1;
x_2 = x_91;
x_7 = x_167;
goto _start;
}
}
}
block_271:
{
if (x_170 == 0)
{
lean_object* x_171; uint8_t x_172; 
x_171 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_inc(x_2);
x_172 = l_Lean_Syntax_isOfKind(x_2, x_171);
if (x_172 == 0)
{
uint8_t x_173; 
x_173 = 0;
x_16 = x_173;
goto block_169;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_174 = l_Lean_Syntax_getArgs(x_2);
x_175 = lean_array_get_size(x_174);
lean_dec(x_174);
x_176 = lean_unsigned_to_nat(2u);
x_177 = lean_nat_dec_eq(x_175, x_176);
lean_dec(x_175);
x_16 = x_177;
goto block_169;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_178 = lean_unsigned_to_nat(0u);
x_179 = l_Lean_Syntax_getArg(x_2, x_178);
x_180 = l_Lean_identKind___closed__2;
lean_inc(x_179);
x_181 = l_Lean_Syntax_isOfKind(x_179, x_180);
if (x_181 == 0)
{
lean_object* x_182; uint8_t x_183; lean_object* x_184; 
lean_dec(x_179);
x_182 = lean_box(0);
x_183 = 1;
lean_inc(x_10);
lean_inc(x_9);
x_184 = l_Lean_Elab_Term_elabTerm(x_2, x_182, x_183, x_9, x_10);
if (lean_obj_tag(x_184) == 0)
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_184, 0);
x_187 = lean_ctor_get(x_184, 1);
x_188 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_186, x_3, x_4, x_5, x_6, x_7, x_9, x_187);
if (lean_obj_tag(x_188) == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; 
x_190 = lean_array_push(x_8, x_188);
lean_ctor_set(x_184, 1, x_10);
lean_ctor_set(x_184, 0, x_190);
return x_184;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_188, 0);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_188);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_array_push(x_8, x_193);
lean_ctor_set(x_184, 1, x_10);
lean_ctor_set(x_184, 0, x_194);
return x_184;
}
}
else
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_188, 0);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
lean_dec(x_195);
x_197 = !lean_is_exclusive(x_188);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_188, 0);
lean_dec(x_198);
x_199 = lean_ctor_get(x_196, 0);
lean_inc(x_199);
lean_dec(x_196);
lean_ctor_set(x_188, 0, x_199);
x_200 = lean_array_push(x_8, x_188);
lean_ctor_set(x_184, 1, x_10);
lean_ctor_set(x_184, 0, x_200);
return x_184;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_188, 1);
lean_inc(x_201);
lean_dec(x_188);
x_202 = lean_ctor_get(x_196, 0);
lean_inc(x_202);
lean_dec(x_196);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = lean_array_push(x_8, x_203);
lean_ctor_set(x_184, 1, x_10);
lean_ctor_set(x_184, 0, x_204);
return x_184;
}
}
else
{
uint8_t x_205; 
lean_free_object(x_184);
lean_dec(x_10);
lean_dec(x_8);
x_205 = !lean_is_exclusive(x_188);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_188, 0);
lean_dec(x_206);
return x_188;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_188, 1);
lean_inc(x_207);
lean_dec(x_188);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_195);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
uint8_t x_209; 
lean_free_object(x_184);
lean_dec(x_8);
x_209 = !lean_is_exclusive(x_188);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_188, 1);
lean_dec(x_210);
x_211 = lean_ctor_get(x_188, 0);
lean_dec(x_211);
lean_ctor_set(x_188, 1, x_10);
return x_188;
}
else
{
lean_object* x_212; 
lean_dec(x_188);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_195);
lean_ctor_set(x_212, 1, x_10);
return x_212;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_184, 0);
x_214 = lean_ctor_get(x_184, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_184);
x_215 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_213, x_3, x_4, x_5, x_6, x_7, x_9, x_214);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_218 = x_215;
} else {
 lean_dec_ref(x_215);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
x_220 = lean_array_push(x_8, x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_10);
return x_221;
}
else
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_215, 0);
lean_inc(x_222);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_222);
x_224 = lean_ctor_get(x_215, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_225 = x_215;
} else {
 lean_dec_ref(x_215);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_223, 0);
lean_inc(x_226);
lean_dec(x_223);
if (lean_is_scalar(x_225)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_225;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_224);
x_228 = lean_array_push(x_8, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_10);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_10);
lean_dec(x_8);
x_230 = lean_ctor_get(x_215, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_231 = x_215;
} else {
 lean_dec_ref(x_215);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_222);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_8);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_233 = x_215;
} else {
 lean_dec_ref(x_215);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_222);
lean_ctor_set(x_234, 1, x_10);
return x_234;
}
}
}
}
else
{
lean_object* x_235; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_235 = lean_ctor_get(x_184, 0);
lean_inc(x_235);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_obj_tag(x_236) == 0)
{
uint8_t x_237; 
lean_dec(x_235);
x_237 = !lean_is_exclusive(x_184);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_238 = lean_ctor_get(x_184, 0);
lean_dec(x_238);
x_239 = lean_ctor_get(x_236, 0);
lean_inc(x_239);
lean_dec(x_236);
lean_ctor_set(x_184, 0, x_239);
x_240 = lean_array_push(x_8, x_184);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_10);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_242 = lean_ctor_get(x_184, 1);
lean_inc(x_242);
lean_dec(x_184);
x_243 = lean_ctor_get(x_236, 0);
lean_inc(x_243);
lean_dec(x_236);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_242);
x_245 = lean_array_push(x_8, x_244);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_10);
return x_246;
}
}
else
{
uint8_t x_247; 
lean_dec(x_10);
lean_dec(x_8);
x_247 = !lean_is_exclusive(x_184);
if (x_247 == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_184, 0);
lean_dec(x_248);
return x_184;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_184, 1);
lean_inc(x_249);
lean_dec(x_184);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_235);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_8);
x_251 = !lean_is_exclusive(x_184);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_184, 1);
lean_dec(x_252);
x_253 = lean_ctor_get(x_184, 0);
lean_dec(x_253);
lean_ctor_set(x_184, 1, x_10);
return x_184;
}
else
{
lean_object* x_254; 
lean_dec(x_184);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_235);
lean_ctor_set(x_254, 1, x_10);
return x_254;
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_255 = lean_unsigned_to_nat(1u);
x_256 = l_Lean_Syntax_getArg(x_2, x_255);
lean_dec(x_2);
x_257 = l_Lean_Syntax_getArgs(x_256);
lean_dec(x_256);
x_258 = l_Array_isEmpty___rarg(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = l_Lean_Syntax_inhabited;
x_260 = lean_array_get(x_259, x_257, x_178);
lean_dec(x_257);
x_261 = l_Lean_Elab_Term_elabExplicitUniv(x_260, x_9, x_10);
lean_dec(x_260);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = l___private_Init_Lean_Elab_App_20__elabAppFnId(x_1, x_179, x_262, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_263);
return x_264;
}
else
{
uint8_t x_265; 
lean_dec(x_179);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_265 = !lean_is_exclusive(x_261);
if (x_265 == 0)
{
return x_261;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_261, 0);
x_267 = lean_ctor_get(x_261, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_261);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
else
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_257);
x_269 = lean_box(0);
x_270 = l___private_Init_Lean_Elab_App_20__elabAppFnId(x_1, x_179, x_269, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_270;
}
}
}
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_279 = lean_unsigned_to_nat(0u);
x_280 = l_Lean_Syntax_getArg(x_2, x_279);
x_281 = lean_unsigned_to_nat(2u);
x_282 = l_Lean_Syntax_getArg(x_2, x_281);
lean_dec(x_2);
x_283 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_283, 0, x_282);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_3);
x_2 = x_280;
x_3 = x_284;
goto _start;
}
}
block_396:
{
if (x_287 == 0)
{
lean_object* x_288; uint8_t x_289; 
x_288 = l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
lean_inc(x_2);
x_289 = l_Lean_Syntax_isOfKind(x_2, x_288);
if (x_289 == 0)
{
uint8_t x_290; 
x_290 = 0;
x_15 = x_290;
goto block_286;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_291 = l_Lean_Syntax_getArgs(x_2);
x_292 = lean_array_get_size(x_291);
lean_dec(x_291);
x_293 = lean_unsigned_to_nat(4u);
x_294 = lean_nat_dec_eq(x_292, x_293);
lean_dec(x_292);
x_15 = x_294;
goto block_286;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
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
x_301 = lean_box(0);
x_302 = 1;
lean_inc(x_10);
lean_inc(x_9);
x_303 = l_Lean_Elab_Term_elabTerm(x_2, x_301, x_302, x_9, x_10);
if (lean_obj_tag(x_303) == 0)
{
uint8_t x_304; 
x_304 = !lean_is_exclusive(x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_303, 0);
x_306 = lean_ctor_get(x_303, 1);
x_307 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_305, x_3, x_4, x_5, x_6, x_7, x_9, x_306);
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
x_334 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_332, x_3, x_4, x_5, x_6, x_7, x_9, x_333);
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
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_374 = l_Lean_Syntax_getId(x_296);
lean_dec(x_296);
x_375 = l_Lean_Name_eraseMacroScopes(x_374);
lean_dec(x_374);
x_376 = l_Lean_Name_components(x_375);
x_377 = l_List_map___main___at___private_Init_Lean_Elab_App_21__elabAppFn___main___spec__1(x_376);
x_378 = lean_unsigned_to_nat(0u);
x_379 = l_Lean_Syntax_getArg(x_2, x_378);
lean_dec(x_2);
x_380 = l_List_append___rarg(x_377, x_3);
x_2 = x_379;
x_3 = x_380;
goto _start;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_382 = l_Lean_fieldIdxKind;
x_383 = l_Lean_Syntax_isNatLitAux(x_382, x_296);
lean_dec(x_296);
x_384 = lean_unsigned_to_nat(0u);
x_385 = l_Lean_Syntax_getArg(x_2, x_384);
lean_dec(x_2);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_386 = l_Nat_Inhabited;
x_387 = l_Option_get_x21___rarg___closed__3;
x_388 = lean_panic_fn(x_386, x_387);
x_389 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_389, 0, x_388);
x_390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_3);
x_2 = x_385;
x_3 = x_390;
goto _start;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_383, 0);
lean_inc(x_392);
lean_dec(x_383);
x_393 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_393, 0, x_392);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_3);
x_2 = x_385;
x_3 = x_394;
goto _start;
}
}
}
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = l_Lean_Syntax_getArgs(x_2);
x_405 = lean_unsigned_to_nat(0u);
x_406 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_21__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_404, x_405, x_8, x_9, x_10);
lean_dec(x_404);
lean_dec(x_2);
return x_406;
}
}
else
{
lean_object* x_407; lean_object* x_408; 
x_407 = lean_box(0);
x_408 = l___private_Init_Lean_Elab_App_20__elabAppFnId(x_1, x_2, x_407, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_408;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_21__elabAppFn___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_21__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_2);
return x_14;
}
}
lean_object* l___private_Init_Lean_Elab_App_21__elabAppFn___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l___private_Init_Lean_Elab_App_21__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l___private_Init_Lean_Elab_App_21__elabAppFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Elab_App_21__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_App_21__elabAppFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l___private_Init_Lean_Elab_App_21__elabAppFn(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Array_filterAux___main___at___private_Init_Lean_Elab_App_22__getSuccess___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_Lean_Elab_App_22__getSuccess(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_filterAux___main___at___private_Init_Lean_Elab_App_22__getSuccess___spec__1(x_1, x_2, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_App_23__toMessageData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = l_Lean_FileMap_toPosition(x_4, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Lean_FileMap_toPosition(x_8, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_23__toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_23__toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_23__toMessageData___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_App_23__toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_App_23__toMessageData___spec__1(x_8, x_3, x_7);
lean_dec(x_8);
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
x_18 = l___private_Init_Lean_Elab_App_23__toMessageData___closed__2;
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
x_38 = l___private_Init_Lean_Elab_App_23__toMessageData___closed__2;
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
lean_object* l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_App_23__toMessageData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getPosition___at___private_Init_Lean_Elab_App_23__toMessageData___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_App_23__toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_App_23__toMessageData(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_24__mergeFailures___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_fget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_3, x_2, x_10);
x_12 = x_9;
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
x_13 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__1;
x_14 = l_unreachable_x21___rarg(x_13);
lean_inc(x_4);
x_15 = lean_apply_2(x_14, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
x_20 = x_16;
x_21 = lean_array_fset(x_11, x_2, x_20);
lean_dec(x_2);
x_2 = x_19;
x_3 = x_21;
x_5 = x_17;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
lean_dec(x_12);
x_28 = l___private_Init_Lean_Elab_App_23__toMessageData(x_27, x_1, x_4, x_5);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_2, x_31);
x_33 = x_29;
x_34 = lean_array_fset(x_11, x_2, x_33);
lean_dec(x_2);
x_2 = x_32;
x_3 = x_34;
x_5 = x_30;
goto _start;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("overloaded, errors ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_App_24__mergeFailures___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = x_1;
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_24__mergeFailures___spec__1___boxed), 5, 3);
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
x_13 = l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__3;
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
lean_object* l___private_Init_Lean_Elab_App_24__mergeFailures(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_App_24__mergeFailures___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_24__mergeFailures___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_24__mergeFailures___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_25__elabAppAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_2);
lean_inc(x_1);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_1);
lean_ctor_set(x_18, 3, x_2);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_15);
x_20 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = x_20;
x_22 = lean_array_fset(x_9, x_3, x_21);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
x_24 = l_Lean_MessageData_Inhabited;
x_25 = l_unreachable_x21___rarg(x_24);
x_26 = x_25;
x_27 = lean_array_fset(x_9, x_3, x_26);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_27;
goto _start;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_25__elabAppAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous, possible interpretations ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_25__elabAppAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_25__elabAppAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_25__elabAppAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Elab_App_25__elabAppAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_App_25__elabAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = l_Array_empty___closed__1;
lean_inc(x_6);
lean_inc(x_2);
x_11 = l___private_Init_Lean_Elab_App_21__elabAppFn___main(x_1, x_2, x_8, x_3, x_4, x_5, x_9, x_10, x_6, x_7);
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
x_18 = l_Array_filterAux___main___at___private_Init_Lean_Elab_App_22__getSuccess___spec__1(x_12, x_17, x_17);
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
x_22 = l___private_Init_Lean_Elab_App_24__mergeFailures___rarg(x_12, x_2, x_6, x_13);
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
x_30 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_25__elabAppAux___spec__1(x_24, x_27, x_17, x_29);
x_31 = x_30;
x_32 = l_Lean_MessageData_ofArray(x_31);
lean_dec(x_31);
x_33 = l___private_Init_Lean_Elab_App_25__elabAppAux___closed__3;
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
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_26__expandApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* _init_l___private_Init_Lean_Elab_App_26__expandApp___closed__1() {
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
lean_object* l___private_Init_Lean_Elab_App_26__expandApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = l___private_Init_Lean_Elab_App_26__expandApp___closed__1;
x_10 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_26__expandApp___spec__1(x_1, x_8, x_4, x_9, x_2, x_3);
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
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_26__expandApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_26__expandApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Elab_App_26__expandApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_App_26__expandApp(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l___private_Init_Lean_Elab_App_26__expandApp(x_1, x_3, x_4);
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
x_12 = l___private_Init_Lean_Elab_App_25__elabAppAux(x_1, x_9, x_10, x_11, x_2, x_3, x_8);
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
x_6 = l___private_Init_Lean_Elab_App_25__elabAppAux(x_1, x_1, x_5, x_5, x_2, x_3, x_4);
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
uint8_t x_5; lean_object* x_83; uint8_t x_84; 
x_83 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_inc(x_1);
x_84 = l_Lean_Syntax_isOfKind(x_1, x_83);
if (x_84 == 0)
{
uint8_t x_85; 
x_85 = 0;
x_5 = x_85;
goto block_82;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = l_Lean_Syntax_getArgs(x_1);
x_87 = lean_array_get_size(x_86);
lean_dec(x_86);
x_88 = lean_unsigned_to_nat(2u);
x_89 = lean_nat_dec_eq(x_87, x_88);
lean_dec(x_87);
x_5 = x_89;
goto block_82;
}
block_82:
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_71; uint8_t x_72; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_71 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_8);
x_72 = l_Lean_Syntax_isOfKind(x_8, x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = l_Lean_Parser_Term_paren___elambda__1___closed__1;
lean_inc(x_8);
x_74 = l_Lean_Syntax_isOfKind(x_8, x_73);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = 0;
x_9 = x_75;
goto block_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = l_Lean_Syntax_getArgs(x_8);
x_77 = lean_array_get_size(x_76);
lean_dec(x_76);
x_78 = lean_unsigned_to_nat(3u);
x_79 = lean_nat_dec_eq(x_77, x_78);
lean_dec(x_77);
x_9 = x_79;
goto block_70;
}
}
else
{
uint8_t x_80; lean_object* x_81; 
lean_dec(x_1);
x_80 = 1;
x_81 = l_Lean_Elab_Term_elabFunCore(x_8, x_2, x_80, x_3, x_4);
return x_81;
}
block_70:
{
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_mkTermIdFromIdent___closed__2;
x_11 = l_Lean_Syntax_isOfKind(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_63; uint8_t x_64; 
x_14 = l_Lean_Syntax_getArg(x_8, x_7);
lean_dec(x_8);
x_63 = l_Lean_nullKind___closed__2;
lean_inc(x_14);
x_64 = l_Lean_Syntax_isOfKind(x_14, x_63);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = 0;
x_15 = x_65;
goto block_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = l_Lean_Syntax_getArgs(x_14);
x_67 = lean_array_get_size(x_66);
lean_dec(x_66);
x_68 = lean_unsigned_to_nat(2u);
x_69 = lean_nat_dec_eq(x_67, x_68);
lean_dec(x_67);
x_15 = x_69;
goto block_62;
}
block_62:
{
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_14, x_17);
x_19 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_18);
x_20 = l_Lean_Syntax_isOfKind(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_53; uint8_t x_54; 
x_22 = l_Lean_Syntax_getArg(x_14, x_7);
lean_dec(x_14);
x_53 = l_Lean_nullKind___closed__2;
lean_inc(x_22);
x_54 = l_Lean_Syntax_isOfKind(x_22, x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_2);
x_55 = 0;
x_23 = x_55;
goto block_52;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_Syntax_getArgs(x_22);
x_57 = lean_array_get_size(x_56);
lean_dec(x_56);
x_58 = lean_nat_dec_eq(x_57, x_17);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_2);
x_59 = lean_nat_dec_eq(x_57, x_7);
lean_dec(x_57);
x_23 = x_59;
goto block_52;
}
else
{
uint8_t x_60; lean_object* x_61; 
lean_dec(x_57);
lean_dec(x_22);
lean_dec(x_1);
x_60 = 1;
x_61 = l_Lean_Elab_Term_elabFunCore(x_18, x_2, x_60, x_3, x_4);
return x_61;
}
}
block_52:
{
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_24 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = l_Lean_Syntax_getArg(x_22, x_17);
lean_dec(x_22);
x_26 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
lean_inc(x_25);
x_27 = l_Lean_Syntax_isOfKind(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_28 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = l_Lean_Syntax_getArgs(x_25);
x_30 = lean_array_get_size(x_29);
lean_dec(x_29);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_33 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Syntax_getArg(x_25, x_7);
lean_dec(x_25);
lean_inc(x_3);
x_35 = l_Lean_Elab_Term_elabType(x_34, x_3, x_4);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_39 = 1;
lean_inc(x_3);
lean_inc(x_38);
x_40 = l_Lean_Elab_Term_elabFunCore(x_18, x_38, x_39, x_3, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_Term_ensureHasType(x_1, x_38, x_41, x_3, x_42);
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_38);
lean_dec(x_3);
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
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_35);
if (x_48 == 0)
{
return x_35;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_35, 0);
x_50 = lean_ctor_get(x_35, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_35);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
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
lean_object* l_Lean_Elab_Term_elabSortApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Elab_Term_elabLevel(x_6, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_getKind(x_11);
x_13 = l_Lean_Parser_Term_sort___elambda__1___closed__2;
x_14 = lean_name_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_mkLevelSucc(x_9);
x_16 = l_Lean_mkSort(x_15);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_mkSort(x_9);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
x_22 = l_Lean_Syntax_getKind(x_21);
x_23 = l_Lean_Parser_Term_sort___elambda__1___closed__2;
x_24 = lean_name_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l_Lean_mkLevelSucc(x_18);
x_26 = l_Lean_mkSort(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_mkSort(x_18);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_19);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
return x_7;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabSortApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_elabSortApp(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabSortApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSortApp___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabSortApp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_sortApp___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabSortApp___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elab_App_27__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__1;
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
lean_object* initialize_Init_Lean_Util_FindMVar(lean_object*);
lean_object* initialize_Init_Lean_Elab_Term(lean_object*);
lean_object* initialize_Init_Lean_Elab_Binders(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_App(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Util_FindMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Binders(lean_io_mk_world());
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
l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__1 = _init_l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__1);
l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__2 = _init_l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__2);
l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__3 = _init_l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__3);
l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__4 = _init_l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__4);
l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__5 = _init_l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__5);
l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__6 = _init_l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__6);
l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__7 = _init_l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__7);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__1 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__1);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__2 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__2);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__4 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__4);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__5 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__5);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__7 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__7);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__8 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__8);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__10 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__10();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__10);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__11 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__11();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__11);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__13 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__13();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__13);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__14 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__14();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__14);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15);
l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16 = _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16();
lean_mark_persistent(l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16);
l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__1 = _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__1);
l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__2 = _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__2);
l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__3 = _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__3);
l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__4 = _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__4);
l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__5 = _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__5);
l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__6 = _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__6);
l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__7 = _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__7);
l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__8 = _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__8);
l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__9 = _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__9);
l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__10 = _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__10();
lean_mark_persistent(l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__10);
l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__11 = _init_l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__11();
lean_mark_persistent(l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__11);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__1 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__1);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__2 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__2);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__3 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__3);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__4 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__4);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__5 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__5);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__6 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__6);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__7 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__7);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__8 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__8);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__9 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__9);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__10 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__10();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__10);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__11 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__11();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__11);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__12 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__12();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__12);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__13 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__13();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__13);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__14 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__14();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__14);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__15 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__15();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__15);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__16 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__16();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__16);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__17 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__17();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__17);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__18 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__18();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__18);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__19 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__19();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__19);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__20 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__20();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__20);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__21);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__22 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__22();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__22);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__23 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__23();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__23);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__25 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__25();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__25);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__26 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__26();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__26);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__27 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__27();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__27);
l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__28 = _init_l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__28();
lean_mark_persistent(l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__28);
l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__1 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__1);
l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2 = _init_l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Elab_App_16__mkBaseProjections___spec__1___closed__2);
l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__1 = _init_l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__1);
l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__2 = _init_l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__2);
l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__3 = _init_l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__3);
l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__1 = _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__1);
l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__2 = _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__2);
l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__3 = _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__3);
l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__4 = _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__4);
l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__5 = _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__5);
l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__6 = _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__6);
l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__7 = _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__7);
l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__8 = _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__8();
lean_mark_persistent(l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__8);
l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__9 = _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__9();
lean_mark_persistent(l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__9);
l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__10 = _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__10();
lean_mark_persistent(l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__10);
l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__11 = _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__11();
lean_mark_persistent(l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__11);
l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__12 = _init_l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__12();
lean_mark_persistent(l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__12);
l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__1 = _init_l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__1);
l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__2 = _init_l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__2);
l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__1 = _init_l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__1);
l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__2 = _init_l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__2);
l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__3 = _init_l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__3);
l___private_Init_Lean_Elab_App_23__toMessageData___closed__1 = _init_l___private_Init_Lean_Elab_App_23__toMessageData___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_App_23__toMessageData___closed__1);
l___private_Init_Lean_Elab_App_23__toMessageData___closed__2 = _init_l___private_Init_Lean_Elab_App_23__toMessageData___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_App_23__toMessageData___closed__2);
l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__1 = _init_l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__1);
l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__2 = _init_l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__2);
l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__3 = _init_l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__3);
l___private_Init_Lean_Elab_App_25__elabAppAux___closed__1 = _init_l___private_Init_Lean_Elab_App_25__elabAppAux___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_App_25__elabAppAux___closed__1);
l___private_Init_Lean_Elab_App_25__elabAppAux___closed__2 = _init_l___private_Init_Lean_Elab_App_25__elabAppAux___closed__2();
lean_mark_persistent(l___private_Init_Lean_Elab_App_25__elabAppAux___closed__2);
l___private_Init_Lean_Elab_App_25__elabAppAux___closed__3 = _init_l___private_Init_Lean_Elab_App_25__elabAppAux___closed__3();
lean_mark_persistent(l___private_Init_Lean_Elab_App_25__elabAppAux___closed__3);
l___private_Init_Lean_Elab_App_26__expandApp___closed__1 = _init_l___private_Init_Lean_Elab_App_26__expandApp___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_App_26__expandApp___closed__1);
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
l___regBuiltin_Lean_Elab_Term_elabSortApp___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabSortApp___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabSortApp___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabSortApp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Init_Lean_Elab_App_27__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
