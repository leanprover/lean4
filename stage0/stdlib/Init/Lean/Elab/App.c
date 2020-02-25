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
lean_object* l___private_Init_Lean_Elab_App_14__resolveLValLoop___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_14__resolveLValLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__10;
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__3;
extern lean_object* l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__1;
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
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1;
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2;
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
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__3;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_26__expandApp___closed__1;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__1;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent(lean_object*);
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
extern lean_object* l___private_Init_Lean_Elab_Util_9__regTraceClasses___closed__1;
extern lean_object* l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_19__elabAppLVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__6;
lean_object* l___private_Init_Lean_Elab_App_23__toMessageData___closed__2;
extern lean_object* l_Lean_Parser_Term_sort___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited;
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__4;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3;
lean_object* l___private_Init_Lean_Elab_App_20__elabAppFnId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___private_Init_Lean_Elab_App_15__resolveLVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__3;
extern lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__3;
lean_object* l___private_Init_Lean_Elab_App_12__throwLValError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
extern uint8_t l___private_Init_Lean_Elab_Term_11__isExplicit___closed__1;
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
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__1;
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName___rarg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__3;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__8;
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__2;
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
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__1;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__3;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_replaceInfo___main(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkConst___closed__4;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__2;
lean_object* l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__2;
lean_object* l_Lean_FindMVar_main___main___at___private_Init_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__12;
lean_object* l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_hasToString(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_21__elabAppFn___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__19;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_26__expandApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__11;
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_ExprDefEq_7__checkTypesAndAssign___closed__7;
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
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__1;
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
uint8_t l_coeDecidableEq(uint8_t);
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
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_19__elabAppLVals___closed__2;
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_24__mergeFailures___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_App_14__resolveLValLoop___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_TermElabResult_inhabited;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__1;
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__6;
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
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__4;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__25;
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo___main(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__6;
lean_object* l___private_Init_Lean_Elab_App_2__elabArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_21__elabAppFn___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__2;
extern lean_object* l_Lean_Meta_Exception_mkAppTypeMismatchMessage___closed__8;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId(lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___private_Init_Lean_Elab_App_22__getSuccess(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__4;
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__13;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__2;
lean_object* l___private_Init_Lean_Elab_App_25__elabAppAux___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__5;
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Elab_Term_elabSortApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__1;
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
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__3;
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__2;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Elab_Term_registerSyntheticMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__14;
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__5;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__3;
extern lean_object* l_Lean_Parser_Term_paren___elambda__1___closed__1;
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Elab_App_6__hasTypeMVar___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChoice(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Elab_App_5__getForallBody___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__5;
lean_object* l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__5;
lean_object* l_Lean_Elab_getPos___at_Lean_Elab_Term_throwError___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__9;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__13;
lean_object* l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
lean_object* l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__1;
lean_object* l_Lean_Elab_Term_whnfCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef(lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__3;
lean_object* l_Lean_Elab_evalSyntaxConstant(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__1;
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
lean_object* l___private_Init_Lean_Elab_App_16__mkBaseProjections___closed__3;
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_16__mkBaseProjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__3;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Term_addBuiltinTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_9__nextArgIsHole___boxed(lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l___private_Init_Lean_Elab_App_5__getForallBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__24;
lean_object* l___private_Init_Lean_Elab_App_14__resolveLValLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1;
lean_object* l___private_Init_Lean_Elab_App_17__addLValArg___main___closed__7;
lean_object* l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
lean_object* l_List_foldlM___main___at___private_Init_Lean_Elab_App_20__elabAppFnId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__16;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__2;
extern lean_object* l_Lean_Meta_Exception_toStr___closed__6;
uint8_t l_Lean_Position_DecidableEq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Init_Lean_Elab_App_13__resolveLValAux___closed__7;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProj(lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp(lean_object*);
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
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__3;
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint32_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
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
x_63 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 4);
x_64 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 5);
x_65 = 0;
x_66 = 0;
x_67 = 0;
x_68 = lean_alloc_ctor(0, 10, 8);
lean_ctor_set(x_68, 0, x_53);
lean_ctor_set(x_68, 1, x_54);
lean_ctor_set(x_68, 2, x_55);
lean_ctor_set(x_68, 3, x_56);
lean_ctor_set(x_68, 4, x_57);
lean_ctor_set(x_68, 5, x_58);
lean_ctor_set(x_68, 6, x_59);
lean_ctor_set(x_68, 7, x_60);
lean_ctor_set(x_68, 8, x_61);
lean_ctor_set(x_68, 9, x_62);
lean_ctor_set_uint8(x_68, sizeof(void*)*10 + 4, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*10 + 5, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*10 + 6, x_65);
lean_ctor_set_uint32(x_68, sizeof(void*)*10, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*10 + 7, x_67);
x_69 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_1, x_52, x_68, x_36);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_unbox(x_70);
lean_dec(x_70);
x_38 = x_72;
x_39 = x_71;
goto block_51;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_73, 0);
lean_inc(x_83);
lean_dec(x_73);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_ctor_get(x_84, 4);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__7;
x_87 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = l_Lean_Elab_Term_throwError___rarg(x_1, x_87, x_4, x_74);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
return x_88;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_88);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; 
x_93 = lean_box(0);
x_75 = x_93;
goto block_82;
}
}
else
{
lean_object* x_94; 
x_94 = lean_box(0);
x_75 = x_94;
goto block_82;
}
block_82:
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_75);
x_76 = l___private_Init_Lean_Elab_App_4__tryCoeFun___closed__4;
x_77 = l_Lean_Elab_Term_throwError___rarg(x_1, x_76, x_4, x_74);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_77);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
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
uint8_t x_95; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_19);
if (x_95 == 0)
{
return x_19;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_19, 0);
x_97 = lean_ctor_get(x_19, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_19);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
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
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 6);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 7);
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
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
else
{
uint8_t x_30; 
x_30 = 1;
return x_30;
}
}
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_13);
lean_dec(x_12);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_32 = 0;
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_33 = 0;
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
x_34 = 0;
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
x_35 = 0;
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_8);
x_36 = 0;
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_7);
x_37 = 0;
return x_37;
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
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
lean_dec(x_7);
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* _init_l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_9__regTraceClasses___closed__1;
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
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 6);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 6);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 7);
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
lean_object* x_106; uint8_t x_107; uint32_t x_108; uint16_t x_109; lean_object* x_110; uint8_t x_111; 
x_106 = lean_ctor_get(x_97, 1);
lean_inc(x_106);
lean_dec(x_97);
x_107 = 1;
x_108 = 0;
x_109 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 7, x_107);
lean_ctor_set_uint32(x_1, sizeof(void*)*7, x_108);
lean_ctor_set_uint16(x_1, sizeof(void*)*7 + 4, x_109);
x_110 = lean_array_get_size(x_7);
x_111 = lean_nat_dec_lt(x_10, x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_112; 
x_112 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
x_114 = l_Array_isEmpty___rarg(x_11);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_115 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_115, 0, x_90);
x_116 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_117 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_119 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
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
lean_ctor_set(x_127, 0, x_119);
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
x_164 = lean_ctor_get(x_113, 0);
lean_inc(x_164);
lean_dec(x_113);
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
x_169 = l_Lean_Elab_evalSyntaxConstant(x_167, x_165);
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
x_225 = lean_ctor_get(x_112, 0);
lean_inc(x_225);
lean_dec(x_112);
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
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
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
x_235 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
x_236 = l_Array_toList___rarg(x_235);
lean_dec(x_235);
x_237 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_236);
x_238 = l_Array_HasRepr___rarg___closed__1;
x_239 = lean_string_append(x_238, x_237);
lean_dec(x_237);
x_240 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_241 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_241, 0, x_240);
x_242 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_242, 0, x_234);
lean_ctor_set(x_242, 1, x_241);
x_243 = l_Lean_Elab_Term_throwError___rarg(x_6, x_242, x_4, x_106);
lean_dec(x_6);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
lean_dec(x_90);
lean_dec(x_11);
x_271 = l_Lean_Elab_Term_getOptions(x_4, x_106);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_275 = l_Lean_checkTraceOption(x_272, x_274);
lean_dec(x_272);
if (x_275 == 0)
{
x_244 = x_273;
goto block_270;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_inc(x_2);
x_276 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_276, 0, x_2);
x_277 = l_Lean_Elab_Term_logTrace(x_274, x_6, x_276, x_4, x_273);
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec(x_277);
x_244 = x_278;
goto block_270;
}
block_270:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_245; 
lean_dec(x_3);
x_245 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_244);
lean_dec(x_12);
if (lean_obj_tag(x_245) == 0)
{
uint8_t x_246; 
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_245, 0);
lean_dec(x_247);
lean_ctor_set(x_245, 0, x_2);
return x_245;
}
else
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_245, 1);
lean_inc(x_248);
lean_dec(x_245);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_2);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
else
{
uint8_t x_250; 
lean_dec(x_2);
x_250 = !lean_is_exclusive(x_245);
if (x_250 == 0)
{
return x_245;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_245, 0);
x_252 = lean_ctor_get(x_245, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_245);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_8, 0);
lean_inc(x_254);
lean_dec(x_8);
lean_inc(x_4);
x_255 = l_Lean_Elab_Term_isDefEq(x_6, x_254, x_3, x_4, x_244);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
lean_dec(x_255);
x_257 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_256);
lean_dec(x_12);
if (lean_obj_tag(x_257) == 0)
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_257);
if (x_258 == 0)
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_257, 0);
lean_dec(x_259);
lean_ctor_set(x_257, 0, x_2);
return x_257;
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_257, 1);
lean_inc(x_260);
lean_dec(x_257);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_2);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
else
{
uint8_t x_262; 
lean_dec(x_2);
x_262 = !lean_is_exclusive(x_257);
if (x_262 == 0)
{
return x_257;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_257, 0);
x_264 = lean_ctor_get(x_257, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_257);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_266 = !lean_is_exclusive(x_255);
if (x_266 == 0)
{
return x_255;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_255, 0);
x_268 = lean_ctor_get(x_255, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_255);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
}
}
}
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_1);
lean_dec(x_90);
lean_dec(x_3);
x_279 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_280 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_279, x_91, x_4, x_106);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint32_t x_285; uint16_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = lean_unsigned_to_nat(1u);
x_284 = lean_nat_add(x_10, x_283);
lean_dec(x_10);
x_285 = 0;
x_286 = 0;
x_287 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_287, 0, x_6);
lean_ctor_set(x_287, 1, x_7);
lean_ctor_set(x_287, 2, x_8);
lean_ctor_set(x_287, 3, x_284);
lean_ctor_set(x_287, 4, x_11);
lean_ctor_set(x_287, 5, x_12);
lean_ctor_set(x_287, 6, x_13);
lean_ctor_set_uint8(x_287, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_287, sizeof(void*)*7 + 7, x_107);
lean_ctor_set_uint32(x_287, sizeof(void*)*7, x_285);
lean_ctor_set_uint16(x_287, sizeof(void*)*7 + 4, x_286);
lean_inc(x_281);
x_288 = l_Lean_mkApp(x_2, x_281);
x_289 = lean_expr_instantiate1(x_92, x_281);
lean_dec(x_281);
lean_dec(x_92);
x_1 = x_287;
x_2 = x_288;
x_3 = x_289;
x_5 = x_282;
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
x_291 = !lean_is_exclusive(x_280);
if (x_291 == 0)
{
return x_280;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_280, 0);
x_293 = lean_ctor_get(x_280, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_280);
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
lean_object* x_299; uint8_t x_300; uint32_t x_301; uint16_t x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_299 = lean_ctor_get(x_97, 1);
lean_inc(x_299);
lean_dec(x_97);
x_300 = 1;
x_301 = 0;
x_302 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_303 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_303, 0, x_6);
lean_ctor_set(x_303, 1, x_7);
lean_ctor_set(x_303, 2, x_8);
lean_ctor_set(x_303, 3, x_10);
lean_ctor_set(x_303, 4, x_11);
lean_ctor_set(x_303, 5, x_12);
lean_ctor_set(x_303, 6, x_13);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_303, sizeof(void*)*7 + 7, x_300);
lean_ctor_set_uint32(x_303, sizeof(void*)*7, x_301);
lean_ctor_set_uint16(x_303, sizeof(void*)*7 + 4, x_302);
x_304 = lean_array_get_size(x_7);
x_305 = lean_nat_dec_lt(x_10, x_304);
lean_dec(x_304);
if (x_305 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_306; 
x_306 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; 
x_307 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_307) == 0)
{
uint8_t x_308; 
lean_dec(x_303);
lean_dec(x_92);
lean_dec(x_91);
x_308 = l_Array_isEmpty___rarg(x_11);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_309 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_309, 0, x_90);
x_310 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_311 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_309);
x_312 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_313 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
x_314 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
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
lean_ctor_set(x_321, 0, x_313);
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
x_356 = lean_ctor_get(x_307, 0);
lean_inc(x_356);
lean_dec(x_307);
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
x_361 = l_Lean_Elab_evalSyntaxConstant(x_359, x_357);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_303);
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
x_1 = x_303;
x_2 = x_395;
x_3 = x_396;
x_5 = x_394;
goto _start;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_303);
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
x_1 = x_303;
x_2 = x_408;
x_3 = x_409;
x_5 = x_407;
goto _start;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_303);
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
lean_dec(x_303);
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
x_417 = lean_ctor_get(x_306, 0);
lean_inc(x_417);
lean_dec(x_306);
lean_inc(x_417);
x_418 = l_Lean_mkApp(x_2, x_417);
x_419 = lean_expr_instantiate1(x_92, x_417);
lean_dec(x_417);
lean_dec(x_92);
x_1 = x_303;
x_2 = x_418;
x_3 = x_419;
x_5 = x_299;
goto _start;
}
}
else
{
uint8_t x_421; 
lean_dec(x_303);
lean_dec(x_92);
lean_dec(x_91);
x_421 = l_Array_isEmpty___rarg(x_11);
if (x_421 == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
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
x_427 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
x_428 = l_Array_toList___rarg(x_427);
lean_dec(x_427);
x_429 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_428);
x_430 = l_Array_HasRepr___rarg___closed__1;
x_431 = lean_string_append(x_430, x_429);
lean_dec(x_429);
x_432 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_432, 0, x_431);
x_433 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_433, 0, x_432);
x_434 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_434, 0, x_426);
lean_ctor_set(x_434, 1, x_433);
x_435 = l_Lean_Elab_Term_throwError___rarg(x_6, x_434, x_4, x_299);
lean_dec(x_6);
return x_435;
}
else
{
lean_object* x_436; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; 
lean_dec(x_90);
lean_dec(x_11);
x_461 = l_Lean_Elab_Term_getOptions(x_4, x_299);
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
lean_dec(x_461);
x_464 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_465 = l_Lean_checkTraceOption(x_462, x_464);
lean_dec(x_462);
if (x_465 == 0)
{
x_436 = x_463;
goto block_460;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
lean_inc(x_2);
x_466 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_466, 0, x_2);
x_467 = l_Lean_Elab_Term_logTrace(x_464, x_6, x_466, x_4, x_463);
x_468 = lean_ctor_get(x_467, 1);
lean_inc(x_468);
lean_dec(x_467);
x_436 = x_468;
goto block_460;
}
block_460:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_437; 
lean_dec(x_3);
x_437 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_436);
lean_dec(x_12);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_ctor_get(x_437, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_439 = x_437;
} else {
 lean_dec_ref(x_437);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_2);
lean_ctor_set(x_440, 1, x_438);
return x_440;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_2);
x_441 = lean_ctor_get(x_437, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_437, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_443 = x_437;
} else {
 lean_dec_ref(x_437);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(1, 2, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_441);
lean_ctor_set(x_444, 1, x_442);
return x_444;
}
}
else
{
lean_object* x_445; lean_object* x_446; 
x_445 = lean_ctor_get(x_8, 0);
lean_inc(x_445);
lean_dec(x_8);
lean_inc(x_4);
x_446 = l_Lean_Elab_Term_isDefEq(x_6, x_445, x_3, x_4, x_436);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_446, 1);
lean_inc(x_447);
lean_dec(x_446);
x_448 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_447);
lean_dec(x_12);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_448, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 x_450 = x_448;
} else {
 lean_dec_ref(x_448);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_2);
lean_ctor_set(x_451, 1, x_449);
return x_451;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_2);
x_452 = lean_ctor_get(x_448, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_448, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 lean_ctor_release(x_448, 1);
 x_454 = x_448;
} else {
 lean_dec_ref(x_448);
 x_454 = lean_box(0);
}
if (lean_is_scalar(x_454)) {
 x_455 = lean_alloc_ctor(1, 2, 0);
} else {
 x_455 = x_454;
}
lean_ctor_set(x_455, 0, x_452);
lean_ctor_set(x_455, 1, x_453);
return x_455;
}
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_456 = lean_ctor_get(x_446, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_446, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 lean_ctor_release(x_446, 1);
 x_458 = x_446;
} else {
 lean_dec_ref(x_446);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(1, 2, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_456);
lean_ctor_set(x_459, 1, x_457);
return x_459;
}
}
}
}
}
}
else
{
lean_object* x_469; lean_object* x_470; 
lean_dec(x_303);
lean_dec(x_90);
lean_dec(x_3);
x_469 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_470 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_469, x_91, x_4, x_299);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint32_t x_475; uint16_t x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
x_473 = lean_unsigned_to_nat(1u);
x_474 = lean_nat_add(x_10, x_473);
lean_dec(x_10);
x_475 = 0;
x_476 = 0;
x_477 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_477, 0, x_6);
lean_ctor_set(x_477, 1, x_7);
lean_ctor_set(x_477, 2, x_8);
lean_ctor_set(x_477, 3, x_474);
lean_ctor_set(x_477, 4, x_11);
lean_ctor_set(x_477, 5, x_12);
lean_ctor_set(x_477, 6, x_13);
lean_ctor_set_uint8(x_477, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_477, sizeof(void*)*7 + 7, x_300);
lean_ctor_set_uint32(x_477, sizeof(void*)*7, x_475);
lean_ctor_set_uint16(x_477, sizeof(void*)*7 + 4, x_476);
lean_inc(x_471);
x_478 = l_Lean_mkApp(x_2, x_471);
x_479 = lean_expr_instantiate1(x_92, x_471);
lean_dec(x_471);
lean_dec(x_92);
x_1 = x_477;
x_2 = x_478;
x_3 = x_479;
x_5 = x_472;
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
x_481 = lean_ctor_get(x_470, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_470, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_483 = x_470;
} else {
 lean_dec_ref(x_470);
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
lean_object* x_506; uint32_t x_507; uint16_t x_508; lean_object* x_509; lean_object* x_510; 
x_506 = lean_ctor_get(x_503, 1);
lean_inc(x_506);
lean_dec(x_503);
x_507 = 0;
x_508 = 0;
lean_ctor_set_uint32(x_1, sizeof(void*)*7, x_507);
lean_ctor_set_uint16(x_1, sizeof(void*)*7 + 4, x_508);
lean_inc(x_501);
x_509 = l_Lean_mkApp(x_2, x_501);
x_510 = lean_expr_instantiate1(x_92, x_501);
lean_dec(x_501);
lean_dec(x_92);
x_2 = x_509;
x_3 = x_510;
x_5 = x_506;
goto _start;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; uint32_t x_515; uint16_t x_516; lean_object* x_517; lean_object* x_518; 
x_512 = lean_ctor_get(x_503, 1);
lean_inc(x_512);
lean_dec(x_503);
x_513 = l_Lean_Expr_mvarId_x21(x_501);
x_514 = lean_array_push(x_13, x_513);
x_515 = 0;
x_516 = 0;
lean_ctor_set(x_1, 6, x_514);
lean_ctor_set_uint32(x_1, sizeof(void*)*7, x_515);
lean_ctor_set_uint16(x_1, sizeof(void*)*7 + 4, x_516);
lean_inc(x_501);
x_517 = l_Lean_mkApp(x_2, x_501);
x_518 = lean_expr_instantiate1(x_92, x_501);
lean_dec(x_501);
lean_dec(x_92);
x_2 = x_517;
x_3 = x_518;
x_5 = x_512;
goto _start;
}
}
else
{
uint8_t x_520; 
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
x_520 = !lean_is_exclusive(x_503);
if (x_520 == 0)
{
return x_503;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_503, 0);
x_522 = lean_ctor_get(x_503, 1);
lean_inc(x_522);
lean_inc(x_521);
lean_dec(x_503);
x_523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_523, 0, x_521);
lean_ctor_set(x_523, 1, x_522);
return x_523;
}
}
}
else
{
lean_object* x_524; uint8_t x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_1);
x_524 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_524, 0, x_91);
x_525 = 0;
x_526 = lean_box(0);
lean_inc(x_4);
x_527 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_524, x_525, x_526, x_4, x_17);
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
lean_dec(x_527);
lean_inc(x_4);
lean_inc(x_528);
x_530 = l_Lean_Elab_Term_isTypeFormer(x_6, x_528, x_4, x_529);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; uint8_t x_532; 
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
x_532 = lean_unbox(x_531);
lean_dec(x_531);
if (x_532 == 0)
{
lean_object* x_533; uint32_t x_534; uint16_t x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_533 = lean_ctor_get(x_530, 1);
lean_inc(x_533);
lean_dec(x_530);
x_534 = 0;
x_535 = 0;
x_536 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_536, 0, x_6);
lean_ctor_set(x_536, 1, x_7);
lean_ctor_set(x_536, 2, x_8);
lean_ctor_set(x_536, 3, x_10);
lean_ctor_set(x_536, 4, x_11);
lean_ctor_set(x_536, 5, x_12);
lean_ctor_set(x_536, 6, x_13);
lean_ctor_set_uint8(x_536, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_536, sizeof(void*)*7 + 7, x_14);
lean_ctor_set_uint32(x_536, sizeof(void*)*7, x_534);
lean_ctor_set_uint16(x_536, sizeof(void*)*7 + 4, x_535);
lean_inc(x_528);
x_537 = l_Lean_mkApp(x_2, x_528);
x_538 = lean_expr_instantiate1(x_92, x_528);
lean_dec(x_528);
lean_dec(x_92);
x_1 = x_536;
x_2 = x_537;
x_3 = x_538;
x_5 = x_533;
goto _start;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; uint32_t x_543; uint16_t x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_540 = lean_ctor_get(x_530, 1);
lean_inc(x_540);
lean_dec(x_530);
x_541 = l_Lean_Expr_mvarId_x21(x_528);
x_542 = lean_array_push(x_13, x_541);
x_543 = 0;
x_544 = 0;
x_545 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_545, 0, x_6);
lean_ctor_set(x_545, 1, x_7);
lean_ctor_set(x_545, 2, x_8);
lean_ctor_set(x_545, 3, x_10);
lean_ctor_set(x_545, 4, x_11);
lean_ctor_set(x_545, 5, x_12);
lean_ctor_set(x_545, 6, x_542);
lean_ctor_set_uint8(x_545, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_545, sizeof(void*)*7 + 7, x_14);
lean_ctor_set_uint32(x_545, sizeof(void*)*7, x_543);
lean_ctor_set_uint16(x_545, sizeof(void*)*7 + 4, x_544);
lean_inc(x_528);
x_546 = l_Lean_mkApp(x_2, x_528);
x_547 = lean_expr_instantiate1(x_92, x_528);
lean_dec(x_528);
lean_dec(x_92);
x_1 = x_545;
x_2 = x_546;
x_3 = x_547;
x_5 = x_540;
goto _start;
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_528);
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
x_549 = lean_ctor_get(x_530, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_530, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_530)) {
 lean_ctor_release(x_530, 0);
 lean_ctor_release(x_530, 1);
 x_551 = x_530;
} else {
 lean_dec_ref(x_530);
 x_551 = lean_box(0);
}
if (lean_is_scalar(x_551)) {
 x_552 = lean_alloc_ctor(1, 2, 0);
} else {
 x_552 = x_551;
}
lean_ctor_set(x_552, 0, x_549);
lean_ctor_set(x_552, 1, x_550);
return x_552;
}
}
}
else
{
lean_object* x_553; uint8_t x_554; 
lean_inc(x_4);
lean_inc(x_1);
x_553 = l___private_Init_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_17);
x_554 = !lean_is_exclusive(x_1);
if (x_554 == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_555 = lean_ctor_get(x_1, 6);
lean_dec(x_555);
x_556 = lean_ctor_get(x_1, 5);
lean_dec(x_556);
x_557 = lean_ctor_get(x_1, 4);
lean_dec(x_557);
x_558 = lean_ctor_get(x_1, 3);
lean_dec(x_558);
x_559 = lean_ctor_get(x_1, 2);
lean_dec(x_559);
x_560 = lean_ctor_get(x_1, 1);
lean_dec(x_560);
x_561 = lean_ctor_get(x_1, 0);
lean_dec(x_561);
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_562; lean_object* x_563; uint8_t x_564; 
x_562 = lean_ctor_get(x_553, 1);
lean_inc(x_562);
lean_dec(x_553);
x_563 = lean_array_get_size(x_7);
x_564 = lean_nat_dec_lt(x_10, x_563);
lean_dec(x_563);
if (x_564 == 0)
{
uint8_t x_565; 
lean_free_object(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
x_565 = l_Array_isEmpty___rarg(x_11);
if (x_565 == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_566 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_566, 0, x_90);
x_567 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_568 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_568, 0, x_567);
lean_ctor_set(x_568, 1, x_566);
x_569 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_570 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_570, 0, x_568);
lean_ctor_set(x_570, 1, x_569);
x_571 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
x_572 = l_Array_toList___rarg(x_571);
lean_dec(x_571);
x_573 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_572);
x_574 = l_Array_HasRepr___rarg___closed__1;
x_575 = lean_string_append(x_574, x_573);
lean_dec(x_573);
x_576 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_576, 0, x_575);
x_577 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_577, 0, x_576);
x_578 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_578, 0, x_570);
lean_ctor_set(x_578, 1, x_577);
x_579 = l_Lean_Elab_Term_throwError___rarg(x_6, x_578, x_4, x_562);
lean_dec(x_6);
return x_579;
}
else
{
lean_object* x_580; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; uint8_t x_611; 
lean_dec(x_90);
lean_dec(x_11);
x_607 = l_Lean_Elab_Term_getOptions(x_4, x_562);
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
lean_dec(x_607);
x_610 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_611 = l_Lean_checkTraceOption(x_608, x_610);
lean_dec(x_608);
if (x_611 == 0)
{
x_580 = x_609;
goto block_606;
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; 
lean_inc(x_2);
x_612 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_612, 0, x_2);
x_613 = l_Lean_Elab_Term_logTrace(x_610, x_6, x_612, x_4, x_609);
x_614 = lean_ctor_get(x_613, 1);
lean_inc(x_614);
lean_dec(x_613);
x_580 = x_614;
goto block_606;
}
block_606:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_581; 
lean_dec(x_3);
x_581 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_580);
lean_dec(x_12);
if (lean_obj_tag(x_581) == 0)
{
uint8_t x_582; 
x_582 = !lean_is_exclusive(x_581);
if (x_582 == 0)
{
lean_object* x_583; 
x_583 = lean_ctor_get(x_581, 0);
lean_dec(x_583);
lean_ctor_set(x_581, 0, x_2);
return x_581;
}
else
{
lean_object* x_584; lean_object* x_585; 
x_584 = lean_ctor_get(x_581, 1);
lean_inc(x_584);
lean_dec(x_581);
x_585 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_585, 0, x_2);
lean_ctor_set(x_585, 1, x_584);
return x_585;
}
}
else
{
uint8_t x_586; 
lean_dec(x_2);
x_586 = !lean_is_exclusive(x_581);
if (x_586 == 0)
{
return x_581;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_581, 0);
x_588 = lean_ctor_get(x_581, 1);
lean_inc(x_588);
lean_inc(x_587);
lean_dec(x_581);
x_589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_589, 0, x_587);
lean_ctor_set(x_589, 1, x_588);
return x_589;
}
}
}
else
{
lean_object* x_590; lean_object* x_591; 
x_590 = lean_ctor_get(x_8, 0);
lean_inc(x_590);
lean_dec(x_8);
lean_inc(x_4);
x_591 = l_Lean_Elab_Term_isDefEq(x_6, x_590, x_3, x_4, x_580);
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_592; lean_object* x_593; 
x_592 = lean_ctor_get(x_591, 1);
lean_inc(x_592);
lean_dec(x_591);
x_593 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_592);
lean_dec(x_12);
if (lean_obj_tag(x_593) == 0)
{
uint8_t x_594; 
x_594 = !lean_is_exclusive(x_593);
if (x_594 == 0)
{
lean_object* x_595; 
x_595 = lean_ctor_get(x_593, 0);
lean_dec(x_595);
lean_ctor_set(x_593, 0, x_2);
return x_593;
}
else
{
lean_object* x_596; lean_object* x_597; 
x_596 = lean_ctor_get(x_593, 1);
lean_inc(x_596);
lean_dec(x_593);
x_597 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_597, 0, x_2);
lean_ctor_set(x_597, 1, x_596);
return x_597;
}
}
else
{
uint8_t x_598; 
lean_dec(x_2);
x_598 = !lean_is_exclusive(x_593);
if (x_598 == 0)
{
return x_593;
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_599 = lean_ctor_get(x_593, 0);
x_600 = lean_ctor_get(x_593, 1);
lean_inc(x_600);
lean_inc(x_599);
lean_dec(x_593);
x_601 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_601, 0, x_599);
lean_ctor_set(x_601, 1, x_600);
return x_601;
}
}
}
else
{
uint8_t x_602; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_602 = !lean_is_exclusive(x_591);
if (x_602 == 0)
{
return x_591;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_603 = lean_ctor_get(x_591, 0);
x_604 = lean_ctor_get(x_591, 1);
lean_inc(x_604);
lean_inc(x_603);
lean_dec(x_591);
x_605 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_605, 0, x_603);
lean_ctor_set(x_605, 1, x_604);
return x_605;
}
}
}
}
}
}
else
{
lean_object* x_615; lean_object* x_616; 
lean_dec(x_90);
lean_dec(x_3);
x_615 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_616 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_615, x_91, x_4, x_562);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; uint8_t x_621; uint32_t x_622; uint16_t x_623; lean_object* x_624; lean_object* x_625; 
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec(x_616);
x_619 = lean_unsigned_to_nat(1u);
x_620 = lean_nat_add(x_10, x_619);
lean_dec(x_10);
x_621 = 1;
x_622 = 0;
x_623 = 0;
lean_ctor_set(x_1, 3, x_620);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 7, x_621);
lean_ctor_set_uint32(x_1, sizeof(void*)*7, x_622);
lean_ctor_set_uint16(x_1, sizeof(void*)*7 + 4, x_623);
lean_inc(x_617);
x_624 = l_Lean_mkApp(x_2, x_617);
x_625 = lean_expr_instantiate1(x_92, x_617);
lean_dec(x_617);
lean_dec(x_92);
x_2 = x_624;
x_3 = x_625;
x_5 = x_618;
goto _start;
}
else
{
uint8_t x_627; 
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
x_627 = !lean_is_exclusive(x_616);
if (x_627 == 0)
{
return x_616;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_616, 0);
x_629 = lean_ctor_get(x_616, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_616);
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
return x_630;
}
}
}
}
else
{
uint8_t x_631; 
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
x_631 = !lean_is_exclusive(x_553);
if (x_631 == 0)
{
return x_553;
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_632 = lean_ctor_get(x_553, 0);
x_633 = lean_ctor_get(x_553, 1);
lean_inc(x_633);
lean_inc(x_632);
lean_dec(x_553);
x_634 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_634, 0, x_632);
lean_ctor_set(x_634, 1, x_633);
return x_634;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_635; lean_object* x_636; uint8_t x_637; 
x_635 = lean_ctor_get(x_553, 1);
lean_inc(x_635);
lean_dec(x_553);
x_636 = lean_array_get_size(x_7);
x_637 = lean_nat_dec_lt(x_10, x_636);
lean_dec(x_636);
if (x_637 == 0)
{
uint8_t x_638; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
x_638 = l_Array_isEmpty___rarg(x_11);
if (x_638 == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_639 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_639, 0, x_90);
x_640 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_641 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_639);
x_642 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_643 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_643, 0, x_641);
lean_ctor_set(x_643, 1, x_642);
x_644 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
x_645 = l_Array_toList___rarg(x_644);
lean_dec(x_644);
x_646 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_645);
x_647 = l_Array_HasRepr___rarg___closed__1;
x_648 = lean_string_append(x_647, x_646);
lean_dec(x_646);
x_649 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_649, 0, x_648);
x_650 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_650, 0, x_649);
x_651 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_651, 0, x_643);
lean_ctor_set(x_651, 1, x_650);
x_652 = l_Lean_Elab_Term_throwError___rarg(x_6, x_651, x_4, x_635);
lean_dec(x_6);
return x_652;
}
else
{
lean_object* x_653; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; uint8_t x_682; 
lean_dec(x_90);
lean_dec(x_11);
x_678 = l_Lean_Elab_Term_getOptions(x_4, x_635);
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_678, 1);
lean_inc(x_680);
lean_dec(x_678);
x_681 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_682 = l_Lean_checkTraceOption(x_679, x_681);
lean_dec(x_679);
if (x_682 == 0)
{
x_653 = x_680;
goto block_677;
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; 
lean_inc(x_2);
x_683 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_683, 0, x_2);
x_684 = l_Lean_Elab_Term_logTrace(x_681, x_6, x_683, x_4, x_680);
x_685 = lean_ctor_get(x_684, 1);
lean_inc(x_685);
lean_dec(x_684);
x_653 = x_685;
goto block_677;
}
block_677:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_654; 
lean_dec(x_3);
x_654 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_653);
lean_dec(x_12);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_655 = lean_ctor_get(x_654, 1);
lean_inc(x_655);
if (lean_is_exclusive(x_654)) {
 lean_ctor_release(x_654, 0);
 lean_ctor_release(x_654, 1);
 x_656 = x_654;
} else {
 lean_dec_ref(x_654);
 x_656 = lean_box(0);
}
if (lean_is_scalar(x_656)) {
 x_657 = lean_alloc_ctor(0, 2, 0);
} else {
 x_657 = x_656;
}
lean_ctor_set(x_657, 0, x_2);
lean_ctor_set(x_657, 1, x_655);
return x_657;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_2);
x_658 = lean_ctor_get(x_654, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_654, 1);
lean_inc(x_659);
if (lean_is_exclusive(x_654)) {
 lean_ctor_release(x_654, 0);
 lean_ctor_release(x_654, 1);
 x_660 = x_654;
} else {
 lean_dec_ref(x_654);
 x_660 = lean_box(0);
}
if (lean_is_scalar(x_660)) {
 x_661 = lean_alloc_ctor(1, 2, 0);
} else {
 x_661 = x_660;
}
lean_ctor_set(x_661, 0, x_658);
lean_ctor_set(x_661, 1, x_659);
return x_661;
}
}
else
{
lean_object* x_662; lean_object* x_663; 
x_662 = lean_ctor_get(x_8, 0);
lean_inc(x_662);
lean_dec(x_8);
lean_inc(x_4);
x_663 = l_Lean_Elab_Term_isDefEq(x_6, x_662, x_3, x_4, x_653);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; 
x_664 = lean_ctor_get(x_663, 1);
lean_inc(x_664);
lean_dec(x_663);
x_665 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_664);
lean_dec(x_12);
if (lean_obj_tag(x_665) == 0)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_666 = lean_ctor_get(x_665, 1);
lean_inc(x_666);
if (lean_is_exclusive(x_665)) {
 lean_ctor_release(x_665, 0);
 lean_ctor_release(x_665, 1);
 x_667 = x_665;
} else {
 lean_dec_ref(x_665);
 x_667 = lean_box(0);
}
if (lean_is_scalar(x_667)) {
 x_668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_668 = x_667;
}
lean_ctor_set(x_668, 0, x_2);
lean_ctor_set(x_668, 1, x_666);
return x_668;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec(x_2);
x_669 = lean_ctor_get(x_665, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_665, 1);
lean_inc(x_670);
if (lean_is_exclusive(x_665)) {
 lean_ctor_release(x_665, 0);
 lean_ctor_release(x_665, 1);
 x_671 = x_665;
} else {
 lean_dec_ref(x_665);
 x_671 = lean_box(0);
}
if (lean_is_scalar(x_671)) {
 x_672 = lean_alloc_ctor(1, 2, 0);
} else {
 x_672 = x_671;
}
lean_ctor_set(x_672, 0, x_669);
lean_ctor_set(x_672, 1, x_670);
return x_672;
}
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_673 = lean_ctor_get(x_663, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_663, 1);
lean_inc(x_674);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 x_675 = x_663;
} else {
 lean_dec_ref(x_663);
 x_675 = lean_box(0);
}
if (lean_is_scalar(x_675)) {
 x_676 = lean_alloc_ctor(1, 2, 0);
} else {
 x_676 = x_675;
}
lean_ctor_set(x_676, 0, x_673);
lean_ctor_set(x_676, 1, x_674);
return x_676;
}
}
}
}
}
else
{
lean_object* x_686; lean_object* x_687; 
lean_dec(x_90);
lean_dec(x_3);
x_686 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_687 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_686, x_91, x_4, x_635);
if (lean_obj_tag(x_687) == 0)
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; uint8_t x_692; uint32_t x_693; uint16_t x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_688 = lean_ctor_get(x_687, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_687, 1);
lean_inc(x_689);
lean_dec(x_687);
x_690 = lean_unsigned_to_nat(1u);
x_691 = lean_nat_add(x_10, x_690);
lean_dec(x_10);
x_692 = 1;
x_693 = 0;
x_694 = 0;
x_695 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_695, 0, x_6);
lean_ctor_set(x_695, 1, x_7);
lean_ctor_set(x_695, 2, x_8);
lean_ctor_set(x_695, 3, x_691);
lean_ctor_set(x_695, 4, x_11);
lean_ctor_set(x_695, 5, x_12);
lean_ctor_set(x_695, 6, x_13);
lean_ctor_set_uint8(x_695, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_695, sizeof(void*)*7 + 7, x_692);
lean_ctor_set_uint32(x_695, sizeof(void*)*7, x_693);
lean_ctor_set_uint16(x_695, sizeof(void*)*7 + 4, x_694);
lean_inc(x_688);
x_696 = l_Lean_mkApp(x_2, x_688);
x_697 = lean_expr_instantiate1(x_92, x_688);
lean_dec(x_688);
lean_dec(x_92);
x_1 = x_695;
x_2 = x_696;
x_3 = x_697;
x_5 = x_689;
goto _start;
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
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
x_699 = lean_ctor_get(x_687, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_687, 1);
lean_inc(x_700);
if (lean_is_exclusive(x_687)) {
 lean_ctor_release(x_687, 0);
 lean_ctor_release(x_687, 1);
 x_701 = x_687;
} else {
 lean_dec_ref(x_687);
 x_701 = lean_box(0);
}
if (lean_is_scalar(x_701)) {
 x_702 = lean_alloc_ctor(1, 2, 0);
} else {
 x_702 = x_701;
}
lean_ctor_set(x_702, 0, x_699);
lean_ctor_set(x_702, 1, x_700);
return x_702;
}
}
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
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
x_703 = lean_ctor_get(x_553, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_553, 1);
lean_inc(x_704);
if (lean_is_exclusive(x_553)) {
 lean_ctor_release(x_553, 0);
 lean_ctor_release(x_553, 1);
 x_705 = x_553;
} else {
 lean_dec_ref(x_553);
 x_705 = lean_box(0);
}
if (lean_is_scalar(x_705)) {
 x_706 = lean_alloc_ctor(1, 2, 0);
} else {
 x_706 = x_705;
}
lean_ctor_set(x_706, 0, x_703);
lean_ctor_set(x_706, 1, x_704);
return x_706;
}
}
}
}
case 2:
{
lean_object* x_707; uint8_t x_708; 
lean_inc(x_4);
lean_inc(x_1);
x_707 = l___private_Init_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_17);
x_708 = !lean_is_exclusive(x_1);
if (x_708 == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_709 = lean_ctor_get(x_1, 6);
lean_dec(x_709);
x_710 = lean_ctor_get(x_1, 5);
lean_dec(x_710);
x_711 = lean_ctor_get(x_1, 4);
lean_dec(x_711);
x_712 = lean_ctor_get(x_1, 3);
lean_dec(x_712);
x_713 = lean_ctor_get(x_1, 2);
lean_dec(x_713);
x_714 = lean_ctor_get(x_1, 1);
lean_dec(x_714);
x_715 = lean_ctor_get(x_1, 0);
lean_dec(x_715);
if (lean_obj_tag(x_707) == 0)
{
lean_object* x_716; uint8_t x_717; uint32_t x_718; uint16_t x_719; lean_object* x_720; uint8_t x_721; 
x_716 = lean_ctor_get(x_707, 1);
lean_inc(x_716);
lean_dec(x_707);
x_717 = 1;
x_718 = 0;
x_719 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 7, x_717);
lean_ctor_set_uint32(x_1, sizeof(void*)*7, x_718);
lean_ctor_set_uint16(x_1, sizeof(void*)*7 + 4, x_719);
x_720 = lean_array_get_size(x_7);
x_721 = lean_nat_dec_lt(x_10, x_720);
lean_dec(x_720);
if (x_721 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_722; 
x_722 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_722) == 0)
{
lean_object* x_723; 
x_723 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_723) == 0)
{
uint8_t x_724; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
x_724 = l_Array_isEmpty___rarg(x_11);
if (x_724 == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_725 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_725, 0, x_90);
x_726 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_727 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_725);
x_728 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_729 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_729, 0, x_727);
lean_ctor_set(x_729, 1, x_728);
x_730 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
x_731 = l_Array_toList___rarg(x_730);
lean_dec(x_730);
x_732 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_731);
x_733 = l_Array_HasRepr___rarg___closed__1;
x_734 = lean_string_append(x_733, x_732);
lean_dec(x_732);
x_735 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_735, 0, x_734);
x_736 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_736, 0, x_735);
x_737 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_737, 0, x_729);
lean_ctor_set(x_737, 1, x_736);
x_738 = l_Lean_Elab_Term_throwError___rarg(x_6, x_737, x_4, x_716);
lean_dec(x_6);
return x_738;
}
else
{
lean_object* x_739; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; uint8_t x_770; 
lean_dec(x_90);
lean_dec(x_11);
x_766 = l_Lean_Elab_Term_getOptions(x_4, x_716);
x_767 = lean_ctor_get(x_766, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_766, 1);
lean_inc(x_768);
lean_dec(x_766);
x_769 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_770 = l_Lean_checkTraceOption(x_767, x_769);
lean_dec(x_767);
if (x_770 == 0)
{
x_739 = x_768;
goto block_765;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
lean_inc(x_2);
x_771 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_771, 0, x_2);
x_772 = l_Lean_Elab_Term_logTrace(x_769, x_6, x_771, x_4, x_768);
x_773 = lean_ctor_get(x_772, 1);
lean_inc(x_773);
lean_dec(x_772);
x_739 = x_773;
goto block_765;
}
block_765:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_740; 
lean_dec(x_3);
x_740 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_739);
lean_dec(x_12);
if (lean_obj_tag(x_740) == 0)
{
uint8_t x_741; 
x_741 = !lean_is_exclusive(x_740);
if (x_741 == 0)
{
lean_object* x_742; 
x_742 = lean_ctor_get(x_740, 0);
lean_dec(x_742);
lean_ctor_set(x_740, 0, x_2);
return x_740;
}
else
{
lean_object* x_743; lean_object* x_744; 
x_743 = lean_ctor_get(x_740, 1);
lean_inc(x_743);
lean_dec(x_740);
x_744 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_744, 0, x_2);
lean_ctor_set(x_744, 1, x_743);
return x_744;
}
}
else
{
uint8_t x_745; 
lean_dec(x_2);
x_745 = !lean_is_exclusive(x_740);
if (x_745 == 0)
{
return x_740;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_746 = lean_ctor_get(x_740, 0);
x_747 = lean_ctor_get(x_740, 1);
lean_inc(x_747);
lean_inc(x_746);
lean_dec(x_740);
x_748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
return x_748;
}
}
}
else
{
lean_object* x_749; lean_object* x_750; 
x_749 = lean_ctor_get(x_8, 0);
lean_inc(x_749);
lean_dec(x_8);
lean_inc(x_4);
x_750 = l_Lean_Elab_Term_isDefEq(x_6, x_749, x_3, x_4, x_739);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; lean_object* x_752; 
x_751 = lean_ctor_get(x_750, 1);
lean_inc(x_751);
lean_dec(x_750);
x_752 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_751);
lean_dec(x_12);
if (lean_obj_tag(x_752) == 0)
{
uint8_t x_753; 
x_753 = !lean_is_exclusive(x_752);
if (x_753 == 0)
{
lean_object* x_754; 
x_754 = lean_ctor_get(x_752, 0);
lean_dec(x_754);
lean_ctor_set(x_752, 0, x_2);
return x_752;
}
else
{
lean_object* x_755; lean_object* x_756; 
x_755 = lean_ctor_get(x_752, 1);
lean_inc(x_755);
lean_dec(x_752);
x_756 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_756, 0, x_2);
lean_ctor_set(x_756, 1, x_755);
return x_756;
}
}
else
{
uint8_t x_757; 
lean_dec(x_2);
x_757 = !lean_is_exclusive(x_752);
if (x_757 == 0)
{
return x_752;
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_758 = lean_ctor_get(x_752, 0);
x_759 = lean_ctor_get(x_752, 1);
lean_inc(x_759);
lean_inc(x_758);
lean_dec(x_752);
x_760 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_760, 0, x_758);
lean_ctor_set(x_760, 1, x_759);
return x_760;
}
}
}
else
{
uint8_t x_761; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_761 = !lean_is_exclusive(x_750);
if (x_761 == 0)
{
return x_750;
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; 
x_762 = lean_ctor_get(x_750, 0);
x_763 = lean_ctor_get(x_750, 1);
lean_inc(x_763);
lean_inc(x_762);
lean_dec(x_750);
x_764 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_764, 0, x_762);
lean_ctor_set(x_764, 1, x_763);
return x_764;
}
}
}
}
}
}
else
{
lean_object* x_774; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_774 = lean_ctor_get(x_723, 0);
lean_inc(x_774);
lean_dec(x_723);
if (lean_obj_tag(x_774) == 4)
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; 
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
lean_dec(x_774);
x_776 = l_Lean_Elab_Term_getEnv___rarg(x_716);
x_777 = lean_ctor_get(x_776, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_776, 1);
lean_inc(x_778);
lean_dec(x_776);
x_779 = l_Lean_Elab_evalSyntaxConstant(x_777, x_775);
if (lean_obj_tag(x_779) == 0)
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_780 = lean_ctor_get(x_779, 0);
lean_inc(x_780);
lean_dec(x_779);
x_781 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_781, 0, x_780);
x_782 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_782, 0, x_781);
x_783 = l_Lean_Elab_Term_throwError___rarg(x_6, x_782, x_4, x_778);
lean_dec(x_6);
return x_783;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_784 = lean_ctor_get(x_779, 0);
lean_inc(x_784);
lean_dec(x_779);
x_785 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_778);
x_786 = lean_ctor_get(x_785, 1);
lean_inc(x_786);
lean_dec(x_785);
x_787 = l_Lean_Elab_Term_getMainModule___rarg(x_786);
x_788 = lean_ctor_get(x_787, 1);
lean_inc(x_788);
lean_dec(x_787);
x_789 = l_Lean_Syntax_getArgs(x_784);
lean_dec(x_784);
x_790 = l_Array_empty___closed__1;
x_791 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_789, x_789, x_94, x_790);
lean_dec(x_789);
x_792 = l_Lean_nullKind___closed__2;
x_793 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_793, 0, x_792);
lean_ctor_set(x_793, 1, x_791);
x_794 = lean_array_push(x_790, x_793);
x_795 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_796 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_796, 0, x_795);
lean_ctor_set(x_796, 1, x_794);
x_797 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_798 = lean_array_push(x_797, x_796);
x_799 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_800 = lean_array_push(x_798, x_799);
x_801 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_802 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_802, 0, x_801);
lean_ctor_set(x_802, 1, x_800);
x_803 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_804 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_805 = lean_nat_sub(x_804, x_94);
lean_dec(x_804);
x_806 = lean_unsigned_to_nat(1u);
x_807 = lean_nat_sub(x_805, x_806);
lean_dec(x_805);
x_808 = l_Lean_Expr_getRevArg_x21___main(x_91, x_807);
lean_dec(x_91);
if (lean_obj_tag(x_803) == 0)
{
lean_object* x_809; lean_object* x_810; 
x_809 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_809, 0, x_802);
lean_inc(x_4);
lean_inc(x_2);
x_810 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_809, x_808, x_4, x_788);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_810, 1);
lean_inc(x_812);
lean_dec(x_810);
lean_inc(x_811);
x_813 = l_Lean_mkApp(x_2, x_811);
x_814 = lean_expr_instantiate1(x_92, x_811);
lean_dec(x_811);
lean_dec(x_92);
x_2 = x_813;
x_3 = x_814;
x_5 = x_812;
goto _start;
}
else
{
uint8_t x_816; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_816 = !lean_is_exclusive(x_810);
if (x_816 == 0)
{
return x_810;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_817 = lean_ctor_get(x_810, 0);
x_818 = lean_ctor_get(x_810, 1);
lean_inc(x_818);
lean_inc(x_817);
lean_dec(x_810);
x_819 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_819, 0, x_817);
lean_ctor_set(x_819, 1, x_818);
return x_819;
}
}
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_820 = lean_ctor_get(x_803, 0);
lean_inc(x_820);
lean_dec(x_803);
x_821 = l_Lean_Syntax_replaceInfo___main(x_820, x_802);
x_822 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_822, 0, x_821);
lean_inc(x_4);
lean_inc(x_2);
x_823 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_822, x_808, x_4, x_788);
if (lean_obj_tag(x_823) == 0)
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_824 = lean_ctor_get(x_823, 0);
lean_inc(x_824);
x_825 = lean_ctor_get(x_823, 1);
lean_inc(x_825);
lean_dec(x_823);
lean_inc(x_824);
x_826 = l_Lean_mkApp(x_2, x_824);
x_827 = lean_expr_instantiate1(x_92, x_824);
lean_dec(x_824);
lean_dec(x_92);
x_2 = x_826;
x_3 = x_827;
x_5 = x_825;
goto _start;
}
else
{
uint8_t x_829; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_829 = !lean_is_exclusive(x_823);
if (x_829 == 0)
{
return x_823;
}
else
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_830 = lean_ctor_get(x_823, 0);
x_831 = lean_ctor_get(x_823, 1);
lean_inc(x_831);
lean_inc(x_830);
lean_dec(x_823);
x_832 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_832, 0, x_830);
lean_ctor_set(x_832, 1, x_831);
return x_832;
}
}
}
}
}
else
{
lean_object* x_833; lean_object* x_834; 
lean_dec(x_774);
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_833 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_834 = l_Lean_Elab_Term_throwError___rarg(x_6, x_833, x_4, x_716);
lean_dec(x_6);
return x_834;
}
}
}
else
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_835 = lean_ctor_get(x_722, 0);
lean_inc(x_835);
lean_dec(x_722);
lean_inc(x_835);
x_836 = l_Lean_mkApp(x_2, x_835);
x_837 = lean_expr_instantiate1(x_92, x_835);
lean_dec(x_835);
lean_dec(x_92);
x_2 = x_836;
x_3 = x_837;
x_5 = x_716;
goto _start;
}
}
else
{
uint8_t x_839; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
x_839 = l_Array_isEmpty___rarg(x_11);
if (x_839 == 0)
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_840 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_840, 0, x_90);
x_841 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_842 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_842, 0, x_841);
lean_ctor_set(x_842, 1, x_840);
x_843 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_844 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_844, 0, x_842);
lean_ctor_set(x_844, 1, x_843);
x_845 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
x_846 = l_Array_toList___rarg(x_845);
lean_dec(x_845);
x_847 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_846);
x_848 = l_Array_HasRepr___rarg___closed__1;
x_849 = lean_string_append(x_848, x_847);
lean_dec(x_847);
x_850 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_850, 0, x_849);
x_851 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_851, 0, x_850);
x_852 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_852, 0, x_844);
lean_ctor_set(x_852, 1, x_851);
x_853 = l_Lean_Elab_Term_throwError___rarg(x_6, x_852, x_4, x_716);
lean_dec(x_6);
return x_853;
}
else
{
lean_object* x_854; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; uint8_t x_885; 
lean_dec(x_90);
lean_dec(x_11);
x_881 = l_Lean_Elab_Term_getOptions(x_4, x_716);
x_882 = lean_ctor_get(x_881, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_881, 1);
lean_inc(x_883);
lean_dec(x_881);
x_884 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_885 = l_Lean_checkTraceOption(x_882, x_884);
lean_dec(x_882);
if (x_885 == 0)
{
x_854 = x_883;
goto block_880;
}
else
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; 
lean_inc(x_2);
x_886 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_886, 0, x_2);
x_887 = l_Lean_Elab_Term_logTrace(x_884, x_6, x_886, x_4, x_883);
x_888 = lean_ctor_get(x_887, 1);
lean_inc(x_888);
lean_dec(x_887);
x_854 = x_888;
goto block_880;
}
block_880:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_855; 
lean_dec(x_3);
x_855 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_854);
lean_dec(x_12);
if (lean_obj_tag(x_855) == 0)
{
uint8_t x_856; 
x_856 = !lean_is_exclusive(x_855);
if (x_856 == 0)
{
lean_object* x_857; 
x_857 = lean_ctor_get(x_855, 0);
lean_dec(x_857);
lean_ctor_set(x_855, 0, x_2);
return x_855;
}
else
{
lean_object* x_858; lean_object* x_859; 
x_858 = lean_ctor_get(x_855, 1);
lean_inc(x_858);
lean_dec(x_855);
x_859 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_859, 0, x_2);
lean_ctor_set(x_859, 1, x_858);
return x_859;
}
}
else
{
uint8_t x_860; 
lean_dec(x_2);
x_860 = !lean_is_exclusive(x_855);
if (x_860 == 0)
{
return x_855;
}
else
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_861 = lean_ctor_get(x_855, 0);
x_862 = lean_ctor_get(x_855, 1);
lean_inc(x_862);
lean_inc(x_861);
lean_dec(x_855);
x_863 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_863, 0, x_861);
lean_ctor_set(x_863, 1, x_862);
return x_863;
}
}
}
else
{
lean_object* x_864; lean_object* x_865; 
x_864 = lean_ctor_get(x_8, 0);
lean_inc(x_864);
lean_dec(x_8);
lean_inc(x_4);
x_865 = l_Lean_Elab_Term_isDefEq(x_6, x_864, x_3, x_4, x_854);
if (lean_obj_tag(x_865) == 0)
{
lean_object* x_866; lean_object* x_867; 
x_866 = lean_ctor_get(x_865, 1);
lean_inc(x_866);
lean_dec(x_865);
x_867 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_866);
lean_dec(x_12);
if (lean_obj_tag(x_867) == 0)
{
uint8_t x_868; 
x_868 = !lean_is_exclusive(x_867);
if (x_868 == 0)
{
lean_object* x_869; 
x_869 = lean_ctor_get(x_867, 0);
lean_dec(x_869);
lean_ctor_set(x_867, 0, x_2);
return x_867;
}
else
{
lean_object* x_870; lean_object* x_871; 
x_870 = lean_ctor_get(x_867, 1);
lean_inc(x_870);
lean_dec(x_867);
x_871 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_871, 0, x_2);
lean_ctor_set(x_871, 1, x_870);
return x_871;
}
}
else
{
uint8_t x_872; 
lean_dec(x_2);
x_872 = !lean_is_exclusive(x_867);
if (x_872 == 0)
{
return x_867;
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_873 = lean_ctor_get(x_867, 0);
x_874 = lean_ctor_get(x_867, 1);
lean_inc(x_874);
lean_inc(x_873);
lean_dec(x_867);
x_875 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_875, 0, x_873);
lean_ctor_set(x_875, 1, x_874);
return x_875;
}
}
}
else
{
uint8_t x_876; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_876 = !lean_is_exclusive(x_865);
if (x_876 == 0)
{
return x_865;
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_877 = lean_ctor_get(x_865, 0);
x_878 = lean_ctor_get(x_865, 1);
lean_inc(x_878);
lean_inc(x_877);
lean_dec(x_865);
x_879 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_879, 0, x_877);
lean_ctor_set(x_879, 1, x_878);
return x_879;
}
}
}
}
}
}
}
else
{
lean_object* x_889; lean_object* x_890; 
lean_dec(x_1);
lean_dec(x_90);
lean_dec(x_3);
x_889 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_890 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_889, x_91, x_4, x_716);
if (lean_obj_tag(x_890) == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; uint32_t x_895; uint16_t x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; 
x_891 = lean_ctor_get(x_890, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_890, 1);
lean_inc(x_892);
lean_dec(x_890);
x_893 = lean_unsigned_to_nat(1u);
x_894 = lean_nat_add(x_10, x_893);
lean_dec(x_10);
x_895 = 0;
x_896 = 0;
x_897 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_897, 0, x_6);
lean_ctor_set(x_897, 1, x_7);
lean_ctor_set(x_897, 2, x_8);
lean_ctor_set(x_897, 3, x_894);
lean_ctor_set(x_897, 4, x_11);
lean_ctor_set(x_897, 5, x_12);
lean_ctor_set(x_897, 6, x_13);
lean_ctor_set_uint8(x_897, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_897, sizeof(void*)*7 + 7, x_717);
lean_ctor_set_uint32(x_897, sizeof(void*)*7, x_895);
lean_ctor_set_uint16(x_897, sizeof(void*)*7 + 4, x_896);
lean_inc(x_891);
x_898 = l_Lean_mkApp(x_2, x_891);
x_899 = lean_expr_instantiate1(x_92, x_891);
lean_dec(x_891);
lean_dec(x_92);
x_1 = x_897;
x_2 = x_898;
x_3 = x_899;
x_5 = x_892;
goto _start;
}
else
{
uint8_t x_901; 
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
x_901 = !lean_is_exclusive(x_890);
if (x_901 == 0)
{
return x_890;
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_902 = lean_ctor_get(x_890, 0);
x_903 = lean_ctor_get(x_890, 1);
lean_inc(x_903);
lean_inc(x_902);
lean_dec(x_890);
x_904 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_904, 0, x_902);
lean_ctor_set(x_904, 1, x_903);
return x_904;
}
}
}
}
else
{
uint8_t x_905; 
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
x_905 = !lean_is_exclusive(x_707);
if (x_905 == 0)
{
return x_707;
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; 
x_906 = lean_ctor_get(x_707, 0);
x_907 = lean_ctor_get(x_707, 1);
lean_inc(x_907);
lean_inc(x_906);
lean_dec(x_707);
x_908 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_908, 0, x_906);
lean_ctor_set(x_908, 1, x_907);
return x_908;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_707) == 0)
{
lean_object* x_909; uint8_t x_910; uint32_t x_911; uint16_t x_912; lean_object* x_913; lean_object* x_914; uint8_t x_915; 
x_909 = lean_ctor_get(x_707, 1);
lean_inc(x_909);
lean_dec(x_707);
x_910 = 1;
x_911 = 0;
x_912 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_913 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_913, 0, x_6);
lean_ctor_set(x_913, 1, x_7);
lean_ctor_set(x_913, 2, x_8);
lean_ctor_set(x_913, 3, x_10);
lean_ctor_set(x_913, 4, x_11);
lean_ctor_set(x_913, 5, x_12);
lean_ctor_set(x_913, 6, x_13);
lean_ctor_set_uint8(x_913, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_913, sizeof(void*)*7 + 7, x_910);
lean_ctor_set_uint32(x_913, sizeof(void*)*7, x_911);
lean_ctor_set_uint16(x_913, sizeof(void*)*7 + 4, x_912);
x_914 = lean_array_get_size(x_7);
x_915 = lean_nat_dec_lt(x_10, x_914);
lean_dec(x_914);
if (x_915 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_916; 
x_916 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_916) == 0)
{
lean_object* x_917; 
x_917 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_917) == 0)
{
uint8_t x_918; 
lean_dec(x_913);
lean_dec(x_92);
lean_dec(x_91);
x_918 = l_Array_isEmpty___rarg(x_11);
if (x_918 == 0)
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_919 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_919, 0, x_90);
x_920 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_921 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_921, 0, x_920);
lean_ctor_set(x_921, 1, x_919);
x_922 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_923 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_923, 0, x_921);
lean_ctor_set(x_923, 1, x_922);
x_924 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
x_925 = l_Array_toList___rarg(x_924);
lean_dec(x_924);
x_926 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_925);
x_927 = l_Array_HasRepr___rarg___closed__1;
x_928 = lean_string_append(x_927, x_926);
lean_dec(x_926);
x_929 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_929, 0, x_928);
x_930 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_930, 0, x_929);
x_931 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_931, 0, x_923);
lean_ctor_set(x_931, 1, x_930);
x_932 = l_Lean_Elab_Term_throwError___rarg(x_6, x_931, x_4, x_909);
lean_dec(x_6);
return x_932;
}
else
{
lean_object* x_933; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; uint8_t x_962; 
lean_dec(x_90);
lean_dec(x_11);
x_958 = l_Lean_Elab_Term_getOptions(x_4, x_909);
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_958, 1);
lean_inc(x_960);
lean_dec(x_958);
x_961 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_962 = l_Lean_checkTraceOption(x_959, x_961);
lean_dec(x_959);
if (x_962 == 0)
{
x_933 = x_960;
goto block_957;
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; 
lean_inc(x_2);
x_963 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_963, 0, x_2);
x_964 = l_Lean_Elab_Term_logTrace(x_961, x_6, x_963, x_4, x_960);
x_965 = lean_ctor_get(x_964, 1);
lean_inc(x_965);
lean_dec(x_964);
x_933 = x_965;
goto block_957;
}
block_957:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_934; 
lean_dec(x_3);
x_934 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_933);
lean_dec(x_12);
if (lean_obj_tag(x_934) == 0)
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; 
x_935 = lean_ctor_get(x_934, 1);
lean_inc(x_935);
if (lean_is_exclusive(x_934)) {
 lean_ctor_release(x_934, 0);
 lean_ctor_release(x_934, 1);
 x_936 = x_934;
} else {
 lean_dec_ref(x_934);
 x_936 = lean_box(0);
}
if (lean_is_scalar(x_936)) {
 x_937 = lean_alloc_ctor(0, 2, 0);
} else {
 x_937 = x_936;
}
lean_ctor_set(x_937, 0, x_2);
lean_ctor_set(x_937, 1, x_935);
return x_937;
}
else
{
lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
lean_dec(x_2);
x_938 = lean_ctor_get(x_934, 0);
lean_inc(x_938);
x_939 = lean_ctor_get(x_934, 1);
lean_inc(x_939);
if (lean_is_exclusive(x_934)) {
 lean_ctor_release(x_934, 0);
 lean_ctor_release(x_934, 1);
 x_940 = x_934;
} else {
 lean_dec_ref(x_934);
 x_940 = lean_box(0);
}
if (lean_is_scalar(x_940)) {
 x_941 = lean_alloc_ctor(1, 2, 0);
} else {
 x_941 = x_940;
}
lean_ctor_set(x_941, 0, x_938);
lean_ctor_set(x_941, 1, x_939);
return x_941;
}
}
else
{
lean_object* x_942; lean_object* x_943; 
x_942 = lean_ctor_get(x_8, 0);
lean_inc(x_942);
lean_dec(x_8);
lean_inc(x_4);
x_943 = l_Lean_Elab_Term_isDefEq(x_6, x_942, x_3, x_4, x_933);
if (lean_obj_tag(x_943) == 0)
{
lean_object* x_944; lean_object* x_945; 
x_944 = lean_ctor_get(x_943, 1);
lean_inc(x_944);
lean_dec(x_943);
x_945 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_944);
lean_dec(x_12);
if (lean_obj_tag(x_945) == 0)
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; 
x_946 = lean_ctor_get(x_945, 1);
lean_inc(x_946);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_947 = x_945;
} else {
 lean_dec_ref(x_945);
 x_947 = lean_box(0);
}
if (lean_is_scalar(x_947)) {
 x_948 = lean_alloc_ctor(0, 2, 0);
} else {
 x_948 = x_947;
}
lean_ctor_set(x_948, 0, x_2);
lean_ctor_set(x_948, 1, x_946);
return x_948;
}
else
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; 
lean_dec(x_2);
x_949 = lean_ctor_get(x_945, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_945, 1);
lean_inc(x_950);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_951 = x_945;
} else {
 lean_dec_ref(x_945);
 x_951 = lean_box(0);
}
if (lean_is_scalar(x_951)) {
 x_952 = lean_alloc_ctor(1, 2, 0);
} else {
 x_952 = x_951;
}
lean_ctor_set(x_952, 0, x_949);
lean_ctor_set(x_952, 1, x_950);
return x_952;
}
}
else
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_953 = lean_ctor_get(x_943, 0);
lean_inc(x_953);
x_954 = lean_ctor_get(x_943, 1);
lean_inc(x_954);
if (lean_is_exclusive(x_943)) {
 lean_ctor_release(x_943, 0);
 lean_ctor_release(x_943, 1);
 x_955 = x_943;
} else {
 lean_dec_ref(x_943);
 x_955 = lean_box(0);
}
if (lean_is_scalar(x_955)) {
 x_956 = lean_alloc_ctor(1, 2, 0);
} else {
 x_956 = x_955;
}
lean_ctor_set(x_956, 0, x_953);
lean_ctor_set(x_956, 1, x_954);
return x_956;
}
}
}
}
}
else
{
lean_object* x_966; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_966 = lean_ctor_get(x_917, 0);
lean_inc(x_966);
lean_dec(x_917);
if (lean_obj_tag(x_966) == 4)
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; 
x_967 = lean_ctor_get(x_966, 0);
lean_inc(x_967);
lean_dec(x_966);
x_968 = l_Lean_Elab_Term_getEnv___rarg(x_909);
x_969 = lean_ctor_get(x_968, 0);
lean_inc(x_969);
x_970 = lean_ctor_get(x_968, 1);
lean_inc(x_970);
lean_dec(x_968);
x_971 = l_Lean_Elab_evalSyntaxConstant(x_969, x_967);
if (lean_obj_tag(x_971) == 0)
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; 
lean_dec(x_913);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_972 = lean_ctor_get(x_971, 0);
lean_inc(x_972);
lean_dec(x_971);
x_973 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_973, 0, x_972);
x_974 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_974, 0, x_973);
x_975 = l_Lean_Elab_Term_throwError___rarg(x_6, x_974, x_4, x_970);
lean_dec(x_6);
return x_975;
}
else
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_976 = lean_ctor_get(x_971, 0);
lean_inc(x_976);
lean_dec(x_971);
x_977 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_970);
x_978 = lean_ctor_get(x_977, 1);
lean_inc(x_978);
lean_dec(x_977);
x_979 = l_Lean_Elab_Term_getMainModule___rarg(x_978);
x_980 = lean_ctor_get(x_979, 1);
lean_inc(x_980);
lean_dec(x_979);
x_981 = l_Lean_Syntax_getArgs(x_976);
lean_dec(x_976);
x_982 = l_Array_empty___closed__1;
x_983 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_981, x_981, x_94, x_982);
lean_dec(x_981);
x_984 = l_Lean_nullKind___closed__2;
x_985 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_985, 0, x_984);
lean_ctor_set(x_985, 1, x_983);
x_986 = lean_array_push(x_982, x_985);
x_987 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_988 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_988, 0, x_987);
lean_ctor_set(x_988, 1, x_986);
x_989 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_990 = lean_array_push(x_989, x_988);
x_991 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_992 = lean_array_push(x_990, x_991);
x_993 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_994 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_994, 0, x_993);
lean_ctor_set(x_994, 1, x_992);
x_995 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_996 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_997 = lean_nat_sub(x_996, x_94);
lean_dec(x_996);
x_998 = lean_unsigned_to_nat(1u);
x_999 = lean_nat_sub(x_997, x_998);
lean_dec(x_997);
x_1000 = l_Lean_Expr_getRevArg_x21___main(x_91, x_999);
lean_dec(x_91);
if (lean_obj_tag(x_995) == 0)
{
lean_object* x_1001; lean_object* x_1002; 
x_1001 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1001, 0, x_994);
lean_inc(x_4);
lean_inc(x_2);
x_1002 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1001, x_1000, x_4, x_980);
if (lean_obj_tag(x_1002) == 0)
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
x_1003 = lean_ctor_get(x_1002, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_1002, 1);
lean_inc(x_1004);
lean_dec(x_1002);
lean_inc(x_1003);
x_1005 = l_Lean_mkApp(x_2, x_1003);
x_1006 = lean_expr_instantiate1(x_92, x_1003);
lean_dec(x_1003);
lean_dec(x_92);
x_1 = x_913;
x_2 = x_1005;
x_3 = x_1006;
x_5 = x_1004;
goto _start;
}
else
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
lean_dec(x_913);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1008 = lean_ctor_get(x_1002, 0);
lean_inc(x_1008);
x_1009 = lean_ctor_get(x_1002, 1);
lean_inc(x_1009);
if (lean_is_exclusive(x_1002)) {
 lean_ctor_release(x_1002, 0);
 lean_ctor_release(x_1002, 1);
 x_1010 = x_1002;
} else {
 lean_dec_ref(x_1002);
 x_1010 = lean_box(0);
}
if (lean_is_scalar(x_1010)) {
 x_1011 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1011 = x_1010;
}
lean_ctor_set(x_1011, 0, x_1008);
lean_ctor_set(x_1011, 1, x_1009);
return x_1011;
}
}
else
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
x_1012 = lean_ctor_get(x_995, 0);
lean_inc(x_1012);
lean_dec(x_995);
x_1013 = l_Lean_Syntax_replaceInfo___main(x_1012, x_994);
x_1014 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1014, 0, x_1013);
lean_inc(x_4);
lean_inc(x_2);
x_1015 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1014, x_1000, x_4, x_980);
if (lean_obj_tag(x_1015) == 0)
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1016 = lean_ctor_get(x_1015, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_1015, 1);
lean_inc(x_1017);
lean_dec(x_1015);
lean_inc(x_1016);
x_1018 = l_Lean_mkApp(x_2, x_1016);
x_1019 = lean_expr_instantiate1(x_92, x_1016);
lean_dec(x_1016);
lean_dec(x_92);
x_1 = x_913;
x_2 = x_1018;
x_3 = x_1019;
x_5 = x_1017;
goto _start;
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
lean_dec(x_913);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1021 = lean_ctor_get(x_1015, 0);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_1015, 1);
lean_inc(x_1022);
if (lean_is_exclusive(x_1015)) {
 lean_ctor_release(x_1015, 0);
 lean_ctor_release(x_1015, 1);
 x_1023 = x_1015;
} else {
 lean_dec_ref(x_1015);
 x_1023 = lean_box(0);
}
if (lean_is_scalar(x_1023)) {
 x_1024 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1024 = x_1023;
}
lean_ctor_set(x_1024, 0, x_1021);
lean_ctor_set(x_1024, 1, x_1022);
return x_1024;
}
}
}
}
else
{
lean_object* x_1025; lean_object* x_1026; 
lean_dec(x_966);
lean_dec(x_913);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_1025 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1026 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1025, x_4, x_909);
lean_dec(x_6);
return x_1026;
}
}
}
else
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1027 = lean_ctor_get(x_916, 0);
lean_inc(x_1027);
lean_dec(x_916);
lean_inc(x_1027);
x_1028 = l_Lean_mkApp(x_2, x_1027);
x_1029 = lean_expr_instantiate1(x_92, x_1027);
lean_dec(x_1027);
lean_dec(x_92);
x_1 = x_913;
x_2 = x_1028;
x_3 = x_1029;
x_5 = x_909;
goto _start;
}
}
else
{
uint8_t x_1031; 
lean_dec(x_913);
lean_dec(x_92);
lean_dec(x_91);
x_1031 = l_Array_isEmpty___rarg(x_11);
if (x_1031 == 0)
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1032 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1032, 0, x_90);
x_1033 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1034 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1034, 0, x_1033);
lean_ctor_set(x_1034, 1, x_1032);
x_1035 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1036 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1036, 0, x_1034);
lean_ctor_set(x_1036, 1, x_1035);
x_1037 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
x_1038 = l_Array_toList___rarg(x_1037);
lean_dec(x_1037);
x_1039 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1038);
x_1040 = l_Array_HasRepr___rarg___closed__1;
x_1041 = lean_string_append(x_1040, x_1039);
lean_dec(x_1039);
x_1042 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1042, 0, x_1041);
x_1043 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1043, 0, x_1042);
x_1044 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1044, 0, x_1036);
lean_ctor_set(x_1044, 1, x_1043);
x_1045 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1044, x_4, x_909);
lean_dec(x_6);
return x_1045;
}
else
{
lean_object* x_1046; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; uint8_t x_1075; 
lean_dec(x_90);
lean_dec(x_11);
x_1071 = l_Lean_Elab_Term_getOptions(x_4, x_909);
x_1072 = lean_ctor_get(x_1071, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_1071, 1);
lean_inc(x_1073);
lean_dec(x_1071);
x_1074 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1075 = l_Lean_checkTraceOption(x_1072, x_1074);
lean_dec(x_1072);
if (x_1075 == 0)
{
x_1046 = x_1073;
goto block_1070;
}
else
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; 
lean_inc(x_2);
x_1076 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1076, 0, x_2);
x_1077 = l_Lean_Elab_Term_logTrace(x_1074, x_6, x_1076, x_4, x_1073);
x_1078 = lean_ctor_get(x_1077, 1);
lean_inc(x_1078);
lean_dec(x_1077);
x_1046 = x_1078;
goto block_1070;
}
block_1070:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1047; 
lean_dec(x_3);
x_1047 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1046);
lean_dec(x_12);
if (lean_obj_tag(x_1047) == 0)
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; 
x_1048 = lean_ctor_get(x_1047, 1);
lean_inc(x_1048);
if (lean_is_exclusive(x_1047)) {
 lean_ctor_release(x_1047, 0);
 lean_ctor_release(x_1047, 1);
 x_1049 = x_1047;
} else {
 lean_dec_ref(x_1047);
 x_1049 = lean_box(0);
}
if (lean_is_scalar(x_1049)) {
 x_1050 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1050 = x_1049;
}
lean_ctor_set(x_1050, 0, x_2);
lean_ctor_set(x_1050, 1, x_1048);
return x_1050;
}
else
{
lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
lean_dec(x_2);
x_1051 = lean_ctor_get(x_1047, 0);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_1047, 1);
lean_inc(x_1052);
if (lean_is_exclusive(x_1047)) {
 lean_ctor_release(x_1047, 0);
 lean_ctor_release(x_1047, 1);
 x_1053 = x_1047;
} else {
 lean_dec_ref(x_1047);
 x_1053 = lean_box(0);
}
if (lean_is_scalar(x_1053)) {
 x_1054 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1054 = x_1053;
}
lean_ctor_set(x_1054, 0, x_1051);
lean_ctor_set(x_1054, 1, x_1052);
return x_1054;
}
}
else
{
lean_object* x_1055; lean_object* x_1056; 
x_1055 = lean_ctor_get(x_8, 0);
lean_inc(x_1055);
lean_dec(x_8);
lean_inc(x_4);
x_1056 = l_Lean_Elab_Term_isDefEq(x_6, x_1055, x_3, x_4, x_1046);
if (lean_obj_tag(x_1056) == 0)
{
lean_object* x_1057; lean_object* x_1058; 
x_1057 = lean_ctor_get(x_1056, 1);
lean_inc(x_1057);
lean_dec(x_1056);
x_1058 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1057);
lean_dec(x_12);
if (lean_obj_tag(x_1058) == 0)
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; 
x_1059 = lean_ctor_get(x_1058, 1);
lean_inc(x_1059);
if (lean_is_exclusive(x_1058)) {
 lean_ctor_release(x_1058, 0);
 lean_ctor_release(x_1058, 1);
 x_1060 = x_1058;
} else {
 lean_dec_ref(x_1058);
 x_1060 = lean_box(0);
}
if (lean_is_scalar(x_1060)) {
 x_1061 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1061 = x_1060;
}
lean_ctor_set(x_1061, 0, x_2);
lean_ctor_set(x_1061, 1, x_1059);
return x_1061;
}
else
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
lean_dec(x_2);
x_1062 = lean_ctor_get(x_1058, 0);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1058, 1);
lean_inc(x_1063);
if (lean_is_exclusive(x_1058)) {
 lean_ctor_release(x_1058, 0);
 lean_ctor_release(x_1058, 1);
 x_1064 = x_1058;
} else {
 lean_dec_ref(x_1058);
 x_1064 = lean_box(0);
}
if (lean_is_scalar(x_1064)) {
 x_1065 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1065 = x_1064;
}
lean_ctor_set(x_1065, 0, x_1062);
lean_ctor_set(x_1065, 1, x_1063);
return x_1065;
}
}
else
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1066 = lean_ctor_get(x_1056, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1056, 1);
lean_inc(x_1067);
if (lean_is_exclusive(x_1056)) {
 lean_ctor_release(x_1056, 0);
 lean_ctor_release(x_1056, 1);
 x_1068 = x_1056;
} else {
 lean_dec_ref(x_1056);
 x_1068 = lean_box(0);
}
if (lean_is_scalar(x_1068)) {
 x_1069 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1069 = x_1068;
}
lean_ctor_set(x_1069, 0, x_1066);
lean_ctor_set(x_1069, 1, x_1067);
return x_1069;
}
}
}
}
}
}
else
{
lean_object* x_1079; lean_object* x_1080; 
lean_dec(x_913);
lean_dec(x_90);
lean_dec(x_3);
x_1079 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1080 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1079, x_91, x_4, x_909);
if (lean_obj_tag(x_1080) == 0)
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; uint32_t x_1085; uint16_t x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; 
x_1081 = lean_ctor_get(x_1080, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1080, 1);
lean_inc(x_1082);
lean_dec(x_1080);
x_1083 = lean_unsigned_to_nat(1u);
x_1084 = lean_nat_add(x_10, x_1083);
lean_dec(x_10);
x_1085 = 0;
x_1086 = 0;
x_1087 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_1087, 0, x_6);
lean_ctor_set(x_1087, 1, x_7);
lean_ctor_set(x_1087, 2, x_8);
lean_ctor_set(x_1087, 3, x_1084);
lean_ctor_set(x_1087, 4, x_11);
lean_ctor_set(x_1087, 5, x_12);
lean_ctor_set(x_1087, 6, x_13);
lean_ctor_set_uint8(x_1087, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_1087, sizeof(void*)*7 + 7, x_910);
lean_ctor_set_uint32(x_1087, sizeof(void*)*7, x_1085);
lean_ctor_set_uint16(x_1087, sizeof(void*)*7 + 4, x_1086);
lean_inc(x_1081);
x_1088 = l_Lean_mkApp(x_2, x_1081);
x_1089 = lean_expr_instantiate1(x_92, x_1081);
lean_dec(x_1081);
lean_dec(x_92);
x_1 = x_1087;
x_2 = x_1088;
x_3 = x_1089;
x_5 = x_1082;
goto _start;
}
else
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; 
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
x_1091 = lean_ctor_get(x_1080, 0);
lean_inc(x_1091);
x_1092 = lean_ctor_get(x_1080, 1);
lean_inc(x_1092);
if (lean_is_exclusive(x_1080)) {
 lean_ctor_release(x_1080, 0);
 lean_ctor_release(x_1080, 1);
 x_1093 = x_1080;
} else {
 lean_dec_ref(x_1080);
 x_1093 = lean_box(0);
}
if (lean_is_scalar(x_1093)) {
 x_1094 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1094 = x_1093;
}
lean_ctor_set(x_1094, 0, x_1091);
lean_ctor_set(x_1094, 1, x_1092);
return x_1094;
}
}
}
else
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
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
x_1095 = lean_ctor_get(x_707, 0);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_707, 1);
lean_inc(x_1096);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_1097 = x_707;
} else {
 lean_dec_ref(x_707);
 x_1097 = lean_box(0);
}
if (lean_is_scalar(x_1097)) {
 x_1098 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1098 = x_1097;
}
lean_ctor_set(x_1098, 0, x_1095);
lean_ctor_set(x_1098, 1, x_1096);
return x_1098;
}
}
}
case 3:
{
if (x_9 == 0)
{
uint8_t x_1099; 
lean_dec(x_90);
lean_dec(x_16);
lean_dec(x_3);
x_1099 = !lean_is_exclusive(x_1);
if (x_1099 == 0)
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; uint8_t x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; uint32_t x_1115; uint16_t x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1100 = lean_ctor_get(x_1, 6);
lean_dec(x_1100);
x_1101 = lean_ctor_get(x_1, 5);
lean_dec(x_1101);
x_1102 = lean_ctor_get(x_1, 4);
lean_dec(x_1102);
x_1103 = lean_ctor_get(x_1, 3);
lean_dec(x_1103);
x_1104 = lean_ctor_get(x_1, 2);
lean_dec(x_1104);
x_1105 = lean_ctor_get(x_1, 1);
lean_dec(x_1105);
x_1106 = lean_ctor_get(x_1, 0);
lean_dec(x_1106);
x_1107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1107, 0, x_91);
x_1108 = 1;
x_1109 = lean_box(0);
lean_inc(x_4);
x_1110 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_1107, x_1108, x_1109, x_4, x_17);
x_1111 = lean_ctor_get(x_1110, 0);
lean_inc(x_1111);
x_1112 = lean_ctor_get(x_1110, 1);
lean_inc(x_1112);
lean_dec(x_1110);
x_1113 = l_Lean_Expr_mvarId_x21(x_1111);
x_1114 = lean_array_push(x_12, x_1113);
x_1115 = 0;
x_1116 = 0;
lean_ctor_set(x_1, 5, x_1114);
lean_ctor_set_uint32(x_1, sizeof(void*)*7, x_1115);
lean_ctor_set_uint16(x_1, sizeof(void*)*7 + 4, x_1116);
lean_inc(x_1111);
x_1117 = l_Lean_mkApp(x_2, x_1111);
x_1118 = lean_expr_instantiate1(x_92, x_1111);
lean_dec(x_1111);
lean_dec(x_92);
x_2 = x_1117;
x_3 = x_1118;
x_5 = x_1112;
goto _start;
}
else
{
lean_object* x_1120; uint8_t x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; uint32_t x_1128; uint16_t x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
lean_dec(x_1);
x_1120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1120, 0, x_91);
x_1121 = 1;
x_1122 = lean_box(0);
lean_inc(x_4);
x_1123 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_1120, x_1121, x_1122, x_4, x_17);
x_1124 = lean_ctor_get(x_1123, 0);
lean_inc(x_1124);
x_1125 = lean_ctor_get(x_1123, 1);
lean_inc(x_1125);
lean_dec(x_1123);
x_1126 = l_Lean_Expr_mvarId_x21(x_1124);
x_1127 = lean_array_push(x_12, x_1126);
x_1128 = 0;
x_1129 = 0;
x_1130 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_1130, 0, x_6);
lean_ctor_set(x_1130, 1, x_7);
lean_ctor_set(x_1130, 2, x_8);
lean_ctor_set(x_1130, 3, x_10);
lean_ctor_set(x_1130, 4, x_11);
lean_ctor_set(x_1130, 5, x_1127);
lean_ctor_set(x_1130, 6, x_13);
lean_ctor_set_uint8(x_1130, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_1130, sizeof(void*)*7 + 7, x_14);
lean_ctor_set_uint32(x_1130, sizeof(void*)*7, x_1128);
lean_ctor_set_uint16(x_1130, sizeof(void*)*7 + 4, x_1129);
lean_inc(x_1124);
x_1131 = l_Lean_mkApp(x_2, x_1124);
x_1132 = lean_expr_instantiate1(x_92, x_1124);
lean_dec(x_1124);
lean_dec(x_92);
x_1 = x_1130;
x_2 = x_1131;
x_3 = x_1132;
x_5 = x_1125;
goto _start;
}
}
else
{
uint8_t x_1134; 
x_1134 = l___private_Init_Lean_Elab_App_9__nextArgIsHole(x_1);
if (x_1134 == 0)
{
lean_object* x_1135; uint8_t x_1136; 
lean_inc(x_4);
lean_inc(x_1);
x_1135 = l___private_Init_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_17);
x_1136 = !lean_is_exclusive(x_1);
if (x_1136 == 0)
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
x_1137 = lean_ctor_get(x_1, 6);
lean_dec(x_1137);
x_1138 = lean_ctor_get(x_1, 5);
lean_dec(x_1138);
x_1139 = lean_ctor_get(x_1, 4);
lean_dec(x_1139);
x_1140 = lean_ctor_get(x_1, 3);
lean_dec(x_1140);
x_1141 = lean_ctor_get(x_1, 2);
lean_dec(x_1141);
x_1142 = lean_ctor_get(x_1, 1);
lean_dec(x_1142);
x_1143 = lean_ctor_get(x_1, 0);
lean_dec(x_1143);
if (lean_obj_tag(x_1135) == 0)
{
lean_object* x_1144; lean_object* x_1145; uint8_t x_1146; 
x_1144 = lean_ctor_get(x_1135, 1);
lean_inc(x_1144);
lean_dec(x_1135);
x_1145 = lean_array_get_size(x_7);
x_1146 = lean_nat_dec_lt(x_10, x_1145);
lean_dec(x_1145);
if (x_1146 == 0)
{
uint8_t x_1147; 
lean_free_object(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
x_1147 = l_Array_isEmpty___rarg(x_11);
if (x_1147 == 0)
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1148 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1148, 0, x_90);
x_1149 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1150 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1150, 0, x_1149);
lean_ctor_set(x_1150, 1, x_1148);
x_1151 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1152 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1152, 0, x_1150);
lean_ctor_set(x_1152, 1, x_1151);
x_1153 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
x_1154 = l_Array_toList___rarg(x_1153);
lean_dec(x_1153);
x_1155 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1154);
x_1156 = l_Array_HasRepr___rarg___closed__1;
x_1157 = lean_string_append(x_1156, x_1155);
lean_dec(x_1155);
x_1158 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1158, 0, x_1157);
x_1159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1159, 0, x_1158);
x_1160 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1160, 0, x_1152);
lean_ctor_set(x_1160, 1, x_1159);
x_1161 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1160, x_4, x_1144);
lean_dec(x_6);
return x_1161;
}
else
{
lean_object* x_1162; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; uint8_t x_1193; 
lean_dec(x_90);
lean_dec(x_11);
x_1189 = l_Lean_Elab_Term_getOptions(x_4, x_1144);
x_1190 = lean_ctor_get(x_1189, 0);
lean_inc(x_1190);
x_1191 = lean_ctor_get(x_1189, 1);
lean_inc(x_1191);
lean_dec(x_1189);
x_1192 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1193 = l_Lean_checkTraceOption(x_1190, x_1192);
lean_dec(x_1190);
if (x_1193 == 0)
{
x_1162 = x_1191;
goto block_1188;
}
else
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; 
lean_inc(x_2);
x_1194 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1194, 0, x_2);
x_1195 = l_Lean_Elab_Term_logTrace(x_1192, x_6, x_1194, x_4, x_1191);
x_1196 = lean_ctor_get(x_1195, 1);
lean_inc(x_1196);
lean_dec(x_1195);
x_1162 = x_1196;
goto block_1188;
}
block_1188:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1163; 
lean_dec(x_3);
x_1163 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1162);
lean_dec(x_12);
if (lean_obj_tag(x_1163) == 0)
{
uint8_t x_1164; 
x_1164 = !lean_is_exclusive(x_1163);
if (x_1164 == 0)
{
lean_object* x_1165; 
x_1165 = lean_ctor_get(x_1163, 0);
lean_dec(x_1165);
lean_ctor_set(x_1163, 0, x_2);
return x_1163;
}
else
{
lean_object* x_1166; lean_object* x_1167; 
x_1166 = lean_ctor_get(x_1163, 1);
lean_inc(x_1166);
lean_dec(x_1163);
x_1167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1167, 0, x_2);
lean_ctor_set(x_1167, 1, x_1166);
return x_1167;
}
}
else
{
uint8_t x_1168; 
lean_dec(x_2);
x_1168 = !lean_is_exclusive(x_1163);
if (x_1168 == 0)
{
return x_1163;
}
else
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; 
x_1169 = lean_ctor_get(x_1163, 0);
x_1170 = lean_ctor_get(x_1163, 1);
lean_inc(x_1170);
lean_inc(x_1169);
lean_dec(x_1163);
x_1171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1171, 0, x_1169);
lean_ctor_set(x_1171, 1, x_1170);
return x_1171;
}
}
}
else
{
lean_object* x_1172; lean_object* x_1173; 
x_1172 = lean_ctor_get(x_8, 0);
lean_inc(x_1172);
lean_dec(x_8);
lean_inc(x_4);
x_1173 = l_Lean_Elab_Term_isDefEq(x_6, x_1172, x_3, x_4, x_1162);
if (lean_obj_tag(x_1173) == 0)
{
lean_object* x_1174; lean_object* x_1175; 
x_1174 = lean_ctor_get(x_1173, 1);
lean_inc(x_1174);
lean_dec(x_1173);
x_1175 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1174);
lean_dec(x_12);
if (lean_obj_tag(x_1175) == 0)
{
uint8_t x_1176; 
x_1176 = !lean_is_exclusive(x_1175);
if (x_1176 == 0)
{
lean_object* x_1177; 
x_1177 = lean_ctor_get(x_1175, 0);
lean_dec(x_1177);
lean_ctor_set(x_1175, 0, x_2);
return x_1175;
}
else
{
lean_object* x_1178; lean_object* x_1179; 
x_1178 = lean_ctor_get(x_1175, 1);
lean_inc(x_1178);
lean_dec(x_1175);
x_1179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1179, 0, x_2);
lean_ctor_set(x_1179, 1, x_1178);
return x_1179;
}
}
else
{
uint8_t x_1180; 
lean_dec(x_2);
x_1180 = !lean_is_exclusive(x_1175);
if (x_1180 == 0)
{
return x_1175;
}
else
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
x_1181 = lean_ctor_get(x_1175, 0);
x_1182 = lean_ctor_get(x_1175, 1);
lean_inc(x_1182);
lean_inc(x_1181);
lean_dec(x_1175);
x_1183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1183, 0, x_1181);
lean_ctor_set(x_1183, 1, x_1182);
return x_1183;
}
}
}
else
{
uint8_t x_1184; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1184 = !lean_is_exclusive(x_1173);
if (x_1184 == 0)
{
return x_1173;
}
else
{
lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; 
x_1185 = lean_ctor_get(x_1173, 0);
x_1186 = lean_ctor_get(x_1173, 1);
lean_inc(x_1186);
lean_inc(x_1185);
lean_dec(x_1173);
x_1187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1187, 0, x_1185);
lean_ctor_set(x_1187, 1, x_1186);
return x_1187;
}
}
}
}
}
}
else
{
lean_object* x_1197; lean_object* x_1198; 
lean_dec(x_90);
lean_dec(x_3);
x_1197 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1198 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1197, x_91, x_4, x_1144);
if (lean_obj_tag(x_1198) == 0)
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; uint8_t x_1203; uint32_t x_1204; uint16_t x_1205; lean_object* x_1206; lean_object* x_1207; 
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1198, 1);
lean_inc(x_1200);
lean_dec(x_1198);
x_1201 = lean_unsigned_to_nat(1u);
x_1202 = lean_nat_add(x_10, x_1201);
lean_dec(x_10);
x_1203 = 1;
x_1204 = 0;
x_1205 = 0;
lean_ctor_set(x_1, 3, x_1202);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 7, x_1203);
lean_ctor_set_uint32(x_1, sizeof(void*)*7, x_1204);
lean_ctor_set_uint16(x_1, sizeof(void*)*7 + 4, x_1205);
lean_inc(x_1199);
x_1206 = l_Lean_mkApp(x_2, x_1199);
x_1207 = lean_expr_instantiate1(x_92, x_1199);
lean_dec(x_1199);
lean_dec(x_92);
x_2 = x_1206;
x_3 = x_1207;
x_5 = x_1200;
goto _start;
}
else
{
uint8_t x_1209; 
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
x_1209 = !lean_is_exclusive(x_1198);
if (x_1209 == 0)
{
return x_1198;
}
else
{
lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
x_1210 = lean_ctor_get(x_1198, 0);
x_1211 = lean_ctor_get(x_1198, 1);
lean_inc(x_1211);
lean_inc(x_1210);
lean_dec(x_1198);
x_1212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1212, 0, x_1210);
lean_ctor_set(x_1212, 1, x_1211);
return x_1212;
}
}
}
}
else
{
uint8_t x_1213; 
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
x_1213 = !lean_is_exclusive(x_1135);
if (x_1213 == 0)
{
return x_1135;
}
else
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
x_1214 = lean_ctor_get(x_1135, 0);
x_1215 = lean_ctor_get(x_1135, 1);
lean_inc(x_1215);
lean_inc(x_1214);
lean_dec(x_1135);
x_1216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1216, 0, x_1214);
lean_ctor_set(x_1216, 1, x_1215);
return x_1216;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1135) == 0)
{
lean_object* x_1217; lean_object* x_1218; uint8_t x_1219; 
x_1217 = lean_ctor_get(x_1135, 1);
lean_inc(x_1217);
lean_dec(x_1135);
x_1218 = lean_array_get_size(x_7);
x_1219 = lean_nat_dec_lt(x_10, x_1218);
lean_dec(x_1218);
if (x_1219 == 0)
{
uint8_t x_1220; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
x_1220 = l_Array_isEmpty___rarg(x_11);
if (x_1220 == 0)
{
lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1221 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1221, 0, x_90);
x_1222 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1223 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1223, 0, x_1222);
lean_ctor_set(x_1223, 1, x_1221);
x_1224 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1225 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1225, 0, x_1223);
lean_ctor_set(x_1225, 1, x_1224);
x_1226 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
x_1227 = l_Array_toList___rarg(x_1226);
lean_dec(x_1226);
x_1228 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1227);
x_1229 = l_Array_HasRepr___rarg___closed__1;
x_1230 = lean_string_append(x_1229, x_1228);
lean_dec(x_1228);
x_1231 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1231, 0, x_1230);
x_1232 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1232, 0, x_1231);
x_1233 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1233, 0, x_1225);
lean_ctor_set(x_1233, 1, x_1232);
x_1234 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1233, x_4, x_1217);
lean_dec(x_6);
return x_1234;
}
else
{
lean_object* x_1235; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; uint8_t x_1264; 
lean_dec(x_90);
lean_dec(x_11);
x_1260 = l_Lean_Elab_Term_getOptions(x_4, x_1217);
x_1261 = lean_ctor_get(x_1260, 0);
lean_inc(x_1261);
x_1262 = lean_ctor_get(x_1260, 1);
lean_inc(x_1262);
lean_dec(x_1260);
x_1263 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1264 = l_Lean_checkTraceOption(x_1261, x_1263);
lean_dec(x_1261);
if (x_1264 == 0)
{
x_1235 = x_1262;
goto block_1259;
}
else
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
lean_inc(x_2);
x_1265 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1265, 0, x_2);
x_1266 = l_Lean_Elab_Term_logTrace(x_1263, x_6, x_1265, x_4, x_1262);
x_1267 = lean_ctor_get(x_1266, 1);
lean_inc(x_1267);
lean_dec(x_1266);
x_1235 = x_1267;
goto block_1259;
}
block_1259:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1236; 
lean_dec(x_3);
x_1236 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1235);
lean_dec(x_12);
if (lean_obj_tag(x_1236) == 0)
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; 
x_1237 = lean_ctor_get(x_1236, 1);
lean_inc(x_1237);
if (lean_is_exclusive(x_1236)) {
 lean_ctor_release(x_1236, 0);
 lean_ctor_release(x_1236, 1);
 x_1238 = x_1236;
} else {
 lean_dec_ref(x_1236);
 x_1238 = lean_box(0);
}
if (lean_is_scalar(x_1238)) {
 x_1239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1239 = x_1238;
}
lean_ctor_set(x_1239, 0, x_2);
lean_ctor_set(x_1239, 1, x_1237);
return x_1239;
}
else
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; 
lean_dec(x_2);
x_1240 = lean_ctor_get(x_1236, 0);
lean_inc(x_1240);
x_1241 = lean_ctor_get(x_1236, 1);
lean_inc(x_1241);
if (lean_is_exclusive(x_1236)) {
 lean_ctor_release(x_1236, 0);
 lean_ctor_release(x_1236, 1);
 x_1242 = x_1236;
} else {
 lean_dec_ref(x_1236);
 x_1242 = lean_box(0);
}
if (lean_is_scalar(x_1242)) {
 x_1243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1243 = x_1242;
}
lean_ctor_set(x_1243, 0, x_1240);
lean_ctor_set(x_1243, 1, x_1241);
return x_1243;
}
}
else
{
lean_object* x_1244; lean_object* x_1245; 
x_1244 = lean_ctor_get(x_8, 0);
lean_inc(x_1244);
lean_dec(x_8);
lean_inc(x_4);
x_1245 = l_Lean_Elab_Term_isDefEq(x_6, x_1244, x_3, x_4, x_1235);
if (lean_obj_tag(x_1245) == 0)
{
lean_object* x_1246; lean_object* x_1247; 
x_1246 = lean_ctor_get(x_1245, 1);
lean_inc(x_1246);
lean_dec(x_1245);
x_1247 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1246);
lean_dec(x_12);
if (lean_obj_tag(x_1247) == 0)
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; 
x_1248 = lean_ctor_get(x_1247, 1);
lean_inc(x_1248);
if (lean_is_exclusive(x_1247)) {
 lean_ctor_release(x_1247, 0);
 lean_ctor_release(x_1247, 1);
 x_1249 = x_1247;
} else {
 lean_dec_ref(x_1247);
 x_1249 = lean_box(0);
}
if (lean_is_scalar(x_1249)) {
 x_1250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1250 = x_1249;
}
lean_ctor_set(x_1250, 0, x_2);
lean_ctor_set(x_1250, 1, x_1248);
return x_1250;
}
else
{
lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; 
lean_dec(x_2);
x_1251 = lean_ctor_get(x_1247, 0);
lean_inc(x_1251);
x_1252 = lean_ctor_get(x_1247, 1);
lean_inc(x_1252);
if (lean_is_exclusive(x_1247)) {
 lean_ctor_release(x_1247, 0);
 lean_ctor_release(x_1247, 1);
 x_1253 = x_1247;
} else {
 lean_dec_ref(x_1247);
 x_1253 = lean_box(0);
}
if (lean_is_scalar(x_1253)) {
 x_1254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1254 = x_1253;
}
lean_ctor_set(x_1254, 0, x_1251);
lean_ctor_set(x_1254, 1, x_1252);
return x_1254;
}
}
else
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1255 = lean_ctor_get(x_1245, 0);
lean_inc(x_1255);
x_1256 = lean_ctor_get(x_1245, 1);
lean_inc(x_1256);
if (lean_is_exclusive(x_1245)) {
 lean_ctor_release(x_1245, 0);
 lean_ctor_release(x_1245, 1);
 x_1257 = x_1245;
} else {
 lean_dec_ref(x_1245);
 x_1257 = lean_box(0);
}
if (lean_is_scalar(x_1257)) {
 x_1258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1258 = x_1257;
}
lean_ctor_set(x_1258, 0, x_1255);
lean_ctor_set(x_1258, 1, x_1256);
return x_1258;
}
}
}
}
}
else
{
lean_object* x_1268; lean_object* x_1269; 
lean_dec(x_90);
lean_dec(x_3);
x_1268 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1269 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1268, x_91, x_4, x_1217);
if (lean_obj_tag(x_1269) == 0)
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; uint8_t x_1274; uint32_t x_1275; uint16_t x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; 
x_1270 = lean_ctor_get(x_1269, 0);
lean_inc(x_1270);
x_1271 = lean_ctor_get(x_1269, 1);
lean_inc(x_1271);
lean_dec(x_1269);
x_1272 = lean_unsigned_to_nat(1u);
x_1273 = lean_nat_add(x_10, x_1272);
lean_dec(x_10);
x_1274 = 1;
x_1275 = 0;
x_1276 = 0;
x_1277 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_1277, 0, x_6);
lean_ctor_set(x_1277, 1, x_7);
lean_ctor_set(x_1277, 2, x_8);
lean_ctor_set(x_1277, 3, x_1273);
lean_ctor_set(x_1277, 4, x_11);
lean_ctor_set(x_1277, 5, x_12);
lean_ctor_set(x_1277, 6, x_13);
lean_ctor_set_uint8(x_1277, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_1277, sizeof(void*)*7 + 7, x_1274);
lean_ctor_set_uint32(x_1277, sizeof(void*)*7, x_1275);
lean_ctor_set_uint16(x_1277, sizeof(void*)*7 + 4, x_1276);
lean_inc(x_1270);
x_1278 = l_Lean_mkApp(x_2, x_1270);
x_1279 = lean_expr_instantiate1(x_92, x_1270);
lean_dec(x_1270);
lean_dec(x_92);
x_1 = x_1277;
x_2 = x_1278;
x_3 = x_1279;
x_5 = x_1271;
goto _start;
}
else
{
lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; 
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
x_1281 = lean_ctor_get(x_1269, 0);
lean_inc(x_1281);
x_1282 = lean_ctor_get(x_1269, 1);
lean_inc(x_1282);
if (lean_is_exclusive(x_1269)) {
 lean_ctor_release(x_1269, 0);
 lean_ctor_release(x_1269, 1);
 x_1283 = x_1269;
} else {
 lean_dec_ref(x_1269);
 x_1283 = lean_box(0);
}
if (lean_is_scalar(x_1283)) {
 x_1284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1284 = x_1283;
}
lean_ctor_set(x_1284, 0, x_1281);
lean_ctor_set(x_1284, 1, x_1282);
return x_1284;
}
}
}
else
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; 
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
x_1285 = lean_ctor_get(x_1135, 0);
lean_inc(x_1285);
x_1286 = lean_ctor_get(x_1135, 1);
lean_inc(x_1286);
if (lean_is_exclusive(x_1135)) {
 lean_ctor_release(x_1135, 0);
 lean_ctor_release(x_1135, 1);
 x_1287 = x_1135;
} else {
 lean_dec_ref(x_1135);
 x_1287 = lean_box(0);
}
if (lean_is_scalar(x_1287)) {
 x_1288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1288 = x_1287;
}
lean_ctor_set(x_1288, 0, x_1285);
lean_ctor_set(x_1288, 1, x_1286);
return x_1288;
}
}
}
else
{
uint8_t x_1289; 
lean_dec(x_90);
lean_dec(x_16);
lean_dec(x_3);
x_1289 = !lean_is_exclusive(x_1);
if (x_1289 == 0)
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; uint8_t x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; uint32_t x_1307; uint16_t x_1308; lean_object* x_1309; lean_object* x_1310; 
x_1290 = lean_ctor_get(x_1, 6);
lean_dec(x_1290);
x_1291 = lean_ctor_get(x_1, 5);
lean_dec(x_1291);
x_1292 = lean_ctor_get(x_1, 4);
lean_dec(x_1292);
x_1293 = lean_ctor_get(x_1, 3);
lean_dec(x_1293);
x_1294 = lean_ctor_get(x_1, 2);
lean_dec(x_1294);
x_1295 = lean_ctor_get(x_1, 1);
lean_dec(x_1295);
x_1296 = lean_ctor_get(x_1, 0);
lean_dec(x_1296);
x_1297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1297, 0, x_91);
x_1298 = 1;
x_1299 = lean_box(0);
lean_inc(x_4);
x_1300 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_1297, x_1298, x_1299, x_4, x_17);
x_1301 = lean_ctor_get(x_1300, 0);
lean_inc(x_1301);
x_1302 = lean_ctor_get(x_1300, 1);
lean_inc(x_1302);
lean_dec(x_1300);
x_1303 = lean_unsigned_to_nat(1u);
x_1304 = lean_nat_add(x_10, x_1303);
lean_dec(x_10);
x_1305 = l_Lean_Expr_mvarId_x21(x_1301);
x_1306 = lean_array_push(x_12, x_1305);
x_1307 = 0;
x_1308 = 0;
lean_ctor_set(x_1, 5, x_1306);
lean_ctor_set(x_1, 3, x_1304);
lean_ctor_set_uint32(x_1, sizeof(void*)*7, x_1307);
lean_ctor_set_uint16(x_1, sizeof(void*)*7 + 4, x_1308);
lean_inc(x_1301);
x_1309 = l_Lean_mkApp(x_2, x_1301);
x_1310 = lean_expr_instantiate1(x_92, x_1301);
lean_dec(x_1301);
lean_dec(x_92);
x_2 = x_1309;
x_3 = x_1310;
x_5 = x_1302;
goto _start;
}
else
{
lean_object* x_1312; uint8_t x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; uint32_t x_1322; uint16_t x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; 
lean_dec(x_1);
x_1312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1312, 0, x_91);
x_1313 = 1;
x_1314 = lean_box(0);
lean_inc(x_4);
x_1315 = l_Lean_Elab_Term_mkFreshExprMVar(x_6, x_1312, x_1313, x_1314, x_4, x_17);
x_1316 = lean_ctor_get(x_1315, 0);
lean_inc(x_1316);
x_1317 = lean_ctor_get(x_1315, 1);
lean_inc(x_1317);
lean_dec(x_1315);
x_1318 = lean_unsigned_to_nat(1u);
x_1319 = lean_nat_add(x_10, x_1318);
lean_dec(x_10);
x_1320 = l_Lean_Expr_mvarId_x21(x_1316);
x_1321 = lean_array_push(x_12, x_1320);
x_1322 = 0;
x_1323 = 0;
x_1324 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_1324, 0, x_6);
lean_ctor_set(x_1324, 1, x_7);
lean_ctor_set(x_1324, 2, x_8);
lean_ctor_set(x_1324, 3, x_1319);
lean_ctor_set(x_1324, 4, x_11);
lean_ctor_set(x_1324, 5, x_1321);
lean_ctor_set(x_1324, 6, x_13);
lean_ctor_set_uint8(x_1324, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_1324, sizeof(void*)*7 + 7, x_14);
lean_ctor_set_uint32(x_1324, sizeof(void*)*7, x_1322);
lean_ctor_set_uint16(x_1324, sizeof(void*)*7 + 4, x_1323);
lean_inc(x_1316);
x_1325 = l_Lean_mkApp(x_2, x_1316);
x_1326 = lean_expr_instantiate1(x_92, x_1316);
lean_dec(x_1316);
lean_dec(x_92);
x_1 = x_1324;
x_2 = x_1325;
x_3 = x_1326;
x_5 = x_1317;
goto _start;
}
}
}
}
default: 
{
lean_object* x_1328; uint8_t x_1329; 
lean_inc(x_4);
lean_inc(x_1);
x_1328 = l___private_Init_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_17);
x_1329 = !lean_is_exclusive(x_1);
if (x_1329 == 0)
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; 
x_1330 = lean_ctor_get(x_1, 6);
lean_dec(x_1330);
x_1331 = lean_ctor_get(x_1, 5);
lean_dec(x_1331);
x_1332 = lean_ctor_get(x_1, 4);
lean_dec(x_1332);
x_1333 = lean_ctor_get(x_1, 3);
lean_dec(x_1333);
x_1334 = lean_ctor_get(x_1, 2);
lean_dec(x_1334);
x_1335 = lean_ctor_get(x_1, 1);
lean_dec(x_1335);
x_1336 = lean_ctor_get(x_1, 0);
lean_dec(x_1336);
if (lean_obj_tag(x_1328) == 0)
{
lean_object* x_1337; uint8_t x_1338; uint32_t x_1339; uint16_t x_1340; lean_object* x_1341; uint8_t x_1342; 
x_1337 = lean_ctor_get(x_1328, 1);
lean_inc(x_1337);
lean_dec(x_1328);
x_1338 = 1;
x_1339 = 0;
x_1340 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 7, x_1338);
lean_ctor_set_uint32(x_1, sizeof(void*)*7, x_1339);
lean_ctor_set_uint16(x_1, sizeof(void*)*7 + 4, x_1340);
x_1341 = lean_array_get_size(x_7);
x_1342 = lean_nat_dec_lt(x_10, x_1341);
lean_dec(x_1341);
if (x_1342 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1343; 
x_1343 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_1343) == 0)
{
lean_object* x_1344; 
x_1344 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_1344) == 0)
{
uint8_t x_1345; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
x_1345 = l_Array_isEmpty___rarg(x_11);
if (x_1345 == 0)
{
lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1346 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1346, 0, x_90);
x_1347 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1348 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1348, 0, x_1347);
lean_ctor_set(x_1348, 1, x_1346);
x_1349 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1350 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1350, 0, x_1348);
lean_ctor_set(x_1350, 1, x_1349);
x_1351 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
x_1352 = l_Array_toList___rarg(x_1351);
lean_dec(x_1351);
x_1353 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1352);
x_1354 = l_Array_HasRepr___rarg___closed__1;
x_1355 = lean_string_append(x_1354, x_1353);
lean_dec(x_1353);
x_1356 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1356, 0, x_1355);
x_1357 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1357, 0, x_1356);
x_1358 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1358, 0, x_1350);
lean_ctor_set(x_1358, 1, x_1357);
x_1359 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1358, x_4, x_1337);
lean_dec(x_6);
return x_1359;
}
else
{
lean_object* x_1360; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; uint8_t x_1391; 
lean_dec(x_90);
lean_dec(x_11);
x_1387 = l_Lean_Elab_Term_getOptions(x_4, x_1337);
x_1388 = lean_ctor_get(x_1387, 0);
lean_inc(x_1388);
x_1389 = lean_ctor_get(x_1387, 1);
lean_inc(x_1389);
lean_dec(x_1387);
x_1390 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1391 = l_Lean_checkTraceOption(x_1388, x_1390);
lean_dec(x_1388);
if (x_1391 == 0)
{
x_1360 = x_1389;
goto block_1386;
}
else
{
lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; 
lean_inc(x_2);
x_1392 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1392, 0, x_2);
x_1393 = l_Lean_Elab_Term_logTrace(x_1390, x_6, x_1392, x_4, x_1389);
x_1394 = lean_ctor_get(x_1393, 1);
lean_inc(x_1394);
lean_dec(x_1393);
x_1360 = x_1394;
goto block_1386;
}
block_1386:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1361; 
lean_dec(x_3);
x_1361 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1360);
lean_dec(x_12);
if (lean_obj_tag(x_1361) == 0)
{
uint8_t x_1362; 
x_1362 = !lean_is_exclusive(x_1361);
if (x_1362 == 0)
{
lean_object* x_1363; 
x_1363 = lean_ctor_get(x_1361, 0);
lean_dec(x_1363);
lean_ctor_set(x_1361, 0, x_2);
return x_1361;
}
else
{
lean_object* x_1364; lean_object* x_1365; 
x_1364 = lean_ctor_get(x_1361, 1);
lean_inc(x_1364);
lean_dec(x_1361);
x_1365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1365, 0, x_2);
lean_ctor_set(x_1365, 1, x_1364);
return x_1365;
}
}
else
{
uint8_t x_1366; 
lean_dec(x_2);
x_1366 = !lean_is_exclusive(x_1361);
if (x_1366 == 0)
{
return x_1361;
}
else
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; 
x_1367 = lean_ctor_get(x_1361, 0);
x_1368 = lean_ctor_get(x_1361, 1);
lean_inc(x_1368);
lean_inc(x_1367);
lean_dec(x_1361);
x_1369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1369, 0, x_1367);
lean_ctor_set(x_1369, 1, x_1368);
return x_1369;
}
}
}
else
{
lean_object* x_1370; lean_object* x_1371; 
x_1370 = lean_ctor_get(x_8, 0);
lean_inc(x_1370);
lean_dec(x_8);
lean_inc(x_4);
x_1371 = l_Lean_Elab_Term_isDefEq(x_6, x_1370, x_3, x_4, x_1360);
if (lean_obj_tag(x_1371) == 0)
{
lean_object* x_1372; lean_object* x_1373; 
x_1372 = lean_ctor_get(x_1371, 1);
lean_inc(x_1372);
lean_dec(x_1371);
x_1373 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1372);
lean_dec(x_12);
if (lean_obj_tag(x_1373) == 0)
{
uint8_t x_1374; 
x_1374 = !lean_is_exclusive(x_1373);
if (x_1374 == 0)
{
lean_object* x_1375; 
x_1375 = lean_ctor_get(x_1373, 0);
lean_dec(x_1375);
lean_ctor_set(x_1373, 0, x_2);
return x_1373;
}
else
{
lean_object* x_1376; lean_object* x_1377; 
x_1376 = lean_ctor_get(x_1373, 1);
lean_inc(x_1376);
lean_dec(x_1373);
x_1377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1377, 0, x_2);
lean_ctor_set(x_1377, 1, x_1376);
return x_1377;
}
}
else
{
uint8_t x_1378; 
lean_dec(x_2);
x_1378 = !lean_is_exclusive(x_1373);
if (x_1378 == 0)
{
return x_1373;
}
else
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
x_1379 = lean_ctor_get(x_1373, 0);
x_1380 = lean_ctor_get(x_1373, 1);
lean_inc(x_1380);
lean_inc(x_1379);
lean_dec(x_1373);
x_1381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1381, 0, x_1379);
lean_ctor_set(x_1381, 1, x_1380);
return x_1381;
}
}
}
else
{
uint8_t x_1382; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1382 = !lean_is_exclusive(x_1371);
if (x_1382 == 0)
{
return x_1371;
}
else
{
lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; 
x_1383 = lean_ctor_get(x_1371, 0);
x_1384 = lean_ctor_get(x_1371, 1);
lean_inc(x_1384);
lean_inc(x_1383);
lean_dec(x_1371);
x_1385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1385, 0, x_1383);
lean_ctor_set(x_1385, 1, x_1384);
return x_1385;
}
}
}
}
}
}
else
{
lean_object* x_1395; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1395 = lean_ctor_get(x_1344, 0);
lean_inc(x_1395);
lean_dec(x_1344);
if (lean_obj_tag(x_1395) == 4)
{
lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; 
x_1396 = lean_ctor_get(x_1395, 0);
lean_inc(x_1396);
lean_dec(x_1395);
x_1397 = l_Lean_Elab_Term_getEnv___rarg(x_1337);
x_1398 = lean_ctor_get(x_1397, 0);
lean_inc(x_1398);
x_1399 = lean_ctor_get(x_1397, 1);
lean_inc(x_1399);
lean_dec(x_1397);
x_1400 = l_Lean_Elab_evalSyntaxConstant(x_1398, x_1396);
if (lean_obj_tag(x_1400) == 0)
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_1401 = lean_ctor_get(x_1400, 0);
lean_inc(x_1401);
lean_dec(x_1400);
x_1402 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1402, 0, x_1401);
x_1403 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1403, 0, x_1402);
x_1404 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1403, x_4, x_1399);
lean_dec(x_6);
return x_1404;
}
else
{
lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; 
x_1405 = lean_ctor_get(x_1400, 0);
lean_inc(x_1405);
lean_dec(x_1400);
x_1406 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1399);
x_1407 = lean_ctor_get(x_1406, 1);
lean_inc(x_1407);
lean_dec(x_1406);
x_1408 = l_Lean_Elab_Term_getMainModule___rarg(x_1407);
x_1409 = lean_ctor_get(x_1408, 1);
lean_inc(x_1409);
lean_dec(x_1408);
x_1410 = l_Lean_Syntax_getArgs(x_1405);
lean_dec(x_1405);
x_1411 = l_Array_empty___closed__1;
x_1412 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1410, x_1410, x_94, x_1411);
lean_dec(x_1410);
x_1413 = l_Lean_nullKind___closed__2;
x_1414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1414, 0, x_1413);
lean_ctor_set(x_1414, 1, x_1412);
x_1415 = lean_array_push(x_1411, x_1414);
x_1416 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_1417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1417, 0, x_1416);
lean_ctor_set(x_1417, 1, x_1415);
x_1418 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1419 = lean_array_push(x_1418, x_1417);
x_1420 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1421 = lean_array_push(x_1419, x_1420);
x_1422 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1423, 0, x_1422);
lean_ctor_set(x_1423, 1, x_1421);
x_1424 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_1425 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_1426 = lean_nat_sub(x_1425, x_94);
lean_dec(x_1425);
x_1427 = lean_unsigned_to_nat(1u);
x_1428 = lean_nat_sub(x_1426, x_1427);
lean_dec(x_1426);
x_1429 = l_Lean_Expr_getRevArg_x21___main(x_91, x_1428);
lean_dec(x_91);
if (lean_obj_tag(x_1424) == 0)
{
lean_object* x_1430; lean_object* x_1431; 
x_1430 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1430, 0, x_1423);
lean_inc(x_4);
lean_inc(x_2);
x_1431 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1430, x_1429, x_4, x_1409);
if (lean_obj_tag(x_1431) == 0)
{
lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; 
x_1432 = lean_ctor_get(x_1431, 0);
lean_inc(x_1432);
x_1433 = lean_ctor_get(x_1431, 1);
lean_inc(x_1433);
lean_dec(x_1431);
lean_inc(x_1432);
x_1434 = l_Lean_mkApp(x_2, x_1432);
x_1435 = lean_expr_instantiate1(x_92, x_1432);
lean_dec(x_1432);
lean_dec(x_92);
x_2 = x_1434;
x_3 = x_1435;
x_5 = x_1433;
goto _start;
}
else
{
uint8_t x_1437; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1437 = !lean_is_exclusive(x_1431);
if (x_1437 == 0)
{
return x_1431;
}
else
{
lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; 
x_1438 = lean_ctor_get(x_1431, 0);
x_1439 = lean_ctor_get(x_1431, 1);
lean_inc(x_1439);
lean_inc(x_1438);
lean_dec(x_1431);
x_1440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1440, 0, x_1438);
lean_ctor_set(x_1440, 1, x_1439);
return x_1440;
}
}
}
else
{
lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; 
x_1441 = lean_ctor_get(x_1424, 0);
lean_inc(x_1441);
lean_dec(x_1424);
x_1442 = l_Lean_Syntax_replaceInfo___main(x_1441, x_1423);
x_1443 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1443, 0, x_1442);
lean_inc(x_4);
lean_inc(x_2);
x_1444 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1443, x_1429, x_4, x_1409);
if (lean_obj_tag(x_1444) == 0)
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; 
x_1445 = lean_ctor_get(x_1444, 0);
lean_inc(x_1445);
x_1446 = lean_ctor_get(x_1444, 1);
lean_inc(x_1446);
lean_dec(x_1444);
lean_inc(x_1445);
x_1447 = l_Lean_mkApp(x_2, x_1445);
x_1448 = lean_expr_instantiate1(x_92, x_1445);
lean_dec(x_1445);
lean_dec(x_92);
x_2 = x_1447;
x_3 = x_1448;
x_5 = x_1446;
goto _start;
}
else
{
uint8_t x_1450; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1450 = !lean_is_exclusive(x_1444);
if (x_1450 == 0)
{
return x_1444;
}
else
{
lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; 
x_1451 = lean_ctor_get(x_1444, 0);
x_1452 = lean_ctor_get(x_1444, 1);
lean_inc(x_1452);
lean_inc(x_1451);
lean_dec(x_1444);
x_1453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1453, 0, x_1451);
lean_ctor_set(x_1453, 1, x_1452);
return x_1453;
}
}
}
}
}
else
{
lean_object* x_1454; lean_object* x_1455; 
lean_dec(x_1395);
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_1454 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1455 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1454, x_4, x_1337);
lean_dec(x_6);
return x_1455;
}
}
}
else
{
lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1456 = lean_ctor_get(x_1343, 0);
lean_inc(x_1456);
lean_dec(x_1343);
lean_inc(x_1456);
x_1457 = l_Lean_mkApp(x_2, x_1456);
x_1458 = lean_expr_instantiate1(x_92, x_1456);
lean_dec(x_1456);
lean_dec(x_92);
x_2 = x_1457;
x_3 = x_1458;
x_5 = x_1337;
goto _start;
}
}
else
{
uint8_t x_1460; 
lean_dec(x_1);
lean_dec(x_92);
lean_dec(x_91);
x_1460 = l_Array_isEmpty___rarg(x_11);
if (x_1460 == 0)
{
lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1461 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1461, 0, x_90);
x_1462 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1463 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1463, 0, x_1462);
lean_ctor_set(x_1463, 1, x_1461);
x_1464 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1465 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1465, 0, x_1463);
lean_ctor_set(x_1465, 1, x_1464);
x_1466 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
x_1467 = l_Array_toList___rarg(x_1466);
lean_dec(x_1466);
x_1468 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1467);
x_1469 = l_Array_HasRepr___rarg___closed__1;
x_1470 = lean_string_append(x_1469, x_1468);
lean_dec(x_1468);
x_1471 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1471, 0, x_1470);
x_1472 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1472, 0, x_1471);
x_1473 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1473, 0, x_1465);
lean_ctor_set(x_1473, 1, x_1472);
x_1474 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1473, x_4, x_1337);
lean_dec(x_6);
return x_1474;
}
else
{
lean_object* x_1475; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; uint8_t x_1506; 
lean_dec(x_90);
lean_dec(x_11);
x_1502 = l_Lean_Elab_Term_getOptions(x_4, x_1337);
x_1503 = lean_ctor_get(x_1502, 0);
lean_inc(x_1503);
x_1504 = lean_ctor_get(x_1502, 1);
lean_inc(x_1504);
lean_dec(x_1502);
x_1505 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1506 = l_Lean_checkTraceOption(x_1503, x_1505);
lean_dec(x_1503);
if (x_1506 == 0)
{
x_1475 = x_1504;
goto block_1501;
}
else
{
lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; 
lean_inc(x_2);
x_1507 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1507, 0, x_2);
x_1508 = l_Lean_Elab_Term_logTrace(x_1505, x_6, x_1507, x_4, x_1504);
x_1509 = lean_ctor_get(x_1508, 1);
lean_inc(x_1509);
lean_dec(x_1508);
x_1475 = x_1509;
goto block_1501;
}
block_1501:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1476; 
lean_dec(x_3);
x_1476 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1475);
lean_dec(x_12);
if (lean_obj_tag(x_1476) == 0)
{
uint8_t x_1477; 
x_1477 = !lean_is_exclusive(x_1476);
if (x_1477 == 0)
{
lean_object* x_1478; 
x_1478 = lean_ctor_get(x_1476, 0);
lean_dec(x_1478);
lean_ctor_set(x_1476, 0, x_2);
return x_1476;
}
else
{
lean_object* x_1479; lean_object* x_1480; 
x_1479 = lean_ctor_get(x_1476, 1);
lean_inc(x_1479);
lean_dec(x_1476);
x_1480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1480, 0, x_2);
lean_ctor_set(x_1480, 1, x_1479);
return x_1480;
}
}
else
{
uint8_t x_1481; 
lean_dec(x_2);
x_1481 = !lean_is_exclusive(x_1476);
if (x_1481 == 0)
{
return x_1476;
}
else
{
lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; 
x_1482 = lean_ctor_get(x_1476, 0);
x_1483 = lean_ctor_get(x_1476, 1);
lean_inc(x_1483);
lean_inc(x_1482);
lean_dec(x_1476);
x_1484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1484, 0, x_1482);
lean_ctor_set(x_1484, 1, x_1483);
return x_1484;
}
}
}
else
{
lean_object* x_1485; lean_object* x_1486; 
x_1485 = lean_ctor_get(x_8, 0);
lean_inc(x_1485);
lean_dec(x_8);
lean_inc(x_4);
x_1486 = l_Lean_Elab_Term_isDefEq(x_6, x_1485, x_3, x_4, x_1475);
if (lean_obj_tag(x_1486) == 0)
{
lean_object* x_1487; lean_object* x_1488; 
x_1487 = lean_ctor_get(x_1486, 1);
lean_inc(x_1487);
lean_dec(x_1486);
x_1488 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1487);
lean_dec(x_12);
if (lean_obj_tag(x_1488) == 0)
{
uint8_t x_1489; 
x_1489 = !lean_is_exclusive(x_1488);
if (x_1489 == 0)
{
lean_object* x_1490; 
x_1490 = lean_ctor_get(x_1488, 0);
lean_dec(x_1490);
lean_ctor_set(x_1488, 0, x_2);
return x_1488;
}
else
{
lean_object* x_1491; lean_object* x_1492; 
x_1491 = lean_ctor_get(x_1488, 1);
lean_inc(x_1491);
lean_dec(x_1488);
x_1492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1492, 0, x_2);
lean_ctor_set(x_1492, 1, x_1491);
return x_1492;
}
}
else
{
uint8_t x_1493; 
lean_dec(x_2);
x_1493 = !lean_is_exclusive(x_1488);
if (x_1493 == 0)
{
return x_1488;
}
else
{
lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; 
x_1494 = lean_ctor_get(x_1488, 0);
x_1495 = lean_ctor_get(x_1488, 1);
lean_inc(x_1495);
lean_inc(x_1494);
lean_dec(x_1488);
x_1496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1496, 0, x_1494);
lean_ctor_set(x_1496, 1, x_1495);
return x_1496;
}
}
}
else
{
uint8_t x_1497; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1497 = !lean_is_exclusive(x_1486);
if (x_1497 == 0)
{
return x_1486;
}
else
{
lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; 
x_1498 = lean_ctor_get(x_1486, 0);
x_1499 = lean_ctor_get(x_1486, 1);
lean_inc(x_1499);
lean_inc(x_1498);
lean_dec(x_1486);
x_1500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1500, 0, x_1498);
lean_ctor_set(x_1500, 1, x_1499);
return x_1500;
}
}
}
}
}
}
}
else
{
lean_object* x_1510; lean_object* x_1511; 
lean_dec(x_1);
lean_dec(x_90);
lean_dec(x_3);
x_1510 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1511 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1510, x_91, x_4, x_1337);
if (lean_obj_tag(x_1511) == 0)
{
lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; uint32_t x_1516; uint16_t x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; 
x_1512 = lean_ctor_get(x_1511, 0);
lean_inc(x_1512);
x_1513 = lean_ctor_get(x_1511, 1);
lean_inc(x_1513);
lean_dec(x_1511);
x_1514 = lean_unsigned_to_nat(1u);
x_1515 = lean_nat_add(x_10, x_1514);
lean_dec(x_10);
x_1516 = 0;
x_1517 = 0;
x_1518 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_1518, 0, x_6);
lean_ctor_set(x_1518, 1, x_7);
lean_ctor_set(x_1518, 2, x_8);
lean_ctor_set(x_1518, 3, x_1515);
lean_ctor_set(x_1518, 4, x_11);
lean_ctor_set(x_1518, 5, x_12);
lean_ctor_set(x_1518, 6, x_13);
lean_ctor_set_uint8(x_1518, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_1518, sizeof(void*)*7 + 7, x_1338);
lean_ctor_set_uint32(x_1518, sizeof(void*)*7, x_1516);
lean_ctor_set_uint16(x_1518, sizeof(void*)*7 + 4, x_1517);
lean_inc(x_1512);
x_1519 = l_Lean_mkApp(x_2, x_1512);
x_1520 = lean_expr_instantiate1(x_92, x_1512);
lean_dec(x_1512);
lean_dec(x_92);
x_1 = x_1518;
x_2 = x_1519;
x_3 = x_1520;
x_5 = x_1513;
goto _start;
}
else
{
uint8_t x_1522; 
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
x_1522 = !lean_is_exclusive(x_1511);
if (x_1522 == 0)
{
return x_1511;
}
else
{
lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; 
x_1523 = lean_ctor_get(x_1511, 0);
x_1524 = lean_ctor_get(x_1511, 1);
lean_inc(x_1524);
lean_inc(x_1523);
lean_dec(x_1511);
x_1525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1525, 0, x_1523);
lean_ctor_set(x_1525, 1, x_1524);
return x_1525;
}
}
}
}
else
{
uint8_t x_1526; 
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
x_1526 = !lean_is_exclusive(x_1328);
if (x_1526 == 0)
{
return x_1328;
}
else
{
lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; 
x_1527 = lean_ctor_get(x_1328, 0);
x_1528 = lean_ctor_get(x_1328, 1);
lean_inc(x_1528);
lean_inc(x_1527);
lean_dec(x_1328);
x_1529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1529, 0, x_1527);
lean_ctor_set(x_1529, 1, x_1528);
return x_1529;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1328) == 0)
{
lean_object* x_1530; uint8_t x_1531; uint32_t x_1532; uint16_t x_1533; lean_object* x_1534; lean_object* x_1535; uint8_t x_1536; 
x_1530 = lean_ctor_get(x_1328, 1);
lean_inc(x_1530);
lean_dec(x_1328);
x_1531 = 1;
x_1532 = 0;
x_1533 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1534 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_1534, 0, x_6);
lean_ctor_set(x_1534, 1, x_7);
lean_ctor_set(x_1534, 2, x_8);
lean_ctor_set(x_1534, 3, x_10);
lean_ctor_set(x_1534, 4, x_11);
lean_ctor_set(x_1534, 5, x_12);
lean_ctor_set(x_1534, 6, x_13);
lean_ctor_set_uint8(x_1534, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_1534, sizeof(void*)*7 + 7, x_1531);
lean_ctor_set_uint32(x_1534, sizeof(void*)*7, x_1532);
lean_ctor_set_uint16(x_1534, sizeof(void*)*7 + 4, x_1533);
x_1535 = lean_array_get_size(x_7);
x_1536 = lean_nat_dec_lt(x_10, x_1535);
lean_dec(x_1535);
if (x_1536 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_1537; 
x_1537 = l_Lean_Expr_getOptParamDefault_x3f(x_91);
if (lean_obj_tag(x_1537) == 0)
{
lean_object* x_1538; 
x_1538 = l_Lean_Expr_getAutoParamTactic_x3f(x_91);
if (lean_obj_tag(x_1538) == 0)
{
uint8_t x_1539; 
lean_dec(x_1534);
lean_dec(x_92);
lean_dec(x_91);
x_1539 = l_Array_isEmpty___rarg(x_11);
if (x_1539 == 0)
{
lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1540 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1540, 0, x_90);
x_1541 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1542 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1542, 0, x_1541);
lean_ctor_set(x_1542, 1, x_1540);
x_1543 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1544 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1544, 0, x_1542);
lean_ctor_set(x_1544, 1, x_1543);
x_1545 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
x_1546 = l_Array_toList___rarg(x_1545);
lean_dec(x_1545);
x_1547 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1546);
x_1548 = l_Array_HasRepr___rarg___closed__1;
x_1549 = lean_string_append(x_1548, x_1547);
lean_dec(x_1547);
x_1550 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1550, 0, x_1549);
x_1551 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1551, 0, x_1550);
x_1552 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1552, 0, x_1544);
lean_ctor_set(x_1552, 1, x_1551);
x_1553 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1552, x_4, x_1530);
lean_dec(x_6);
return x_1553;
}
else
{
lean_object* x_1554; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; uint8_t x_1583; 
lean_dec(x_90);
lean_dec(x_11);
x_1579 = l_Lean_Elab_Term_getOptions(x_4, x_1530);
x_1580 = lean_ctor_get(x_1579, 0);
lean_inc(x_1580);
x_1581 = lean_ctor_get(x_1579, 1);
lean_inc(x_1581);
lean_dec(x_1579);
x_1582 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1583 = l_Lean_checkTraceOption(x_1580, x_1582);
lean_dec(x_1580);
if (x_1583 == 0)
{
x_1554 = x_1581;
goto block_1578;
}
else
{
lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; 
lean_inc(x_2);
x_1584 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1584, 0, x_2);
x_1585 = l_Lean_Elab_Term_logTrace(x_1582, x_6, x_1584, x_4, x_1581);
x_1586 = lean_ctor_get(x_1585, 1);
lean_inc(x_1586);
lean_dec(x_1585);
x_1554 = x_1586;
goto block_1578;
}
block_1578:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1555; 
lean_dec(x_3);
x_1555 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1554);
lean_dec(x_12);
if (lean_obj_tag(x_1555) == 0)
{
lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; 
x_1556 = lean_ctor_get(x_1555, 1);
lean_inc(x_1556);
if (lean_is_exclusive(x_1555)) {
 lean_ctor_release(x_1555, 0);
 lean_ctor_release(x_1555, 1);
 x_1557 = x_1555;
} else {
 lean_dec_ref(x_1555);
 x_1557 = lean_box(0);
}
if (lean_is_scalar(x_1557)) {
 x_1558 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1558 = x_1557;
}
lean_ctor_set(x_1558, 0, x_2);
lean_ctor_set(x_1558, 1, x_1556);
return x_1558;
}
else
{
lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; 
lean_dec(x_2);
x_1559 = lean_ctor_get(x_1555, 0);
lean_inc(x_1559);
x_1560 = lean_ctor_get(x_1555, 1);
lean_inc(x_1560);
if (lean_is_exclusive(x_1555)) {
 lean_ctor_release(x_1555, 0);
 lean_ctor_release(x_1555, 1);
 x_1561 = x_1555;
} else {
 lean_dec_ref(x_1555);
 x_1561 = lean_box(0);
}
if (lean_is_scalar(x_1561)) {
 x_1562 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1562 = x_1561;
}
lean_ctor_set(x_1562, 0, x_1559);
lean_ctor_set(x_1562, 1, x_1560);
return x_1562;
}
}
else
{
lean_object* x_1563; lean_object* x_1564; 
x_1563 = lean_ctor_get(x_8, 0);
lean_inc(x_1563);
lean_dec(x_8);
lean_inc(x_4);
x_1564 = l_Lean_Elab_Term_isDefEq(x_6, x_1563, x_3, x_4, x_1554);
if (lean_obj_tag(x_1564) == 0)
{
lean_object* x_1565; lean_object* x_1566; 
x_1565 = lean_ctor_get(x_1564, 1);
lean_inc(x_1565);
lean_dec(x_1564);
x_1566 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1565);
lean_dec(x_12);
if (lean_obj_tag(x_1566) == 0)
{
lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; 
x_1567 = lean_ctor_get(x_1566, 1);
lean_inc(x_1567);
if (lean_is_exclusive(x_1566)) {
 lean_ctor_release(x_1566, 0);
 lean_ctor_release(x_1566, 1);
 x_1568 = x_1566;
} else {
 lean_dec_ref(x_1566);
 x_1568 = lean_box(0);
}
if (lean_is_scalar(x_1568)) {
 x_1569 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1569 = x_1568;
}
lean_ctor_set(x_1569, 0, x_2);
lean_ctor_set(x_1569, 1, x_1567);
return x_1569;
}
else
{
lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; 
lean_dec(x_2);
x_1570 = lean_ctor_get(x_1566, 0);
lean_inc(x_1570);
x_1571 = lean_ctor_get(x_1566, 1);
lean_inc(x_1571);
if (lean_is_exclusive(x_1566)) {
 lean_ctor_release(x_1566, 0);
 lean_ctor_release(x_1566, 1);
 x_1572 = x_1566;
} else {
 lean_dec_ref(x_1566);
 x_1572 = lean_box(0);
}
if (lean_is_scalar(x_1572)) {
 x_1573 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1573 = x_1572;
}
lean_ctor_set(x_1573, 0, x_1570);
lean_ctor_set(x_1573, 1, x_1571);
return x_1573;
}
}
else
{
lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1574 = lean_ctor_get(x_1564, 0);
lean_inc(x_1574);
x_1575 = lean_ctor_get(x_1564, 1);
lean_inc(x_1575);
if (lean_is_exclusive(x_1564)) {
 lean_ctor_release(x_1564, 0);
 lean_ctor_release(x_1564, 1);
 x_1576 = x_1564;
} else {
 lean_dec_ref(x_1564);
 x_1576 = lean_box(0);
}
if (lean_is_scalar(x_1576)) {
 x_1577 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1577 = x_1576;
}
lean_ctor_set(x_1577, 0, x_1574);
lean_ctor_set(x_1577, 1, x_1575);
return x_1577;
}
}
}
}
}
else
{
lean_object* x_1587; 
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
x_1587 = lean_ctor_get(x_1538, 0);
lean_inc(x_1587);
lean_dec(x_1538);
if (lean_obj_tag(x_1587) == 4)
{
lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; 
x_1588 = lean_ctor_get(x_1587, 0);
lean_inc(x_1588);
lean_dec(x_1587);
x_1589 = l_Lean_Elab_Term_getEnv___rarg(x_1530);
x_1590 = lean_ctor_get(x_1589, 0);
lean_inc(x_1590);
x_1591 = lean_ctor_get(x_1589, 1);
lean_inc(x_1591);
lean_dec(x_1589);
x_1592 = l_Lean_Elab_evalSyntaxConstant(x_1590, x_1588);
if (lean_obj_tag(x_1592) == 0)
{
lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; 
lean_dec(x_1534);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_1593 = lean_ctor_get(x_1592, 0);
lean_inc(x_1593);
lean_dec(x_1592);
x_1594 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1594, 0, x_1593);
x_1595 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1595, 0, x_1594);
x_1596 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1595, x_4, x_1591);
lean_dec(x_6);
return x_1596;
}
else
{
lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; 
x_1597 = lean_ctor_get(x_1592, 0);
lean_inc(x_1597);
lean_dec(x_1592);
x_1598 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_1591);
x_1599 = lean_ctor_get(x_1598, 1);
lean_inc(x_1599);
lean_dec(x_1598);
x_1600 = l_Lean_Elab_Term_getMainModule___rarg(x_1599);
x_1601 = lean_ctor_get(x_1600, 1);
lean_inc(x_1601);
lean_dec(x_1600);
x_1602 = l_Lean_Syntax_getArgs(x_1597);
lean_dec(x_1597);
x_1603 = l_Array_empty___closed__1;
x_1604 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1602, x_1602, x_94, x_1603);
lean_dec(x_1602);
x_1605 = l_Lean_nullKind___closed__2;
x_1606 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1606, 0, x_1605);
lean_ctor_set(x_1606, 1, x_1604);
x_1607 = lean_array_push(x_1603, x_1606);
x_1608 = l_Lean_Parser_Tactic_seq___elambda__1___closed__4;
x_1609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1609, 0, x_1608);
lean_ctor_set(x_1609, 1, x_1607);
x_1610 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1611 = lean_array_push(x_1610, x_1609);
x_1612 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1613 = lean_array_push(x_1611, x_1612);
x_1614 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__2;
x_1615 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1615, 0, x_1614);
lean_ctor_set(x_1615, 1, x_1613);
x_1616 = l_Lean_Syntax_getHeadInfo___main(x_6);
x_1617 = l_Lean_Expr_getAppNumArgsAux___main(x_91, x_94);
x_1618 = lean_nat_sub(x_1617, x_94);
lean_dec(x_1617);
x_1619 = lean_unsigned_to_nat(1u);
x_1620 = lean_nat_sub(x_1618, x_1619);
lean_dec(x_1618);
x_1621 = l_Lean_Expr_getRevArg_x21___main(x_91, x_1620);
lean_dec(x_91);
if (lean_obj_tag(x_1616) == 0)
{
lean_object* x_1622; lean_object* x_1623; 
x_1622 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1622, 0, x_1615);
lean_inc(x_4);
lean_inc(x_2);
x_1623 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1622, x_1621, x_4, x_1601);
if (lean_obj_tag(x_1623) == 0)
{
lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; 
x_1624 = lean_ctor_get(x_1623, 0);
lean_inc(x_1624);
x_1625 = lean_ctor_get(x_1623, 1);
lean_inc(x_1625);
lean_dec(x_1623);
lean_inc(x_1624);
x_1626 = l_Lean_mkApp(x_2, x_1624);
x_1627 = lean_expr_instantiate1(x_92, x_1624);
lean_dec(x_1624);
lean_dec(x_92);
x_1 = x_1534;
x_2 = x_1626;
x_3 = x_1627;
x_5 = x_1625;
goto _start;
}
else
{
lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; 
lean_dec(x_1534);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1629 = lean_ctor_get(x_1623, 0);
lean_inc(x_1629);
x_1630 = lean_ctor_get(x_1623, 1);
lean_inc(x_1630);
if (lean_is_exclusive(x_1623)) {
 lean_ctor_release(x_1623, 0);
 lean_ctor_release(x_1623, 1);
 x_1631 = x_1623;
} else {
 lean_dec_ref(x_1623);
 x_1631 = lean_box(0);
}
if (lean_is_scalar(x_1631)) {
 x_1632 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1632 = x_1631;
}
lean_ctor_set(x_1632, 0, x_1629);
lean_ctor_set(x_1632, 1, x_1630);
return x_1632;
}
}
else
{
lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; 
x_1633 = lean_ctor_get(x_1616, 0);
lean_inc(x_1633);
lean_dec(x_1616);
x_1634 = l_Lean_Syntax_replaceInfo___main(x_1633, x_1615);
x_1635 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1635, 0, x_1634);
lean_inc(x_4);
lean_inc(x_2);
x_1636 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1635, x_1621, x_4, x_1601);
if (lean_obj_tag(x_1636) == 0)
{
lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; 
x_1637 = lean_ctor_get(x_1636, 0);
lean_inc(x_1637);
x_1638 = lean_ctor_get(x_1636, 1);
lean_inc(x_1638);
lean_dec(x_1636);
lean_inc(x_1637);
x_1639 = l_Lean_mkApp(x_2, x_1637);
x_1640 = lean_expr_instantiate1(x_92, x_1637);
lean_dec(x_1637);
lean_dec(x_92);
x_1 = x_1534;
x_2 = x_1639;
x_3 = x_1640;
x_5 = x_1638;
goto _start;
}
else
{
lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; 
lean_dec(x_1534);
lean_dec(x_92);
lean_dec(x_4);
lean_dec(x_2);
x_1642 = lean_ctor_get(x_1636, 0);
lean_inc(x_1642);
x_1643 = lean_ctor_get(x_1636, 1);
lean_inc(x_1643);
if (lean_is_exclusive(x_1636)) {
 lean_ctor_release(x_1636, 0);
 lean_ctor_release(x_1636, 1);
 x_1644 = x_1636;
} else {
 lean_dec_ref(x_1636);
 x_1644 = lean_box(0);
}
if (lean_is_scalar(x_1644)) {
 x_1645 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1645 = x_1644;
}
lean_ctor_set(x_1645, 0, x_1642);
lean_ctor_set(x_1645, 1, x_1643);
return x_1645;
}
}
}
}
else
{
lean_object* x_1646; lean_object* x_1647; 
lean_dec(x_1587);
lean_dec(x_1534);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_2);
x_1646 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1647 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1646, x_4, x_1530);
lean_dec(x_6);
return x_1647;
}
}
}
else
{
lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; 
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_1648 = lean_ctor_get(x_1537, 0);
lean_inc(x_1648);
lean_dec(x_1537);
lean_inc(x_1648);
x_1649 = l_Lean_mkApp(x_2, x_1648);
x_1650 = lean_expr_instantiate1(x_92, x_1648);
lean_dec(x_1648);
lean_dec(x_92);
x_1 = x_1534;
x_2 = x_1649;
x_3 = x_1650;
x_5 = x_1530;
goto _start;
}
}
else
{
uint8_t x_1652; 
lean_dec(x_1534);
lean_dec(x_92);
lean_dec(x_91);
x_1652 = l_Array_isEmpty___rarg(x_11);
if (x_1652 == 0)
{
lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_1653 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1653, 0, x_90);
x_1654 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1655 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1655, 0, x_1654);
lean_ctor_set(x_1655, 1, x_1653);
x_1656 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1657 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1657, 0, x_1655);
lean_ctor_set(x_1657, 1, x_1656);
x_1658 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_94, x_11);
x_1659 = l_Array_toList___rarg(x_1658);
lean_dec(x_1658);
x_1660 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1659);
x_1661 = l_Array_HasRepr___rarg___closed__1;
x_1662 = lean_string_append(x_1661, x_1660);
lean_dec(x_1660);
x_1663 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1663, 0, x_1662);
x_1664 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1664, 0, x_1663);
x_1665 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1665, 0, x_1657);
lean_ctor_set(x_1665, 1, x_1664);
x_1666 = l_Lean_Elab_Term_throwError___rarg(x_6, x_1665, x_4, x_1530);
lean_dec(x_6);
return x_1666;
}
else
{
lean_object* x_1667; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; uint8_t x_1696; 
lean_dec(x_90);
lean_dec(x_11);
x_1692 = l_Lean_Elab_Term_getOptions(x_4, x_1530);
x_1693 = lean_ctor_get(x_1692, 0);
lean_inc(x_1693);
x_1694 = lean_ctor_get(x_1692, 1);
lean_inc(x_1694);
lean_dec(x_1692);
x_1695 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1696 = l_Lean_checkTraceOption(x_1693, x_1695);
lean_dec(x_1693);
if (x_1696 == 0)
{
x_1667 = x_1694;
goto block_1691;
}
else
{
lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; 
lean_inc(x_2);
x_1697 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1697, 0, x_2);
x_1698 = l_Lean_Elab_Term_logTrace(x_1695, x_6, x_1697, x_4, x_1694);
x_1699 = lean_ctor_get(x_1698, 1);
lean_inc(x_1699);
lean_dec(x_1698);
x_1667 = x_1699;
goto block_1691;
}
block_1691:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_1668; 
lean_dec(x_3);
x_1668 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1667);
lean_dec(x_12);
if (lean_obj_tag(x_1668) == 0)
{
lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; 
x_1669 = lean_ctor_get(x_1668, 1);
lean_inc(x_1669);
if (lean_is_exclusive(x_1668)) {
 lean_ctor_release(x_1668, 0);
 lean_ctor_release(x_1668, 1);
 x_1670 = x_1668;
} else {
 lean_dec_ref(x_1668);
 x_1670 = lean_box(0);
}
if (lean_is_scalar(x_1670)) {
 x_1671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1671 = x_1670;
}
lean_ctor_set(x_1671, 0, x_2);
lean_ctor_set(x_1671, 1, x_1669);
return x_1671;
}
else
{
lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; 
lean_dec(x_2);
x_1672 = lean_ctor_get(x_1668, 0);
lean_inc(x_1672);
x_1673 = lean_ctor_get(x_1668, 1);
lean_inc(x_1673);
if (lean_is_exclusive(x_1668)) {
 lean_ctor_release(x_1668, 0);
 lean_ctor_release(x_1668, 1);
 x_1674 = x_1668;
} else {
 lean_dec_ref(x_1668);
 x_1674 = lean_box(0);
}
if (lean_is_scalar(x_1674)) {
 x_1675 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1675 = x_1674;
}
lean_ctor_set(x_1675, 0, x_1672);
lean_ctor_set(x_1675, 1, x_1673);
return x_1675;
}
}
else
{
lean_object* x_1676; lean_object* x_1677; 
x_1676 = lean_ctor_get(x_8, 0);
lean_inc(x_1676);
lean_dec(x_8);
lean_inc(x_4);
x_1677 = l_Lean_Elab_Term_isDefEq(x_6, x_1676, x_3, x_4, x_1667);
if (lean_obj_tag(x_1677) == 0)
{
lean_object* x_1678; lean_object* x_1679; 
x_1678 = lean_ctor_get(x_1677, 1);
lean_inc(x_1678);
lean_dec(x_1677);
x_1679 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_6, x_12, x_94, x_4, x_1678);
lean_dec(x_12);
if (lean_obj_tag(x_1679) == 0)
{
lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; 
x_1680 = lean_ctor_get(x_1679, 1);
lean_inc(x_1680);
if (lean_is_exclusive(x_1679)) {
 lean_ctor_release(x_1679, 0);
 lean_ctor_release(x_1679, 1);
 x_1681 = x_1679;
} else {
 lean_dec_ref(x_1679);
 x_1681 = lean_box(0);
}
if (lean_is_scalar(x_1681)) {
 x_1682 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1682 = x_1681;
}
lean_ctor_set(x_1682, 0, x_2);
lean_ctor_set(x_1682, 1, x_1680);
return x_1682;
}
else
{
lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; 
lean_dec(x_2);
x_1683 = lean_ctor_get(x_1679, 0);
lean_inc(x_1683);
x_1684 = lean_ctor_get(x_1679, 1);
lean_inc(x_1684);
if (lean_is_exclusive(x_1679)) {
 lean_ctor_release(x_1679, 0);
 lean_ctor_release(x_1679, 1);
 x_1685 = x_1679;
} else {
 lean_dec_ref(x_1679);
 x_1685 = lean_box(0);
}
if (lean_is_scalar(x_1685)) {
 x_1686 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1686 = x_1685;
}
lean_ctor_set(x_1686, 0, x_1683);
lean_ctor_set(x_1686, 1, x_1684);
return x_1686;
}
}
else
{
lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1687 = lean_ctor_get(x_1677, 0);
lean_inc(x_1687);
x_1688 = lean_ctor_get(x_1677, 1);
lean_inc(x_1688);
if (lean_is_exclusive(x_1677)) {
 lean_ctor_release(x_1677, 0);
 lean_ctor_release(x_1677, 1);
 x_1689 = x_1677;
} else {
 lean_dec_ref(x_1677);
 x_1689 = lean_box(0);
}
if (lean_is_scalar(x_1689)) {
 x_1690 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1690 = x_1689;
}
lean_ctor_set(x_1690, 0, x_1687);
lean_ctor_set(x_1690, 1, x_1688);
return x_1690;
}
}
}
}
}
}
else
{
lean_object* x_1700; lean_object* x_1701; 
lean_dec(x_1534);
lean_dec(x_90);
lean_dec(x_3);
x_1700 = lean_array_fget(x_7, x_10);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1701 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1700, x_91, x_4, x_1530);
if (lean_obj_tag(x_1701) == 0)
{
lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; uint32_t x_1706; uint16_t x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; 
x_1702 = lean_ctor_get(x_1701, 0);
lean_inc(x_1702);
x_1703 = lean_ctor_get(x_1701, 1);
lean_inc(x_1703);
lean_dec(x_1701);
x_1704 = lean_unsigned_to_nat(1u);
x_1705 = lean_nat_add(x_10, x_1704);
lean_dec(x_10);
x_1706 = 0;
x_1707 = 0;
x_1708 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_1708, 0, x_6);
lean_ctor_set(x_1708, 1, x_7);
lean_ctor_set(x_1708, 2, x_8);
lean_ctor_set(x_1708, 3, x_1705);
lean_ctor_set(x_1708, 4, x_11);
lean_ctor_set(x_1708, 5, x_12);
lean_ctor_set(x_1708, 6, x_13);
lean_ctor_set_uint8(x_1708, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_1708, sizeof(void*)*7 + 7, x_1531);
lean_ctor_set_uint32(x_1708, sizeof(void*)*7, x_1706);
lean_ctor_set_uint16(x_1708, sizeof(void*)*7 + 4, x_1707);
lean_inc(x_1702);
x_1709 = l_Lean_mkApp(x_2, x_1702);
x_1710 = lean_expr_instantiate1(x_92, x_1702);
lean_dec(x_1702);
lean_dec(x_92);
x_1 = x_1708;
x_2 = x_1709;
x_3 = x_1710;
x_5 = x_1703;
goto _start;
}
else
{
lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; 
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
x_1712 = lean_ctor_get(x_1701, 0);
lean_inc(x_1712);
x_1713 = lean_ctor_get(x_1701, 1);
lean_inc(x_1713);
if (lean_is_exclusive(x_1701)) {
 lean_ctor_release(x_1701, 0);
 lean_ctor_release(x_1701, 1);
 x_1714 = x_1701;
} else {
 lean_dec_ref(x_1701);
 x_1714 = lean_box(0);
}
if (lean_is_scalar(x_1714)) {
 x_1715 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1715 = x_1714;
}
lean_ctor_set(x_1715, 0, x_1712);
lean_ctor_set(x_1715, 1, x_1713);
return x_1715;
}
}
}
else
{
lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; 
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
x_1716 = lean_ctor_get(x_1328, 0);
lean_inc(x_1716);
x_1717 = lean_ctor_get(x_1328, 1);
lean_inc(x_1717);
if (lean_is_exclusive(x_1328)) {
 lean_ctor_release(x_1328, 0);
 lean_ctor_release(x_1328, 1);
 x_1718 = x_1328;
} else {
 lean_dec_ref(x_1328);
 x_1718 = lean_box(0);
}
if (lean_is_scalar(x_1718)) {
 x_1719 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1719 = x_1718;
}
lean_ctor_set(x_1719, 0, x_1716);
lean_ctor_set(x_1719, 1, x_1717);
return x_1719;
}
}
}
}
}
else
{
lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; 
lean_dec(x_90);
lean_dec(x_3);
x_1720 = lean_ctor_get(x_95, 0);
lean_inc(x_1720);
lean_dec(x_95);
x_1721 = l_Lean_Elab_Term_NamedArg_inhabited;
x_1722 = lean_array_get(x_1721, x_11, x_1720);
x_1723 = l_Array_eraseIdx___rarg(x_11, x_1720);
lean_dec(x_1720);
x_1724 = lean_ctor_get(x_1722, 1);
lean_inc(x_1724);
lean_dec(x_1722);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_6);
x_1725 = l___private_Init_Lean_Elab_App_2__elabArg(x_6, x_2, x_1724, x_91, x_4, x_17);
if (lean_obj_tag(x_1725) == 0)
{
lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; uint8_t x_1729; 
x_1726 = lean_ctor_get(x_1725, 0);
lean_inc(x_1726);
x_1727 = lean_ctor_get(x_1725, 1);
lean_inc(x_1727);
lean_dec(x_1725);
lean_inc(x_4);
lean_inc(x_1);
x_1728 = l___private_Init_Lean_Elab_App_8__propagateExpectedType(x_1, x_16, x_4, x_1727);
x_1729 = !lean_is_exclusive(x_1);
if (x_1729 == 0)
{
lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; 
x_1730 = lean_ctor_get(x_1, 6);
lean_dec(x_1730);
x_1731 = lean_ctor_get(x_1, 5);
lean_dec(x_1731);
x_1732 = lean_ctor_get(x_1, 4);
lean_dec(x_1732);
x_1733 = lean_ctor_get(x_1, 3);
lean_dec(x_1733);
x_1734 = lean_ctor_get(x_1, 2);
lean_dec(x_1734);
x_1735 = lean_ctor_get(x_1, 1);
lean_dec(x_1735);
x_1736 = lean_ctor_get(x_1, 0);
lean_dec(x_1736);
if (lean_obj_tag(x_1728) == 0)
{
lean_object* x_1737; uint8_t x_1738; uint32_t x_1739; uint16_t x_1740; lean_object* x_1741; lean_object* x_1742; 
x_1737 = lean_ctor_get(x_1728, 1);
lean_inc(x_1737);
lean_dec(x_1728);
x_1738 = 1;
x_1739 = 0;
x_1740 = 0;
lean_ctor_set(x_1, 4, x_1723);
lean_ctor_set_uint8(x_1, sizeof(void*)*7 + 7, x_1738);
lean_ctor_set_uint32(x_1, sizeof(void*)*7, x_1739);
lean_ctor_set_uint16(x_1, sizeof(void*)*7 + 4, x_1740);
lean_inc(x_1726);
x_1741 = l_Lean_mkApp(x_2, x_1726);
x_1742 = lean_expr_instantiate1(x_92, x_1726);
lean_dec(x_1726);
lean_dec(x_92);
x_2 = x_1741;
x_3 = x_1742;
x_5 = x_1737;
goto _start;
}
else
{
uint8_t x_1744; 
lean_free_object(x_1);
lean_dec(x_1726);
lean_dec(x_1723);
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1744 = !lean_is_exclusive(x_1728);
if (x_1744 == 0)
{
return x_1728;
}
else
{
lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; 
x_1745 = lean_ctor_get(x_1728, 0);
x_1746 = lean_ctor_get(x_1728, 1);
lean_inc(x_1746);
lean_inc(x_1745);
lean_dec(x_1728);
x_1747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1747, 0, x_1745);
lean_ctor_set(x_1747, 1, x_1746);
return x_1747;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1728) == 0)
{
lean_object* x_1748; uint8_t x_1749; uint32_t x_1750; uint16_t x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; 
x_1748 = lean_ctor_get(x_1728, 1);
lean_inc(x_1748);
lean_dec(x_1728);
x_1749 = 1;
x_1750 = 0;
x_1751 = 0;
x_1752 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_1752, 0, x_6);
lean_ctor_set(x_1752, 1, x_7);
lean_ctor_set(x_1752, 2, x_8);
lean_ctor_set(x_1752, 3, x_10);
lean_ctor_set(x_1752, 4, x_1723);
lean_ctor_set(x_1752, 5, x_12);
lean_ctor_set(x_1752, 6, x_13);
lean_ctor_set_uint8(x_1752, sizeof(void*)*7 + 6, x_9);
lean_ctor_set_uint8(x_1752, sizeof(void*)*7 + 7, x_1749);
lean_ctor_set_uint32(x_1752, sizeof(void*)*7, x_1750);
lean_ctor_set_uint16(x_1752, sizeof(void*)*7 + 4, x_1751);
lean_inc(x_1726);
x_1753 = l_Lean_mkApp(x_2, x_1726);
x_1754 = lean_expr_instantiate1(x_92, x_1726);
lean_dec(x_1726);
lean_dec(x_92);
x_1 = x_1752;
x_2 = x_1753;
x_3 = x_1754;
x_5 = x_1748;
goto _start;
}
else
{
lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; 
lean_dec(x_1726);
lean_dec(x_1723);
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1756 = lean_ctor_get(x_1728, 0);
lean_inc(x_1756);
x_1757 = lean_ctor_get(x_1728, 1);
lean_inc(x_1757);
if (lean_is_exclusive(x_1728)) {
 lean_ctor_release(x_1728, 0);
 lean_ctor_release(x_1728, 1);
 x_1758 = x_1728;
} else {
 lean_dec_ref(x_1728);
 x_1758 = lean_box(0);
}
if (lean_is_scalar(x_1758)) {
 x_1759 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1759 = x_1758;
}
lean_ctor_set(x_1759, 0, x_1756);
lean_ctor_set(x_1759, 1, x_1757);
return x_1759;
}
}
}
else
{
uint8_t x_1760; 
lean_dec(x_1723);
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
x_1760 = !lean_is_exclusive(x_1725);
if (x_1760 == 0)
{
return x_1725;
}
else
{
lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; 
x_1761 = lean_ctor_get(x_1725, 0);
x_1762 = lean_ctor_get(x_1725, 1);
lean_inc(x_1762);
lean_inc(x_1761);
lean_dec(x_1725);
x_1763 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1763, 0, x_1761);
lean_ctor_set(x_1763, 1, x_1762);
return x_1763;
}
}
}
}
else
{
lean_object* x_1764; 
lean_dec(x_13);
x_1764 = lean_box(0);
x_18 = x_1764;
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
uint8_t x_1765; 
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
x_1765 = !lean_is_exclusive(x_15);
if (x_1765 == 0)
{
return x_15;
}
else
{
lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; 
x_1766 = lean_ctor_get(x_15, 0);
x_1767 = lean_ctor_get(x_15, 1);
lean_inc(x_1767);
lean_inc(x_1766);
lean_dec(x_15);
x_1768 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1768, 0, x_1766);
lean_ctor_set(x_1768, 1, x_1767);
return x_1768;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
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
x_52 = l_Lean_Elab_Term_getOptions(x_7, x_14);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__2;
x_56 = l_Lean_checkTraceOption(x_53, x_55);
lean_dec(x_53);
if (x_56 == 0)
{
x_15 = x_54;
goto block_51;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_inc(x_2);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_2);
lean_inc(x_13);
x_58 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_58, 0, x_13);
if (x_6 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__8;
x_60 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
x_61 = l___private_Init_Lean_Meta_ExprDefEq_7__checkTypesAndAssign___closed__7;
x_62 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
x_64 = l_Lean_Elab_Term_logTrace(x_55, x_1, x_63, x_7, x_54);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_15 = x_65;
goto block_51;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = l___private_Init_Lean_Elab_App_11__elabAppArgs___closed__11;
x_67 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_57);
x_68 = l___private_Init_Lean_Meta_ExprDefEq_7__checkTypesAndAssign___closed__7;
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_58);
x_71 = l_Lean_Elab_Term_logTrace(x_55, x_1, x_70, x_7, x_54);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_15 = x_72;
goto block_51;
}
}
block_51:
{
uint8_t x_16; 
x_16 = l_Array_isEmpty___rarg(x_3);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Term_tryPostponeIfMVar(x_13, x_7, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint32_t x_22; uint16_t x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_empty___closed__1;
x_21 = 0;
x_22 = 0;
x_23 = 0;
x_24 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_5);
lean_ctor_set(x_24, 3, x_19);
lean_ctor_set(x_24, 4, x_3);
lean_ctor_set(x_24, 5, x_20);
lean_ctor_set(x_24, 6, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*7 + 6, x_6);
lean_ctor_set_uint8(x_24, sizeof(void*)*7 + 7, x_21);
lean_ctor_set_uint32(x_24, sizeof(void*)*7, x_22);
lean_ctor_set_uint16(x_24, sizeof(void*)*7 + 4, x_23);
x_25 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main(x_24, x_2, x_13, x_7, x_18);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
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
x_30 = l_Array_isEmpty___rarg(x_4);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_Elab_Term_tryPostponeIfMVar(x_13, x_7, x_15);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint32_t x_36; uint16_t x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Array_empty___closed__1;
x_35 = 0;
x_36 = 0;
x_37 = 0;
x_38 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_4);
lean_ctor_set(x_38, 2, x_5);
lean_ctor_set(x_38, 3, x_33);
lean_ctor_set(x_38, 4, x_3);
lean_ctor_set(x_38, 5, x_34);
lean_ctor_set(x_38, 6, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 6, x_6);
lean_ctor_set_uint8(x_38, sizeof(void*)*7 + 7, x_35);
lean_ctor_set_uint32(x_38, sizeof(void*)*7, x_36);
lean_ctor_set_uint16(x_38, sizeof(void*)*7 + 4, x_37);
x_39 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main(x_38, x_2, x_13, x_7, x_32);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_31);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint32_t x_47; uint16_t x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_empty___closed__1;
x_46 = 0;
x_47 = 0;
x_48 = 0;
x_49 = lean_alloc_ctor(0, 7, 8);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_4);
lean_ctor_set(x_49, 2, x_5);
lean_ctor_set(x_49, 3, x_44);
lean_ctor_set(x_49, 4, x_3);
lean_ctor_set(x_49, 5, x_45);
lean_ctor_set(x_49, 6, x_45);
lean_ctor_set_uint8(x_49, sizeof(void*)*7 + 6, x_6);
lean_ctor_set_uint8(x_49, sizeof(void*)*7 + 7, x_46);
lean_ctor_set_uint32(x_49, sizeof(void*)*7, x_47);
lean_ctor_set_uint16(x_49, sizeof(void*)*7 + 4, x_48);
x_50 = l___private_Init_Lean_Elab_App_10__elabAppArgsAux___main(x_49, x_2, x_13, x_7, x_15);
return x_50;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_9);
if (x_73 == 0)
{
return x_9;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_9, 0);
x_75 = lean_ctor_get(x_9, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_9);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
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
uint8_t x_15; uint8_t x_292; lean_object* x_405; uint8_t x_406; 
x_405 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
lean_inc(x_2);
x_406 = l_Lean_Syntax_isOfKind(x_2, x_405);
if (x_406 == 0)
{
uint8_t x_407; 
x_407 = 0;
x_292 = x_407;
goto block_404;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_411; 
x_408 = l_Lean_Syntax_getArgs(x_2);
x_409 = lean_array_get_size(x_408);
lean_dec(x_408);
x_410 = lean_unsigned_to_nat(3u);
x_411 = lean_nat_dec_eq(x_409, x_410);
lean_dec(x_409);
x_292 = x_411;
goto block_404;
}
block_291:
{
uint8_t x_16; 
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_173; lean_object* x_277; uint8_t x_278; 
x_277 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_2);
x_278 = l_Lean_Syntax_isOfKind(x_2, x_277);
if (x_278 == 0)
{
uint8_t x_279; 
x_279 = 0;
x_173 = x_279;
goto block_276;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_280 = l_Lean_Syntax_getArgs(x_2);
x_281 = lean_array_get_size(x_280);
lean_dec(x_280);
x_282 = lean_unsigned_to_nat(2u);
x_283 = lean_nat_dec_eq(x_281, x_282);
lean_dec(x_281);
x_173 = x_283;
goto block_276;
}
block_172:
{
uint8_t x_18; 
x_18 = l_coeDecidableEq(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_box(0);
x_20 = 1;
lean_inc(x_10);
lean_inc(x_9);
x_21 = l_Lean_Elab_Term_elabTerm(x_2, x_19, x_20, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_9, x_24);
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
x_52 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_50, x_3, x_4, x_5, x_6, x_7, x_9, x_51);
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
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; 
x_92 = lean_unsigned_to_nat(1u);
x_93 = l_Lean_Syntax_getArg(x_2, x_92);
x_94 = l_Lean_mkTermIdFromIdent___closed__2;
lean_inc(x_93);
x_95 = l_Lean_Syntax_isOfKind(x_93, x_94);
x_96 = l_coeDecidableEq(x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; lean_object* x_99; 
lean_dec(x_93);
x_97 = lean_box(0);
x_98 = 1;
lean_inc(x_10);
lean_inc(x_9);
x_99 = l_Lean_Elab_Term_elabTerm(x_2, x_97, x_98, x_9, x_10);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
x_103 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_101, x_3, x_4, x_5, x_6, x_7, x_9, x_102);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_array_push(x_8, x_103);
lean_ctor_set(x_99, 1, x_10);
lean_ctor_set(x_99, 0, x_105);
return x_99;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_103, 0);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_103);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_array_push(x_8, x_108);
lean_ctor_set(x_99, 1, x_10);
lean_ctor_set(x_99, 0, x_109);
return x_99;
}
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
lean_dec(x_110);
x_112 = !lean_is_exclusive(x_103);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_103, 0);
lean_dec(x_113);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
lean_dec(x_111);
lean_ctor_set(x_103, 0, x_114);
x_115 = lean_array_push(x_8, x_103);
lean_ctor_set(x_99, 1, x_10);
lean_ctor_set(x_99, 0, x_115);
return x_99;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_103, 1);
lean_inc(x_116);
lean_dec(x_103);
x_117 = lean_ctor_get(x_111, 0);
lean_inc(x_117);
lean_dec(x_111);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_array_push(x_8, x_118);
lean_ctor_set(x_99, 1, x_10);
lean_ctor_set(x_99, 0, x_119);
return x_99;
}
}
else
{
uint8_t x_120; 
lean_free_object(x_99);
lean_dec(x_10);
lean_dec(x_8);
x_120 = !lean_is_exclusive(x_103);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_103, 0);
lean_dec(x_121);
return x_103;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_103, 1);
lean_inc(x_122);
lean_dec(x_103);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_110);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_free_object(x_99);
lean_dec(x_8);
x_124 = !lean_is_exclusive(x_103);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_103, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_103, 0);
lean_dec(x_126);
lean_ctor_set(x_103, 1, x_10);
return x_103;
}
else
{
lean_object* x_127; 
lean_dec(x_103);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_110);
lean_ctor_set(x_127, 1, x_10);
return x_127;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_99, 0);
x_129 = lean_ctor_get(x_99, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_99);
x_130 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_128, x_3, x_4, x_5, x_6, x_7, x_9, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
x_135 = lean_array_push(x_8, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_10);
return x_136;
}
else
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_130, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_137);
x_139 = lean_ctor_get(x_130, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_140 = x_130;
} else {
 lean_dec_ref(x_130);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_138, 0);
lean_inc(x_141);
lean_dec(x_138);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_139);
x_143 = lean_array_push(x_8, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_10);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_10);
lean_dec(x_8);
x_145 = lean_ctor_get(x_130, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_146 = x_130;
} else {
 lean_dec_ref(x_130);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_137);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_8);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_148 = x_130;
} else {
 lean_dec_ref(x_130);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_137);
lean_ctor_set(x_149, 1, x_10);
return x_149;
}
}
}
}
else
{
lean_object* x_150; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_150 = lean_ctor_get(x_99, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
uint8_t x_152; 
lean_dec(x_150);
x_152 = !lean_is_exclusive(x_99);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_99, 0);
lean_dec(x_153);
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
lean_dec(x_151);
lean_ctor_set(x_99, 0, x_154);
x_155 = lean_array_push(x_8, x_99);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_10);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_99, 1);
lean_inc(x_157);
lean_dec(x_99);
x_158 = lean_ctor_get(x_151, 0);
lean_inc(x_158);
lean_dec(x_151);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
x_160 = lean_array_push(x_8, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_10);
return x_161;
}
}
else
{
uint8_t x_162; 
lean_dec(x_10);
lean_dec(x_8);
x_162 = !lean_is_exclusive(x_99);
if (x_162 == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_99, 0);
lean_dec(x_163);
return x_99;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_99, 1);
lean_inc(x_164);
lean_dec(x_99);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_150);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_8);
x_166 = !lean_is_exclusive(x_99);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_99, 1);
lean_dec(x_167);
x_168 = lean_ctor_get(x_99, 0);
lean_dec(x_168);
lean_ctor_set(x_99, 1, x_10);
return x_99;
}
else
{
lean_object* x_169; 
lean_dec(x_99);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_150);
lean_ctor_set(x_169, 1, x_10);
return x_169;
}
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_2);
x_170 = 1;
x_2 = x_93;
x_7 = x_170;
goto _start;
}
}
}
block_276:
{
uint8_t x_174; 
x_174 = l_coeDecidableEq(x_173);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_inc(x_2);
x_176 = l_Lean_Syntax_isOfKind(x_2, x_175);
if (x_176 == 0)
{
uint8_t x_177; 
x_177 = 0;
x_17 = x_177;
goto block_172;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_178 = l_Lean_Syntax_getArgs(x_2);
x_179 = lean_array_get_size(x_178);
lean_dec(x_178);
x_180 = lean_unsigned_to_nat(2u);
x_181 = lean_nat_dec_eq(x_179, x_180);
lean_dec(x_179);
x_17 = x_181;
goto block_172;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_186; 
x_182 = lean_unsigned_to_nat(0u);
x_183 = l_Lean_Syntax_getArg(x_2, x_182);
x_184 = l_Lean_identKind___closed__2;
lean_inc(x_183);
x_185 = l_Lean_Syntax_isOfKind(x_183, x_184);
x_186 = l_coeDecidableEq(x_185);
if (x_186 == 0)
{
lean_object* x_187; uint8_t x_188; lean_object* x_189; 
lean_dec(x_183);
x_187 = lean_box(0);
x_188 = 1;
lean_inc(x_10);
lean_inc(x_9);
x_189 = l_Lean_Elab_Term_elabTerm(x_2, x_187, x_188, x_9, x_10);
if (lean_obj_tag(x_189) == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_189, 0);
x_192 = lean_ctor_get(x_189, 1);
x_193 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_191, x_3, x_4, x_5, x_6, x_7, x_9, x_192);
if (lean_obj_tag(x_193) == 0)
{
uint8_t x_194; 
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; 
x_195 = lean_array_push(x_8, x_193);
lean_ctor_set(x_189, 1, x_10);
lean_ctor_set(x_189, 0, x_195);
return x_189;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_193, 0);
x_197 = lean_ctor_get(x_193, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_193);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_array_push(x_8, x_198);
lean_ctor_set(x_189, 1, x_10);
lean_ctor_set(x_189, 0, x_199);
return x_189;
}
}
else
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_193, 0);
lean_inc(x_200);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
if (lean_obj_tag(x_201) == 0)
{
uint8_t x_202; 
lean_dec(x_200);
x_202 = !lean_is_exclusive(x_193);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_193, 0);
lean_dec(x_203);
x_204 = lean_ctor_get(x_201, 0);
lean_inc(x_204);
lean_dec(x_201);
lean_ctor_set(x_193, 0, x_204);
x_205 = lean_array_push(x_8, x_193);
lean_ctor_set(x_189, 1, x_10);
lean_ctor_set(x_189, 0, x_205);
return x_189;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_193, 1);
lean_inc(x_206);
lean_dec(x_193);
x_207 = lean_ctor_get(x_201, 0);
lean_inc(x_207);
lean_dec(x_201);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
x_209 = lean_array_push(x_8, x_208);
lean_ctor_set(x_189, 1, x_10);
lean_ctor_set(x_189, 0, x_209);
return x_189;
}
}
else
{
uint8_t x_210; 
lean_free_object(x_189);
lean_dec(x_10);
lean_dec(x_8);
x_210 = !lean_is_exclusive(x_193);
if (x_210 == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_193, 0);
lean_dec(x_211);
return x_193;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_193, 1);
lean_inc(x_212);
lean_dec(x_193);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_200);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_free_object(x_189);
lean_dec(x_8);
x_214 = !lean_is_exclusive(x_193);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_193, 1);
lean_dec(x_215);
x_216 = lean_ctor_get(x_193, 0);
lean_dec(x_216);
lean_ctor_set(x_193, 1, x_10);
return x_193;
}
else
{
lean_object* x_217; 
lean_dec(x_193);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_200);
lean_ctor_set(x_217, 1, x_10);
return x_217;
}
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_189, 0);
x_219 = lean_ctor_get(x_189, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_189);
x_220 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_218, x_3, x_4, x_5, x_6, x_7, x_9, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
x_225 = lean_array_push(x_8, x_224);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_10);
return x_226;
}
else
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_220, 0);
lean_inc(x_227);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_227);
x_229 = lean_ctor_get(x_220, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_230 = x_220;
} else {
 lean_dec_ref(x_220);
 x_230 = lean_box(0);
}
x_231 = lean_ctor_get(x_228, 0);
lean_inc(x_231);
lean_dec(x_228);
if (lean_is_scalar(x_230)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_230;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_229);
x_233 = lean_array_push(x_8, x_232);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_10);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_10);
lean_dec(x_8);
x_235 = lean_ctor_get(x_220, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_236 = x_220;
} else {
 lean_dec_ref(x_220);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_227);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_8);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_238 = x_220;
} else {
 lean_dec_ref(x_220);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_227);
lean_ctor_set(x_239, 1, x_10);
return x_239;
}
}
}
}
else
{
lean_object* x_240; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_240 = lean_ctor_get(x_189, 0);
lean_inc(x_240);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
if (lean_obj_tag(x_241) == 0)
{
uint8_t x_242; 
lean_dec(x_240);
x_242 = !lean_is_exclusive(x_189);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_243 = lean_ctor_get(x_189, 0);
lean_dec(x_243);
x_244 = lean_ctor_get(x_241, 0);
lean_inc(x_244);
lean_dec(x_241);
lean_ctor_set(x_189, 0, x_244);
x_245 = lean_array_push(x_8, x_189);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_10);
return x_246;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = lean_ctor_get(x_189, 1);
lean_inc(x_247);
lean_dec(x_189);
x_248 = lean_ctor_get(x_241, 0);
lean_inc(x_248);
lean_dec(x_241);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = lean_array_push(x_8, x_249);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_10);
return x_251;
}
}
else
{
uint8_t x_252; 
lean_dec(x_10);
lean_dec(x_8);
x_252 = !lean_is_exclusive(x_189);
if (x_252 == 0)
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_189, 0);
lean_dec(x_253);
return x_189;
}
else
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_189, 1);
lean_inc(x_254);
lean_dec(x_189);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_240);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_8);
x_256 = !lean_is_exclusive(x_189);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_189, 1);
lean_dec(x_257);
x_258 = lean_ctor_get(x_189, 0);
lean_dec(x_258);
lean_ctor_set(x_189, 1, x_10);
return x_189;
}
else
{
lean_object* x_259; 
lean_dec(x_189);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_240);
lean_ctor_set(x_259, 1, x_10);
return x_259;
}
}
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_260 = lean_unsigned_to_nat(1u);
x_261 = l_Lean_Syntax_getArg(x_2, x_260);
lean_dec(x_2);
x_262 = l_Lean_Syntax_getArgs(x_261);
lean_dec(x_261);
x_263 = l_Array_isEmpty___rarg(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = l_Lean_Syntax_inhabited;
x_265 = lean_array_get(x_264, x_262, x_182);
lean_dec(x_262);
x_266 = l_Lean_Elab_Term_elabExplicitUniv(x_265, x_9, x_10);
lean_dec(x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = l___private_Init_Lean_Elab_App_20__elabAppFnId(x_1, x_183, x_267, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_268);
return x_269;
}
else
{
uint8_t x_270; 
lean_dec(x_183);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_270 = !lean_is_exclusive(x_266);
if (x_270 == 0)
{
return x_266;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_266, 0);
x_272 = lean_ctor_get(x_266, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_266);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
}
else
{
lean_object* x_274; lean_object* x_275; 
lean_dec(x_262);
x_274 = lean_box(0);
x_275 = l___private_Init_Lean_Elab_App_20__elabAppFnId(x_1, x_183, x_274, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_275;
}
}
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_284 = lean_unsigned_to_nat(0u);
x_285 = l_Lean_Syntax_getArg(x_2, x_284);
x_286 = lean_unsigned_to_nat(2u);
x_287 = l_Lean_Syntax_getArg(x_2, x_286);
lean_dec(x_2);
x_288 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_288, 0, x_287);
x_289 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_3);
x_2 = x_285;
x_3 = x_289;
goto _start;
}
}
block_404:
{
uint8_t x_293; 
x_293 = l_coeDecidableEq(x_292);
if (x_293 == 0)
{
lean_object* x_294; uint8_t x_295; 
x_294 = l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
lean_inc(x_2);
x_295 = l_Lean_Syntax_isOfKind(x_2, x_294);
if (x_295 == 0)
{
uint8_t x_296; 
x_296 = 0;
x_15 = x_296;
goto block_291;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_297 = l_Lean_Syntax_getArgs(x_2);
x_298 = lean_array_get_size(x_297);
lean_dec(x_297);
x_299 = lean_unsigned_to_nat(4u);
x_300 = lean_nat_dec_eq(x_298, x_299);
lean_dec(x_298);
x_15 = x_300;
goto block_291;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; uint8_t x_305; 
x_301 = lean_unsigned_to_nat(2u);
x_302 = l_Lean_Syntax_getArg(x_2, x_301);
x_303 = l_Lean_fieldIdxKind___closed__2;
lean_inc(x_302);
x_304 = l_Lean_Syntax_isOfKind(x_302, x_303);
x_305 = l_coeDecidableEq(x_304);
if (x_305 == 0)
{
lean_object* x_306; uint8_t x_307; uint8_t x_308; 
x_306 = l_Lean_identKind___closed__2;
lean_inc(x_302);
x_307 = l_Lean_Syntax_isOfKind(x_302, x_306);
x_308 = l_coeDecidableEq(x_307);
if (x_308 == 0)
{
lean_object* x_309; uint8_t x_310; lean_object* x_311; 
lean_dec(x_302);
x_309 = lean_box(0);
x_310 = 1;
lean_inc(x_10);
lean_inc(x_9);
x_311 = l_Lean_Elab_Term_elabTerm(x_2, x_309, x_310, x_9, x_10);
if (lean_obj_tag(x_311) == 0)
{
uint8_t x_312; 
x_312 = !lean_is_exclusive(x_311);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_311, 0);
x_314 = lean_ctor_get(x_311, 1);
x_315 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_313, x_3, x_4, x_5, x_6, x_7, x_9, x_314);
if (lean_obj_tag(x_315) == 0)
{
uint8_t x_316; 
x_316 = !lean_is_exclusive(x_315);
if (x_316 == 0)
{
lean_object* x_317; 
x_317 = lean_array_push(x_8, x_315);
lean_ctor_set(x_311, 1, x_10);
lean_ctor_set(x_311, 0, x_317);
return x_311;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_318 = lean_ctor_get(x_315, 0);
x_319 = lean_ctor_get(x_315, 1);
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_315);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
x_321 = lean_array_push(x_8, x_320);
lean_ctor_set(x_311, 1, x_10);
lean_ctor_set(x_311, 0, x_321);
return x_311;
}
}
else
{
lean_object* x_322; 
x_322 = lean_ctor_get(x_315, 0);
lean_inc(x_322);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
if (lean_obj_tag(x_323) == 0)
{
uint8_t x_324; 
lean_dec(x_322);
x_324 = !lean_is_exclusive(x_315);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_315, 0);
lean_dec(x_325);
x_326 = lean_ctor_get(x_323, 0);
lean_inc(x_326);
lean_dec(x_323);
lean_ctor_set(x_315, 0, x_326);
x_327 = lean_array_push(x_8, x_315);
lean_ctor_set(x_311, 1, x_10);
lean_ctor_set(x_311, 0, x_327);
return x_311;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_328 = lean_ctor_get(x_315, 1);
lean_inc(x_328);
lean_dec(x_315);
x_329 = lean_ctor_get(x_323, 0);
lean_inc(x_329);
lean_dec(x_323);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_328);
x_331 = lean_array_push(x_8, x_330);
lean_ctor_set(x_311, 1, x_10);
lean_ctor_set(x_311, 0, x_331);
return x_311;
}
}
else
{
uint8_t x_332; 
lean_free_object(x_311);
lean_dec(x_10);
lean_dec(x_8);
x_332 = !lean_is_exclusive(x_315);
if (x_332 == 0)
{
lean_object* x_333; 
x_333 = lean_ctor_get(x_315, 0);
lean_dec(x_333);
return x_315;
}
else
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_315, 1);
lean_inc(x_334);
lean_dec(x_315);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_322);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
}
else
{
uint8_t x_336; 
lean_free_object(x_311);
lean_dec(x_8);
x_336 = !lean_is_exclusive(x_315);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_315, 1);
lean_dec(x_337);
x_338 = lean_ctor_get(x_315, 0);
lean_dec(x_338);
lean_ctor_set(x_315, 1, x_10);
return x_315;
}
else
{
lean_object* x_339; 
lean_dec(x_315);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_322);
lean_ctor_set(x_339, 1, x_10);
return x_339;
}
}
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_311, 0);
x_341 = lean_ctor_get(x_311, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_311);
x_342 = l___private_Init_Lean_Elab_App_19__elabAppLVals(x_1, x_340, x_3, x_4, x_5, x_6, x_7, x_9, x_341);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_345 = x_342;
} else {
 lean_dec_ref(x_342);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_344);
x_347 = lean_array_push(x_8, x_346);
x_348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_10);
return x_348;
}
else
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_342, 0);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_349);
x_351 = lean_ctor_get(x_342, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_352 = x_342;
} else {
 lean_dec_ref(x_342);
 x_352 = lean_box(0);
}
x_353 = lean_ctor_get(x_350, 0);
lean_inc(x_353);
lean_dec(x_350);
if (lean_is_scalar(x_352)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_352;
}
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_351);
x_355 = lean_array_push(x_8, x_354);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_10);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_10);
lean_dec(x_8);
x_357 = lean_ctor_get(x_342, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_358 = x_342;
} else {
 lean_dec_ref(x_342);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_349);
lean_ctor_set(x_359, 1, x_357);
return x_359;
}
}
else
{
lean_object* x_360; lean_object* x_361; 
lean_dec(x_8);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_360 = x_342;
} else {
 lean_dec_ref(x_342);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_349);
lean_ctor_set(x_361, 1, x_10);
return x_361;
}
}
}
}
else
{
lean_object* x_362; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_362 = lean_ctor_get(x_311, 0);
lean_inc(x_362);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
if (lean_obj_tag(x_363) == 0)
{
uint8_t x_364; 
lean_dec(x_362);
x_364 = !lean_is_exclusive(x_311);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = lean_ctor_get(x_311, 0);
lean_dec(x_365);
x_366 = lean_ctor_get(x_363, 0);
lean_inc(x_366);
lean_dec(x_363);
lean_ctor_set(x_311, 0, x_366);
x_367 = lean_array_push(x_8, x_311);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_10);
return x_368;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_369 = lean_ctor_get(x_311, 1);
lean_inc(x_369);
lean_dec(x_311);
x_370 = lean_ctor_get(x_363, 0);
lean_inc(x_370);
lean_dec(x_363);
x_371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_369);
x_372 = lean_array_push(x_8, x_371);
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_10);
return x_373;
}
}
else
{
uint8_t x_374; 
lean_dec(x_10);
lean_dec(x_8);
x_374 = !lean_is_exclusive(x_311);
if (x_374 == 0)
{
lean_object* x_375; 
x_375 = lean_ctor_get(x_311, 0);
lean_dec(x_375);
return x_311;
}
else
{
lean_object* x_376; lean_object* x_377; 
x_376 = lean_ctor_get(x_311, 1);
lean_inc(x_376);
lean_dec(x_311);
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_362);
lean_ctor_set(x_377, 1, x_376);
return x_377;
}
}
}
else
{
uint8_t x_378; 
lean_dec(x_8);
x_378 = !lean_is_exclusive(x_311);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_311, 1);
lean_dec(x_379);
x_380 = lean_ctor_get(x_311, 0);
lean_dec(x_380);
lean_ctor_set(x_311, 1, x_10);
return x_311;
}
else
{
lean_object* x_381; 
lean_dec(x_311);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_362);
lean_ctor_set(x_381, 1, x_10);
return x_381;
}
}
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_382 = l_Lean_Syntax_getId(x_302);
lean_dec(x_302);
x_383 = l_Lean_Name_eraseMacroScopes(x_382);
lean_dec(x_382);
x_384 = l_Lean_Name_components(x_383);
x_385 = l_List_map___main___at___private_Init_Lean_Elab_App_21__elabAppFn___main___spec__1(x_384);
x_386 = lean_unsigned_to_nat(0u);
x_387 = l_Lean_Syntax_getArg(x_2, x_386);
lean_dec(x_2);
x_388 = l_List_append___rarg(x_385, x_3);
x_2 = x_387;
x_3 = x_388;
goto _start;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_390 = l_Lean_fieldIdxKind;
x_391 = l_Lean_Syntax_isNatLitAux(x_390, x_302);
lean_dec(x_302);
x_392 = lean_unsigned_to_nat(0u);
x_393 = l_Lean_Syntax_getArg(x_2, x_392);
lean_dec(x_2);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_394 = l_Nat_Inhabited;
x_395 = l_Option_get_x21___rarg___closed__3;
x_396 = lean_panic_fn(x_394, x_395);
x_397 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_397, 0, x_396);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_3);
x_2 = x_393;
x_3 = x_398;
goto _start;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_391, 0);
lean_inc(x_400);
lean_dec(x_391);
x_401 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_401, 0, x_400);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_3);
x_2 = x_393;
x_3 = x_402;
goto _start;
}
}
}
}
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = l_Lean_Syntax_getArgs(x_2);
x_413 = lean_unsigned_to_nat(0u);
x_414 = l_Array_iterateMAux___main___at___private_Init_Lean_Elab_App_21__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_412, x_413, x_8, x_9, x_10);
lean_dec(x_412);
lean_dec(x_2);
return x_414;
}
}
else
{
lean_object* x_415; lean_object* x_416; 
x_415 = lean_box(0);
x_416 = l___private_Init_Lean_Elab_App_20__elabAppFnId(x_1, x_2, x_415, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_416;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = l_Array_empty___closed__1;
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_3, x_2);
x_12 = lean_box(0);
x_13 = x_12;
x_14 = lean_array_fset(x_3, x_2, x_13);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__1;
x_16 = l_unreachable_x21___rarg(x_15);
lean_inc(x_4);
x_17 = lean_apply_2(x_16, x_4, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = x_18;
lean_dec(x_11);
x_23 = lean_array_fset(x_14, x_2, x_22);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_23;
x_5 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_11, 0);
lean_inc(x_29);
x_30 = l___private_Init_Lean_Elab_App_23__toMessageData(x_29, x_1, x_4, x_5);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_2, x_33);
x_35 = x_31;
lean_dec(x_11);
x_36 = lean_array_fset(x_14, x_2, x_35);
lean_dec(x_2);
x_2 = x_34;
x_3 = x_36;
x_5 = x_32;
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
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_24__mergeFailures___spec__1(x_2, x_5, x_1, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_MessageData_ofArray(x_7);
lean_dec(x_7);
x_10 = l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___closed__3;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Elab_Term_throwError___rarg(x_2, x_11, x_3, x_8);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_App_24__mergeFailures(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___boxed), 4, 0);
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
lean_object* l___private_Init_Lean_Elab_App_24__mergeFailures___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_App_24__mergeFailures___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_4, x_3);
x_10 = lean_box(0);
x_11 = x_10;
x_12 = lean_array_fset(x_4, x_3, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_2);
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_1);
lean_ctor_set(x_20, 3, x_2);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_17);
x_22 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = x_22;
lean_dec(x_9);
x_24 = lean_array_fset(x_12, x_3, x_23);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_Lean_MessageData_Inhabited;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = x_27;
lean_dec(x_9);
x_29 = lean_array_fset(x_12, x_3, x_28);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_29;
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
lean_dec(x_2);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
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
x_29 = l_Array_umapMAux___main___at___private_Init_Lean_Elab_App_25__elabAppAux___spec__1(x_24, x_27, x_17, x_18);
x_30 = l_Lean_MessageData_ofArray(x_29);
lean_dec(x_29);
x_31 = l___private_Init_Lean_Elab_App_25__elabAppAux___closed__3;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Elab_Term_throwError___rarg(x_2, x_32, x_6, x_28);
lean_dec(x_2);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_2);
x_34 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_35 = lean_array_get(x_34, x_18, x_17);
lean_dec(x_18);
x_36 = l_Lean_Elab_Term_applyResult(x_35, x_6, x_13);
lean_dec(x_13);
lean_dec(x_6);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
x_37 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_array_get(x_37, x_12, x_38);
lean_dec(x_12);
x_40 = l_Lean_Elab_Term_applyResult(x_39, x_6, x_13);
lean_dec(x_13);
lean_dec(x_6);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_6);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
return x_11;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_11, 0);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabApp");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabApp), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabApp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_mkAppStx___closed__8;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabId");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabId), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_mkTermIdFromIdent___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_114; uint8_t x_115; 
x_114 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_inc(x_1);
x_115 = l_Lean_Syntax_isOfKind(x_1, x_114);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = 0;
x_5 = x_116;
goto block_113;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_117 = l_Lean_Syntax_getArgs(x_1);
x_118 = lean_array_get_size(x_117);
lean_dec(x_117);
x_119 = lean_unsigned_to_nat(2u);
x_120 = lean_nat_dec_eq(x_118, x_119);
lean_dec(x_118);
x_5 = x_120;
goto block_113;
}
block_113:
{
uint8_t x_6; 
x_6 = l_coeDecidableEq(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_101; uint8_t x_102; uint8_t x_103; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_101 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_9);
x_102 = l_Lean_Syntax_isOfKind(x_9, x_101);
x_103 = l_coeDecidableEq(x_102);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = l_Lean_Parser_Term_paren___elambda__1___closed__1;
lean_inc(x_9);
x_105 = l_Lean_Syntax_isOfKind(x_9, x_104);
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = 0;
x_10 = x_106;
goto block_100;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = l_Lean_Syntax_getArgs(x_9);
x_108 = lean_array_get_size(x_107);
lean_dec(x_107);
x_109 = lean_unsigned_to_nat(3u);
x_110 = lean_nat_dec_eq(x_108, x_109);
lean_dec(x_108);
x_10 = x_110;
goto block_100;
}
}
else
{
uint8_t x_111; lean_object* x_112; 
lean_dec(x_1);
x_111 = 1;
x_112 = l_Lean_Elab_Term_elabFunCore(x_9, x_2, x_111, x_3, x_4);
return x_112;
}
block_100:
{
uint8_t x_11; 
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_12 = l_Lean_mkTermIdFromIdent___closed__2;
x_13 = l_Lean_Syntax_isOfKind(x_9, x_12);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_93; uint8_t x_94; 
x_17 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_93 = l_Lean_nullKind___closed__2;
lean_inc(x_17);
x_94 = l_Lean_Syntax_isOfKind(x_17, x_93);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = 0;
x_18 = x_95;
goto block_92;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = l_Lean_Syntax_getArgs(x_17);
x_97 = lean_array_get_size(x_96);
lean_dec(x_96);
x_98 = lean_unsigned_to_nat(2u);
x_99 = lean_nat_dec_eq(x_97, x_98);
lean_dec(x_97);
x_18 = x_99;
goto block_92;
}
block_92:
{
uint8_t x_19; 
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_17, x_21);
x_23 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_22);
x_24 = l_Lean_Syntax_isOfKind(x_22, x_23);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_79; uint8_t x_80; 
x_27 = l_Lean_Syntax_getArg(x_17, x_8);
lean_dec(x_17);
x_79 = l_Lean_nullKind___closed__2;
lean_inc(x_27);
x_80 = l_Lean_Syntax_isOfKind(x_27, x_79);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = l___private_Init_Lean_Elab_Term_11__isExplicit___closed__1;
if (x_81 == 0)
{
uint8_t x_82; 
lean_dec(x_2);
x_82 = 0;
x_28 = x_82;
goto block_78;
}
else
{
uint8_t x_83; lean_object* x_84; 
lean_dec(x_27);
lean_dec(x_1);
x_83 = 1;
x_84 = l_Lean_Elab_Term_elabFunCore(x_22, x_2, x_83, x_3, x_4);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_88; 
x_85 = l_Lean_Syntax_getArgs(x_27);
x_86 = lean_array_get_size(x_85);
lean_dec(x_85);
x_87 = lean_nat_dec_eq(x_86, x_21);
x_88 = l_coeDecidableEq(x_87);
if (x_88 == 0)
{
uint8_t x_89; 
lean_dec(x_2);
x_89 = lean_nat_dec_eq(x_86, x_8);
lean_dec(x_86);
x_28 = x_89;
goto block_78;
}
else
{
uint8_t x_90; lean_object* x_91; 
lean_dec(x_86);
lean_dec(x_27);
lean_dec(x_1);
x_90 = 1;
x_91 = l_Lean_Elab_Term_elabFunCore(x_22, x_2, x_90, x_3, x_4);
return x_91;
}
}
block_78:
{
uint8_t x_29; 
x_29 = l_coeDecidableEq(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_1);
x_30 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = l_Lean_Syntax_getArg(x_27, x_21);
lean_dec(x_27);
x_32 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
lean_inc(x_31);
x_33 = l_Lean_Syntax_isOfKind(x_31, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l___private_Init_Lean_Elab_Term_11__isExplicit___closed__1;
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_31);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_1);
x_35 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_Syntax_getArg(x_31, x_8);
lean_dec(x_31);
lean_inc(x_3);
x_37 = l_Lean_Elab_Term_elabType(x_36, x_3, x_4);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_38);
x_41 = 1;
lean_inc(x_3);
lean_inc(x_40);
x_42 = l_Lean_Elab_Term_elabFunCore(x_22, x_40, x_41, x_3, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Elab_Term_ensureHasType(x_1, x_40, x_43, x_3, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_40);
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
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
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; 
x_54 = l_Lean_Syntax_getArgs(x_31);
x_55 = lean_array_get_size(x_54);
lean_dec(x_54);
x_56 = lean_unsigned_to_nat(2u);
x_57 = lean_nat_dec_eq(x_55, x_56);
lean_dec(x_55);
x_58 = l_coeDecidableEq(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_31);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_1);
x_59 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_4);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Lean_Syntax_getArg(x_31, x_8);
lean_dec(x_31);
lean_inc(x_3);
x_61 = l_Lean_Elab_Term_elabType(x_60, x_3, x_4);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_62);
x_65 = 1;
lean_inc(x_3);
lean_inc(x_64);
x_66 = l_Lean_Elab_Term_elabFunCore(x_22, x_64, x_65, x_3, x_63);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Elab_Term_ensureHasType(x_1, x_64, x_67, x_3, x_68);
return x_69;
}
else
{
uint8_t x_70; 
lean_dec(x_64);
lean_dec(x_3);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 0);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_66);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_61);
if (x_74 == 0)
{
return x_61;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_61, 0);
x_76 = lean_ctor_get(x_61, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_61);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabExplicit");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabExplicit), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabChoice");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabChoice), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabChoice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_choiceKind___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabProj");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabProj), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabProj(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_proj___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabArrayRef");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrayRef), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_arrayRef___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabRawIdent");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabRawIdent), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_identKind___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabSortApp");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabSortApp___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_sortApp___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
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
l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabApp___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabApp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabId___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabId(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabExplicit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabChoice___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabChoice(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabProj___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabProj(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabArrayRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabRawIdent(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabSortApp(lean_io_mk_world());
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
